#![cfg_attr(not(test), no_std)]
// #![deny(missing_docs)]
#![doc = include_str!("../README.md")]

// Assumptions made in this crate:
//
// - flash erase size is quite big, aka, this is a paged flash
// - flash write size is quite small, so it writes words and not full pages
// - flash read size is 1, so the flash is byte addressable

use core::{fmt::Debug, ops::Range};
use embedded_storage::nor_flash::NorFlash;

pub mod map;
pub mod queue;

#[cfg(test)]
mod mock_flash;

fn find_first_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    starting_page_index: usize,
    page_state: PageState,
) -> Result<Option<usize>, Error<S::Error>> {
    for page_index in get_pages::<S>(flash_range.clone(), starting_page_index) {
        if page_state == get_page_state::<S>(flash, flash_range.clone(), page_index)? {
            return Ok(Some(page_index));
        }
    }

    Ok(None)
}

/// Get all pages in the flash range from the given start to end (that might wrap back to 0)
fn get_pages<S: NorFlash>(
    flash_range: Range<u32>,
    starting_page_index: usize,
) -> impl DoubleEndedIterator<Item = usize> {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    flash_range
        .step_by(S::ERASE_SIZE)
        .enumerate()
        .map(move |(index, _)| (index + starting_page_index) % page_count)
}

fn next_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    (page_index + 1) % page_count
}

fn previous_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;

    match page_index.checked_sub(1) {
        Some(new_page_index) => new_page_index,
        None => page_count - 1,
    }
}

fn calculate_page_address<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> u32 {
    flash_range.start + (S::ERASE_SIZE * page_index) as u32
}
fn calculate_page_end_address<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> u32 {
    flash_range.start + (S::ERASE_SIZE * (page_index + 1)) as u32
}

fn get_page_state<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<PageState, Error<S::Error>> {
    let page_address = calculate_page_address::<S>(flash_range, page_index);

    let mut buffer = [0; 16];
    flash
        .read(page_address, &mut buffer[..S::READ_SIZE])
        .map_err(Error::Storage)?;
    let start_marker = buffer[0];

    if start_marker != MARKER {
        #[cfg(feature = "defmt")]
        defmt::trace!("Page {} is open", page_index);

        // The page start is not marked, so it is unused
        return Ok(PageState::Open);
    }

    // The page start is marked, so it can be full or partially full
    // We need to look at the end marker to know

    flash
        .read(
            page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
            &mut buffer[..S::READ_SIZE],
        )
        .map_err(Error::Storage)?;
    let end_marker = buffer[S::READ_SIZE - 1];

    if end_marker != MARKER {
        #[cfg(feature = "defmt")]
        defmt::trace!("Page {} is partial open", page_index);
        // The page end is not marked, so it is only partially filled and thus open
        return Ok(PageState::PartialOpen);
    }

    #[cfg(feature = "defmt")]
    defmt::trace!("Page {} is closed", page_index);
    // Both start and end are marked, so this page is closed
    Ok(PageState::Closed)
}

/// Fully closes a page by writing both the start and end marker
fn close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<(), Error<S::Error>> {
    partial_close_page::<S>(flash, flash_range.clone(), page_index)?;

    let current_state = get_page_state::<S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::PartialOpen {
        return Ok(());
    }

    let buffer = [MARKER; 16];
    // Close the end marker
    flash
        .write(
            calculate_page_end_address::<S>(flash_range, page_index) - S::WRITE_SIZE as u32,
            &buffer[..S::WRITE_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(())
}

/// Partially close a page by writing the start marker
fn partial_close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<(), Error<S::Error>> {
    let current_state = get_page_state::<S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::Open {
        return Ok(());
    }

    let buffer = [MARKER; 16];
    // Close the start marker
    flash
        .write(
            calculate_page_address::<S>(flash_range, page_index),
            &buffer[..S::WRITE_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PageState {
    Closed,
    PartialOpen,
    Open,
}

impl PageState {
    /// Returns `true` if the page state is [`Closed`].
    ///
    /// [`Closed`]: PageState::Closed
    #[must_use]
    fn is_closed(&self) -> bool {
        matches!(self, Self::Closed)
    }

    /// Returns `true` if the page state is [`PartialOpen`].
    ///
    /// [`PartialOpen`]: PageState::PartialOpen
    #[must_use]
    fn is_partial_open(&self) -> bool {
        matches!(self, Self::PartialOpen)
    }

    /// Returns `true` if the page state is [`Open`].
    ///
    /// [`Open`]: PageState::Open
    #[must_use]
    fn is_open(&self) -> bool {
        matches!(self, Self::Open)
    }
}

const MARKER: u8 = 0;

/// The main error type
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error<S> {
    /// An error in the storage (flash)
    Storage(S),
    /// The item cannot be stored anymore because the storage is full.
    /// If you get this error some data may be lost.
    FullStorage,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::map::{StorageItem, StorageItemError};

    type MockFlash = mock_flash::MockFlashBase<4, 4, 64>;

    #[derive(Debug, PartialEq, Eq)]
    struct MockStorageItem {
        key: u8,
        value: u8,
    }

    #[derive(Debug, PartialEq, Eq)]
    enum MockStorageItemError {
        BufferTooSmall,
        InvalidKey,
    }

    impl StorageItemError for MockStorageItemError {
        fn is_buffer_too_small(&self) -> bool {
            matches!(self, MockStorageItemError::BufferTooSmall)
        }
    }

    impl StorageItem for MockStorageItem {
        type Key = u8;

        type Error = MockStorageItemError;

        fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
            if buffer.len() < 2 {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            // The serialized value must not be all 0xFF
            if self.key == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            buffer[0] = self.key;
            buffer[1] = self.value;

            Ok(2)
        }

        fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), Self::Error>
        where
            Self: Sized,
        {
            if buffer.len() < 2 {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            if buffer[0] == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            Ok((
                Self {
                    key: buffer[0],
                    value: buffer[1],
                },
                2,
            ))
        }

        fn key(&self) -> Self::Key {
            self.key
        }
    }

    #[test]
    fn test_find_pages() {
        // Page setup:
        // 0: closed
        // 1: closed
        // 2: partial-open
        // 3: open

        let mut flash = MockFlash::new();
        // Page 0 markers
        flash.write(0x000, &[MARKER, 0, 0, 0]).unwrap();
        flash.write(0x100 - 4, &[0, 0, 0, MARKER]).unwrap();
        // Page 1 markers
        flash.write(0x100, &[MARKER, 0, 0, 0]).unwrap();
        flash.write(0x200 - 4, &[0, 0, 0, MARKER]).unwrap();
        // Page 2 markers
        flash.write(0x200, &[MARKER, 0, 0, 0]).unwrap();

        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 0, PageState::Open).unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 0, PageState::PartialOpen).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 1, PageState::PartialOpen).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 2, PageState::PartialOpen).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 3, PageState::Open).unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x200, 0, PageState::PartialOpen).unwrap(),
            None
        );

        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 0, PageState::Closed).unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 1, PageState::Closed).unwrap(),
            Some(1)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 2, PageState::Closed).unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x000..0x400, 3, PageState::Closed).unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(&mut flash, 0x200..0x400, 0, PageState::Closed).unwrap(),
            None
        );
    }
}
