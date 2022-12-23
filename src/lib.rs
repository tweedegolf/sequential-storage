#![cfg_attr(not(test), no_std)]

use core::{fmt::Debug, ops::Range};
use embedded_storage::nor_flash::NorFlash;

#[cfg(test)]
mod mock_flash;

pub fn fetch_item<I: StorageItem, S: NorFlash, const BUFFER_SIZE: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<Option<I>, Error<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    let Some(first_open_page) = find_first_open_page_index::<I, S>(flash, flash_range.clone(), 0)? else {
        // There is no open page, so something is wrong. We'll just reset the flash to recover
        flash.erase(flash_range.start, flash_range.end).map_err(|e| Error::Storage(e))?;
        return Ok(None);
    };

    let page_count = flash_range.len() / S::ERASE_SIZE;
    let available_page_start_addresses = flash_range.clone().step_by(S::ERASE_SIZE);

    // We need to find the page that is

    let mut buffer = [0; BUFFER_SIZE];

    let mut index = flash_range.start;

    todo!()
}

pub fn store_item<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    item: I,
) -> Result<(), Error<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    todo!()
}

fn find_first_open_page_index<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    starting_page_index: usize,
) -> Result<Option<usize>, Error<I::Error, S::Error>> {
    for (page_index, page_address) in get_pages::<S>(flash_range, starting_page_index) {
        let mut buffer = [0; 16];
        flash
            .read(page_address, &mut buffer[..S::READ_SIZE])
            .map_err(|e| Error::Storage(e))?;
        let start_marker = buffer[0];

        if start_marker != MARKER {
            // The page start is not marked, so it is unused
            return Ok(Some(page_index));
        }

        // The page start is marked, so it can be full or partially full
        // We need to look at the end marker to know

        flash
            .read(
                page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
                &mut buffer[..S::READ_SIZE],
            )
            .map_err(|e| Error::Storage(e))?;
        let end_marker = buffer[S::READ_SIZE - 1];

        if end_marker != MARKER {
            // The page end is not marked, so it is only partially filled and thus open
            return Ok(Some(page_index));
        }
    }

    // We should never really get here, but somehow all pages are closed
    Ok(None)
}

fn find_first_closed_page_index<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    starting_page_index: usize,
) -> Result<Option<usize>, Error<I::Error, S::Error>> {
    for (page_index, page_address) in get_pages::<S>(flash_range, starting_page_index) {
        let mut buffer = [0; 16];
        flash
            .read(page_address, &mut buffer[..S::READ_SIZE])
            .map_err(|e| Error::Storage(e))?;
        let start_marker = buffer[0];

        if start_marker != MARKER {
            // The page start is not marked, so it is unused
            continue;
        }

        // The page start is marked, so it can be full or partially full
        // We need to look at the end marker to know

        flash
            .read(
                page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
                &mut buffer[..S::READ_SIZE],
            )
            .map_err(|e| Error::Storage(e))?;
        let end_marker = buffer[S::READ_SIZE - 1];

        if end_marker != MARKER {
            // The page end is not marked, so it is only partially filled and thus open
            continue;
        }

        // Both start and end are marked, so this page is closed
        return Ok(Some(page_index));
    }

    Ok(None)
}

/// Get all pages in the flash range from the given start to end (that might wrap back to 0)
fn get_pages<S: NorFlash>(
    flash_range: Range<u32>,
    starting_page_index: usize,
) -> impl Iterator<Item = (usize, u32)> {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    flash_range
        .step_by(S::ERASE_SIZE)
        .enumerate()
        .cycle()
        .skip(starting_page_index)
        .take(page_count)
}

fn get_page_state<S: NorFlash>(flash: &mut S, page_address: u32) -> PageState {
    
}

enum PageState {
    Closed,
    PartialOpen,
    Open
}

const MARKER: u8 = 0;

pub trait StorageItem {
    type Key: Eq;
    type Error: Debug;

    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error>;
    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), Self::Error>
    where
        Self: Sized;

    fn key(&self) -> Self::Key;
}

#[derive(Debug)]
pub enum Error<I, S> {
    Item(I),
    Storage(S),
}

#[cfg(test)]
mod tests {
    use super::*;

    type MockFlash = mock_flash::MockFlashBase<4, 4, 64>;

    struct MockStorageItem {
        key: u8,
        value: u8,
    }

    impl StorageItem for MockStorageItem {
        type Key = u8;

        type Error = ();

        fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
            if buffer.len() < 2 {
                return Err(());
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
                return Err(());
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
            find_first_open_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 0).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_open_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 1).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_open_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 2).unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_open_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 3).unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_open_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x200, 0).unwrap(),
            None
        );

        assert_eq!(
            find_first_closed_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 0)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_closed_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 1)
                .unwrap(),
            Some(1)
        );
        assert_eq!(
            find_first_closed_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 2)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_closed_page_index::<MockStorageItem, _>(&mut flash, 0x000..0x400, 3)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_closed_page_index::<MockStorageItem, _>(&mut flash, 0x200..0x400, 0)
                .unwrap(),
            None
        );
    }
}
