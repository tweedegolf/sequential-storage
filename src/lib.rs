#![cfg_attr(not(any(test, doctest, feature = "_test")), no_std)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

// Assumptions made in this crate:
//
// - flash erase size is quite big, aka, this is a paged flash
// - flash write size is quite small, so it writes words and not full pages

use cache::{Cache, PagePointersCache, PageStatesCache};
use core::{
    fmt::Debug,
    ops::{Deref, DerefMut, Range},
};
use embedded_storage_async::nor_flash::NorFlash;

use crate::cache::NoCache;

pub mod cache;
mod item;
pub mod map;
pub mod queue;

#[cfg(any(test, doctest, feature = "_test"))]
/// An in-memory flash type that can be used for mocking.
pub mod mock_flash;

/// The biggest wordsize we support.
///
/// Stm32 internal flash has 256-bit words, so 32 bytes.
/// Many flashes have 4-byte or 1-byte words.
const MAX_WORD_SIZE: usize = 32;

// Type representing buffer aligned to 4 byte boundary.
#[repr(align(4))]
pub(crate) struct AlignedBuf<const SIZE: usize>(pub(crate) [u8; SIZE]);
impl<const SIZE: usize> Deref for AlignedBuf<SIZE> {
    type Target = [u8];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const SIZE: usize> DerefMut for AlignedBuf<SIZE> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

async fn try_general_repair<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<(), Error<S::Error>> {
    use crate::cache::PrivateCacheImpl;

    // Loop through the pages and get their state. If one returns the corrupted error,
    // the page is likely half-erased. Fix for that is to re-erase again to hopefully finish the job.
    for page_index in get_pages::<S>(flash_range.clone(), 0) {
        if matches!(
            get_page_state(
                flash,
                flash_range.clone(),
                NoCache::new().inner(),
                page_index
            )
            .await,
            Err(Error::Corrupted { .. })
        ) {
            open_page(
                flash,
                flash_range.clone(),
                NoCache::new().inner(),
                page_index,
            )
            .await?;
        }
    }

    Ok(())
}

/// Find the first page that is in the given page state.
///
/// The search starts at starting_page_index (and wraps around back to 0 if required)
async fn find_first_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
    starting_page_index: usize,
    page_state: PageState,
) -> Result<Option<usize>, Error<S::Error>> {
    for page_index in get_pages::<S>(flash_range.clone(), starting_page_index) {
        if page_state == get_page_state::<S>(flash, flash_range.clone(), cache, page_index).await? {
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

/// Get the next page index (wrapping around to 0 if required)
fn next_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    (page_index + 1) % page_count
}

/// Get the previous page index (wrapping around to the biggest page if required)
fn previous_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;

    match page_index.checked_sub(1) {
        Some(new_page_index) => new_page_index,
        None => page_count - 1,
    }
}

/// Calculate the first address of the given page
const fn calculate_page_address<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> u32 {
    flash_range.start + (S::ERASE_SIZE * page_index) as u32
}
/// Calculate the last address (exclusive) of the given page
const fn calculate_page_end_address<S: NorFlash>(
    flash_range: Range<u32>,
    page_index: usize,
) -> u32 {
    flash_range.start + (S::ERASE_SIZE * (page_index + 1)) as u32
}
/// Get the page index from any address located inside that page
#[allow(unused)]
const fn calculate_page_index<S: NorFlash>(flash_range: Range<u32>, address: u32) -> usize {
    (address - flash_range.start) as usize / S::ERASE_SIZE
}

/// The marker being used for page states
const MARKER: u8 = 0;

/// Get the state of the page located at the given index
async fn get_page_state<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
    page_index: usize,
) -> Result<PageState, Error<S::Error>> {
    if let Some(cached_page_state) = cache.get_page_state(page_index) {
        return Ok(cached_page_state);
    }

    let page_address = calculate_page_address::<S>(flash_range, page_index);
    /// We only care about the data in the first byte to aid shutdown/cancellation.
    /// But we also don't want it to be too too definitive because we want to survive the occasional bitflip.
    /// So only half of the byte needs to be zero.
    const HALF_MARKER_BITS: u32 = 4;

    let mut buffer = [0; MAX_WORD_SIZE];
    flash
        .read(page_address, &mut buffer[..S::READ_SIZE])
        .await
        .map_err(|e| Error::Storage {
            value: e,
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })?;
    let start_marked = buffer[..S::READ_SIZE]
        .iter()
        .map(|marker_byte| marker_byte.count_zeros())
        .sum::<u32>()
        >= HALF_MARKER_BITS;

    flash
        .read(
            page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
            &mut buffer[..S::READ_SIZE],
        )
        .await
        .map_err(|e| Error::Storage {
            value: e,
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })?;
    let end_marked = buffer[..S::READ_SIZE]
        .iter()
        .map(|marker_byte| marker_byte.count_zeros())
        .sum::<u32>()
        >= HALF_MARKER_BITS;

    let discovered_state = match (start_marked, end_marked) {
        (true, true) => PageState::Closed,
        (true, false) => PageState::PartialOpen,
        // Probably an interrupted erase
        (false, true) => {
            return Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })
        }
        (false, false) => PageState::Open,
    };

    // Not dirty because nothing changed and nothing can be inconsistent
    cache.notice_page_state(page_index, discovered_state, false);

    Ok(discovered_state)
}

/// Erase the page to open it again
async fn open_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
    page_index: usize,
) -> Result<(), Error<S::Error>> {
    cache.notice_page_state(page_index, PageState::Open, true);

    flash
        .erase(
            calculate_page_address::<S>(flash_range.clone(), page_index),
            calculate_page_end_address::<S>(flash_range.clone(), page_index),
        )
        .await
        .map_err(|e| Error::Storage {
            value: e,
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })?;

    Ok(())
}

/// Fully closes a page by writing both the start and end marker
async fn close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
    page_index: usize,
) -> Result<(), Error<S::Error>> {
    let current_state =
        partial_close_page::<S>(flash, flash_range.clone(), cache, page_index).await?;

    if current_state != PageState::PartialOpen {
        return Ok(());
    }

    cache.notice_page_state(page_index, PageState::Closed, true);

    let buffer = AlignedBuf([MARKER; MAX_WORD_SIZE]);
    // Close the end marker
    flash
        .write(
            calculate_page_end_address::<S>(flash_range, page_index) - S::WORD_SIZE as u32,
            &buffer[..S::WORD_SIZE],
        )
        .await
        .map_err(|e| Error::Storage {
            value: e,
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })?;

    Ok(())
}

/// Partially close a page by writing the start marker
async fn partial_close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
    page_index: usize,
) -> Result<PageState, Error<S::Error>> {
    let current_state = get_page_state::<S>(flash, flash_range.clone(), cache, page_index).await?;

    if current_state != PageState::Open {
        return Ok(current_state);
    }

    let new_state = match current_state {
        PageState::Closed => PageState::Closed,
        PageState::PartialOpen => PageState::PartialOpen,
        PageState::Open => PageState::PartialOpen,
    };

    cache.notice_page_state(page_index, new_state, true);

    let buffer = AlignedBuf([MARKER; MAX_WORD_SIZE]);
    // Close the start marker
    flash
        .write(
            calculate_page_address::<S>(flash_range, page_index),
            &buffer[..S::WORD_SIZE],
        )
        .await
        .map_err(|e| Error::Storage {
            value: e,
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })?;

    Ok(new_state)
}

/// The state of a page
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PageState {
    /// This page was fully written and has now been sealed
    Closed,
    /// This page has been written to, but may have some space left over
    PartialOpen,
    /// This page is fully erased
    Open,
}

#[allow(dead_code)]
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

/// The main error type
#[non_exhaustive]
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error<S> {
    /// An error in the storage (flash)
    Storage {
        /// The error value
        value: S,
        #[cfg(feature = "_test")]
        /// Backtrace made at the construction of the error
        backtrace: std::backtrace::Backtrace,
    },
    /// The item cannot be stored anymore because the storage is full.
    /// If you get this error some data may be lost.
    FullStorage,
    /// It's been detected that the memory is likely corrupted.
    /// You may want to erase the memory to recover.
    Corrupted {
        #[cfg(feature = "_test")]
        /// Backtrace made at the construction of the error
        backtrace: std::backtrace::Backtrace,
    },
    /// A provided buffer was to big to be used
    BufferTooBig,
    /// A provided buffer was to small to be used (usize is size needed)
    BufferTooSmall(usize),
}

impl<S: PartialEq> PartialEq for Error<S> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Storage { value: l_value, .. }, Self::Storage { value: r_value, .. }) => {
                l_value == r_value
            }
            (Self::BufferTooSmall(l0), Self::BufferTooSmall(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

/// Round up the the given number to align with the wordsize of the flash.
/// If the number is already aligned, it is not changed.
const fn round_up_to_alignment<S: NorFlash>(value: u32) -> u32 {
    let alignment = S::WORD_SIZE as u32;
    match value % alignment {
        0 => value,
        r => value + (alignment - r),
    }
}

/// Round up the the given number to align with the wordsize of the flash.
/// If the number is already aligned, it is not changed.
const fn round_up_to_alignment_usize<S: NorFlash>(value: usize) -> usize {
    round_up_to_alignment::<S>(value as u32) as usize
}

/// Round down the the given number to align with the wordsize of the flash.
/// If the number is already aligned, it is not changed.
const fn round_down_to_alignment<S: NorFlash>(value: u32) -> u32 {
    let alignment = S::WORD_SIZE as u32;
    (value / alignment) * alignment
}

/// Round down the the given number to align with the wordsize of the flash.
/// If the number is already aligned, it is not changed.
const fn round_down_to_alignment_usize<S: NorFlash>(value: usize) -> usize {
    round_down_to_alignment::<S>(value as u32) as usize
}

/// Extension trait to get the overall word size, which is the largest of the write and read word size
trait NorFlashExt {
    /// The largest of the write and read word size
    const WORD_SIZE: usize;
}

impl<S: NorFlash> NorFlashExt for S {
    const WORD_SIZE: usize = if Self::WRITE_SIZE > Self::READ_SIZE {
        Self::WRITE_SIZE
    } else {
        Self::READ_SIZE
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cache::PrivateCacheImpl;
    use futures_test::test;

    type MockFlash = mock_flash::MockFlashBase<4, 4, 64>;

    async fn write_aligned(
        flash: &mut MockFlash,
        offset: u32,
        bytes: &[u8],
    ) -> Result<(), mock_flash::MockFlashError> {
        let mut buf = AlignedBuf([0; 256]);
        buf[..bytes.len()].copy_from_slice(bytes);
        flash.write(offset, &buf[..bytes.len()]).await
    }

    #[test]
    async fn test_find_pages() {
        // Page setup:
        // 0: closed
        // 1: closed
        // 2: partial-open
        // 3: open

        let mut flash = MockFlash::default();
        // Page 0 markers
        write_aligned(&mut flash, 0x000, &[MARKER, 0, 0, 0])
            .await
            .unwrap();
        write_aligned(&mut flash, 0x100 - 4, &[0, 0, 0, MARKER])
            .await
            .unwrap();
        // Page 1 markers
        write_aligned(&mut flash, 0x100, &[MARKER, 0, 0, 0])
            .await
            .unwrap();
        write_aligned(&mut flash, 0x200 - 4, &[0, 0, 0, MARKER])
            .await
            .unwrap();
        // Page 2 markers
        write_aligned(&mut flash, 0x200, &[MARKER, 0, 0, 0])
            .await
            .unwrap();

        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                0,
                PageState::Open
            )
            .await
            .unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                0,
                PageState::PartialOpen
            )
            .await
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                1,
                PageState::PartialOpen
            )
            .await
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                2,
                PageState::PartialOpen
            )
            .await
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                3,
                PageState::Open
            )
            .await
            .unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x200,
                cache::NoCache::new().inner(),
                0,
                PageState::PartialOpen
            )
            .await
            .unwrap(),
            None
        );

        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                0,
                PageState::Closed
            )
            .await
            .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                1,
                PageState::Closed
            )
            .await
            .unwrap(),
            Some(1)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                2,
                PageState::Closed
            )
            .await
            .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x000..0x400,
                cache::NoCache::new().inner(),
                3,
                PageState::Closed
            )
            .await
            .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page(
                &mut flash,
                0x200..0x400,
                cache::NoCache::new().inner(),
                0,
                PageState::Closed
            )
            .await
            .unwrap(),
            None
        );
    }
}
