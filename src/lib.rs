#![cfg_attr(not(any(test, doctest, feature = "_test")), no_std)]
#![deny(missing_docs)]
#![doc = include_str!("../README.md")]

// Assumptions made in this crate:
//
// - flash erase size is quite big, aka, this is a paged flash
// - flash write size is quite small, so it writes words and not full pages

use core::{
    fmt::Debug,
    ops::{ControlFlow, Range},
};
use embedded_storage::nor_flash::NorFlash;

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

/// Try to repair the state of the flash to hopefull get back everything in working order.
/// Care is taken that no data is lost, but this depends on correctly repairing the state and
/// so is only best effort.
///
/// This function might be called after a different function returned the [Error::Corrupted] error.
/// There's no guarantee it will work.
///
/// If this function or the function call after this crate returns [Error::Corrupted], then it's unlikely
/// that the state can be recovered. To at least make everything function again at the cost of losing the data,
/// erase the flash range.
pub fn try_repair<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<(), Error<S::Error>> {
    // Loop through the pages and get their state. If one returns the corrupted error,
    // the page is likely half-erased. Fix for that is to re-erase again to hopefully finish the job.
    for page_index in get_pages::<S>(flash_range.clone(), 0) {
        if matches!(
            get_page_state(flash, flash_range.clone(), page_index),
            Err(Error::Corrupted)
        ) {
            flash
                .erase(
                    calculate_page_address::<S>(flash_range.clone(), page_index),
                    calculate_page_end_address::<S>(flash_range.clone(), page_index),
                )
                .map_err(Error::Storage)?;
        }
    }

    Ok(())
}

/// Find the first page that is in the given page state.
///
/// The search starts at starting_page_index (and wraps around back to 0 if required)
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
fn get_page_state<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<PageState, Error<S::Error>> {
    let page_address = calculate_page_address::<S>(flash_range, page_index);
    let half_marker_bits = (S::READ_SIZE * 8 / 2) as u32;

    let mut buffer = [0; MAX_WORD_SIZE];
    flash
        .read(page_address, &mut buffer[..S::READ_SIZE])
        .map_err(Error::Storage)?;
    let start_marked = buffer[..S::READ_SIZE]
        .iter()
        .map(|marker_byte| marker_byte.count_zeros())
        .sum::<u32>()
        >= half_marker_bits;

    flash
        .read(
            page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
            &mut buffer[..S::READ_SIZE],
        )
        .map_err(Error::Storage)?;
    let end_marked = buffer[..S::READ_SIZE]
        .iter()
        .map(|marker_byte| marker_byte.count_zeros())
        .sum::<u32>()
        >= half_marker_bits;

    match (start_marked, end_marked) {
        (true, true) => Ok(PageState::Closed),
        (true, false) => Ok(PageState::PartialOpen),
        // Probably an interrupted erase
        (false, true) => Err(Error::Corrupted),
        (false, false) => Ok(PageState::Open),
    }
}

/// Fully closes a page by writing both the start and end marker
fn close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<(), Error<S::Error>> {
    let current_state = partial_close_page::<S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::PartialOpen {
        return Ok(());
    }

    let buffer = [MARKER; MAX_WORD_SIZE];
    // Close the end marker
    flash
        .write(
            calculate_page_end_address::<S>(flash_range, page_index) - S::WORD_SIZE as u32,
            &buffer[..S::WORD_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(())
}

/// Partially close a page by writing the start marker
fn partial_close_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<PageState, Error<S::Error>> {
    let current_state = get_page_state::<S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::Open {
        return Ok(current_state);
    }

    let buffer = [MARKER; MAX_WORD_SIZE];
    // Close the start marker
    flash
        .write(
            calculate_page_address::<S>(flash_range, page_index),
            &buffer[..S::WORD_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(match current_state {
        PageState::Closed => PageState::Closed,
        PageState::PartialOpen => PageState::PartialOpen,
        PageState::Open => PageState::PartialOpen,
    })
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
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum Error<S> {
    /// An error in the storage (flash)
    Storage(S),
    /// The item cannot be stored anymore because the storage is full.
    /// If you get this error some data may be lost.
    FullStorage,
    /// It's been detected that the memory is likely corrupted.
    /// You may want to erase the memory to recover.
    Corrupted,
    /// A provided buffer was to big to be used
    BufferTooBig,
    /// A provided buffer was to small to be used (usize is size needed)
    BufferTooSmall(usize),
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

/// Some plumbing for things not yet stable in std/core
trait ResultToControlflow<B, C> {
    fn to_controlflow(self) -> ControlFlow<B, C>;
}

impl<B, C, E> ResultToControlflow<B, C> for Result<C, E>
where
    // T: Into<C>,
    E: Into<B>,
{
    fn to_controlflow(self) -> ControlFlow<B, C> {
        match self {
            Ok(c) => ControlFlow::Continue(c),
            Err(b) => ControlFlow::Break(b.into()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type MockFlash = mock_flash::MockFlashBase<4, 4, 64>;

    #[test]
    fn test_find_pages() {
        // Page setup:
        // 0: closed
        // 1: closed
        // 2: partial-open
        // 3: open

        let mut flash = MockFlash::default();
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
