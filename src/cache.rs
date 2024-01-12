use core::ops::Range;

use embedded_storage_async::nor_flash::NorFlash;

use crate::{calculate_page_address, Error, PageState, MAX_WORD_SIZE};

#[allow(private_bounds)]
pub trait Cache: StateQuery {}

impl<T: StateQuery> Cache for T {}

pub(crate) trait StateQuery {
    fn invalidate_cache_state(&mut self);
    fn mark_dirty(&mut self);
    fn unmark_dirty(&mut self);
    fn is_dirty(&self) -> bool;

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);

    /// Get the state of the page located at the given index
    async fn get_page_state<S: NorFlash>(
        &self,
        flash: &mut S,
        flash_range: Range<u32>,
        page_index: usize,
    ) -> Result<PageState, Error<S::Error>>;
}

pub struct NoCache;

impl StateQuery for NoCache {
    fn invalidate_cache_state(&mut self) {}

    fn mark_dirty(&mut self) {}

    fn unmark_dirty(&mut self) {}

    fn is_dirty(&self) -> bool {
        false
    }

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {
        todo!()
    }

    async fn get_page_state<S: NorFlash>(
        &self,
        flash: &mut S,
        flash_range: Range<u32>,
        page_index: usize,
    ) -> Result<PageState, Error<S::Error>> {
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

        match (start_marked, end_marked) {
            (true, true) => Ok(PageState::Closed),
            (true, false) => Ok(PageState::PartialOpen),
            // Probably an interrupted erase
            (false, true) => Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            }),
            (false, false) => Ok(PageState::Open),
        }
    }
}
