//! A queue (fifo) implementation for storing arbitrary data in flash memory.
//!
//! Use [push] to add data to the fifo and use [peek] and [pop] to get the data back.
//!
//! ```rust
//! # use sequential_storage::queue::{push, peek, pop};
//! # use sequential_storage::cache::NoCache;
//! # use mock_flash::MockFlashBase;
//! # use futures::executor::block_on;
//! # type Flash = MockFlashBase<10, 1, 4096>;
//! # mod mock_flash {
//! #   include!("mock_flash.rs");
//! # }
//! #
//! # fn init_flash() -> Flash {
//! #     Flash::new(mock_flash::WriteCountCheck::Twice, None, false)
//! # }
//! #
//! # block_on(async {
//!
//! // Initialize the flash. This can be internal or external
//! let mut flash = init_flash();
//! // These are the flash addresses in which the crate will operate.
//! // The crate will not read, write or erase outside of this range.
//! let flash_range = 0x1000..0x3000;
//! // We need to give the crate a buffer to work with.
//! // It must be big enough to serialize the biggest value of your storage type in.
//! let mut data_buffer = [0; 128];
//!
//! let my_data = [10, 47, 29];
//!
//! // We can push some data to the queue
//! push(&mut flash, flash_range.clone(), NoCache::new(), &my_data, false).await.unwrap();
//!
//! // We can peek at the oldest data
//!
//! assert_eq!(
//!     &peek(&mut flash, flash_range.clone(), NoCache::new(), &mut data_buffer).await.unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // With popping we get back the oldest data, but that data is now also removed
//!
//! assert_eq!(
//!     &pop(&mut flash, flash_range.clone(), NoCache::new(), &mut data_buffer).await.unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // If we pop again, we find there's no data anymore
//!
//! assert_eq!(
//!     pop(&mut flash, flash_range.clone(), NoCache::new(), &mut data_buffer).await,
//!     Ok(None)
//! );
//! # });
//! ```

use crate::{
    cache::Cache,
    item::{find_next_free_item_spot, is_page_empty, Item, ItemHeader, ItemHeaderIter},
};

use self::cache::{CacheImpl, PageStatesCache};

use super::*;
use embedded_storage_async::nor_flash::MultiwriteNorFlash;

/// Push data into the queue in the given flash memory with the given range.
/// The data can only be taken out with the [pop] function.
///
/// Old data will not be overwritten unless `allow_overwrite_old_data` is true.
/// If it is, then if the queue is full, the oldest data is removed to make space for the new data.
///
/// *Note: If a page is already used and you push more data than the remaining capacity of the page,
/// the entire remaining capacity will go unused because the data is stored on the next page.*
pub async fn push<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    mut cache: impl CacheImpl,
    data: &[u8],
    allow_overwrite_old_data: bool,
) -> Result<(), Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let cache = cache.inner();

    if cache.is_dirty() {
        cache.invalidate_cache_state();
    }

    // Data must fit in a single page
    if data.len()
        > ItemHeader::available_data_bytes::<S>((S::ERASE_SIZE - S::WORD_SIZE * 2) as u32).unwrap()
            as usize
    {
        cache.unmark_dirty();
        return Err(Error::BufferTooBig);
    }

    let current_page = find_youngest_page(flash, flash_range.clone(), cache).await?;

    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), current_page) - S::WORD_SIZE as u32;

    partial_close_page(flash, flash_range.clone(), cache, current_page).await?;

    // Find the last item on the page so we know where we need to write

    let mut next_address = find_next_free_item_spot(
        flash,
        flash_range.clone(),
        cache,
        page_data_start_address,
        page_data_end_address,
        data.len() as u32,
    )
    .await?;

    if next_address.is_none() {
        // No cap left on this page, move to the next page
        let next_page = next_page::<S>(flash_range.clone(), current_page);
        match get_page_state(flash, flash_range.clone(), cache, next_page).await? {
            PageState::Open => {
                close_page(flash, flash_range.clone(), cache, current_page).await?;
                partial_close_page(flash, flash_range.clone(), cache, next_page).await?;
                next_address = Some(
                    calculate_page_address::<S>(flash_range.clone(), next_page)
                        + S::WORD_SIZE as u32,
                );
            }
            state @ PageState::Closed => {
                let next_page_data_start_address =
                    calculate_page_address::<S>(flash_range.clone(), next_page)
                        + S::WORD_SIZE as u32;

                if !allow_overwrite_old_data
                    && !is_page_empty(flash, flash_range.clone(), cache, next_page, Some(state))
                        .await?
                {
                    cache.unmark_dirty();
                    return Err(Error::FullStorage);
                }

                open_page(flash, flash_range.clone(), cache, next_page).await?;
                close_page(flash, flash_range.clone(), cache, current_page).await?;
                partial_close_page(flash, flash_range.clone(), cache, next_page).await?;
                next_address = Some(next_page_data_start_address);
            }
            PageState::PartialOpen => {
                // This should never happen
                return Err(Error::Corrupted {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                });
            }
        }
    }

    Item::write_new(
        flash,
        flash_range.clone(),
        cache,
        next_address.unwrap(),
        data,
    )
    .await?;

    cache.unmark_dirty();
    Ok(())
}

/// Peek at the data from oldest to newest.
///
/// If you also want to remove the data use [pop_many].
///
/// Returns an iterator-like type that can be used to peek into the data.
pub async fn peek_many<S: NorFlash, CI: CacheImpl>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: CI,
) -> Result<PeekIterator<'_, S, CI>, Error<S::Error>> {
    Ok(PeekIterator {
        iter: QueueIterator::new(flash, flash_range, cache).await?,
    })
}

/// Peek at the oldest data.
///
/// If you also want to remove the data use [pop].
///
/// The data is written to the given `data_buffer` and the part that was written is returned.
/// It is valid to only use the length of the returned slice and use the original `data_buffer`.
/// The `data_buffer` may contain extra data on ranges after the returned slice.
/// You should not depend on that data.
///
/// If the data buffer is not big enough an error is returned.
pub async fn peek<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: impl CacheImpl,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    peek_many(flash, flash_range, cache)
        .await?
        .next(data_buffer)
        .await
}

/// Pop the data from oldest to newest.
///
/// If you don't want to remove the data use [peek_many].
///
/// Returns an iterator-like type that can be used to pop the data.
pub async fn pop_many<S: MultiwriteNorFlash, CI: CacheImpl>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: CI,
) -> Result<PopIterator<'_, S, CI>, Error<S::Error>> {
    Ok(PopIterator {
        iter: QueueIterator::new(flash, flash_range, cache).await?,
    })
}

/// Pop the oldest data from the queue.
///
/// If you don't want to remove the data use [peek].
///
/// The data is written to the given `data_buffer` and the part that was written is returned.
/// It is valid to only use the length of the returned slice and use the original `data_buffer`.
/// The `data_buffer` may contain extra data on ranges after the returned slice.
/// You should not depend on that data.
///
/// If the data buffer is not big enough an error is returned.
pub async fn pop<'d, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: impl CacheImpl,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    pop_many(flash, flash_range, cache)
        .await?
        .next(data_buffer)
        .await
}

/// Iterator for pop'ing elements in the queue.
#[derive(Debug)]
pub struct PopIterator<'d, S: MultiwriteNorFlash, CI: CacheImpl> {
    iter: QueueIterator<'d, S, CI>,
}

impl<'d, S: MultiwriteNorFlash, CI: CacheImpl> PopIterator<'d, S, CI> {
    /// Pop the next data.
    ///
    /// The data is written to the given `data_buffer` and the part that was written is returned.
    /// It is valid to only use the length of the returned slice and use the original `data_buffer`.
    /// The `data_buffer` may contain extra data on ranges after the returned slice.
    /// You should not depend on that data.
    ///
    /// If the data buffer is not big enough an error is returned.
    pub async fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<&'m mut [u8]>, Error<S::Error>> {
        if self.iter.cache.inner().is_dirty() {
            self.iter.cache.inner().invalidate_cache_state();
        }

        let reset_point = self.iter.create_reset_point();

        if let Some((item, item_address)) = self.iter.next(data_buffer).await? {
            let (header, data_buffer) = item.destruct();
            let ret = &mut data_buffer[..header.length as usize];

            match header
                .erase_data(
                    self.iter.flash,
                    self.iter.flash_range.clone(),
                    self.iter.cache.inner(),
                    item_address,
                )
                .await
            {
                Ok(_) => {
                    self.iter.cache.inner().unmark_dirty();
                    Ok(Some(ret))
                }
                Err(e) => {
                    self.iter.recover_from_reset_point(reset_point);
                    Err(e)
                }
            }
        } else {
            self.iter.cache.inner().unmark_dirty();
            Ok(None)
        }
    }
}

/// Iterator for peek'ing elements in the queue.
#[derive(Debug)]
pub struct PeekIterator<'d, S: NorFlash, CI: CacheImpl> {
    iter: QueueIterator<'d, S, CI>,
}

impl<'d, S: NorFlash, CI: CacheImpl> PeekIterator<'d, S, CI> {
    /// Peek at the next data.
    ///
    /// The data is written to the given `data_buffer` and the part that was written is returned.
    /// It is valid to only use the length of the returned slice and use the original `data_buffer`.
    /// The `data_buffer` may contain extra data on ranges after the returned slice.
    /// You should not depend on that data.
    ///
    /// If the data buffer is not big enough an error is returned.
    pub async fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<&'m mut [u8]>, Error<S::Error>> {
        if self.iter.cache.inner().is_dirty() {
            self.iter.cache.inner().invalidate_cache_state();
        }

        Ok(self.iter.next(data_buffer).await?.map(|(item, _)| {
            let (header, data_buffer) = item.destruct();
            &mut data_buffer[..header.length as usize]
        }))
    }
}

/// An iterator-like interface for peeking into data stored in flash.
struct QueueIterator<'d, S: NorFlash, CI: CacheImpl> {
    flash: &'d mut S,
    flash_range: Range<u32>,
    cache: CI,
    current_address: CurrentAddress,
}

impl<'d, S: NorFlash, CI: CacheImpl> Debug for QueueIterator<'d, S, CI> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("QueueIterator")
            .field("current_address", &self.current_address)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone)]
enum CurrentAddress {
    Address(u32),
    PageAfter(usize),
}

impl<'d, S: NorFlash, CI: CacheImpl> QueueIterator<'d, S, CI> {
    async fn new(
        flash: &'d mut S,
        flash_range: Range<u32>,
        mut cache: CI,
    ) -> Result<Self, Error<S::Error>> {
        assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
        assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

        assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
        assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

        if cache.inner().is_dirty() {
            cache.inner().invalidate_cache_state();
        }

        let oldest_page = find_oldest_page(flash, flash_range.clone(), cache.inner()).await?;

        // We start at the start of the oldest page
        let current_address = match cache.inner().first_item_after_erased(oldest_page) {
            Some(address) => address,
            None => {
                calculate_page_address::<S>(flash_range.clone(), oldest_page) + S::WORD_SIZE as u32
            }
        };

        Ok(Self {
            flash,
            flash_range,
            cache,
            current_address: CurrentAddress::Address(current_address),
        })
    }

    async fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<(Item<'m>, u32)>, Error<S::Error>> {
        let mut data_buffer = Some(data_buffer);

        if self.cache.inner().is_dirty() {
            self.cache.inner().invalidate_cache_state();
        }

        loop {
            // Get the current page and address based on what was stored
            let (current_page, current_address) = match self.current_address {
                CurrentAddress::PageAfter(previous_page) => {
                    let next_page = next_page::<S>(self.flash_range.clone(), previous_page);
                    if get_page_state(
                        self.flash,
                        self.flash_range.clone(),
                        self.cache.inner(),
                        next_page,
                    )
                    .await?
                    .is_open()
                        || next_page
                            == find_oldest_page(
                                self.flash,
                                self.flash_range.clone(),
                                self.cache.inner(),
                            )
                            .await?
                    {
                        self.cache.inner().unmark_dirty();
                        return Ok(None);
                    }

                    let current_address =
                        calculate_page_address::<S>(self.flash_range.clone(), next_page)
                            + S::WORD_SIZE as u32;

                    self.current_address = CurrentAddress::Address(current_address);

                    (next_page, current_address)
                }
                CurrentAddress::Address(address) => (
                    calculate_page_index::<S>(self.flash_range.clone(), address),
                    address,
                ),
            };

            let page_data_end_address =
                calculate_page_end_address::<S>(self.flash_range.clone(), current_page)
                    - S::WORD_SIZE as u32;

            // Search for the first item with data
            let mut it = ItemHeaderIter::new(current_address, page_data_end_address);
            // No need to worry about cache here since that has been dealt with at the creation of this iterator
            if let (Some(found_item_header), found_item_address) = it
                .traverse(self.flash, |header, _| header.crc.is_none())
                .await?
            {
                let maybe_item = found_item_header
                    .read_item(
                        self.flash,
                        data_buffer.take().unwrap(),
                        found_item_address,
                        page_data_end_address,
                    )
                    .await?;

                match maybe_item {
                    item::MaybeItem::Corrupted(header, db) => {
                        let next_address = header.next_item_address::<S>(found_item_address);
                        self.current_address = if next_address >= page_data_end_address {
                            CurrentAddress::PageAfter(current_page)
                        } else {
                            CurrentAddress::Address(next_address)
                        };
                        data_buffer.replace(db);
                    }
                    item::MaybeItem::Erased(_, _) => unreachable!("Item is already erased"),
                    item::MaybeItem::Present(item) => {
                        let next_address = item.header.next_item_address::<S>(found_item_address);
                        self.current_address = if next_address >= page_data_end_address {
                            CurrentAddress::PageAfter(current_page)
                        } else {
                            CurrentAddress::Address(next_address)
                        };
                        // Return the item we found
                        self.cache.inner().unmark_dirty();
                        return Ok(Some((item, found_item_address)));
                    }
                }
            } else {
                self.current_address = CurrentAddress::PageAfter(current_page);
            }
        }
    }

    fn create_reset_point(&self) -> QueueIteratorResetPoint {
        QueueIteratorResetPoint(self.current_address.clone())
    }

    fn recover_from_reset_point(&mut self, reset_point: QueueIteratorResetPoint) {
        self.current_address = reset_point.0;
    }
}

struct QueueIteratorResetPoint(CurrentAddress);

/// Find the largest size of data that can be stored.
///
/// This will read through the entire flash to find the largest chunk of
/// data that can be stored, taking alignment requirements of the item into account.
///
/// If there is no space left, `None` is returned.
pub async fn find_max_fit<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    mut cache: impl CacheImpl,
) -> Result<Option<u32>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let cache = cache.inner();

    if cache.is_dirty() {
        cache.invalidate_cache_state();
    }

    let current_page = find_youngest_page(flash, flash_range.clone(), cache).await?;

    // Check if we have space on the next page
    let next_page = next_page::<S>(flash_range.clone(), current_page);
    match get_page_state(flash, flash_range.clone(), cache, next_page).await? {
        state @ PageState::Closed => {
            if is_page_empty(flash, flash_range.clone(), cache, next_page, Some(state)).await? {
                cache.unmark_dirty();
                return Ok(Some((S::ERASE_SIZE - (2 * S::WORD_SIZE)) as u32));
            }
        }
        PageState::Open => {
            cache.unmark_dirty();
            return Ok(Some((S::ERASE_SIZE - (2 * S::WORD_SIZE)) as u32));
        }
        PageState::PartialOpen => {
            // This should never happen
            return Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        }
    };

    // See how much space we can find in the current page.
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), current_page) - S::WORD_SIZE as u32;

    let next_item_address = match cache.first_item_after_written(current_page) {
        Some(next_item_address) => next_item_address,
        None => {
            ItemHeaderIter::new(
                cache
                    .first_item_after_erased(current_page)
                    .unwrap_or(page_data_start_address),
                page_data_end_address,
            )
            .traverse(flash, |_, _| true)
            .await?
            .1
        }
    };

    cache.unmark_dirty();
    Ok(ItemHeader::available_data_bytes::<S>(
        page_data_end_address - next_item_address,
    ))
}

async fn find_youngest_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
) -> Result<usize, Error<S::Error>> {
    let last_used_page =
        find_first_page(flash, flash_range.clone(), cache, 0, PageState::PartialOpen).await?;

    if let Some(last_used_page) = last_used_page {
        return Ok(last_used_page);
    }

    // We have no partial open page. Search for an open page to start in
    let first_open_page = find_first_page(flash, flash_range, cache, 0, PageState::Open).await?;

    if let Some(first_open_page) = first_open_page {
        return Ok(first_open_page);
    }

    // All pages are closed... This is not correct.
    Err(Error::Corrupted {
        #[cfg(feature = "_test")]
        backtrace: std::backtrace::Backtrace::capture(),
    })
}

async fn find_oldest_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut Cache<impl PageStatesCache, impl PagePointersCache>,
) -> Result<usize, Error<S::Error>> {
    let youngest_page = find_youngest_page(flash, flash_range.clone(), cache).await?;

    // The oldest page is the first non-open page after the youngest page
    let oldest_closed_page =
        find_first_page(flash, flash_range, cache, youngest_page, PageState::Closed).await?;

    Ok(oldest_closed_page.unwrap_or(youngest_page))
}

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
pub async fn try_repair<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    mut cache: impl CacheImpl,
) -> Result<(), Error<S::Error>> {
    cache.inner().invalidate_cache_state();
    drop(cache);

    crate::try_general_repair(flash, flash_range.clone()).await?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use crate::cache::PrivateCacheImpl;
    use crate::mock_flash::{FlashAverageStatsResult, FlashStatsResult, WriteCountCheck};

    use super::*;
    use futures_test::test;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    async fn peek_and_overwrite_old_data() {
        let mut flash = MockFlashTiny::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x00..0x40;
        let mut data_buffer = AlignedBuf([0; 1024]);
        const DATA_SIZE: usize = 22;

        assert_eq!(
            peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap(),
            None
        );

        data_buffer[..DATA_SIZE].copy_from_slice(&[0xAA; DATA_SIZE]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[..DATA_SIZE],
            false,
        )
        .await
        .unwrap();
        assert_eq!(
            &peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xAA; DATA_SIZE]
        );
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xBB; DATA_SIZE]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[..DATA_SIZE],
            false,
        )
        .await
        .unwrap();
        assert_eq!(
            &peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xAA; DATA_SIZE]
        );

        // Flash is full, this should fail
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xCC; DATA_SIZE]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[..DATA_SIZE],
            false,
        )
        .await
        .unwrap_err();
        // Now we allow overwrite, so it should work
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xDD; DATA_SIZE]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[..DATA_SIZE],
            true,
        )
        .await
        .unwrap();

        assert_eq!(
            &peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xBB; DATA_SIZE]
        );
        assert_eq!(
            &pop(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xBB; DATA_SIZE]
        );

        assert_eq!(
            &peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xDD; DATA_SIZE]
        );
        assert_eq!(
            &pop(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xDD; DATA_SIZE]
        );

        assert_eq!(
            peek(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap(),
            None
        );
        assert_eq!(
            pop(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap(),
            None
        );
    }

    #[test]
    async fn push_pop() {
        let mut flash = MockFlashBig::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x000..0x1000;
        let mut data_buffer = AlignedBuf([0; 1024]);

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 512 + 1];

            push(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &data,
                true,
            )
            .await
            .unwrap();
            assert_eq!(
                &peek(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap()
                .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                &pop(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap()
                .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                peek(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    async fn push_pop_tiny() {
        let mut flash = MockFlashTiny::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x00..0x40;
        let mut data_buffer = AlignedBuf([0; 1024]);

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            println!("PUSH");
            push(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &data,
                true,
            )
            .await
            .unwrap();
            assert_eq!(
                &peek(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap()
                .unwrap()[..],
                &data,
                "At {i}"
            );
            println!("POP");
            assert_eq!(
                &pop(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap()
                .unwrap()[..],
                &data,
                "At {i}"
            );
            println!("PEEK");
            assert_eq!(
                peek(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &mut data_buffer
                )
                .await
                .unwrap(),
                None,
                "At {i}"
            );
            println!("DONE");
        }
    }

    #[test]
    /// Same as [push_lots_then_pop_lots], except with added peeking and using the iterator style
    async fn push_peek_pop_many() {
        let mut flash = MockFlashBig::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x000..0x1000;
        let mut data_buffer = AlignedBuf([0; 1024]);

        let mut push_stats = FlashStatsResult::default();
        let mut pushes = 0;
        let mut peek_stats = FlashStatsResult::default();
        let mut peeks = 0;
        let mut pop_stats = FlashStatsResult::default();
        let mut pops = 0;

        let mut cache = cache::NoCache::new();

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &mut cache, &data, false)
                    .await
                    .unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }

            let start_snapshot = flash.stats_snapshot();
            let mut peeker = peek_many(&mut flash, flash_range.clone(), &mut cache)
                .await
                .unwrap();
            peek_stats += start_snapshot.compare_to(peeker.iter.flash.stats_snapshot());
            for i in 0..5 {
                let start_snapshot = peeker.iter.flash.stats_snapshot();
                let mut data = vec![i as u8; 50];
                assert_eq!(
                    peeker.next(&mut data_buffer).await.unwrap(),
                    Some(&mut data[..]),
                    "At {i}"
                );
                peeks += 1;
                peek_stats += start_snapshot.compare_to(peeker.iter.flash.stats_snapshot());
            }

            let start_snapshot = flash.stats_snapshot();
            let mut popper = pop_many(&mut flash, flash_range.clone(), &mut cache)
                .await
                .unwrap();
            pop_stats += start_snapshot.compare_to(popper.iter.flash.stats_snapshot());
            for i in 0..5 {
                let start_snapshot = popper.iter.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    &popper.next(&mut data_buffer).await.unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(popper.iter.flash.stats_snapshot());
            }

            for i in 20..25 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &mut cache, &data, false)
                    .await
                    .unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }

            let start_snapshot = flash.stats_snapshot();
            let mut peeker = peek_many(&mut flash, flash_range.clone(), &mut cache)
                .await
                .unwrap();
            peek_stats += start_snapshot.compare_to(peeker.iter.flash.stats_snapshot());
            for i in 5..25 {
                let start_snapshot = peeker.iter.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    &peeker.next(&mut data_buffer).await.unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                peeks += 1;
                peek_stats += start_snapshot.compare_to(peeker.iter.flash.stats_snapshot());
            }

            let start_snapshot = flash.stats_snapshot();
            let mut popper = pop_many(&mut flash, flash_range.clone(), &mut cache)
                .await
                .unwrap();
            pop_stats += start_snapshot.compare_to(popper.iter.flash.stats_snapshot());
            for i in 5..25 {
                let start_snapshot = popper.iter.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    &popper.next(&mut data_buffer).await.unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(popper.iter.flash.stats_snapshot());
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        approx::assert_relative_eq!(
            push_stats.take_average(pushes),
            FlashAverageStatsResult {
                avg_erases: 0.0612,
                avg_reads: 17.902,
                avg_writes: 3.1252,
                avg_bytes_read: 113.7248,
                avg_bytes_written: 60.5008
            }
        );
        approx::assert_relative_eq!(
            peek_stats.take_average(peeks),
            FlashAverageStatsResult {
                avg_erases: 0.0,
                avg_reads: 8.0188,
                avg_writes: 0.0,
                avg_bytes_read: 96.4224,
                avg_bytes_written: 0.0
            }
        );
        approx::assert_relative_eq!(
            pop_stats.take_average(pops),
            FlashAverageStatsResult {
                avg_erases: 0.0,
                avg_reads: 8.0188,
                avg_writes: 1.0,
                avg_bytes_read: 96.4224,
                avg_bytes_written: 8.0
            }
        );
    }

    #[test]
    async fn push_lots_then_pop_lots() {
        let mut flash = MockFlashBig::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x000..0x1000;
        let mut data_buffer = AlignedBuf([0; 1024]);

        let mut push_stats = FlashStatsResult::default();
        let mut pushes = 0;
        let mut pop_stats = FlashStatsResult::default();
        let mut pops = 0;

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                push(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &data,
                    false,
                )
                .await
                .unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }

            for i in 0..5 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    &pop(
                        &mut flash,
                        flash_range.clone(),
                        cache::NoCache::new(),
                        &mut data_buffer
                    )
                    .await
                    .unwrap()
                    .unwrap()[..],
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }

            for i in 20..25 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                push(
                    &mut flash,
                    flash_range.clone(),
                    cache::NoCache::new(),
                    &data,
                    false,
                )
                .await
                .unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }

            for i in 5..25 {
                let start_snapshot = flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    &pop(
                        &mut flash,
                        flash_range.clone(),
                        cache::NoCache::new(),
                        &mut data_buffer
                    )
                    .await
                    .unwrap()
                    .unwrap()[..],
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(flash.stats_snapshot());
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        approx::assert_relative_eq!(
            push_stats.take_average(pushes),
            FlashAverageStatsResult {
                avg_erases: 0.0612,
                avg_reads: 17.902,
                avg_writes: 3.1252,
                avg_bytes_read: 113.7248,
                avg_bytes_written: 60.5008
            }
        );
        approx::assert_relative_eq!(
            pop_stats.take_average(pops),
            FlashAverageStatsResult {
                avg_erases: 0.0,
                avg_reads: 82.618,
                avg_writes: 1.0,
                avg_bytes_read: 567.9904,
                avg_bytes_written: 8.0
            }
        );
    }

    #[test]
    async fn pop_with_empty_section() {
        let mut flash = MockFlashTiny::new(WriteCountCheck::Twice, None, true);
        let flash_range = 0x00..0x40;
        let mut data_buffer = AlignedBuf([0; 1024]);

        data_buffer[..20].copy_from_slice(&[0xAA; 20]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[0..20],
            false,
        )
        .await
        .unwrap();
        data_buffer[..20].copy_from_slice(&[0xBB; 20]);
        push(
            &mut flash,
            flash_range.clone(),
            cache::NoCache::new(),
            &data_buffer[0..20],
            false,
        )
        .await
        .unwrap();

        // There's now an unused gap at the end of the first page

        assert_eq!(
            &pop(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xAA; 20]
        );

        assert_eq!(
            &pop(
                &mut flash,
                flash_range.clone(),
                cache::NoCache::new(),
                &mut data_buffer
            )
            .await
            .unwrap()
            .unwrap()[..],
            &[0xBB; 20]
        );
    }

    #[test]
    async fn search_pages() {
        let mut flash = MockFlashBig::new(WriteCountCheck::Twice, None, true);

        const FLASH_RANGE: Range<u32> = 0x000..0x1000;

        close_page(&mut flash, FLASH_RANGE, cache::NoCache::new().inner(), 0)
            .await
            .unwrap();
        close_page(&mut flash, FLASH_RANGE, cache::NoCache::new().inner(), 1)
            .await
            .unwrap();
        partial_close_page(&mut flash, FLASH_RANGE, cache::NoCache::new().inner(), 2)
            .await
            .unwrap();

        assert_eq!(
            find_youngest_page(&mut flash, FLASH_RANGE, cache::NoCache::new().inner())
                .await
                .unwrap(),
            2
        );
        assert_eq!(
            find_oldest_page(&mut flash, FLASH_RANGE, cache::NoCache::new().inner())
                .await
                .unwrap(),
            0
        );
    }
}
