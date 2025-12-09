//! A queue (fifo) implementation for storing arbitrary data in flash memory.
//!
//! Use [push] to add data to the fifo and use [peek] and [pop] to get the data back.
//!
//! ```rust
//! # use sequential_storage::cache::NoCache;
//! # use sequential_storage::Storage;
//! # use sequential_storage::queue::QueueConfig;
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
//!
//! let mut storage = Storage::new_queue(flash, const { QueueConfig::new(0x1000..0x3000) }, NoCache::new());
//! // We need to give the crate a buffer to work with.
//! // It must be big enough to serialize the biggest value of your storage type in.
//! let mut data_buffer = [0; 128];
//!
//! let my_data = [10, 47, 29];
//!
//! // We can push some data to the queue
//! storage.push(&my_data, false).await.unwrap();
//!
//! // We can peek at the oldest data
//!
//! assert_eq!(
//!     &storage.peek(&mut data_buffer).await.unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // With popping we get back the oldest data, but that data is now also removed
//!
//! assert_eq!(
//!     &storage.pop(&mut data_buffer).await.unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // If we pop again, we find there's no data anymore
//!
//! assert_eq!(
//!     storage.pop(&mut data_buffer).await,
//!     Ok(None)
//! );
//! # });
//! ```

use crate::item::{Item, ItemHeader, ItemHeaderIter};

use self::{cache::CacheImpl, item::ItemUnborrowed};

use super::*;
use embedded_storage_async::nor_flash::MultiwriteNorFlash;

pub struct QueueConfig<S> {
    flash_range: Range<u32>,
    _phantom: PhantomData<S>,
}

impl<S: NorFlash> QueueConfig<S> {
    pub const fn new(flash_range: Range<u32>) -> Self {
        Self::try_new(flash_range).expect("Queue config must be correct")
    }

    pub const fn try_new(flash_range: Range<u32>) -> Option<Self> {
        if !flash_range.start.is_multiple_of(S::ERASE_SIZE as u32) {
            return None;
        }
        if !flash_range.end.is_multiple_of(S::ERASE_SIZE as u32) {
            return None;
        }

        if S::ERASE_SIZE < S::WORD_SIZE * 4 {
            return None;
        }
        if S::WORD_SIZE > MAX_WORD_SIZE {
            return None;
        }

        Some(Self {
            flash_range,
            _phantom: PhantomData,
        })
    }
}

impl<S: NorFlash, C: CacheImpl> Storage<Queue, S, C> {
    pub const fn new_queue(storage: S, config: QueueConfig<S>, cache: C) -> Self {
        Self {
            flash: storage,
            flash_range: config.flash_range,
            cache,
            _phantom: PhantomData,
        }
    }

    /// Push data into the queue in the given flash memory with the given range.
    /// The data can only be taken out with the [pop] function.
    ///
    /// Old data will not be overwritten unless `allow_overwrite_old_data` is true.
    /// If it is, then if the queue is full, the oldest data is removed to make space for the new data.
    ///
    /// *Note: If a page is already used and you push more data than the remaining capacity of the page,
    /// the entire remaining capacity will go unused because the data is stored on the next page.*
    pub async fn push(
        &mut self,
        data: &[u8],
        allow_overwrite_old_data: bool,
    ) -> Result<(), Error<S::Error>> {
        run_with_auto_repair!(
            function = self.push_inner(data, allow_overwrite_old_data).await,
            repair = self.try_repair().await?
        )
    }

    async fn push_inner(
        &mut self,
        data: &[u8],
        allow_overwrite_old_data: bool,
    ) -> Result<(), Error<S::Error>> {
        if self.cache.is_dirty() {
            self.cache.invalidate_cache_state();
        }

        // Data must fit in a single page
        if data.len() > u16::MAX as usize
            || data.len()
                > calculate_page_size::<S>()
                    .saturating_sub(ItemHeader::data_address::<S>(0) as usize)
        {
            self.cache.unmark_dirty();
            return Err(Error::ItemTooBig);
        }

        let current_page = self.find_youngest_page().await?;

        let page_data_start_address =
            calculate_page_address::<S>(self.flash_range.clone(), current_page)
                + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(self.flash_range.clone(), current_page)
                - S::WORD_SIZE as u32;

        self.partial_close_page(current_page).await?;

        // Find the last item on the page so we know where we need to write

        let mut next_address = self
            .find_next_free_item_spot(
                page_data_start_address,
                page_data_end_address,
                data.len() as u32,
            )
            .await?;

        if next_address.is_none() {
            // No cap left on this page, move to the next page
            let next_page = self.next_page(current_page);
            let next_page_state = self.get_page_state(next_page).await?;
            let single_page = next_page == current_page;

            match (next_page_state, single_page) {
                (PageState::Open, _) => {
                    self.close_page(current_page).await?;
                    self.partial_close_page(next_page).await?;
                    next_address = Some(
                        calculate_page_address::<S>(self.flash_range.clone(), next_page)
                            + S::WORD_SIZE as u32,
                    );
                }
                (PageState::Closed, _) | (PageState::PartialOpen, true) => {
                    let next_page_data_start_address =
                        calculate_page_address::<S>(self.flash_range.clone(), next_page)
                            + S::WORD_SIZE as u32;

                    if !allow_overwrite_old_data
                        && !self.is_page_empty(next_page, Some(next_page_state)).await?
                    {
                        self.cache.unmark_dirty();
                        return Err(Error::FullStorage);
                    }

                    self.open_page(next_page).await?;
                    if !single_page {
                        self.close_page(current_page).await?;
                    }
                    self.partial_close_page(next_page).await?;
                    next_address = Some(next_page_data_start_address);
                }
                (PageState::PartialOpen, false) => {
                    // This should never happen
                    return Err(Error::Corrupted {
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    });
                }
            }
        }

        Item::write_new(
            &mut self.flash,
            self.flash_range.clone(),
            &mut self.cache,
            next_address.unwrap(),
            data,
        )
        .await?;

        self.cache.unmark_dirty();
        Ok(())
    }

    /// Get an iterator-like interface to iterate over the items stored in the queue.
    /// This goes from oldest to newest.
    ///
    /// The iteration happens non-destructively, or in other words it peeks at every item.
    /// The returned entry has a [QueueIteratorEntry::pop] function with which you can decide to pop the item
    /// after you've seen the contents.
    pub async fn iter(&mut self) -> Result<QueueIterator<'_, S, C>, Error<S::Error>> {
        // Note: Corruption repair is done in these functions already
        QueueIterator::new(self).await
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
    pub async fn peek<'d>(
        &mut self,
        data_buffer: &'d mut [u8],
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
        // Note: Corruption repair is done in these functions already
        let mut iterator = self.iter().await?;

        let next_value = iterator.next(data_buffer).await?;

        match next_value {
            Some(entry) => Ok(Some(entry.into_buf())),
            None => Ok(None),
        }
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
    pub async fn pop<'d>(
        &mut self,
        data_buffer: &'d mut [u8],
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        let mut iterator = self.iter().await?;

        let next_value = iterator.next(data_buffer).await?;

        match next_value {
            Some(entry) => Ok(Some(entry.pop().await?)),
            None => Ok(None),
        }
    }

    /// Find the largest size of data that can be stored.
    ///
    /// This will read through the entire flash to find the largest chunk of
    /// data that can be stored, taking alignment requirements of the item into account.
    ///
    /// If there is no space left, `None` is returned.
    pub async fn find_max_fit(&mut self) -> Result<Option<u32>, Error<S::Error>> {
        run_with_auto_repair!(
            function = self.find_max_fit_inner().await,
            repair = self.try_repair().await?
        )
    }

    async fn find_max_fit_inner(&mut self) -> Result<Option<u32>, Error<S::Error>> {
        if self.cache.is_dirty() {
            self.cache.invalidate_cache_state();
        }

        let current_page = self.find_youngest_page().await?;

        // Check if we have space on the next page
        let next_page = self.next_page(current_page);
        match self.get_page_state(next_page).await? {
            state @ PageState::Closed => {
                if self.is_page_empty(next_page, Some(state)).await? {
                    self.cache.unmark_dirty();
                    return Ok(Some((S::ERASE_SIZE - (2 * S::WORD_SIZE)) as u32));
                }
            }
            PageState::Open => {
                self.cache.unmark_dirty();
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
            calculate_page_address::<S>(self.flash_range.clone(), current_page)
                + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(self.flash_range.clone(), current_page)
                - S::WORD_SIZE as u32;

        let next_item_address = match self.cache.first_item_after_written(current_page) {
            Some(next_item_address) => next_item_address,
            None => {
                ItemHeaderIter::new(
                    self.cache
                        .first_item_after_erased(current_page)
                        .unwrap_or(page_data_start_address),
                    page_data_end_address,
                )
                .traverse(&mut self.flash, |_, _| true)
                .await?
                .1
            }
        };

        self.cache.unmark_dirty();
        Ok(ItemHeader::available_data_bytes::<S>(
            page_data_end_address - next_item_address,
        ))
    }

    /// Calculate how much space is left free in the queue (in bytes).
    ///
    /// The number given back is accurate, however there are lots of things that add overhead and padding.
    /// Every push is an item with its own overhead. You can check the overhead per item with [crate::item_overhead_size].
    ///
    /// Furthermore, every item has to fully fit in a page. So if a page has 50 bytes left and you push an item of 60 bytes,
    /// the current page is closed and the item is stored on the next page, 'wasting' the 50 you had.
    ///
    /// So unless you're tracking all this, the returned number should only be used as a rough indication.
    pub async fn space_left(&mut self) -> Result<u32, Error<S::Error>> {
        run_with_auto_repair!(
            function = self.space_left_inner().await,
            repair = self.try_repair().await?
        )
    }

    async fn space_left_inner(&mut self) -> Result<u32, Error<S::Error>> {
        if self.cache.is_dirty() {
            self.cache.invalidate_cache_state();
        }

        let mut total_free_space = 0;

        for page in self.get_pages(0) {
            let state = self.get_page_state(page).await?;
            let page_empty = self.is_page_empty(page, Some(state)).await?;

            if state.is_closed() && !page_empty {
                continue;
            }

            // See how much space we can find in the current page.
            let page_data_start_address =
                calculate_page_address::<S>(self.flash_range.clone(), page) + S::WORD_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(self.flash_range.clone(), page)
                    - S::WORD_SIZE as u32;

            if page_empty {
                total_free_space += page_data_end_address - page_data_start_address;
                continue;
            }

            // Partial open page
            let next_item_address = match self.cache.first_item_after_written(page) {
                Some(next_item_address) => next_item_address,
                None => {
                    ItemHeaderIter::new(
                        self.cache
                            .first_item_after_erased(page)
                            .unwrap_or(page_data_start_address),
                        page_data_end_address,
                    )
                    .traverse(&mut self.flash, |_, _| true)
                    .await?
                    .1
                }
            };

            if ItemHeader::available_data_bytes::<S>(page_data_end_address - next_item_address)
                .is_none()
            {
                // No data fits on this partial open page anymore.
                // So if all data on this is already erased, then this page might as well be counted as empty.
                // We can use [is_page_empty] and lie to to it so it checks the items.
                if self.is_page_empty(page, Some(PageState::Closed)).await? {
                    total_free_space += page_data_end_address - page_data_start_address;
                    continue;
                }
            }

            total_free_space += page_data_end_address - next_item_address;
        }

        self.cache.unmark_dirty();
        Ok(total_free_space)
    }

    async fn find_youngest_page(&mut self) -> Result<usize, Error<S::Error>> {
        let last_used_page = self.find_first_page(0, PageState::PartialOpen).await?;

        if let Some(last_used_page) = last_used_page {
            return Ok(last_used_page);
        }

        // We have no partial open page. Search for a closed page to anker ourselves to
        let first_closed_page = self.find_first_page(0, PageState::Closed).await?;

        let first_open_page = match first_closed_page {
            Some(anchor) => {
                // We have at least one closed page
                // The first one after is the page we need to use
                self.find_first_page(anchor, PageState::Open).await?
            }
            None => {
                // No closed pages and no partial open pages, so all pages should be open
                // Might as well start at page 0
                Some(0)
            }
        };

        if let Some(first_open_page) = first_open_page {
            return Ok(first_open_page);
        }

        // All pages are closed... This is not correct.
        Err(Error::Corrupted {
            #[cfg(feature = "_test")]
            backtrace: std::backtrace::Backtrace::capture(),
        })
    }

    async fn find_oldest_page(&mut self) -> Result<usize, Error<S::Error>> {
        let youngest_page = self.find_youngest_page().await?;

        // The oldest page is the first non-open page after the youngest page
        let oldest_closed_page = self
            .find_first_page(youngest_page, PageState::Closed)
            .await?;

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
    async fn try_repair(&mut self) -> Result<(), Error<S::Error>> {
        self.cache.invalidate_cache_state();

        self.try_general_repair().await?;
        Ok(())
    }

    async fn find_start_address(&mut self) -> Result<NextAddress, Error<S::Error>> {
        if self.cache.is_dirty() {
            self.cache.invalidate_cache_state();
        }

        let oldest_page = self.find_oldest_page().await?;

        // We start at the start of the oldest page
        let current_address = match self.cache.first_item_after_erased(oldest_page) {
            Some(address) => address,
            None => {
                calculate_page_address::<S>(self.flash_range.clone(), oldest_page)
                    + S::WORD_SIZE as u32
            }
        };

        Ok(NextAddress::Address(current_address))
    }
}

#[derive(PartialEq, Eq, Clone, Copy, Debug)]
enum PreviousItemStates {
    AllPopped,
    AllButCurrentPopped,
    Unpopped,
}

/// An iterator-like interface for peeking into data stored in flash with the option to pop it.
pub struct QueueIterator<'s, S: NorFlash, C: CacheImpl> {
    storage: &'s mut Storage<Queue, S, C>,
    next_address: NextAddress,
    previous_item_states: PreviousItemStates,
    oldest_page: usize,
}

impl<S: NorFlash, C: CacheImpl> Debug for QueueIterator<'_, S, C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("QueueIterator")
            .field("current_address", &self.next_address)
            .finish_non_exhaustive()
    }
}

#[derive(Debug, Clone, Copy)]
enum NextAddress {
    Address(u32),
    PageAfter(usize),
}

impl<'s, S: NorFlash, C: CacheImpl> QueueIterator<'s, S, C> {
    async fn new(storage: &'s mut Storage<Queue, S, C>) -> Result<Self, Error<S::Error>> {
        let start_address = run_with_auto_repair!(
            function = storage.find_start_address().await,
            repair = storage.try_repair().await?
        )?;

        let oldest_page = match start_address {
            NextAddress::Address(address) => {
                calculate_page_index::<S>(storage.flash_range.clone(), address)
            }
            NextAddress::PageAfter(index) => storage.next_page(index),
        };

        Ok(Self {
            storage,
            next_address: start_address,
            previous_item_states: PreviousItemStates::AllPopped,
            oldest_page,
        })
    }

    /// Get the next entry.
    ///
    /// If there are no more entries, None is returned.
    ///
    /// The `data_buffer` has to be large enough to be able to hold the largest item in flash.
    pub async fn next<'d, 'q>(
        &'q mut self,
        data_buffer: &'d mut [u8],
    ) -> Result<Option<QueueIteratorEntry<'s, 'd, 'q, S, C>>, Error<S::Error>> {
        // We continue from a place where the current item wasn't popped
        // That means that from now on, the next item will have unpopped items behind it
        if self.previous_item_states == PreviousItemStates::AllButCurrentPopped {
            self.previous_item_states = PreviousItemStates::Unpopped;
        }

        let value = run_with_auto_repair!(
            function = self.next_inner(data_buffer).await,
            repair = self.storage.try_repair().await?
        );

        value.map(|v| {
            v.map(|(item, address)| QueueIteratorEntry {
                iter: self,
                item: item.reborrow(data_buffer),
                address,
            })
        })
    }

    async fn next_inner(
        &mut self,
        data_buffer: &mut [u8],
    ) -> Result<Option<(ItemUnborrowed, u32)>, Error<S::Error>> {
        let mut data_buffer = Some(data_buffer);

        if self.storage.cache.is_dirty() {
            self.storage.cache.invalidate_cache_state();
        }

        loop {
            // Get the current page and address based on what was stored
            let (current_page, current_address) = match self.next_address {
                NextAddress::PageAfter(previous_page) => {
                    let next_page = self.storage.next_page(previous_page);
                    if self.storage.get_page_state(next_page).await?.is_open()
                        || next_page == self.oldest_page
                    {
                        self.storage.cache.unmark_dirty();
                        return Ok(None);
                    }

                    // We now know the previous page was left because there were no items on there anymore
                    // If we know all those items were popped, we can proactively open the previous page
                    // This is amazing for performance
                    if self.previous_item_states == PreviousItemStates::AllPopped {
                        self.storage.open_page(previous_page).await?;
                    }

                    let current_address =
                        calculate_page_address::<S>(self.storage.flash_range.clone(), next_page)
                            + S::WORD_SIZE as u32;

                    self.next_address = NextAddress::Address(current_address);

                    (next_page, current_address)
                }
                NextAddress::Address(address) => (
                    calculate_page_index::<S>(self.storage.flash_range.clone(), address),
                    address,
                ),
            };

            let page_data_end_address =
                calculate_page_end_address::<S>(self.storage.flash_range.clone(), current_page)
                    - S::WORD_SIZE as u32;

            // Search for the first item with data
            let mut it = ItemHeaderIter::new(current_address, page_data_end_address);
            // No need to worry about cache here since that has been dealt with at the creation of this iterator
            if let (Some(found_item_header), found_item_address) = it
                .traverse(&mut self.storage.flash, |header, _| header.crc.is_none())
                .await?
            {
                let maybe_item = found_item_header
                    .read_item(
                        &mut self.storage.flash,
                        data_buffer.take().unwrap(),
                        found_item_address,
                        page_data_end_address,
                    )
                    .await?;

                match maybe_item {
                    item::MaybeItem::Corrupted(header, db) => {
                        let next_address = header.next_item_address::<S>(found_item_address);
                        self.next_address = if next_address >= page_data_end_address {
                            NextAddress::PageAfter(current_page)
                        } else {
                            NextAddress::Address(next_address)
                        };
                        data_buffer.replace(db);
                    }
                    item::MaybeItem::Erased(_, _) => unreachable!("Item is already erased"),
                    item::MaybeItem::Present(item) => {
                        let next_address = item.header.next_item_address::<S>(found_item_address);
                        self.next_address = if next_address >= page_data_end_address {
                            NextAddress::PageAfter(current_page)
                        } else {
                            NextAddress::Address(next_address)
                        };

                        // Record that the current item hasn't been popped (yet)
                        if self.previous_item_states == PreviousItemStates::AllPopped {
                            self.previous_item_states = PreviousItemStates::AllButCurrentPopped;
                        }

                        // Return the item we found
                        self.storage.cache.unmark_dirty();
                        return Ok(Some((item.unborrow(), found_item_address)));
                    }
                }
            } else {
                self.next_address = NextAddress::PageAfter(current_page);
            }
        }
    }
}

/// An entry in the iteration over the queue flash
pub struct QueueIteratorEntry<'s, 'd, 'q, S: NorFlash, CI: CacheImpl> {
    iter: &'q mut QueueIterator<'s, S, CI>,
    address: u32,
    item: Item<'d>,
}

impl<S: NorFlash, CI: CacheImpl> Deref for QueueIteratorEntry<'_, '_, '_, S, CI> {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.item.data()
    }
}

impl<S: NorFlash, CI: CacheImpl> DerefMut for QueueIteratorEntry<'_, '_, '_, S, CI> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.item.data_mut()
    }
}

impl<'d, S: NorFlash, CI: CacheImpl> QueueIteratorEntry<'_, 'd, '_, S, CI> {
    /// Get a mutable reference to the data of this entry, but consume the entry too.
    /// This function has some relaxed lifetime constraints compared to the deref impls.
    pub fn into_buf(self) -> &'d mut [u8] {
        let (header, data) = self.item.destruct();
        &mut data[..header.length as usize]
    }

    /// Pop the data in flash that corresponds to this entry. This makes it so
    /// future peeks won't find this data anymore.
    pub async fn pop(self) -> Result<&'d mut [u8], Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        let (header, data_buffer) = self.item.destruct();
        let ret = &mut data_buffer[..header.length as usize];

        // We're popping ourself, so if all previous but us were popped, then now all are popped again
        if self.iter.previous_item_states == PreviousItemStates::AllButCurrentPopped {
            self.iter.previous_item_states = PreviousItemStates::AllPopped;
        }

        header
            .erase_data(
                &mut self.iter.storage.flash,
                self.iter.storage.flash_range.clone(),
                &mut self.iter.storage.cache,
                self.address,
            )
            .await?;

        self.iter.storage.cache.unmark_dirty();
        Ok(ret)
    }

    /// Get the flash address of the item
    #[cfg(feature = "_test")]
    pub fn address(&self) -> u32 {
        self.address
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        cache::NoCache,
        mock_flash::{FlashAverageStatsResult, FlashStatsResult, WriteCountCheck},
    };

    use super::*;
    use futures_test::test;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    async fn peek_and_overwrite_old_data() {
        let mut storage = Storage::new_queue(
            MockFlashTiny::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x00..0x40) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 1024]);
        const DATA_SIZE: usize = 22;

        assert_eq!(storage.space_left().await.unwrap(), 60);

        assert_eq!(storage.peek(&mut data_buffer).await.unwrap(), None);

        data_buffer[..DATA_SIZE].copy_from_slice(&[0xAA; DATA_SIZE]);
        storage
            .push(&data_buffer[..DATA_SIZE], false)
            .await
            .unwrap();

        assert_eq!(storage.space_left().await.unwrap(), 30);

        assert_eq!(
            storage.peek(&mut data_buffer).await.unwrap().unwrap(),
            &[0xAA; DATA_SIZE]
        );
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xBB; DATA_SIZE]);
        storage
            .push(&data_buffer[..DATA_SIZE], false)
            .await
            .unwrap();

        assert_eq!(storage.space_left().await.unwrap(), 0);

        assert_eq!(
            storage.peek(&mut data_buffer).await.unwrap().unwrap(),
            &[0xAA; DATA_SIZE]
        );

        // Flash is full, this should fail
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xCC; DATA_SIZE]);
        storage
            .push(&data_buffer[..DATA_SIZE], false)
            .await
            .unwrap_err();
        // Now we allow overwrite, so it should work
        data_buffer[..DATA_SIZE].copy_from_slice(&[0xDD; DATA_SIZE]);
        storage.push(&data_buffer[..DATA_SIZE], true).await.unwrap();

        assert_eq!(
            storage.peek(&mut data_buffer).await.unwrap().unwrap(),
            &[0xBB; DATA_SIZE]
        );
        assert_eq!(
            storage.pop(&mut data_buffer).await.unwrap().unwrap(),
            &[0xBB; DATA_SIZE]
        );

        assert_eq!(storage.space_left().await.unwrap(), 30);

        assert_eq!(
            storage.peek(&mut data_buffer).await.unwrap().unwrap(),
            &[0xDD; DATA_SIZE]
        );
        assert_eq!(
            storage.pop(&mut data_buffer).await.unwrap().unwrap(),
            &[0xDD; DATA_SIZE]
        );

        assert_eq!(storage.space_left().await.unwrap(), 60);

        assert_eq!(storage.peek(&mut data_buffer).await.unwrap(), None);
        assert_eq!(storage.pop(&mut data_buffer).await.unwrap(), None);
    }

    #[test]
    async fn push_pop() {
        let mut storage = Storage::new_queue(
            MockFlashBig::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        let mut data_buffer = AlignedBuf([0; 1024]);

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 512 + 1];

            storage.push(&data, true).await.unwrap();
            assert_eq!(
                storage.peek(&mut data_buffer).await.unwrap().unwrap(),
                &data,
                "At {i}"
            );
            assert_eq!(
                storage.pop(&mut data_buffer).await.unwrap().unwrap(),
                &data,
                "At {i}"
            );
            assert_eq!(
                storage.peek(&mut data_buffer).await.unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    async fn push_pop_tiny() {
        let mut storage = Storage::new_queue(
            MockFlashTiny::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x00..0x40) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 1024]);

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            println!("PUSH");
            storage.push(&data, true).await.unwrap();
            assert_eq!(
                storage.peek(&mut data_buffer).await.unwrap().unwrap(),
                &data,
                "At {i}"
            );
            println!("POP");
            assert_eq!(
                storage.pop(&mut data_buffer).await.unwrap().unwrap(),
                &data,
                "At {i}"
            );
            println!("PEEK");
            assert_eq!(
                storage.peek(&mut data_buffer).await.unwrap(),
                None,
                "At {i}"
            );
            println!("DONE");
        }
    }

    #[test]
    /// Same as [push_lots_then_pop_lots], except with added peeking and using the iterator style
    async fn push_peek_pop_many() {
        let mut storage = Storage::new_queue(
            MockFlashBig::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x1000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 1024]);

        let mut push_stats = FlashStatsResult::default();
        let mut pushes = 0;
        let mut peek_stats = FlashStatsResult::default();
        let mut peeks = 0;
        let mut pop_stats = FlashStatsResult::default();
        let mut pops = 0;

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                storage.push(&data, false).await.unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }

            let start_snapshot = storage.flash.stats_snapshot();
            let mut iterator = storage.iter().await.unwrap();
            peek_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            for i in 0..5 {
                let start_snapshot = iterator.storage.flash.stats_snapshot();
                let data = [i as u8; 50];
                assert_eq!(
                    iterator
                        .next(&mut data_buffer)
                        .await
                        .unwrap()
                        .unwrap()
                        .deref(),
                    &data[..],
                    "At {i}"
                );
                peeks += 1;
                peek_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            }

            let start_snapshot = storage.flash.stats_snapshot();
            let mut iterator = storage.iter().await.unwrap();
            pop_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            for i in 0..5 {
                let start_snapshot = iterator.storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    iterator
                        .next(&mut data_buffer)
                        .await
                        .unwrap()
                        .unwrap()
                        .pop()
                        .await
                        .unwrap(),
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            }

            for i in 20..25 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                storage.push(&data, false).await.unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }

            let start_snapshot = storage.flash.stats_snapshot();
            let mut iterator = storage.iter().await.unwrap();
            peek_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            for i in 5..25 {
                let start_snapshot = iterator.storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    iterator
                        .next(&mut data_buffer)
                        .await
                        .unwrap()
                        .unwrap()
                        .deref(),
                    &data,
                    "At {i}"
                );
                peeks += 1;
                peek_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            }

            let start_snapshot = storage.flash.stats_snapshot();
            let mut iterator = storage.iter().await.unwrap();
            pop_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            for i in 5..25 {
                let start_snapshot = iterator.storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    iterator
                        .next(&mut data_buffer)
                        .await
                        .unwrap()
                        .unwrap()
                        .pop()
                        .await
                        .unwrap(),
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(iterator.storage.flash.stats_snapshot());
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        approx::assert_relative_eq!(
            push_stats.take_average(pushes),
            FlashAverageStatsResult {
                avg_erases: 0.0,
                avg_reads: 16.864,
                avg_writes: 3.1252,
                avg_bytes_read: 105.4112,
                avg_bytes_written: 60.5008
            }
        );
        approx::assert_relative_eq!(
            peek_stats.take_average(peeks),
            FlashAverageStatsResult {
                avg_erases: 0.0052,
                avg_reads: 3.8656,
                avg_writes: 0.0,
                avg_bytes_read: 70.4256,
                avg_bytes_written: 0.0
            }
        );
        approx::assert_relative_eq!(
            pop_stats.take_average(pops),
            FlashAverageStatsResult {
                avg_erases: 0.0572,
                avg_reads: 3.7772,
                avg_writes: 1.0,
                avg_bytes_read: 69.7184,
                avg_bytes_written: 8.0
            }
        );
    }

    #[test]
    async fn push_lots_then_pop_lots() {
        let mut storage = Storage::new_queue(
            MockFlashBig::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x1000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 1024]);

        let mut push_stats = FlashStatsResult::default();
        let mut pushes = 0;
        let mut pop_stats = FlashStatsResult::default();
        let mut pops = 0;

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                storage.push(&data, false).await.unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }

            for i in 0..5 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    storage.pop(&mut data_buffer).await.unwrap().unwrap(),
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }

            for i in 20..25 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                storage.push(&data, false).await.unwrap();
                pushes += 1;
                push_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }

            for i in 5..25 {
                let start_snapshot = storage.flash.stats_snapshot();
                let data = vec![i as u8; 50];
                assert_eq!(
                    storage.pop(&mut data_buffer).await.unwrap().unwrap(),
                    &data,
                    "At {i}"
                );
                pops += 1;
                pop_stats += start_snapshot.compare_to(storage.flash.stats_snapshot());
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        approx::assert_relative_eq!(
            push_stats.take_average(pushes),
            FlashAverageStatsResult {
                avg_erases: 0.0,
                avg_reads: 16.864,
                avg_writes: 3.1252,
                avg_bytes_read: 105.4112,
                avg_bytes_written: 60.5008
            }
        );
        approx::assert_relative_eq!(
            pop_stats.take_average(pops),
            FlashAverageStatsResult {
                avg_erases: 0.0624,
                avg_reads: 23.5768,
                avg_writes: 1.0,
                avg_bytes_read: 180.512,
                avg_bytes_written: 8.0
            }
        );
    }

    #[test]
    async fn pop_with_empty_section() {
        let mut storage = Storage::new_queue(
            MockFlashTiny::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x00..0x40) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 1024]);

        data_buffer[..20].copy_from_slice(&[0xAA; 20]);
        storage.push(&data_buffer[0..20], false).await.unwrap();
        data_buffer[..20].copy_from_slice(&[0xBB; 20]);
        storage.push(&data_buffer[0..20], false).await.unwrap();

        // There's now an unused gap at the end of the first page

        assert_eq!(
            storage.pop(&mut data_buffer).await.unwrap().unwrap(),
            &[0xAA; 20]
        );

        assert_eq!(
            storage.pop(&mut data_buffer).await.unwrap().unwrap(),
            &[0xBB; 20]
        );
    }

    #[test]
    async fn search_pages() {
        let mut storage = Storage::new_queue(
            MockFlashBig::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        storage.close_page(0).await.unwrap();
        storage.close_page(1).await.unwrap();
        storage.partial_close_page(2).await.unwrap();

        assert_eq!(storage.find_youngest_page().await.unwrap(), 2);
        assert_eq!(storage.find_oldest_page().await.unwrap(), 0);
    }

    #[test]
    async fn store_too_big_item() {
        let mut storage = Storage::new_queue(
            MockFlashBig::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        storage
            .push(&AlignedBuf([0; 1024 - 4 * 2 - 8]), false)
            .await
            .unwrap();

        assert_eq!(
            storage
                .push(&AlignedBuf([0; 1024 - 4 * 2 - 8 + 1]), false,)
                .await,
            Err(Error::ItemTooBig)
        );
    }

    #[test]
    async fn push_on_single_page() {
        let mut storage = Storage::new_queue(
            mock_flash::MockFlashBase::<1, 4, 256>::new(WriteCountCheck::Twice, None, true),
            const { QueueConfig::new(0x000..0x400) },
            NoCache::new(),
        );

        for _ in 0..100 {
            match storage.push(&[0, 1, 2, 3, 4], true).await {
                Ok(_) => {}
                Err(e) => {
                    println!("{}", storage.print_items().await);
                    panic!("{e}");
                }
            }
        }
    }
}
