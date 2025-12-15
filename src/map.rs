//! Implementation of the map logic.

use core::{marker::PhantomData, mem::size_of};
use embedded_storage_async::nor_flash::MultiwriteNorFlash;

use crate::item::{Item, ItemHeader, ItemIter};

use self::{
    cache::KeyCacheImpl,
    item::{ItemHeaderIter, ItemUnborrowed},
};

use super::{
    Debug, Error, GenericStorage, MAX_WORD_SIZE, NorFlash, NorFlashExt, PageState, Range, cache,
    calculate_page_address, calculate_page_end_address, calculate_page_index, calculate_page_size,
    item, run_with_auto_repair,
};

/// Configuration for a map
pub struct MapConfig<S> {
    flash_range: Range<u32>,
    _phantom: PhantomData<S>,
}

impl<S: NorFlash> MapConfig<S> {
    /// Create a new map configuration. Will panic if the data is invalid.
    /// If you want a fallible version, use [`Self::try_new`].
    #[must_use]
    pub const fn new(flash_range: Range<u32>) -> Self {
        Self::try_new(flash_range).expect("Map config must be correct")
    }

    /// Create a new map configuration. Will return None if the data is invalid
    #[must_use]
    pub const fn try_new(flash_range: Range<u32>) -> Option<Self> {
        if !flash_range.start.is_multiple_of(S::ERASE_SIZE as u32) {
            return None;
        }
        if !flash_range.end.is_multiple_of(S::ERASE_SIZE as u32) {
            return None;
        }
        // At least 2 pages are used
        if flash_range.end - flash_range.start < S::ERASE_SIZE as u32 * 2 {
            return None;
        }

        if S::ERASE_SIZE < S::WORD_SIZE * 3 {
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

/// A map-like storage
///
/// When a key-value is stored, it overwrites the any old items with the same key.
///
/// ## Basic API
///
/// ```rust
/// # use sequential_storage::cache::NoCache;
/// # use sequential_storage::map::{MapConfig, MapStorage};
/// # use mock_flash::MockFlashBase;
/// # use futures::executor::block_on;
/// # type Flash = MockFlashBase<10, 1, 4096>;
/// # mod mock_flash {
/// #   include!("mock_flash.rs");
/// # }
/// # fn init_flash() -> Flash {
/// #     Flash::new(mock_flash::WriteCountCheck::Twice, None, false)
/// # }
///
/// # block_on(async {
/// // Initialize the flash. This can be internal or external
/// let mut flash = init_flash();
///
/// // Create the storage instance
///
/// // We provide the flash addresses in which it will operate.
/// // The storage will not read, write or erase outside of this range.
///
/// // We also put the config in a const block so if the config is bad we'll get a compile time error
///
/// // With the generics we specify that this is a map with `u8` as the key
/// let mut storage = MapStorage::<u8, _, _>::new(flash, const { MapConfig::new(0x1000..0x3000) }, NoCache::new());
///
/// // We need to give the crate a buffer to work with.
/// // It must be big enough to serialize the biggest value of your storage type in,
/// // rounded up to to word alignment of the flash. Some kinds of internal flash may require
/// // this buffer to be aligned in RAM as well.
/// let mut data_buffer = [0; 128];
///
/// // We can fetch an item from the flash. We're using `u8` as our key type and `u32` as our value type.
/// // Nothing is stored in it yet, so it will return None.
///
/// assert_eq!(
///     storage.fetch_item::<u32>(
///         &mut data_buffer,
///         &42,
///     ).await.unwrap(),
///     None
/// );
///
/// // Now we store an item the flash with key 42.
/// // Again we make sure we pass the correct key and value types, u8 and u32.
/// // It is important to do this consistently.
///
/// storage.store_item(
///     &mut data_buffer,
///     &42u8,
///     &104729u32,
/// ).await.unwrap();
///
/// // When we ask for key 42, we now get back a Some with the correct value
///
/// assert_eq!(
///     storage.fetch_item::<u32>(
///         &mut data_buffer,
///         &42,
///     ).await.unwrap(),
///     Some(104729)
/// );
/// # });
/// ```
///
/// For your convenience there are premade implementations for the [Key] and [Value] traits.
pub struct MapStorage<K: Key, S: NorFlash, C: KeyCacheImpl<K>> {
    inner: GenericStorage<S, C>,
    _phantom: PhantomData<K>,
}

impl<S: NorFlash, C: KeyCacheImpl<K>, K: Key> MapStorage<K, S, C> {
    /// Create a new map instance
    /// 
    /// The provided cache instance must be new or must be in the exact correct state for the current flash contents.
    /// If the cache is bad, undesirable things will happen.
    /// So, it's ok to reuse the cache gotten from the [`Self::destroy`] method when the flash hasn't changed since calling destroy.
    pub const fn new(storage: S, config: MapConfig<S>, cache: C) -> Self {
        Self {
            inner: GenericStorage {
                flash: storage,
                flash_range: config.flash_range,
                cache,
            },
            _phantom: PhantomData,
        }
    }

    /// Get the last stored value from the flash that is associated with the given key.
    /// If no value with the key is found, None is returned.
    ///
    /// You must make sure the used type as [Value] is correct for the key used.
    /// If not, there can be wrong values or deserialization errors.
    ///
    /// The data buffer must be long enough to hold the longest serialized data of your [Key] + [Value] types combined,
    /// rounded up to flash word alignment.
    pub async fn fetch_item<'d, V: Value<'d>>(
        &mut self,
        data_buffer: &'d mut [u8],
        search_key: &K,
    ) -> Result<Option<V>, Error<S::Error>> {
        let result = run_with_auto_repair!(
            function = self.fetch_item_with_location(data_buffer, search_key).await,
            repair = self.try_repair(data_buffer).await?
        );

        let Some((item, _, item_key_len)) = result? else {
            return Ok(None);
        };

        let data_len = item.header.length as usize;
        let item_key_len = match item_key_len {
            Some(item_key_len) => item_key_len,
            None => K::get_len(&data_buffer[..data_len])?,
        };

        let (value, _size) =
            V::deserialize_from(&data_buffer[item_key_len..][..data_len - item_key_len])
                .map_err(Error::SerializationError)?;
        Ok(Some(value))
    }

    /// Fetch the item, but with the item unborrowed, the address of the item and the length of the key
    #[allow(clippy::type_complexity)]
    async fn fetch_item_with_location(
        &mut self,
        data_buffer: &mut [u8],
        search_key: &K,
    ) -> Result<Option<(ItemUnborrowed, u32, Option<usize>)>, Error<S::Error>> {
        if self.inner.cache.is_dirty() {
            self.inner.cache.invalidate_cache_state();
        }

        'cache: {
            if let Some(cached_location) = self.inner.cache.key_location(search_key) {
                let page_index = calculate_page_index::<S>(self.flash_range(), cached_location);
                let page_data_end_address =
                    calculate_page_end_address::<S>(self.flash_range(), page_index)
                        - S::WORD_SIZE as u32;

                let Some(header) = ItemHeader::read_new(
                    &mut self.inner.flash,
                    cached_location,
                    page_data_end_address,
                )
                .await?
                else {
                    // The cache points to a non-existing item?
                    #[expect(clippy::assertions_on_constants, reason = "Clippy is wrong here")]
                    {
                        assert!(
                            !cfg!(feature = "_test"),
                            "Wrong cache value. Addr: {cached_location}"
                        );
                    }
                    self.inner.cache.invalidate_cache_state();
                    break 'cache;
                };

                let item = header
                    .read_item(
                        &mut self.inner.flash,
                        data_buffer,
                        cached_location,
                        page_data_end_address,
                    )
                    .await?;

                match item {
                    item::MaybeItem::Corrupted(_, _) | item::MaybeItem::Erased(_, _) => {
                        #[expect(clippy::assertions_on_constants, reason = "Clippy is wrong here")]
                        {
                            assert!(
                                !cfg!(feature = "_test"),
                                "Wrong cache value. Addr: {cached_location}"
                            );
                        }

                        // The cache points to a corrupted or erased item?
                        self.inner.cache.invalidate_cache_state();
                        break 'cache;
                    }
                    item::MaybeItem::Present(item) => {
                        return Ok(Some((item.unborrow(), cached_location, None)));
                    }
                }
            }
        }

        // We need to find the page we were last using. This should be the only partial open page.
        let mut last_used_page = self
            .inner
            .find_first_page(0, PageState::PartialOpen)
            .await?;

        if last_used_page.is_none() {
            // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
            // If the page one before that is closed, then that's the last used page.
            if let Some(first_open_page) = self.inner.find_first_page(0, PageState::Open).await? {
                let previous_page = self.inner.previous_page(first_open_page);
                if self.inner.get_page_state(previous_page).await?.is_closed() {
                    last_used_page = Some(previous_page);
                } else {
                    // The page before the open page is not closed, so it must be open.
                    // This means that all pages are open and that we don't have any items yet.
                    self.inner.cache.unmark_dirty();
                    return Ok(None);
                }
            } else {
                // There are no open pages, so everything must be closed.
                // Something is up and this should never happen.
                // To recover, we will just erase all the flash.
                return Err(Error::Corrupted {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                });
            }
        }

        // We must now find the most recent storage item with the key that was asked for.
        // If we don't find it in the current page, then we check again in the previous page if that page is closed.

        let mut current_page_to_check = last_used_page.unwrap();
        let mut newest_found_item_data = None;

        loop {
            let page_data_start_address =
                calculate_page_address::<S>(self.flash_range(), current_page_to_check)
                    + S::WORD_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(self.flash_range(), current_page_to_check)
                    - S::WORD_SIZE as u32;

            let mut it = ItemIter::new(page_data_start_address, page_data_end_address);
            while let Some((item, address)) = it.next(&mut self.inner.flash, data_buffer).await? {
                let (found_key, found_key_len) = K::deserialize_from(item.data())?;
                if found_key == *search_key {
                    newest_found_item_data = Some((address, found_key_len));
                }
            }

            // We've found the item! We can stop searching
            if let Some((newest_found_item_address, _)) = newest_found_item_data.as_ref() {
                self.inner
                    .cache
                    .notice_key_location(search_key, *newest_found_item_address, false);

                break;
            }

            // We have not found the item. We've got to look in the previous page, but only if that page is closed and contains data.
            let previous_page = self.inner.previous_page(current_page_to_check);

            if self.inner.get_page_state(previous_page).await? != PageState::Closed {
                // We've looked through all the pages with data and couldn't find the item
                self.inner.cache.unmark_dirty();
                return Ok(None);
            }

            current_page_to_check = previous_page;
        }

        self.inner.cache.unmark_dirty();

        // We now need to reread the item because we lost all its data other than its address

        if let Some((newest_found_item_address, newest_found_item_key_len)) = newest_found_item_data
        {
            let item =
                ItemHeader::read_new(&mut self.inner.flash, newest_found_item_address, u32::MAX)
                    .await?
                    .ok_or_else(|| {
                        // How come there's no item header here!? We just found it!
                        Error::Corrupted {
                            #[cfg(feature = "_test")]
                            backtrace: std::backtrace::Backtrace::capture(),
                        }
                    })?
                    .read_item(
                        &mut self.inner.flash,
                        data_buffer,
                        newest_found_item_address,
                        u32::MAX,
                    )
                    .await?;

            Ok(Some((
                item.unwrap()?.unborrow(),
                newest_found_item_address,
                Some(newest_found_item_key_len),
            )))
        } else {
            Ok(None)
        }
    }

    /// Store a key-value pair into flash memory.
    /// It will (logically) overwrite the last value that has the same key.
    ///
    /// The data buffer must be long enough to hold the longest serialized data of your [Key] + [Value] types combined,
    /// rounded up to flash word alignment.
    pub async fn store_item<'d, V: Value<'d>>(
        &mut self,
        data_buffer: &mut [u8],
        key: &K,
        item: &V,
    ) -> Result<(), Error<S::Error>> {
        run_with_auto_repair!(
            function = self.store_item_inner(data_buffer, key, item).await,
            repair = self.try_repair(data_buffer).await?
        )
    }

    async fn store_item_inner(
        &mut self,
        data_buffer: &mut [u8],
        key: &K,
        item: &dyn Value<'_>,
    ) -> Result<(), Error<S::Error>> {
        if self.inner.cache.is_dirty() {
            self.inner.cache.invalidate_cache_state();
        }

        let mut recursion_level = 0;
        loop {
            // Check if we're in an infinite recursion which happens when we don't have enough space to store the new data
            if recursion_level == self.inner.get_pages(0).count() {
                self.inner.cache.unmark_dirty();
                return Err(Error::FullStorage);
            }

            // If there is a partial open page, we try to write in that first if there is enough space
            let next_page_to_use = if let Some(partial_open_page) = self
                .inner
                .find_first_page(0, PageState::PartialOpen)
                .await?
            {
                // We found a partial open page, but at this point it's relatively cheap to do a consistency check
                if !self
                    .inner
                    .get_page_state(self.inner.next_page(partial_open_page))
                    .await?
                    .is_open()
                {
                    // Oh oh, the next page which serves as the buffer page is not open. We're corrupt.
                    // This likely happened because of an unexpected shutdown during data migration from the
                    // then new buffer page to the new partial open page.
                    // The repair function should be able to repair this.
                    return Err(Error::Corrupted {
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    });
                }

                // We've got to search where the free space is since the page starts with items present already

                let page_data_start_address =
                    calculate_page_address::<S>(self.flash_range(), partial_open_page)
                        + S::WORD_SIZE as u32;
                let page_data_end_address =
                    calculate_page_end_address::<S>(self.flash_range(), partial_open_page)
                        - S::WORD_SIZE as u32;

                let key_len = key.serialize_into(data_buffer)?;
                let item_data_length = key_len
                    + item
                        .serialize_into(&mut data_buffer[key_len..])
                        .map_err(Error::SerializationError)?;

                if item_data_length > u16::MAX as usize
                    || item_data_length
                        > calculate_page_size::<S>()
                            .saturating_sub(ItemHeader::data_address::<S>(0) as usize)
                {
                    self.inner.cache.unmark_dirty();
                    return Err(Error::ItemTooBig);
                }

                let free_spot_address = self
                    .inner
                    .find_next_free_item_spot(
                        page_data_start_address,
                        page_data_end_address,
                        item_data_length as u32,
                    )
                    .await?;

                if let Some(free_spot_address) = free_spot_address {
                    self.inner
                        .cache
                        .notice_key_location(key, free_spot_address, true);
                    Item::write_new(
                        &mut self.inner.flash,
                        self.inner.flash_range.clone(),
                        &mut self.inner.cache,
                        free_spot_address,
                        &data_buffer[..item_data_length],
                    )
                    .await?;

                    self.inner.cache.unmark_dirty();
                    return Ok(());
                }

                // The item doesn't fit here, so we need to close this page and move to the next
                self.inner.close_page(partial_open_page).await?;
                Some(self.inner.next_page(partial_open_page))
            } else {
                None
            };

            // If we get here, there was no partial page found or the partial page has now been closed because the item didn't fit.
            // If there was a partial page, then we need to look at the next page. It's supposed to be open since it was the previous empty buffer page.
            // The new buffer page has to be emptied if it was closed.
            // If there was no partial page, we just use the first open page.

            if let Some(next_page_to_use) = next_page_to_use {
                let next_page_state = self.inner.get_page_state(next_page_to_use).await?;

                if !next_page_state.is_open() {
                    // What was the previous buffer page was not open...
                    return Err(Error::Corrupted {
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    });
                }

                // Since we're gonna write data here, let's already partially close the page
                // This could be done after moving the data, but this is more robust in the
                // face of shutdowns and cancellations
                self.inner.partial_close_page(next_page_to_use).await?;

                let next_buffer_page = self.inner.next_page(next_page_to_use);
                let next_buffer_page_state = self.inner.get_page_state(next_buffer_page).await?;

                if !next_buffer_page_state.is_open() {
                    self.migrate_items(data_buffer, next_buffer_page, next_page_to_use)
                        .await?;
                }
            } else {
                // There's no partial open page, so we just gotta turn the first open page into a partial open one
                let Some(first_open_page) = self.inner.find_first_page(0, PageState::Open).await?
                else {
                    // Uh oh, no open pages.
                    // Something has gone wrong.
                    // We should never get here.
                    return Err(Error::Corrupted {
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    });
                };

                self.inner.partial_close_page(first_open_page).await?;
            }

            // If we get here, we just freshly partially closed a new page, so the next loop iteration should succeed.
            recursion_level += 1;
        }
    }

    /// Fully remove an item. Additional calls to fetch with the same key will return None until
    /// a new one is stored again.
    ///
    /// <div class="warning">
    /// This is really slow!
    ///
    /// All items in flash have to be read and deserialized to find the items with the key.
    /// This is unlikely to be cached well.
    ///
    /// Alternatively, e.g. when you don't have a [`MultiwriteNorFlash`] flash, you could store your value inside an Option
    /// and store the value `None` to mark it as erased.
    /// </div>
    pub async fn remove_item(
        &mut self,
        data_buffer: &mut [u8],
        search_key: &K,
    ) -> Result<(), Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        run_with_auto_repair!(
            function = self.remove_item_inner(data_buffer, Some(search_key)).await,
            repair = self.try_repair(data_buffer).await?
        )
    }

    /// Fully remove all stored items. Additional calls to fetch with any key will return None until
    /// new items are stored again.
    ///
    /// <div class="warning">
    /// This might be really slow! This doesn't simply erase flash, but goes through all items and marks them as deleted.
    /// This is better for flash endurance.
    ///
    /// You might want to simply erase the flash range, e.g. if your flash does not implement [`MultiwriteNorFlash`].
    /// Consider using the helper method for that: [`Self::erase_all`].
    /// </div>
    pub async fn remove_all_items(&mut self, data_buffer: &mut [u8]) -> Result<(), Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        run_with_auto_repair!(
            function = self.remove_item_inner(data_buffer, None).await,
            repair = self.try_repair(data_buffer).await?
        )
    }

    /// If `search_key` is None, then all items will be removed
    async fn remove_item_inner(
        &mut self,
        data_buffer: &mut [u8],
        search_key: Option<&K>,
    ) -> Result<(), Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        if let Some(key) = &search_key {
            self.inner.cache.notice_key_erased(key);
        } else {
            self.inner.cache.invalidate_cache_state();
        }

        // Search for the last used page. We're gonna erase from the one after this first.
        // If we get an early shutoff or cancellation, this will make it so that we don't return
        // an old version of the key on the next fetch.
        let last_used_page = self
            .inner
            .find_first_page(0, PageState::PartialOpen)
            .await?
            .unwrap_or_default();

        // Go through all the pages
        for page_index in self.inner.get_pages(self.inner.next_page(last_used_page)) {
            if self.inner.get_page_state(page_index).await?.is_open() {
                // This page is open, we don't have to check it
                continue;
            }

            let page_data_start_address =
                calculate_page_address::<S>(self.flash_range(), page_index) + S::WORD_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(self.flash_range(), page_index)
                    - S::WORD_SIZE as u32;

            // Go through all items on the page
            let mut item_headers =
                ItemHeaderIter::new(page_data_start_address, page_data_end_address);

            while let (Some(item_header), item_address) =
                item_headers.next(&mut self.inner.flash).await?
            {
                let item = item_header
                    .read_item(
                        &mut self.inner.flash,
                        data_buffer,
                        item_address,
                        page_data_end_address,
                    )
                    .await?;

                match item {
                    item::MaybeItem::Corrupted(_, _) | item::MaybeItem::Erased(_, _) => continue,
                    item::MaybeItem::Present(item) => {
                        let item_match = match search_key {
                            Some(search_key) => K::deserialize_from(item.data())?.0 == *search_key,
                            _ => true,
                        };
                        // If this item has the same key as the key we're trying to erase, then erase the item.
                        // But keep going! We need to erase everything.
                        if item_match {
                            item.header
                                .erase_data(
                                    &mut self.inner.flash,
                                    self.inner.flash_range.clone(),
                                    &mut self.inner.cache,
                                    item_address,
                                )
                                .await?;
                        }
                    }
                }
            }
        }

        // We're done, we now know the cache is in a good state
        self.inner.cache.unmark_dirty();

        Ok(())
    }

    /// Get an iterator that iterates over all non-erased & non-corrupted items in the map.
    ///
    /// <div class="warning">
    /// You should be very careful when using the map item iterator:
    /// <ul>
    /// <li>
    /// Because map doesn't erase the items when you insert a new one with the same key,
    /// so it's expected that the iterator returns items with the same key multiple times.
    /// Only the last returned one is the `active` one.
    /// </li>
    /// <li>
    /// The iterator requires ALL items in the storage have the SAME Value type.
    /// If you have different types of items in your map, the iterator might return incorrect data or error.
    /// </li>
    /// </ul>
    /// </div>
    ///
    /// The following is a simple example of how to use the iterator:
    /// ```rust
    /// # use sequential_storage::cache::NoCache;
    /// # use sequential_storage::map::{MapConfig, MapStorage};
    /// # use mock_flash::MockFlashBase;
    /// # use futures::executor::block_on;
    /// # use std::collections::HashMap;
    /// # type Flash = MockFlashBase<10, 1, 4096>;
    /// # mod mock_flash {
    /// #   include!("mock_flash.rs");
    /// # }
    /// # fn init_flash() -> Flash {
    /// #     Flash::new(mock_flash::WriteCountCheck::Twice, None, false)
    /// # }
    ///
    /// # block_on(async {
    /// let mut flash = init_flash();
    ///
    /// let mut storage = MapStorage::<u8, _, _>::new(flash, const { MapConfig::new(0x1000..0x3000) }, NoCache::new());
    /// let mut data_buffer = [0; 128];
    ///
    /// // Create the iterator of map items
    /// let mut iterator = storage.fetch_all_items(
    ///     &mut data_buffer
    /// )
    /// .await
    /// .unwrap();
    ///
    /// let mut all_items = HashMap::new();
    ///
    /// // Iterate through all items, suppose the Key and Value types are u8, u32
    /// while let Some((key, value)) = iterator
    ///     .next::<u32>(&mut data_buffer)
    ///     .await
    ///     .unwrap()
    /// {
    ///     // Do something with the item.
    ///     // Please note that for the same key there might be multiple items returned,
    ///     // the last one is the current active one.
    ///     all_items.insert(key, value);
    /// }
    /// # })
    /// ```
    pub async fn fetch_all_items(
        &mut self,
        data_buffer: &mut [u8],
    ) -> Result<MapItemIter<'_, K, S, C>, Error<S::Error>> {
        // Get the first page index.
        // The first page used by the map is the next page of the `PartialOpen` page or the last `Closed` page
        let first_page = run_with_auto_repair!(
            function = {
                match self
                    .inner
                    .find_first_page(0, PageState::PartialOpen)
                    .await?
                {
                    Some(last_used_page) => {
                        // The next page of the `PartialOpen` page is the first page
                        Ok(self.inner.next_page(last_used_page))
                    }
                    None => {
                        // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
                        // If the page one before that is closed, then that's the last used page.
                        if let Some(first_open_page) =
                            self.inner.find_first_page(0, PageState::Open).await?
                        {
                            let previous_page = self.inner.previous_page(first_open_page);
                            if self.inner.get_page_state(previous_page).await?.is_closed() {
                                // The previous page is closed, so the first_open_page is what we want
                                Ok(first_open_page)
                            } else {
                                // The page before the open page is not closed, so it must be open.
                                // This means that all pages are open and that we don't have any items yet.
                                self.inner.cache.unmark_dirty();
                                Ok(0)
                            }
                        } else {
                            // There are no open pages, so everything must be closed.
                            // Something is up and this should never happen.
                            // To recover, we will just erase all the flash.
                            Err(Error::Corrupted {
                                #[cfg(feature = "_test")]
                                backtrace: std::backtrace::Backtrace::capture(),
                            })
                        }
                    }
                }
            },
            repair = self.try_repair(data_buffer).await?
        )?;

        let start_address =
            calculate_page_address::<S>(self.flash_range(), first_page) + S::WORD_SIZE as u32;
        let end_address =
            calculate_page_end_address::<S>(self.flash_range(), first_page) - S::WORD_SIZE as u32;

        Ok(MapItemIter {
            storage: self,
            first_page,
            current_page_index: first_page,
            current_iter: ItemIter::new(start_address, end_address),
            _key: PhantomData,
        })
    }

    async fn migrate_items(
        &mut self,
        data_buffer: &mut [u8],
        source_page: usize,
        target_page: usize,
    ) -> Result<(), Error<S::Error>> {
        // We need to move the data from the next buffer page to the next_page_to_use, but only if that data
        // doesn't have a newer value somewhere else.

        let mut next_page_write_address =
            calculate_page_address::<S>(self.flash_range(), target_page) + S::WORD_SIZE as u32;

        let mut it = ItemIter::new(
            calculate_page_address::<S>(self.flash_range(), source_page) + S::WORD_SIZE as u32,
            calculate_page_end_address::<S>(self.flash_range(), source_page) - S::WORD_SIZE as u32,
        );
        while let Some((item, item_address)) = it.next(&mut self.inner.flash, data_buffer).await? {
            let (key, _) = K::deserialize_from(item.data())?;

            // We're in a decent state here
            self.inner.cache.unmark_dirty();

            // Search for the newest item with the key we found
            let Some((found_item, found_address, _)) =
                self.fetch_item_with_location(data_buffer, &key).await?
            else {
                // We couldn't even find our own item?
                return Err(Error::Corrupted {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                });
            };

            let found_item = found_item
                .reborrow(data_buffer)
                .ok_or_else(|| Error::LogicBug {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                })?;

            if found_address == item_address {
                self.inner
                    .cache
                    .notice_key_location(&key, next_page_write_address, true);
                found_item
                    .write(
                        &mut self.inner.flash,
                        self.inner.flash_range.clone(),
                        &mut self.inner.cache,
                        next_page_write_address,
                    )
                    .await?;
                next_page_write_address = found_item
                    .header
                    .next_item_address::<S>(next_page_write_address);
            }
        }

        self.inner.open_page(source_page).await?;

        Ok(())
    }

    /// Try to repair the state of the flash to hopefull get back everything in working order.
    /// Care is taken that no data is lost, but this depends on correctly repairing the state and
    /// so is only best effort.
    ///
    /// This function might be called after a different function returned the [`Error::Corrupted`] error.
    /// There's no guarantee it will work.
    ///
    /// If this function or the function call after this crate returns [`Error::Corrupted`], then it's unlikely
    /// that the state can be recovered. To at least make everything function again at the cost of losing the data,
    /// erase the flash range.
    async fn try_repair(&mut self, data_buffer: &mut [u8]) -> Result<(), Error<S::Error>> {
        self.inner.cache.invalidate_cache_state();

        self.inner.try_general_repair().await?;

        // Let's check if we corrupted in the middle of a migration
        if let Some(partial_open_page) = self
            .inner
            .find_first_page(0, PageState::PartialOpen)
            .await?
        {
            let buffer_page = self.inner.next_page(partial_open_page);
            if !self.inner.get_page_state(buffer_page).await?.is_open() {
                // Yes, the migration got interrupted. Let's redo it.
                // To do that, we erase the partial open page first because it contains incomplete data.
                self.inner.open_page(partial_open_page).await?;

                // Then partially close it again
                self.inner.partial_close_page(partial_open_page).await?;

                self.migrate_items(data_buffer, buffer_page, partial_open_page)
                    .await?;
            }
        }

        Ok(())
    }

    /// Resets the flash in the entire given flash range.
    ///
    /// This is just a thin helper function as it just calls the flash's erase function.
    pub fn erase_all(&mut self) -> impl Future<Output = Result<(), Error<S::Error>>> {
        self.inner.erase_all()
    }

    /// Get the minimal overhead size per stored item for the given flash type.
    ///
    /// The associated data of each item is additionally padded to a full flash word size, but that's not part of this number.\
    /// This means the full item length is `returned number + (data length).next_multiple_of(S::WORD_SIZE)`.
    #[must_use]
    pub const fn item_overhead_size() -> u32 {
        GenericStorage::<S, C>::item_overhead_size()
    }

    /// Destroy the instance to get back the flash and the cache.
    ///
    /// The cache can be passed to a new storage instance, but only for the same flash region and if nothing has changed in flash.
    pub fn destroy(self) -> (S, C) {
        self.inner.destroy()
    }

    /// Get a reference to the flash. Mutating the memory is at your own risk.
    pub const fn flash(&mut self) -> &mut S {
        self.inner.flash()
    }

    /// Get the flash range being used
    pub const fn flash_range(&self) -> Range<u32> {
        self.inner.flash_range()
    }

    #[cfg(any(test, feature = "std"))]
    /// Print all items in flash to the returned string
    /// 
    /// This is meant as a debugging utility. The string format is not stable.
    pub fn print_items(&mut self) -> impl Future<Output = String> {
        self.inner.print_items()
    }
}

/// Iterator which iterates all non-erased & non-corrupted items in the map.
///
/// The iterator will return the (Key, Value) tuple when calling `next()`.
/// If the iterator ends, it will return `Ok(None)`.
///
/// The following is a simple example of how to use the iterator:
/// ```rust
/// # use sequential_storage::cache::NoCache;
/// # use sequential_storage::map::{MapConfig, MapStorage};
/// # use mock_flash::MockFlashBase;
/// # use futures::executor::block_on;
/// # use std::collections::HashMap;
/// # type Flash = MockFlashBase<10, 1, 4096>;
/// # mod mock_flash {
/// #   include!("mock_flash.rs");
/// # }
/// # fn init_flash() -> Flash {
/// #     Flash::new(mock_flash::WriteCountCheck::Twice, None, false)
/// # }
///
/// # block_on(async {
/// let mut flash = init_flash();
///
/// let mut storage = MapStorage::<u8, _, _>::new(flash, const { MapConfig::new(0x1000..0x3000) }, NoCache::new());
/// let mut data_buffer = [0; 128];
///
/// // Create the iterator of map items
/// let mut iterator = storage.fetch_all_items(
///     &mut data_buffer
/// )
/// .await
/// .unwrap();
///
/// let mut all_items = HashMap::new();
///
/// // Iterate through all items, suppose the Key and Value types are u8, u32
/// while let Some((key, value)) = iterator
///     .next::<u32>(&mut data_buffer)
///     .await
///     .unwrap()
/// {
///     // Do something with the item.
///     // Please note that for the same key there might be multiple items returned,
///     // the last one is the current active one.
///     all_items.insert(key, value);
/// }
/// # })
/// ```
pub struct MapItemIter<'s, K: Key, S: NorFlash, C: KeyCacheImpl<K>> {
    storage: &'s mut MapStorage<K, S, C>,
    first_page: usize,
    current_page_index: usize,
    pub(crate) current_iter: ItemIter,
    _key: PhantomData<K>,
}

impl<K: Key, S: NorFlash, C: KeyCacheImpl<K>> MapItemIter<'_, K, S, C> {
    /// Get the next item in the iterator. Be careful that the given `data_buffer` should large enough to contain the serialized key and value.
    pub async fn next<'a, V: Value<'a>>(
        &mut self,
        data_buffer: &'a mut [u8],
    ) -> Result<Option<(K, V)>, Error<S::Error>> {
        // Find the next item
        let item = loop {
            if let Some((item, _address)) = self
                .current_iter
                .next(&mut self.storage.inner.flash, data_buffer)
                .await?
            {
                // We've found the next item, quit the loop
                break item;
            }

            // The current page is done, we need to find the next page
            // Find next page which is not open, update `self.current_iter`
            loop {
                self.current_page_index = self.storage.inner.next_page(self.current_page_index);

                // We've looped back to the first page, which means all pages are checked, there's nothing left so we return None
                if self.current_page_index == self.first_page {
                    return Ok(None);
                }

                match self
                    .storage
                    .inner
                    .get_page_state(self.current_page_index)
                    .await
                {
                    Ok(PageState::Closed | PageState::PartialOpen) => {
                        self.current_iter = ItemIter::new(
                            calculate_page_address::<S>(
                                self.storage.inner.flash_range.clone(),
                                self.current_page_index,
                            ) + S::WORD_SIZE as u32,
                            calculate_page_end_address::<S>(
                                self.storage.inner.flash_range.clone(),
                                self.current_page_index,
                            ) - S::WORD_SIZE as u32,
                        );
                        break;
                    }
                    _ => continue,
                }
            }
        };

        let data_len = item.header.length as usize;
        let (key, key_len) = K::deserialize_from(item.data())?;
        let (value, _value_len) = V::deserialize_from(&data_buffer[..data_len][key_len..])
            .map_err(Error::SerializationError)?;

        Ok(Some((key, value)))
    }
}

/// Anything implementing this trait can be used as a key in the map functions.
///
/// It provides a way to serialize and deserialize the key.
///
/// The `Eq` bound is used because we need to be able to compare keys and the
/// `Clone` bound helps us pass the key around.
///
/// The key cannot have a lifetime like the [Value]
pub trait Key: Eq + Clone + Sized {
    /// Serialize the key into the given buffer.
    /// The serialized size is returned.
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError>;
    /// Deserialize the key from the given buffer.
    /// The key is returned together with the serialized length.
    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError>;
    /// Get the length of the key from the buffer.
    /// This is an optimized version of [`Self::deserialize_from`] that doesn't have to deserialize everything.
    fn get_len(buffer: &[u8]) -> Result<usize, SerializationError> {
        Self::deserialize_from(buffer).map(|(_, len)| len)
    }
}

macro_rules! impl_key_num {
    ($int:ty) => {
        impl Key for $int {
            fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
                let self_bytes = self.to_le_bytes();

                match buffer.get_mut(..self_bytes.len()) {
                    Some(buffer) => {
                        buffer.copy_from_slice(&self_bytes);
                        Ok(buffer.len())
                    }
                    None => Err(SerializationError::BufferTooSmall),
                }
            }

            fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
                let value = Self::from_le_bytes(
                    buffer
                        .get(..size_of::<Self>())
                        .ok_or(SerializationError::BufferTooSmall)?
                        .try_into()
                        .unwrap(),
                );
                Ok((value, size_of::<Self>()))
            }

            fn get_len(_buffer: &[u8]) -> Result<usize, SerializationError> {
                Ok(size_of::<Self>())
            }
        }
    };
}

impl_key_num!(u8);
impl_key_num!(u16);
impl_key_num!(u32);
impl_key_num!(u64);
impl_key_num!(u128);
impl_key_num!(i8);
impl_key_num!(i16);
impl_key_num!(i32);
impl_key_num!(i64);
impl_key_num!(i128);

impl<const N: usize> Key for [u8; N] {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        buffer
            .get_mut(..N)
            .ok_or(SerializationError::BufferTooSmall)?
            .copy_from_slice(self);
        Ok(N)
    }

    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
        Ok((
            buffer
                .get(..N)
                .ok_or(SerializationError::BufferTooSmall)?
                .try_into()
                .unwrap(),
            N,
        ))
    }

    fn get_len(_buffer: &[u8]) -> Result<usize, SerializationError> {
        Ok(N)
    }
}

impl Key for () {
    fn serialize_into(&self, _buffer: &mut [u8]) -> Result<usize, SerializationError> {
        Ok(0)
    }

    fn deserialize_from(_buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
        Ok(((), 0))
    }
}

/// The trait that defines how map values are serialized and deserialized.
///
/// It also carries a lifetime so that zero-copy deserialization is supported.
/// Zero-copy serialization is not supported due to technical restrictions.
pub trait Value<'a> {
    /// Serialize the value into the given buffer. If everything went ok, this function returns the length
    /// of the used part of the buffer.
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError>;
    /// Deserialize the value from the buffer. Because of the added lifetime, the implementation can borrow from the
    /// buffer which opens up some zero-copy possibilities.
    ///
    /// The buffer will be the same length as the serialize function returned for this value. Though note that the length
    /// is written from flash, so bitflips can affect that (though the length is separately crc-protected) and the key deserialization might
    /// return a wrong length.
    ///
    /// Returns the decoded value and the amount of bytes used from the buffer.
    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized;
}

impl<'a> Value<'a> for bool {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        <u8 as Value>::serialize_into(&u8::from(*self), buffer)
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized,
    {
        let (value, size) = <u8 as Value>::deserialize_from(buffer)?;
        Ok((value != 0, size))
    }
}

impl<'a, T: Value<'a>> Value<'a> for Option<T> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        if let Some(val) = self {
            let mut size = 0;
            size += <bool as Value>::serialize_into(&true, buffer)?;
            size += <T as Value>::serialize_into(
                val,
                buffer
                    .get_mut(size..)
                    .ok_or(SerializationError::BufferTooSmall)?,
            )?;
            Ok(size)
        } else {
            <bool as Value>::serialize_into(&false, buffer)
        }
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized,
    {
        let (is_some, tag_size) = <bool as Value>::deserialize_from(buffer)?;
        if is_some {
            let (value, value_size) = <T as Value>::deserialize_from(
                buffer
                    .get(tag_size..)
                    .ok_or(SerializationError::BufferTooSmall)?,
            )?;
            Ok((Some(value), tag_size + value_size))
        } else {
            Ok((None, tag_size))
        }
    }
}

impl<'a> Value<'a> for &'a [u8] {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
        buffer
            .get_mut(..self.len())
            .ok_or(SerializationError::BufferTooSmall)?
            .copy_from_slice(self);
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<(Self, usize), SerializationError>
    where
        Self: Sized,
    {
        Ok((buffer, buffer.len()))
    }
}

macro_rules! impl_map_item_num {
    ($num:ty) => {
        impl<'a> Value<'a> for $num {
            fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
                let self_bytes = self.to_le_bytes();

                match buffer.get_mut(..self_bytes.len()) {
                    Some(buffer) => {
                        buffer.copy_from_slice(&self_bytes);
                        Ok(buffer.len())
                    }
                    None => Err(SerializationError::BufferTooSmall),
                }
            }

            fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
                let value = Self::from_le_bytes(
                    buffer
                        .get(..size_of::<Self>())
                        .ok_or(SerializationError::BufferTooSmall)?
                        .try_into()
                        .unwrap(),
                );
                Ok((value, size_of::<Self>()))
            }
        }

        // Also implement `Value` for arrays of numbers.
        impl<'a, const N: usize> Value<'a> for [$num; N] {
            fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, SerializationError> {
                let elem_size = size_of::<$num>();

                let buffer = buffer
                    .get_mut(0..elem_size * N)
                    .ok_or(SerializationError::BufferTooSmall)?;

                for (chunk, number) in buffer.chunks_exact_mut(elem_size).zip(self.iter()) {
                    chunk.copy_from_slice(&number.to_le_bytes())
                }
                Ok(elem_size * N)
            }

            fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), SerializationError> {
                let elem_size = size_of::<$num>();
                if buffer.len() < elem_size * N {
                    return Err(SerializationError::BufferTooSmall);
                }

                let mut array = [0 as $num; N];
                for (chunk, number) in buffer.chunks_exact(elem_size).zip(array.iter_mut()) {
                    *number = <$num>::from_le_bytes(chunk.try_into().unwrap());
                }
                Ok((array, elem_size * N))
            }
        }
    };
}

impl_map_item_num!(u8);
impl_map_item_num!(u16);
impl_map_item_num!(u32);
impl_map_item_num!(u64);
impl_map_item_num!(u128);
impl_map_item_num!(i8);
impl_map_item_num!(i16);
impl_map_item_num!(i32);
impl_map_item_num!(i64);
impl_map_item_num!(i128);
impl_map_item_num!(f32);
impl_map_item_num!(f64);

/// Error for map value (de)serialization.
///
/// This error type is predefined (in contrast to using generics) to save many kilobytes of binary size.
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum SerializationError {
    /// The provided buffer was too small.
    BufferTooSmall,
    /// The serialization could not succeed because the data was not in order. (e.g. too big to fit)
    InvalidData,
    /// The deserialization could not succeed because the bytes are in an invalid format.
    InvalidFormat,
    /// An implementation defined error that might contain more information than the other predefined
    /// error variants.
    Custom(i32),
}

impl core::fmt::Display for SerializationError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SerializationError::BufferTooSmall => write!(f, "Buffer too small"),
            SerializationError::InvalidData => write!(f, "Invalid data"),
            SerializationError::InvalidFormat => write!(f, "Invalid format"),
            SerializationError::Custom(val) => write!(f, "Custom error: {val}"),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{AlignedBuf, cache::NoCache, mock_flash};

    use super::*;
    use futures_test::test;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    async fn store_and_fetch() {
        let mut storage = MapStorage::<u8, _, _>::new(
            MockFlashBig::default(),
            MapConfig::new(0x000..0x1000),
            cache::NoCache::new(),
        );

        let mut data_buffer = AlignedBuf([0; 128]);

        let start_snapshot = storage.flash().stats_snapshot();

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &0)
            .await
            .unwrap();
        assert_eq!(item, None);

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &60)
            .await
            .unwrap();
        assert_eq!(item, None);

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &0xFF)
            .await
            .unwrap();
        assert_eq!(item, None);

        storage
            .store_item(&mut data_buffer, &0u8, &[5u8])
            .await
            .unwrap();
        storage
            .store_item(&mut data_buffer, &0u8, &[5u8, 6])
            .await
            .unwrap();

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &0)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(item, &[5, 6]);

        storage
            .store_item(&mut data_buffer, &1u8, &[2u8, 2, 2, 2, 2, 2])
            .await
            .unwrap();

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &0)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(item, &[5, 6]);

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &1)
            .await
            .unwrap()
            .unwrap();
        assert_eq!(item, &[2, 2, 2, 2, 2, 2]);

        for index in 0..4000 {
            storage
                .store_item(
                    &mut data_buffer,
                    &((index % 10) as u8),
                    &vec![(index % 10) as u8 * 2; index % 10].as_slice(),
                )
                .await
                .unwrap();
        }

        for i in 0..10 {
            let item = storage
                .fetch_item::<&[u8]>(&mut data_buffer, &i)
                .await
                .unwrap()
                .unwrap();
            assert_eq!(item, &vec![(i % 10) * 2; (i % 10) as usize]);
        }

        for _ in 0..4000 {
            storage
                .store_item(&mut data_buffer, &11u8, &[0; 10])
                .await
                .unwrap();
        }

        for i in 0..10 {
            let item = storage
                .fetch_item::<&[u8]>(&mut data_buffer, &i)
                .await
                .unwrap()
                .unwrap();
            assert_eq!(item, &vec![(i % 10) * 2; (i % 10) as usize]);
        }

        println!(
            "{:?}",
            start_snapshot.compare_to(storage.flash().stats_snapshot()),
        );
    }

    #[test]
    async fn store_too_many_items() {
        const UPPER_BOUND: u8 = 3;

        let mut storage = MapStorage::new(
            MockFlashTiny::default(),
            const { MapConfig::new(0x00..0x40) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            println!("Storing {i:?}");

            storage
                .store_item(&mut data_buffer, &i, &vec![i; i as usize].as_slice())
                .await
                .unwrap();
        }

        assert_eq!(
            storage
                .store_item(
                    &mut data_buffer,
                    &UPPER_BOUND,
                    &vec![0; UPPER_BOUND as usize].as_slice(),
                )
                .await,
            Err(Error::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = storage
                .fetch_item::<&[u8]>(&mut data_buffer, &i)
                .await
                .unwrap()
                .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item, vec![i; i as usize]);
        }
    }

    #[test]
    async fn store_too_many_items_big() {
        const UPPER_BOUND: u8 = 68;

        let mut storage = MapStorage::new(
            MockFlashBig::default(),
            const { MapConfig::new(0x0000..0x1000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            println!("Storing {i:?}");

            storage
                .store_item(&mut data_buffer, &i, &vec![i; i as usize].as_slice())
                .await
                .unwrap();
        }

        assert_eq!(
            storage
                .store_item(
                    &mut data_buffer,
                    &UPPER_BOUND,
                    &vec![0; UPPER_BOUND as usize].as_slice(),
                )
                .await,
            Err(Error::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = storage
                .fetch_item::<&[u8]>(&mut data_buffer, &i)
                .await
                .unwrap()
                .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item, vec![i; i as usize]);
        }
    }

    #[test]
    async fn store_many_items_big() {
        let mut storage = MapStorage::new(
            mock_flash::MockFlashBase::<4, 1, 4096>::default(),
            const { MapConfig::new(0x0000..0x4000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 128]);

        const LENGHT_PER_KEY: [usize; 24] = [
            11, 13, 6, 13, 13, 10, 2, 3, 5, 36, 1, 65, 4, 6, 1, 15, 10, 7, 3, 15, 9, 3, 4, 5,
        ];

        for _ in 0..100 {
            #[allow(clippy::needless_range_loop)]
            for i in 0..24 {
                storage
                    .store_item(
                        &mut data_buffer,
                        &(i as u16),
                        &vec![i as u8; LENGHT_PER_KEY[i]].as_slice(),
                    )
                    .await
                    .unwrap();
            }
        }

        #[allow(clippy::needless_range_loop)]
        for i in 0..24 {
            let item = storage
                .fetch_item::<&[u8]>(&mut data_buffer, &(i as u16))
                .await
                .unwrap()
                .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item, vec![i as u8; LENGHT_PER_KEY[i]]);
        }
    }

    #[test]
    async fn remove_items() {
        let mut storage = MapStorage::new(
            mock_flash::MockFlashBase::<4, 1, 4096>::new(
                mock_flash::WriteCountCheck::Twice,
                None,
                true,
            ),
            const { MapConfig::new(0x0000..0x4000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 128]);

        // Add some data to flash
        for j in 0..10 {
            for i in 0..24 {
                storage
                    .store_item(
                        &mut data_buffer,
                        &(i as u8),
                        &vec![i as u8; j + 2].as_slice(),
                    )
                    .await
                    .unwrap();
            }
        }

        for j in (0..24).rev() {
            // Are all things still in flash that we expect?
            for i in 0..=j {
                assert!(
                    storage
                        .fetch_item::<&[u8]>(&mut data_buffer, &i)
                        .await
                        .unwrap()
                        .is_some()
                );
            }

            // Remove the item
            storage.remove_item(&mut data_buffer, &j).await.unwrap();

            // Are all things still in flash that we expect?
            for i in 0..j {
                assert!(
                    storage
                        .fetch_item::<&[u8]>(&mut data_buffer, &i)
                        .await
                        .unwrap()
                        .is_some()
                );
            }

            assert!(
                storage
                    .fetch_item::<&[u8]>(&mut data_buffer, &j)
                    .await
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    async fn remove_all() {
        let mut storage = MapStorage::new(
            mock_flash::MockFlashBase::<4, 1, 4096>::new(
                mock_flash::WriteCountCheck::Twice,
                None,
                true,
            ),
            const { MapConfig::new(0x0000..0x4000) },
            NoCache::new(),
        );
        let mut data_buffer = AlignedBuf([0; 128]);

        // Add some data to flash
        for value in 0..10 {
            for key in 0..24u8 {
                storage
                    .store_item(&mut data_buffer, &key, &vec![key; value + 2].as_slice())
                    .await
                    .unwrap();
            }
        }

        // Sanity check that we can find all the keys we just added.
        for key in 0..24u8 {
            assert!(
                storage
                    .fetch_item::<&[u8]>(&mut data_buffer, &key)
                    .await
                    .unwrap()
                    .is_some()
            );
        }

        // Remove all the items
        storage.remove_all_items(&mut data_buffer).await.unwrap();

        // Verify that none of the keys are present in flash.
        for key in 0..24 {
            assert!(
                storage
                    .fetch_item::<&[u8]>(&mut data_buffer, &key)
                    .await
                    .unwrap()
                    .is_none()
            );
        }
    }

    #[test]
    async fn store_too_big_item() {
        let mut storage = MapStorage::new(
            MockFlashBig::new(mock_flash::WriteCountCheck::Twice, None, true),
            const { MapConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        storage
            .store_item(&mut [0; 1024], &0u8, &[0u8; 1024 - 4 * 2 - 8 - 1])
            .await
            .unwrap();

        assert_eq!(
            storage
                .store_item(&mut [0; 1024], &0u8, &[0u8; 1024 - 4 * 2 - 8 - 1 + 1],)
                .await,
            Err(Error::ItemTooBig)
        );
    }

    #[test]
    async fn item_iterator() {
        const UPPER_BOUND: u8 = 64;
        let mut storage = MapStorage::new(
            MockFlashBig::default(),
            const { MapConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            storage
                .store_item(&mut data_buffer, &i, &vec![i; i as usize].as_slice())
                .await
                .unwrap();
        }

        // Save 10 times for key 1
        for i in 0..10 {
            storage
                .store_item(&mut data_buffer, &1u8, &vec![i; i as usize].as_slice())
                .await
                .unwrap();
        }

        let mut map_iter = storage.fetch_all_items(&mut data_buffer).await.unwrap();

        let mut count = 0;
        let mut last_value_buffer = [0u8; 64];
        let mut last_value_length = 0;
        while let Ok(Some((key, value))) = map_iter.next::<&[u8]>(&mut data_buffer).await {
            if key == 1 {
                // This is the key we stored multiple times, record the last value
                last_value_length = value.len();
                last_value_buffer[..value.len()].copy_from_slice(value);
            } else {
                assert_eq!(value, vec![key; key as usize]);
                count += 1;
            }
        }

        assert_eq!(last_value_length, 9);
        assert_eq!(
            &last_value_buffer[..last_value_length],
            vec![9u8; 9].as_slice()
        );

        // Check total number of fetched items, +1 since we didn't count key 1
        assert_eq!(count + 1, UPPER_BOUND);
    }

    #[test]
    async fn store_unit_key() {
        let mut storage = MapStorage::new(
            MockFlashBig::default(),
            const { MapConfig::new(0x000..0x1000) },
            NoCache::new(),
        );

        let mut data_buffer = AlignedBuf([0; 128]);

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &())
            .await
            .unwrap();
        assert_eq!(item, None);

        storage
            .store_item(&mut data_buffer, &(), &[5u8])
            .await
            .unwrap();
        storage
            .store_item(&mut data_buffer, &(), &[5u8, 6])
            .await
            .unwrap();

        let item = storage
            .fetch_item::<&[u8]>(&mut data_buffer, &())
            .await
            .unwrap()
            .unwrap();
        assert_eq!(item, &[5, 6]);
    }

    #[test]
    async fn option_value() {
        let mut buffer = [0; 2];

        assert_eq!(Some(42u8).serialize_into(&mut buffer), Ok(2));
        assert_eq!(Option::<u8>::deserialize_from(&buffer), Ok((Some(42u8), 2)));
        assert_eq!(buffer, [1, 42]);

        let mut buffer = [0; 1];

        assert_eq!(Option::<u8>::None.serialize_into(&mut buffer), Ok(1));
        assert_eq!(Option::<u8>::deserialize_from(&buffer), Ok((None, 1)));
        assert_eq!(buffer, [0]);
    }

    #[test]
    async fn array_value() {
        let mut buffer = [0; 3];
        assert_eq!(Value::serialize_into(&[1u8, 2, 3], &mut buffer), Ok(3));
        assert_eq!(buffer, [1, 2, 3]);
        assert_eq!(
            <[u8; 3] as Value>::deserialize_from(&buffer),
            Ok(([1, 2, 3], 3))
        );

        let mut buffer = [0; 4];
        assert_eq!(
            Value::serialize_into(&[0x1234u16, 0x5678], &mut buffer),
            Ok(4)
        );
        assert_eq!(buffer, [0x34, 0x12, 0x78, 0x56]);
        assert_eq!(
            <[u16; 2]>::deserialize_from(&buffer),
            Ok(([0x1234, 0x5678], 4))
        );
    }
}
