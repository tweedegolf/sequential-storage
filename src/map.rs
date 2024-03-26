//! A module for storing key-value pairs in flash with minimal erase cycles.
//!
//! When a key-value is stored, it overwrites the any old items with the same key.
//!
//! ## Basic API:
//!
//! ```rust
//! # use sequential_storage::map::{store_item, fetch_item};
//! # use sequential_storage::cache::NoCache;
//! # use mock_flash::MockFlashBase;
//! # use futures::executor::block_on;
//! # type Flash = MockFlashBase<10, 1, 4096>;
//! # mod mock_flash {
//! #   include!("mock_flash.rs");
//! # }
//! # fn init_flash() -> Flash {
//! #     Flash::new(mock_flash::WriteCountCheck::Twice, None, false)
//! # }
//!
//! # block_on(async {
//! // Initialize the flash. This can be internal or external
//! let mut flash = init_flash();
//! // These are the flash addresses in which the crate will operate.
//! // The crate will not read, write or erase outside of this range.
//! let flash_range = 0x1000..0x3000;
//! // We need to give the crate a buffer to work with.
//! // It must be big enough to serialize the biggest value of your storage type in,
//! // rounded up to to word alignment of the flash. Some kinds of flash may require
//! // this buffer to be aligned in RAM as well.
//! let mut data_buffer = [0; 128];
//!
//! // We can fetch an item from the flash.
//! // Nothing is stored in it yet, so it will return None.
//!
//! assert_eq!(
//!     fetch_item::<u8, u32, _>(
//!         &mut flash,
//!         flash_range.clone(),
//!         &mut NoCache::new(),
//!         &mut data_buffer,
//!         42,
//!     ).await.unwrap(),
//!     None
//! );
//!
//! // Now we store an item the flash with key 42
//!
//! store_item(
//!     &mut flash,
//!     flash_range.clone(),
//!     &mut NoCache::new(),
//!     &mut data_buffer,
//!     42u8,
//!     &104729u32,
//! ).await.unwrap();
//!
//! // When we ask for key 42, we not get back a Some with the correct value
//!
//! assert_eq!(
//!     fetch_item::<u8, u32, _>(
//!         &mut flash,
//!         flash_range.clone(),
//!         &mut NoCache::new(),
//!         &mut data_buffer,
//!         42,
//!     ).await.unwrap(),
//!     Some(104729)
//! );
//! # });
//! ```

use embedded_storage_async::nor_flash::MultiwriteNorFlash;

use crate::item::{find_next_free_item_spot, Item, ItemHeader, ItemIter};

use self::{
    cache::{KeyCacheImpl, PrivateKeyCacheImpl},
    item::{ItemHeaderIter, ItemUnborrowed},
};

use super::*;

// TODO revise
// /// Get a storage item from the flash.
// /// Only the last stored item of the given key is returned.
// ///
// /// If no value with the key is found, None is returned.
// ///
// /// The data buffer must be long enough to hold the longest serialized data of your [StorageItem] type,
// /// rounded up to flash word alignment.
// ///
// /// *Note: On a given flash range, make sure to use only the same type as [StorageItem] every time
// /// or types that serialize and deserialize the key in the same way.*
pub async fn fetch_item<'d, K: Key, V: Value<'d>, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &'d mut [u8],
    search_key: K,
) -> Result<Option<V>, Error<S::Error>> {
    let result = run_with_auto_repair!(
        function = {
            fetch_item_with_location(
                flash,
                flash_range.clone(),
                cache,
                data_buffer,
                search_key.clone(),
            )
            .await
        },
        repair = try_repair::<K, _>(flash, flash_range.clone(), cache, data_buffer).await?
    );

    let Some((item, _)) = result? else {
        return Ok(None);
    };

    let item = item.reborrow(data_buffer);

    let data_len = item.data().len();

    Ok(Some(
        V::deserialize_from(&item.destruct().1[K::LEN..][..data_len - K::LEN])
            .map_err(Error::Item)?,
    ))
}

/// Fetch the item, but with the address and header
#[allow(clippy::type_complexity)]
async fn fetch_item_with_location<'d, K: Key, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl PrivateKeyCacheImpl<K>,
    data_buffer: &'d mut [u8],
    search_key: K,
) -> Result<Option<(ItemUnborrowed, u32)>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);
    assert!(flash_range.end - flash_range.start >= S::ERASE_SIZE as u32 * 2);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 3);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    if cache.is_dirty() {
        cache.invalidate_cache_state();
    }

    'cache: {
        if let Some(cached_location) = cache.key_location(&search_key) {
            let page_index = calculate_page_index::<S>(flash_range.clone(), cached_location);
            let page_data_end_address =
                calculate_page_end_address::<S>(flash_range.clone(), page_index)
                    - S::WORD_SIZE as u32;

            let Some(header) =
                ItemHeader::read_new(flash, cached_location, page_data_end_address).await?
            else {
                // The cache points to a non-existing item?
                if cfg!(feature = "_test") {
                    panic!("Wrong cache value. Addr: {cached_location}");
                }
                cache.invalidate_cache_state();
                break 'cache;
            };

            let item = header
                .read_item(flash, data_buffer, cached_location, page_data_end_address)
                .await?;

            match item {
                item::MaybeItem::Corrupted(_, _) | item::MaybeItem::Erased(_, _) => {
                    if cfg!(feature = "_test") {
                        panic!("Wrong cache value. Addr: {cached_location}");
                    }

                    // The cache points to a corrupted or erased item?
                    cache.invalidate_cache_state();
                    break 'cache;
                }
                item::MaybeItem::Present(item) => {
                    return Ok(Some((item.unborrow(), cached_location)));
                }
            }
        }
    }

    // We need to find the page we were last using. This should be the only partial open page.
    let mut last_used_page =
        find_first_page(flash, flash_range.clone(), cache, 0, PageState::PartialOpen).await?;

    if last_used_page.is_none() {
        // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
        // If the page one before that is closed, then that's the last used page.
        if let Some(first_open_page) =
            find_first_page(flash, flash_range.clone(), cache, 0, PageState::Open).await?
        {
            let previous_page = previous_page::<S>(flash_range.clone(), first_open_page);
            if get_page_state(flash, flash_range.clone(), cache, previous_page)
                .await?
                .is_closed()
            {
                last_used_page = Some(previous_page);
            } else {
                // The page before the open page is not closed, so it must be open.
                // This means that all pages are open and that we don't have any items yet.
                cache.unmark_dirty();
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
    let mut newest_found_item_address = None;

    loop {
        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), current_page_to_check)
                + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), current_page_to_check)
                - S::WORD_SIZE as u32;

        let mut it = ItemIter::new(page_data_start_address, page_data_end_address);
        while let Some((item, address)) = it.next(flash, data_buffer).await? {
            if K::deserialize_from(&item.data()[..K::LEN]) == search_key {
                newest_found_item_address = Some(address);
            }
        }

        // We've found the item! We can stop searching
        if let Some(newest_found_item_address) = newest_found_item_address.as_ref() {
            cache.notice_key_location(search_key, *newest_found_item_address, false);

            break;
        }

        // We have not found the item. We've got to look in the previous page, but only if that page is closed and contains data.
        let previous_page = previous_page::<S>(flash_range.clone(), current_page_to_check);

        if get_page_state(flash, flash_range.clone(), cache, previous_page).await?
            != PageState::Closed
        {
            // We've looked through all the pages with data and couldn't find the item
            cache.unmark_dirty();
            return Ok(None);
        }

        current_page_to_check = previous_page;
    }

    cache.unmark_dirty();

    // We now need to reread the item because we lost all its data other than its address

    if let Some(newest_found_item_address) = newest_found_item_address {
        let item = ItemHeader::read_new(flash, newest_found_item_address, u32::MAX)
            .await?
            .ok_or_else(|| {
                // How come there's no item header here!? We just found it!
                Error::Corrupted {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                }
            })?
            .read_item(flash, data_buffer, newest_found_item_address, u32::MAX)
            .await?;

        Ok(Some((item.unwrap()?.unborrow(), newest_found_item_address)))
    } else {
        Ok(None)
    }
}

// TODO revise
// /// Store an item into flash memory.
// /// It will overwrite the last value that has the same key.
// /// The flash needs to be at least 2 pages long.
// ///
// /// The data buffer must be long enough to hold the longest serialized data of your [StorageItem] type.
// ///
// /// *Note: On a given flash range, make sure to use only the same type as [StorageItem] every time
// /// or types that serialize and deserialize the key in the same way.*
pub async fn store_item<'d, K: Key, V: Value<'d>, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &mut [u8],
    key: K,
    item: &V,
) -> Result<(), Error<S::Error>> {
    run_with_auto_repair!(
        function = store_item_inner(
            flash,
            flash_range.clone(),
            cache,
            data_buffer,
            key.clone(),
            item
        )
        .await,
        repair = try_repair::<K, _>(flash, flash_range.clone(), cache, data_buffer).await?
    )
}

async fn store_item_inner<'d, K: Key, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &mut [u8],
    key: K,
    item: &dyn Value<'d>,
) -> Result<(), Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(flash_range.end - flash_range.start >= S::ERASE_SIZE as u32 * 2);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 3);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    if cache.is_dirty() {
        cache.invalidate_cache_state();
    }

    let mut recursion_level = 0;
    loop {
        // Check if we're in an infinite recursion which happens when we don't have enough space to store the new data
        if recursion_level == get_pages::<S>(flash_range.clone(), 0).count() {
            cache.unmark_dirty();
            return Err(Error::FullStorage);
        }

        // If there is a partial open page, we try to write in that first if there is enough space
        let next_page_to_use = if let Some(partial_open_page) =
            find_first_page(flash, flash_range.clone(), cache, 0, PageState::PartialOpen).await?
        {
            // We found a partial open page, but at this point it's relatively cheap to do a consistency check
            if !get_page_state(
                flash,
                flash_range.clone(),
                cache,
                next_page::<S>(flash_range.clone(), partial_open_page),
            )
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
                calculate_page_address::<S>(flash_range.clone(), partial_open_page)
                    + S::WORD_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(flash_range.clone(), partial_open_page)
                    - S::WORD_SIZE as u32;

            key.serialize_into(&mut data_buffer[..K::LEN]);
            let item_data_length = K::LEN
                + item
                    .serialize_into(&mut data_buffer[K::LEN..])
                    .map_err(Error::Item)?;

            let free_spot_address = find_next_free_item_spot(
                flash,
                flash_range.clone(),
                cache,
                page_data_start_address,
                page_data_end_address,
                item_data_length as u32,
            )
            .await?;

            match free_spot_address {
                Some(free_spot_address) => {
                    cache.notice_key_location(key.clone(), free_spot_address, true);
                    Item::write_new(
                        flash,
                        flash_range.clone(),
                        cache,
                        free_spot_address,
                        &data_buffer[..item_data_length],
                    )
                    .await?;

                    cache.unmark_dirty();
                    return Ok(());
                }
                None => {
                    // The item doesn't fit here, so we need to close this page and move to the next
                    close_page(flash, flash_range.clone(), cache, partial_open_page).await?;
                    Some(next_page::<S>(flash_range.clone(), partial_open_page))
                }
            }
        } else {
            None
        };

        // If we get here, there was no partial page found or the partial page has now been closed because the item didn't fit.
        // If there was a partial page, then we need to look at the next page. It's supposed to be open since it was the previous empty buffer page.
        // The new buffer page has to be emptied if it was closed.
        // If there was no partial page, we just use the first open page.

        match next_page_to_use {
            Some(next_page_to_use) => {
                let next_page_state =
                    get_page_state(flash, flash_range.clone(), cache, next_page_to_use).await?;

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
                partial_close_page(flash, flash_range.clone(), cache, next_page_to_use).await?;

                let next_buffer_page = next_page::<S>(flash_range.clone(), next_page_to_use);
                let next_buffer_page_state =
                    get_page_state(flash, flash_range.clone(), cache, next_buffer_page).await?;

                if !next_buffer_page_state.is_open() {
                    migrate_items::<K, _>(
                        flash,
                        flash_range.clone(),
                        cache,
                        data_buffer,
                        next_buffer_page,
                        next_page_to_use,
                    )
                    .await?;
                }
            }
            None => {
                // There's no partial open page, so we just gotta turn the first open page into a partial open one
                let first_open_page =
                    match find_first_page(flash, flash_range.clone(), cache, 0, PageState::Open)
                        .await?
                    {
                        Some(first_open_page) => first_open_page,
                        None => {
                            // Uh oh, no open pages.
                            // Something has gone wrong.
                            // We should never get here.
                            return Err(Error::Corrupted {
                                #[cfg(feature = "_test")]
                                backtrace: std::backtrace::Backtrace::capture(),
                            });
                        }
                    };

                partial_close_page(flash, flash_range.clone(), cache, first_open_page).await?;
            }
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
/// </div>
pub async fn remove_item<K: Key, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &mut [u8],
    search_key: K,
) -> Result<(), Error<S::Error>> {
    run_with_auto_repair!(
        function = remove_item_inner::<K, _>(
            flash,
            flash_range.clone(),
            cache,
            data_buffer,
            search_key.clone()
        )
        .await,
        repair = try_repair::<K, _>(flash, flash_range.clone(), cache, data_buffer).await?
    )
}

async fn remove_item_inner<K: Key, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &mut [u8],
    search_key: K,
) -> Result<(), Error<S::Error>> {
    cache.notice_key_erased(&search_key);

    // Search for the last used page. We're gonna erase from the one after this first.
    // If we get an early shutoff or cancellation, this will make it so that we don't return
    // an old version of the key on the next fetch.
    let last_used_page =
        find_first_page(flash, flash_range.clone(), cache, 0, PageState::PartialOpen)
            .await?
            .unwrap_or_default();

    // Go through all the pages
    for page_index in get_pages::<S>(
        flash_range.clone(),
        next_page::<S>(flash_range.clone(), last_used_page),
    ) {
        if get_page_state(flash, flash_range.clone(), cache, page_index)
            .await?
            .is_open()
        {
            // This page is open, we don't have to check it
            continue;
        }

        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), page_index) + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), page_index) - S::WORD_SIZE as u32;

        // Go through all items on the page
        let mut item_headers = ItemHeaderIter::new(page_data_start_address, page_data_end_address);

        while let (Some(item_header), item_address) = item_headers.next(flash).await? {
            let item = item_header
                .read_item(flash, data_buffer, item_address, page_data_end_address)
                .await?;

            match item {
                item::MaybeItem::Corrupted(_, _) => continue,
                item::MaybeItem::Erased(_, _) => continue,
                item::MaybeItem::Present(item) => {
                    let item_key = K::deserialize_from(&item.data()[..K::LEN]);

                    // If this item has the same key as the key we're trying to erase, then erase the item.
                    // But keep going! We need to erase everything.
                    if item_key == search_key {
                        item.header
                            .erase_data(flash, flash_range.clone(), cache, item_address)
                            .await?;
                    }
                }
            }
        }
    }

    // We're done, we now know the cache is in a good state
    cache.unmark_dirty();

    Ok(())
}

pub trait Key: Eq + Clone + Sized {
    const LEN: usize;

    fn serialize_into(&self, buffer: &mut [u8]);
    fn deserialize_from(buffer: &[u8]) -> Self;
}

macro_rules! impl_key_num {
    ($int:ty) => {
        impl Key for $int {
            const LEN: usize = core::mem::size_of::<Self>();

            fn serialize_into(&self, buffer: &mut [u8]) {
                buffer.copy_from_slice(&self.to_le_bytes());
            }

            fn deserialize_from(buffer: &[u8]) -> Self {
                Self::from_le_bytes(buffer.try_into().unwrap())
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
    const LEN: usize = N;

    fn serialize_into(&self, buffer: &mut [u8]) {
        buffer.copy_from_slice(self);
    }

    fn deserialize_from(buffer: &[u8]) -> Self {
        buffer[..Self::LEN].try_into().unwrap()
    }
}

pub trait Value<'a> {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, MapItemError>;
    fn deserialize_from(buffer: &'a [u8]) -> Result<Self, MapItemError>
    where
        Self: Sized;
}

impl<'a> Value<'a> for &'a [u8] {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, MapItemError> {
        if buffer.len() < self.len() {
            return Err(MapItemError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self);
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<Self, MapItemError>
    where
        Self: Sized,
    {
        Ok(buffer)
    }
}

impl<'a, const N: usize> Value<'a> for [u8; N] {
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, MapItemError> {
        if buffer.len() < self.len() {
            return Err(MapItemError::BufferTooSmall);
        }

        buffer[..self.len()].copy_from_slice(self);
        Ok(self.len())
    }

    fn deserialize_from(buffer: &'a [u8]) -> Result<Self, MapItemError>
    where
        Self: Sized,
    {
        buffer.try_into().map_err(|_| MapItemError::BufferTooSmall)
    }
}

macro_rules! impl_map_item_num {
    ($int:ty) => {
        impl<'a> Value<'a> for $int {
            fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, MapItemError> {
                buffer[..core::mem::size_of::<Self>()].copy_from_slice(&self.to_le_bytes());
                Ok(core::mem::size_of::<Self>())
            }

            fn deserialize_from(buffer: &[u8]) -> Result<Self, MapItemError> {
                Ok(Self::from_le_bytes(
                    buffer[..core::mem::size_of::<Self>()]
                        .try_into()
                        .map_err(|_| MapItemError::BufferTooSmall)?,
                ))
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

#[non_exhaustive]
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub enum MapItemError {
    BufferTooSmall,
    InvalidFormat,
}

impl core::fmt::Display for MapItemError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            MapItemError::BufferTooSmall => write!(f, "Buffer too small"),
            MapItemError::InvalidFormat => write!(f, "Invalid format"),
        }
    }
}

async fn migrate_items<K: Key, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl PrivateKeyCacheImpl<K>,
    data_buffer: &mut [u8],
    source_page: usize,
    target_page: usize,
) -> Result<(), Error<S::Error>> {
    // We need to move the data from the next buffer page to the next_page_to_use, but only if that data
    // doesn't have a newer value somewhere else.

    let mut next_page_write_address =
        calculate_page_address::<S>(flash_range.clone(), target_page) + S::WORD_SIZE as u32;

    let mut it = ItemIter::new(
        calculate_page_address::<S>(flash_range.clone(), source_page) + S::WORD_SIZE as u32,
        calculate_page_end_address::<S>(flash_range.clone(), source_page) - S::WORD_SIZE as u32,
    );
    while let Some((item, item_address)) = it.next(flash, data_buffer).await? {
        let key = K::deserialize_from(&item.data()[..K::LEN]);
        let (_, data_buffer) = item.destruct();

        // We're in a decent state here
        cache.unmark_dirty();

        // Search for the newest item with the key we found
        let Some((found_item, found_address)) = fetch_item_with_location::<K, S>(
            flash,
            flash_range.clone(),
            cache,
            data_buffer,
            key.clone(),
        )
        .await?
        else {
            // We couldn't even find our own item?
            return Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        };

        let found_item = found_item.reborrow(data_buffer);

        if found_address == item_address {
            cache.notice_key_location(key, next_page_write_address, true);
            found_item
                .write(flash, flash_range.clone(), cache, next_page_write_address)
                .await?;
            next_page_write_address = found_item
                .header
                .next_item_address::<S>(next_page_write_address);
        }
    }

    open_page(flash, flash_range.clone(), cache, source_page).await?;

    Ok(())
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
async fn try_repair<K: Key, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    cache: &mut impl KeyCacheImpl<K>,
    data_buffer: &mut [u8],
) -> Result<(), Error<S::Error>> {
    cache.invalidate_cache_state();

    crate::try_general_repair(flash, flash_range.clone(), cache).await?;

    // Let's check if we corrupted in the middle of a migration
    if let Some(partial_open_page) =
        find_first_page(flash, flash_range.clone(), cache, 0, PageState::PartialOpen).await?
    {
        let buffer_page = next_page::<S>(flash_range.clone(), partial_open_page);
        if !get_page_state(flash, flash_range.clone(), cache, buffer_page)
            .await?
            .is_open()
        {
            // Yes, the migration got interrupted. Let's redo it.
            // To do that, we erase the partial open page first because it contains incomplete data.
            open_page(flash, flash_range.clone(), cache, partial_open_page).await?;

            // Then partially close it again
            partial_close_page(flash, flash_range.clone(), cache, partial_open_page).await?;

            migrate_items::<K, _>(
                flash,
                flash_range.clone(),
                cache,
                data_buffer,
                buffer_page,
                partial_open_page,
            )
            .await?;
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures_test::test;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    async fn store_and_fetch() {
        let mut flash = MockFlashBig::default();
        let flash_range = 0x000..0x1000;

        let mut data_buffer = AlignedBuf([0; 128]);

        let start_snapshot = flash.stats_snapshot();

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            60,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0xFF,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        store_item(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0u8,
            &[5],
        )
        .await
        .unwrap();
        store_item(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0u8,
            &[5, 6],
        )
        .await
        .unwrap();

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item, &[5, 6]);

        store_item(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            1u8,
            &[2, 2, 2, 2, 2, 2],
        )
        .await
        .unwrap();

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            0,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item, &[5, 6]);

        let item = fetch_item::<u8, &[u8], _>(
            &mut flash,
            flash_range.clone(),
            &mut cache::NoCache::new(),
            &mut data_buffer,
            1,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item, &[2, 2, 2, 2, 2, 2]);

        for index in 0..4000 {
            store_item(
                &mut flash,
                flash_range.clone(),
                &mut cache::NoCache::new(),
                &mut data_buffer,
                (index % 10) as u8,
                &vec![(index % 10) as u8 * 2; index % 10].as_slice(),
            )
            .await
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<u8, &[u8], _>(
                &mut flash,
                flash_range.clone(),
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
            )
            .await
            .unwrap()
            .unwrap();
            assert_eq!(item, &vec![(i % 10) * 2; (i % 10) as usize]);
        }

        for _ in 0..4000 {
            store_item(
                &mut flash,
                flash_range.clone(),
                &mut cache::NoCache::new(),
                &mut data_buffer,
                11u8,
                &[0; 10],
            )
            .await
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<u8, &[u8], _>(
                &mut flash,
                flash_range.clone(),
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
            )
            .await
            .unwrap()
            .unwrap();
            assert_eq!(item, &vec![(i % 10) * 2; (i % 10) as usize]);
        }

        println!("{:?}", start_snapshot.compare_to(flash.stats_snapshot()),);
    }

    #[test]
    async fn store_too_many_items() {
        const UPPER_BOUND: u8 = 3;

        let mut tiny_flash = MockFlashTiny::default();
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            println!("Storing {i:?}");

            store_item(
                &mut tiny_flash,
                0x00..0x40,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
                &vec![i; i as usize].as_slice(),
            )
            .await
            .unwrap();
        }

        assert_eq!(
            store_item(
                &mut tiny_flash,
                0x00..0x40,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                UPPER_BOUND,
                &vec![0; UPPER_BOUND as usize].as_slice(),
            )
            .await,
            Err(Error::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = fetch_item::<u8, &[u8], _>(
                &mut tiny_flash,
                0x00..0x40,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
            )
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

        let mut big_flash = MockFlashBig::default();
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            println!("Storing {i:?}");

            store_item(
                &mut big_flash,
                0x0000..0x1000,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
                &vec![i; i as usize].as_slice(),
            )
            .await
            .unwrap();
        }

        assert_eq!(
            store_item(
                &mut big_flash,
                0x0000..0x1000,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                UPPER_BOUND,
                &vec![0; UPPER_BOUND as usize].as_slice(),
            )
            .await,
            Err(Error::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = fetch_item::<u8, &[u8], _>(
                &mut big_flash,
                0x0000..0x1000,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i,
            )
            .await
            .unwrap()
            .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item, vec![i; i as usize]);
        }
    }

    #[test]
    async fn store_many_items_big() {
        let mut flash = mock_flash::MockFlashBase::<4, 1, 4096>::default();
        let mut data_buffer = AlignedBuf([0; 128]);

        const LENGHT_PER_KEY: [usize; 24] = [
            11, 13, 6, 13, 13, 10, 2, 3, 5, 36, 1, 65, 4, 6, 1, 15, 10, 7, 3, 15, 9, 3, 4, 5,
        ];

        for _ in 0..100 {
            for i in 0..24 {
                store_item(
                    &mut flash,
                    0x0000..0x4000,
                    &mut cache::NoCache::new(),
                    &mut data_buffer,
                    i as u16,
                    &vec![i as u8; LENGHT_PER_KEY[i]].as_slice(),
                )
                .await
                .unwrap();
            }
        }

        for i in 0..24 {
            let item = fetch_item::<u16, &[u8], _>(
                &mut flash,
                0x0000..0x4000,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                i as u16,
            )
            .await
            .unwrap()
            .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item, vec![i as u8; LENGHT_PER_KEY[i]]);
        }
    }

    #[test]
    async fn remove_items() {
        let mut flash = mock_flash::MockFlashBase::<4, 1, 4096>::new(
            mock_flash::WriteCountCheck::Twice,
            None,
            true,
        );
        let mut data_buffer = AlignedBuf([0; 128]);
        const FLASH_RANGE: Range<u32> = 0x0000..0x4000;

        // Add some data to flash
        for j in 0..10 {
            for i in 0..24 {
                store_item(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache::NoCache::new(),
                    &mut data_buffer,
                    i as u8,
                    &vec![i as u8; j + 2].as_slice(),
                )
                .await
                .unwrap();
            }
        }

        for j in (0..24).rev() {
            // Are all things still in flash that we expect?
            for i in 0..=j {
                assert!(fetch_item::<u8, &[u8], _>(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache::NoCache::new(),
                    &mut data_buffer,
                    i
                )
                .await
                .unwrap()
                .is_some());
            }

            // Remove the item
            remove_item::<u8, _>(
                &mut flash,
                FLASH_RANGE,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                j,
            )
            .await
            .unwrap();

            // Are all things still in flash that we expect?
            for i in 0..j {
                assert!(fetch_item::<u8, &[u8], _>(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache::NoCache::new(),
                    &mut data_buffer,
                    i
                )
                .await
                .unwrap()
                .is_some());
            }

            assert!(fetch_item::<u8, &[u8], _>(
                &mut flash,
                FLASH_RANGE,
                &mut cache::NoCache::new(),
                &mut data_buffer,
                j
            )
            .await
            .unwrap()
            .is_none());
        }
    }
}
