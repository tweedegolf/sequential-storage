//! A module for storing key-value pairs in flash with minimal erase cycles.
//!
//! When a key-value is stored, it overwrites the any old items with the same key.
//!
//! Make sure to use the same [StorageItem] type on a given range in flash.
//! In theory you could use multiple types if you're careful, but they must at least have the same key definition and format.
//!
//! ## Basic API:
//!
//! ```rust
//! # use sequential_storage::map::{store_item, fetch_item, StorageItem};
//! # use sequential_storage::cache::NoCache;
//! # use mock_flash::MockFlashBase;
//! # use futures::executor::block_on;
//! # type Flash = MockFlashBase<10, 1, 4096>;
//! # mod mock_flash {
//! #   include!("mock_flash.rs");
//! # }
//! // We create the type we want to store in this part of flash.
//! // It itself must contain the key and the value.
//! // On this part of flash, we must only call the functions using this type.
//! // If you start to mix, bad things will happen.
//!
//! #[derive(Debug, PartialEq)]
//! struct MyCustomType {
//!     key: u8,
//!     data: u32,
//! }
//!
//! // We implement StorageItem for our type. This lets the crate
//! // know how to serialize and deserialize the data and get its key for comparison.
//!
//! impl StorageItem for MyCustomType {
//!     type Key = u8;
//!     type Error = Error;
//!     
//!     fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
//!         if buffer.len() < 5 {
//!             return Err(Error::BufferTooSmall);
//!         }
//!
//!         buffer[0] = self.key;
//!         buffer[1..5].copy_from_slice(&self.data.to_le_bytes());
//!
//!         Ok(5)
//!     }
//!     fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error> {
//!         // We don't have to check the length. This buffer has the same length
//!         // as what we serialized, so in this case it's always 5.
//!         
//!         Ok(Self {
//!             key: buffer[0],
//!             data: u32::from_le_bytes(buffer[1..5].try_into().unwrap()),
//!         })
//!     }
//!     fn key(&self) -> Self::Key { self.key }
//! }
//!
//! #[derive(Debug)]
//! enum Error {
//!     BufferTooSmall
//! }
//!
//! # block_on(async {
//! // Initialize the flash. This can be internal or external
//! let mut flash = Flash::default();
//! // These are the flash addresses in which the crate will operate.
//! // The crate will not read, write or erase outside of this range.
//! let flash_range = 0x1000..0x3000;
//! // We need to give the crate a buffer to work with.
//! // It must be big enough to serialize the biggest value of your storage type in,
//! // rounded up to to word alignment of the flash. Some kinds of flash may require
//! // this buffer to be aligned in RAM as well.
//! let mut data_buffer = [0; 100];
//!
//! let mut cache = NoCache;
//!
//! // We can fetch an item from the flash.
//! // Nothing is stored in it yet, so it will return None.
//!
//! assert_eq!(
//!     fetch_item::<MyCustomType, _>(
//!         &mut flash,
//!         flash_range.clone(),
//!         &mut cache,
//!         &mut data_buffer,
//!         42,
//!     ).await.unwrap(),
//!     None
//! );
//!
//! // Now we store an item the flash with key 42
//!
//! store_item::<MyCustomType, _>(
//!     &mut flash,
//!     flash_range.clone(),
//!     &mut cache,
//!     &mut data_buffer,
//!     MyCustomType { key: 42, data: 104729 },
//! ).await.unwrap();
//!
//! // When we ask for key 42, we not get back a Some with the correct value
//!
//! assert_eq!(
//!     fetch_item::<MyCustomType, _>(
//!         &mut flash,
//!         flash_range.clone(),
//!         &mut cache,
//!         &mut data_buffer,
//!         42,
//!     ).await.unwrap(),
//!     Some(MyCustomType { key: 42, data: 104729 })
//! );
//! # });
//! ```

use crate::{
    cache::Cache,
    item::{find_next_free_item_spot, Item, ItemHeader, ItemIter},
};

use super::*;

/// Get a storage item from the flash.
/// Only the last stored item of the given key is returned.
///
/// If no value with the key is found, None is returned.
///
/// The data buffer must be long enough to hold the longest serialized data of your [StorageItem] type,
/// rounded up to flash word alignment.
///
/// *Note: On a given flash range, make sure to use only the same type as [StorageItem] every time
/// or types that serialize and deserialize the key in the same way.*
pub async fn fetch_item<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    query: &mut impl Cache,
    data_buffer: &mut [u8],
    search_key: I::Key,
) -> Result<Option<I>, MapError<I::Error, S::Error>> {
    Ok(
        fetch_item_with_location(flash, flash_range, query, data_buffer, search_key)
            .await?
            .map(|(item, _, _)| item),
    )
}

/// Fetch the item, but with the address and header
#[allow(clippy::type_complexity)]
async fn fetch_item_with_location<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    query: &mut impl StateQuery,
    data_buffer: &mut [u8],
    search_key: I::Key,
) -> Result<Option<(I, u32, ItemHeader)>, MapError<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);
    assert!(flash_range.end - flash_range.start >= S::ERASE_SIZE as u32 * 2);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 3);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    // We need to find the page we were last using. This should be the only partial open page.
    let mut last_used_page =
        find_first_page(flash, flash_range.clone(), query, 0, PageState::PartialOpen).await?;

    #[cfg(feature = "defmt")]
    defmt::trace!("Fetch item, last used page: {}", last_used_page);

    if last_used_page.is_none() {
        // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
        // If the page one before that is closed, then that's the last used page.
        if let Some(first_open_page) =
            find_first_page(flash, flash_range.clone(), query, 0, PageState::Open).await?
        {
            let previous_page = previous_page::<S>(flash_range.clone(), first_open_page);
            if query
                .get_page_state(flash, flash_range.clone(), previous_page)
                .await?
                .is_closed()
            {
                last_used_page = Some(previous_page);
            } else {
                // The page before the open page is not closed, so it must be open.
                // This means that all pages are open and that we don't have any items yet.
                return Ok(None);
            }
        } else {
            // There are no open pages, so everything must be closed.
            // Something is up and this should never happen.
            // To recover, we will just erase all the flash.
            return Err(MapError::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        }
    }

    // We must now find the most recent storage item with the key that was asked for.
    // If we don't find it in the current page, then we check again in the previous page if that page is closed.

    let mut current_page_to_check = last_used_page.unwrap();
    let mut newest_found_item = None;

    loop {
        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), current_page_to_check)
                + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), current_page_to_check)
                - S::WORD_SIZE as u32;

        let mut it = ItemIter::new(page_data_start_address, page_data_end_address);
        while let Some((item, address)) = it.next(flash, data_buffer).await? {
            if I::deserialize_key_only(item.data()).map_err(MapError::Item)? == search_key {
                newest_found_item = Some((
                    I::deserialize_from(item.data()).map_err(MapError::Item)?,
                    address,
                    item.header,
                ));
            }
        }

        // We've found the item! We can stop searching
        if newest_found_item.is_some() {
            break;
        }

        // We have not found the item. We've got to look in the previous page, but only if that page is closed and contains data.
        let previous_page = previous_page::<S>(flash_range.clone(), current_page_to_check);

        if query
            .get_page_state(flash, flash_range.clone(), previous_page)
            .await?
            != PageState::Closed
        {
            // We've looked through all the pages with data and couldn't find the item
            return Ok(None);
        }

        current_page_to_check = previous_page;
    }

    Ok(newest_found_item)
}

/// Store an item into flash memory.
/// It will overwrite the last value that has the same key.
/// The flash needs to be at least 2 pages long.
///
/// The data buffer must be long enough to hold the longest serialized data of your [StorageItem] type.
///
/// *Note: On a given flash range, make sure to use only the same type as [StorageItem] every time
/// or types that serialize and deserialize the key in the same way.*
pub async fn store_item<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    query: &mut impl Cache,
    data_buffer: &mut [u8],
    item: I,
) -> Result<(), MapError<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(flash_range.len() / S::ERASE_SIZE >= 2);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 3);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let mut recursion_level = 0;
    loop {
        #[cfg(feature = "defmt")]
        defmt::trace!("Store item inner. Recursion: {}", recursion_level);

        // Check if we're in an infinite recursion which happens when we don't have enough space to store the new data
        if recursion_level == get_pages::<S>(flash_range.clone(), 0).count() {
            return Err(MapError::FullStorage);
        }

        // If there is a partial open page, we try to write in that first if there is enough space
        let next_page_to_use = if let Some(partial_open_page) =
            find_first_page(flash, flash_range.clone(), query, 0, PageState::PartialOpen).await?
        {
            #[cfg(feature = "defmt")]
            defmt::trace!("Partial open page found: {}", partial_open_page);

            // We found a partial open page, but at this point it's relatively cheap to do a consistency check
            if !query
                .get_page_state(
                    flash,
                    flash_range.clone(),
                    next_page::<S>(flash_range.clone(), partial_open_page),
                )
                .await?
                .is_open()
            {
                // Oh oh, the next page which serves as the buffer page is not open. We're corrupt.
                // This likely happened because of an unexpected shutdown during data migration from the
                // then new buffer page to the new partial open page.
                // The repair function should be able to repair this.
                return Err(MapError::Corrupted {
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

            let item_data_length = item.serialize_into(data_buffer).map_err(MapError::Item)?;

            let free_spot_address = find_next_free_item_spot(
                flash,
                page_data_start_address,
                page_data_end_address,
                item_data_length as u32,
            )
            .await?;

            match free_spot_address {
                Some(free_spot_address) => {
                    Item::write_new(flash, free_spot_address, &data_buffer[..item_data_length])
                        .await?;

                    #[cfg(feature = "defmt")]
                    defmt::trace!("Item has been written ok");

                    return Ok(());
                }
                None => {
                    #[cfg(feature = "defmt")]
                    defmt::trace!(
                        "Partial open page is too small. Closing it now: {}",
                        partial_open_page
                    );

                    // The item doesn't fit here, so we need to close this page and move to the next
                    close_page(flash, flash_range.clone(), query, partial_open_page).await?;
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

        #[cfg(feature = "defmt")]
        defmt::trace!("Next page to use: {}", next_page_to_use);

        match next_page_to_use {
            Some(next_page_to_use) => {
                let next_page_state = query
                    .get_page_state(flash, flash_range.clone(), next_page_to_use)
                    .await?;

                if !next_page_state.is_open() {
                    // What was the previous buffer page was not open...
                    return Err(MapError::Corrupted {
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    });
                }

                // Since we're gonna write data here, let's already partially close the page
                // This could be done after moving the data, but this is more robust in the
                // face of shutdowns and cancellations
                partial_close_page(flash, flash_range.clone(), query, next_page_to_use).await?;

                let next_buffer_page = next_page::<S>(flash_range.clone(), next_page_to_use);
                let next_buffer_page_state = query
                    .get_page_state(flash, flash_range.clone(), next_buffer_page)
                    .await?;

                if !next_buffer_page_state.is_open() {
                    migrate_items::<I, _>(
                        flash,
                        flash_range.clone(),
                        query,
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
                    match find_first_page(flash, flash_range.clone(), query, 0, PageState::Open)
                        .await?
                    {
                        Some(first_open_page) => first_open_page,
                        None => {
                            #[cfg(feature = "defmt")]
                            defmt::error!(
                                "No open pages found for sequential storage in the range: {}",
                                flash_range
                            );
                            // Uh oh, no open pages.
                            // Something has gone wrong.
                            // We should never get here.
                            return Err(MapError::Corrupted {
                                #[cfg(feature = "_test")]
                                backtrace: std::backtrace::Backtrace::capture(),
                            });
                        }
                    };

                partial_close_page(flash, flash_range.clone(), query, first_open_page).await?;
            }
        }

        // If we get here, we just freshly partially closed a new page, so the next loop iteration should succeed.
        recursion_level += 1;
    }
}

/// A way of serializing and deserializing items in the storage.
///
/// Serialized items must not be 0 bytes and may not be longer than [u16::MAX].
/// Items must also fit within a page (together with the bits of overhead added in the storage process).
pub trait StorageItem {
    /// The key type of the key-value pair
    type Key: Eq;
    /// The error type for serialization and deserialization
    type Error;

    /// Serialize the key-value item into the given buffer.
    /// Returns the number of bytes the buffer was filled with or an error.
    ///
    /// The serialized data does not have to self-describe its length or do framing.
    /// This crate already stores the length of any item in flash.
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error>;
    /// Deserialize the key-value item from the given buffer. This buffer should be as long
    /// as what was serialized before.
    fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error>
    where
        Self: Sized;
    /// Optimization for deserializing the key only. Can give a small performance boost if
    /// your key is easily extractable from the buffer.
    fn deserialize_key_only(buffer: &[u8]) -> Result<Self::Key, Self::Error>
    where
        Self: Sized,
    {
        // This works for any impl, but could be overridden by the user
        Ok(Self::deserialize_from(buffer)?.key())
    }

    /// The key of the key-value item. It is used by the storage to know what the key of this item is.
    fn key(&self) -> Self::Key;
}

/// The error type for map operations
#[non_exhaustive]
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum MapError<I, S> {
    /// A storage item error
    Item(I),
    /// An error in the storage (flash)
    Storage {
        /// The value of the error
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

impl<S, I> From<super::Error<S>> for MapError<I, S> {
    fn from(value: super::Error<S>) -> Self {
        match value {
            Error::Storage {
                value,
                #[cfg(feature = "_test")]
                backtrace,
            } => Self::Storage {
                value,
                #[cfg(feature = "_test")]
                backtrace,
            },
            Error::FullStorage => Self::FullStorage,
            Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace,
            } => Self::Corrupted {
                #[cfg(feature = "_test")]
                backtrace,
            },
            Error::BufferTooBig => Self::BufferTooBig,
            Error::BufferTooSmall(needed) => Self::BufferTooSmall(needed),
        }
    }
}

impl<S: PartialEq, I: PartialEq> PartialEq for MapError<I, S> {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Item(l0), Self::Item(r0)) => l0 == r0,
            (Self::Storage { value: l_value, .. }, Self::Storage { value: r_value, .. }) => {
                l_value == r_value
            }
            (Self::BufferTooSmall(l0), Self::BufferTooSmall(r0)) => l0 == r0,
            _ => core::mem::discriminant(self) == core::mem::discriminant(other),
        }
    }
}

async fn migrate_items<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    query: &mut impl StateQuery,
    data_buffer: &mut [u8],
    source_page: usize,
    target_page: usize,
) -> Result<(), MapError<I::Error, S::Error>> {
    // We need to move the data from the next buffer page to the next_page_to_use, but only if that data
    // doesn't have a newer value somewhere else.

    let mut next_page_write_address =
        calculate_page_address::<S>(flash_range.clone(), target_page) + S::WORD_SIZE as u32;

    let mut it = ItemIter::new(
        calculate_page_address::<S>(flash_range.clone(), source_page) + S::WORD_SIZE as u32,
        calculate_page_end_address::<S>(flash_range.clone(), source_page) - S::WORD_SIZE as u32,
    );
    while let Some((item, item_address)) = it.next(flash, data_buffer).await? {
        let key = I::deserialize_key_only(item.data()).map_err(MapError::Item)?;
        let (item_header, data_buffer) = item.destruct();

        // Search for the newest item with the key we found
        let Some((_, found_address, _)) =
            fetch_item_with_location::<I, S>(flash, flash_range.clone(), query, data_buffer, key)
                .await?
        else {
            // We couldn't even find our own item?
            return Err(MapError::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        };

        if found_address == item_address {
            // The newest item with this key is the item we're about to erase
            // This means we need to copy it over to the next_page_to_use
            let item = item_header
                .read_item(flash, data_buffer, item_address, u32::MAX)
                .await?
                .unwrap()?;
            item.write(flash, next_page_write_address).await?;
            next_page_write_address = item.header.next_item_address::<S>(next_page_write_address);
        }
    }

    open_page(flash, flash_range.clone(), query, source_page).await?;

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
pub async fn try_repair<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    query: &mut impl Cache,
    data_buffer: &mut [u8],
) -> Result<(), MapError<I::Error, S::Error>> {
    query.invalidate_cache_state();
    #[allow(dropping_references)]
    drop(query);

    crate::try_general_repair(flash, flash_range.clone(), &mut NoCache).await?;

    // Let's check if we corrupted in the middle of a migration
    if let Some(partial_open_page) = find_first_page(
        flash,
        flash_range.clone(),
        &mut NoCache,
        0,
        PageState::PartialOpen,
    )
    .await?
    {
        let buffer_page = next_page::<S>(flash_range.clone(), partial_open_page);
        if !NoCache
            .get_page_state(flash, flash_range.clone(), buffer_page)
            .await?
            .is_open()
        {
            // Yes, the migration got interrupted. Let's redo it.
            // To do that, we erase the partial open page first because it contains incomplete data.
            open_page(flash, flash_range.clone(), &mut NoCache, partial_open_page).await?;

            // Then partially close it again
            partial_close_page(flash, flash_range.clone(), &mut NoCache, partial_open_page).await?;

            migrate_items::<I, _>(
                flash,
                flash_range.clone(),
                &mut NoCache,
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

    #[derive(Debug, PartialEq, Eq)]
    struct MockStorageItem {
        key: u8,
        value: Vec<u8>,
    }

    #[derive(Debug, PartialEq, Eq)]
    enum MockStorageItemError {
        BufferTooSmall,
        InvalidKey,
        BufferTooBig,
    }

    impl StorageItem for MockStorageItem {
        type Key = u8;

        type Error = MockStorageItemError;

        fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
            if buffer.len() < 2 + self.value.len() {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            if self.value.len() > 255 {
                return Err(MockStorageItemError::BufferTooBig);
            }

            // The serialized value must not be all 0xFF
            if self.key == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            buffer[0] = self.key;
            buffer[1] = self.value.len() as u8;
            buffer[2..][..self.value.len()].copy_from_slice(&self.value);

            Ok(2 + self.value.len())
        }

        fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error>
        where
            Self: Sized,
        {
            if buffer.len() < 2 {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            if buffer[0] == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            let len = buffer[1];

            if buffer.len() < 2 + len as usize {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            Ok(Self {
                key: buffer[0],
                value: buffer[2..][..len as usize].to_vec(),
            })
        }

        fn key(&self) -> Self::Key {
            self.key
        }
    }

    #[test]
    async fn store_and_fetch() {
        let mut flash = MockFlashBig::default();
        let flash_range = 0x000..0x1000;

        let mut data_buffer = AlignedBuf([0; 128]);

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            0,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            60,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            0xFF,
        )
        .await
        .unwrap();
        assert_eq!(item, None);

        store_item::<_, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            MockStorageItem {
                key: 0,
                value: vec![5],
            },
        )
        .await
        .unwrap();
        store_item::<_, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            MockStorageItem {
                key: 0,
                value: vec![5, 6],
            },
        )
        .await
        .unwrap();

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            0,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item.key, 0);
        assert_eq!(item.value, vec![5, 6]);

        store_item::<_, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            MockStorageItem {
                key: 1,
                value: vec![2, 2, 2, 2, 2, 2],
            },
        )
        .await
        .unwrap();

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            0,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item.key, 0);
        assert_eq!(item.value, vec![5, 6]);

        let item = fetch_item::<MockStorageItem, _>(
            &mut flash,
            flash_range.clone(),
            &mut NoCache,
            &mut data_buffer,
            1,
        )
        .await
        .unwrap()
        .unwrap();
        assert_eq!(item.key, 1);
        assert_eq!(item.value, vec![2, 2, 2, 2, 2, 2]);

        for index in 0..4000 {
            store_item::<_, _>(
                &mut flash,
                flash_range.clone(),
                &mut NoCache,
                &mut data_buffer,
                MockStorageItem {
                    key: (index % 10) as u8,
                    value: vec![(index % 10) as u8 * 2; index % 10],
                },
            )
            .await
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<MockStorageItem, _>(
                &mut flash,
                flash_range.clone(),
                &mut NoCache,
                &mut data_buffer,
                i,
            )
            .await
            .unwrap()
            .unwrap();
            assert_eq!(item.key, i);
            assert_eq!(item.value, vec![(i % 10) as u8 * 2; (i % 10) as usize]);
        }

        for _ in 0..4000 {
            store_item::<_, _>(
                &mut flash,
                flash_range.clone(),
                &mut NoCache,
                &mut data_buffer,
                MockStorageItem {
                    key: 11,
                    value: vec![0; 10],
                },
            )
            .await
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<MockStorageItem, _>(
                &mut flash,
                flash_range.clone(),
                &mut NoCache,
                &mut data_buffer,
                i,
            )
            .await
            .unwrap()
            .unwrap();
            assert_eq!(item.key, i);
            assert_eq!(item.value, vec![(i % 10) as u8 * 2; (i % 10) as usize]);
        }

        println!(
            "Erases: {}, reads: {}, writes: {}",
            flash.erases, flash.reads, flash.writes
        );
    }

    #[test]
    async fn store_too_many_items() {
        const UPPER_BOUND: u8 = 2;

        let mut tiny_flash = MockFlashTiny::default();
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            let item = MockStorageItem {
                key: i as u8,
                value: vec![i as u8; i as usize],
            };
            println!("Storing {item:?}");

            store_item::<_, _>(
                &mut tiny_flash,
                0x00..0x40,
                &mut NoCache,
                &mut data_buffer,
                item,
            )
            .await
            .unwrap();
        }

        assert_eq!(
            store_item::<_, _>(
                &mut tiny_flash,
                0x00..0x40,
                &mut NoCache,
                &mut data_buffer,
                MockStorageItem {
                    key: UPPER_BOUND,
                    value: vec![0; UPPER_BOUND as usize],
                },
            )
            .await,
            Err(MapError::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = fetch_item::<MockStorageItem, _>(
                &mut tiny_flash,
                0x00..0x40,
                &mut NoCache,
                &mut data_buffer,
                i as u8,
            )
            .await
            .unwrap()
            .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item.value, vec![i as u8; i as usize]);
        }
    }

    #[test]
    async fn store_too_many_items_big() {
        const UPPER_BOUND: u8 = 67;

        let mut big_flash = MockFlashBig::default();
        let mut data_buffer = AlignedBuf([0; 128]);

        for i in 0..UPPER_BOUND {
            let item = MockStorageItem {
                key: i as u8,
                value: vec![i as u8; i as usize],
            };
            println!("Storing {item:?}");

            store_item::<_, _>(
                &mut big_flash,
                0x0000..0x1000,
                &mut NoCache,
                &mut data_buffer,
                item,
            )
            .await
            .unwrap();
        }

        assert_eq!(
            store_item::<_, _>(
                &mut big_flash,
                0x0000..0x1000,
                &mut NoCache,
                &mut data_buffer,
                MockStorageItem {
                    key: UPPER_BOUND,
                    value: vec![0; UPPER_BOUND as usize],
                },
            )
            .await,
            Err(MapError::FullStorage)
        );

        for i in 0..UPPER_BOUND {
            let item = fetch_item::<MockStorageItem, _>(
                &mut big_flash,
                0x0000..0x1000,
                &mut NoCache,
                &mut data_buffer,
                i as u8,
            )
            .await
            .unwrap()
            .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item.value, vec![i as u8; i as usize]);
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
                let item = MockStorageItem {
                    key: i as u8,
                    value: vec![i as u8; LENGHT_PER_KEY[i]],
                };

                store_item::<_, _>(
                    &mut flash,
                    0x0000..0x4000,
                    &mut NoCache,
                    &mut data_buffer,
                    item,
                )
                .await
                .unwrap();
            }
        }

        for i in 0..24 {
            let item = fetch_item::<MockStorageItem, _>(
                &mut flash,
                0x0000..0x4000,
                &mut NoCache,
                &mut data_buffer,
                i as u8,
            )
            .await
            .unwrap()
            .unwrap();

            println!("Fetched {item:?}");

            assert_eq!(item.value, vec![i as u8; LENGHT_PER_KEY[i]]);
        }
    }
}
