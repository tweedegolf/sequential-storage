use super::*;

/// Get a storage item from the flash.
/// Only the last stored item of the given key is returned.
///
/// If no value with the key is found, None is returned.
pub fn fetch_item<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    search_key: I::Key,
) -> Result<Option<I>, MapError<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 3);
    assert_eq!(S::READ_SIZE, 1);

    // We need to find the page we were last using. This should be the only partial open page.
    let mut last_used_page =
        find_first_page(flash, flash_range.clone(), 0, PageState::PartialOpen)?;

    #[cfg(feature = "defmt")]
    defmt::trace!("Fetch item, last used page: {}", last_used_page);

    if last_used_page.is_none() {
        // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
        // If the page one before that is closed, then that's the last used page.
        if let Some(first_open_page) =
            find_first_page(flash, flash_range.clone(), 0, PageState::Open)?
        {
            let previous_page = previous_page::<S>(flash_range.clone(), first_open_page);
            if get_page_state(flash, flash_range.clone(), previous_page)?.is_closed() {
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
            flash
                .erase(flash_range.start, flash_range.end)
                .map_err(Error::Storage)?;
            return Ok(None);
        }
    }

    // We must now find the most recent storage item with the key that was asked for.
    // If we don't find it in the current page, then we check again in the previous page if that page is closed.

    let mut current_page_to_check = last_used_page.unwrap();
    let mut newest_found_item = None;

    loop {
        for found_item_result in
            read_page_items::<I, S>(flash, flash_range.clone(), current_page_to_check)?
        {
            let found_item = found_item_result?.0;
            if found_item.key() == search_key {
                newest_found_item = Some(found_item);
            }
        }

        // We've found the item! We can stop searching
        if newest_found_item.is_some() {
            break;
        }

        // We have not found the item. We've got to look in the previous page, but only if that page is closed and contains data.
        let previous_page = previous_page::<S>(flash_range.clone(), current_page_to_check);

        if get_page_state(flash, flash_range.clone(), previous_page)? != PageState::Closed {
            // We've looked through all the pages with data and couldn't find the item
            return Ok(None);
        }

        current_page_to_check = previous_page;
    }

    Ok(newest_found_item)
}

/// Store an item into flash memory.
/// It will overwrite the last value that has the same key.
///
/// Because const-generics are not fully done in Rust yet, you will have to provide the `PAGE_BUFFER_SIZE`, which has
/// to be the same value as the `ERASE_SIZE` of the flash.
pub fn store_item<I: StorageItem, S: NorFlash, const PAGE_BUFFER_SIZE: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
    item: I,
) -> Result<(), MapError<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 3);
    assert_eq!(S::READ_SIZE, 1);

    assert_eq!(PAGE_BUFFER_SIZE, S::ERASE_SIZE);

    return store_item_inner::<I, S, PAGE_BUFFER_SIZE>(flash, flash_range, item, 0);

    fn store_item_inner<I: StorageItem, S: NorFlash, const PAGE_BUFFER_SIZE: usize>(
        flash: &mut S,
        flash_range: Range<u32>,
        item: I,
        recursion_level: usize,
    ) -> Result<(), MapError<I::Error, S::Error>> {
        #[cfg(feature = "defmt")]
        defmt::trace!("Store item inner. Recursion: {}", recursion_level);

        // Check if we're in an infinite recursion which happens when
        if recursion_level == get_pages::<S>(flash_range.clone(), 0).count() {
            return Err(MapError::FullStorage);
        }

        let mut next_page_to_use = None;

        // If there is a partial open page, we try to write in that first if there is enough space
        if let Some(partial_open_page) =
            find_first_page(flash, flash_range.clone(), 0, PageState::PartialOpen)?
        {
            #[cfg(feature = "defmt")]
            defmt::trace!("Partial open page found: {}", partial_open_page);

            // We've got to search where the free space is since the page starts with items present already

            let page_data_start_address =
                calculate_page_address::<S>(flash_range.clone(), partial_open_page)
                    + S::WRITE_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(flash_range.clone(), partial_open_page)
                    - S::WRITE_SIZE as u32;

            let mut last_start_address = page_data_start_address;

            for found_item_result in
                read_page_items::<I, S>(flash, flash_range.clone(), partial_open_page)?
            {
                let (_, item_address, item_size) = found_item_result?;
                last_start_address = item_address + item_size as u32;
            }

            let available_bytes_in_page = (page_data_end_address - last_start_address) as usize;

            let mut buffer = [0xFF; MAX_STORAGE_ITEM_SIZE];
            match item
                .serialize_into(&mut buffer[..MAX_STORAGE_ITEM_SIZE.min(available_bytes_in_page)])
            {
                Ok(mut used_bytes) => {
                    // The item fits, so let's write it to flash
                    // We must round up the used size because we can only write with full words
                    if used_bytes % S::WRITE_SIZE > 0 {
                        used_bytes += S::WRITE_SIZE - (used_bytes % S::WRITE_SIZE);
                    }

                    flash
                        .write(last_start_address, &buffer[..used_bytes])
                        .map_err(MapError::Storage)?;

                    #[cfg(feature = "defmt")]
                    defmt::trace!("Item has been written ok");

                    return Ok(());
                }
                Err(e) if e.is_buffer_too_small() => {
                    #[cfg(feature = "defmt")]
                    defmt::trace!(
                        "Partial open page is too small. Closing it now: {}",
                        partial_open_page
                    );

                    // The item doesn't fit here, so we need to close this page and move to the next
                    close_page(flash, flash_range.clone(), partial_open_page)?;
                    next_page_to_use = Some(next_page::<S>(flash_range.clone(), partial_open_page));
                }
                Err(e) => {
                    return Err(MapError::Item(e));
                }
            }
        }

        // If we get here, there was no partial page found or the partial page has now been closed because the item didn't fit.
        // If there was a partial page, then we need to look at the next page. If it's open we just use it and if it's closed we must erase it.
        // If there was no partial page, we just use the first open page.

        #[cfg(feature = "defmt")]
        defmt::trace!("Next page to use: {}", next_page_to_use);

        match next_page_to_use {
            Some(next_page_to_use) => {
                let next_page_state = get_page_state(flash, flash_range.clone(), next_page_to_use)?;

                if next_page_state.is_open() {
                    partial_close_page(flash, flash_range.clone(), next_page_to_use)?;
                } else {
                    let mut page_cache_buffer = [0; PAGE_BUFFER_SIZE];

                    // So the next page isn't open. We must clear it.
                    // But in that process we can lose information. A value could only be stored once in the page we're now gonna clear.
                    // So we must read the full page into ram, clear the page and then add the now missing value back.
                    flash
                        .read(
                            calculate_page_address::<S>(flash_range.clone(), next_page_to_use),
                            &mut page_cache_buffer,
                        )
                        .map_err(Error::Storage)?;
                    flash
                        .erase(
                            calculate_page_address::<S>(flash_range.clone(), next_page_to_use),
                            calculate_page_end_address::<S>(flash_range.clone(), next_page_to_use),
                        )
                        .map_err(Error::Storage)?;

                    partial_close_page(flash, flash_range.clone(), next_page_to_use)?;

                    // Now add back any messages we now miss
                    // Because the page is already cleared, we can just search for the message keys through the normal API
                    // And also because partial page writes go before this, we can just write the items through the normal API

                    let mut old_data_slice =
                        &page_cache_buffer[S::WRITE_SIZE..S::ERASE_SIZE - S::WRITE_SIZE];

                    while !old_data_slice.iter().all(|b| *b == 0xFF) {
                        let (item, mut used_bytes) =
                            I::deserialize_from(old_data_slice).map_err(MapError::Item)?;

                        if fetch_item::<I, S>(flash, flash_range.clone(), item.key())?.is_none() {
                            store_item_inner::<I, S, PAGE_BUFFER_SIZE>(
                                flash,
                                flash_range.clone(),
                                item,
                                recursion_level, // We don't need to increase the recursion level here because the old item will always fit on the new page
                            )?;
                        }

                        // Round up to the nearest word
                        if used_bytes % S::WRITE_SIZE > 0 {
                            used_bytes += S::WRITE_SIZE - (used_bytes % S::WRITE_SIZE);
                        }

                        old_data_slice = &old_data_slice[used_bytes..];
                    }
                }
            }
            None => {
                // There's no partial open page, so we just gotta turn the first open page into a partial open one
                let first_open_page =
                    match find_first_page(flash, flash_range.clone(), 0, PageState::Open)? {
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
                            // Let's recover
                            flash
                                .erase(flash_range.start, flash_range.end)
                                .map_err(MapError::Storage)?;

                            0
                        }
                    };

                partial_close_page(flash, flash_range.clone(), first_open_page)?;
            }
        }

        // If we get here, we just freshly partially closed a new page, so this should succeed
        store_item_inner::<I, S, PAGE_BUFFER_SIZE>(flash, flash_range, item, recursion_level + 1)
    }
}

fn read_page_items<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<
    impl Iterator<Item = Result<(I, u32, usize), MapError<I::Error, S::Error>>> + '_,
    MapError<I::Error, S::Error>,
> {
    let mut read_buffer = [0xFF; MAX_STORAGE_ITEM_SIZE];
    let mut used_read_buffer = 0;
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), page_index) + S::WRITE_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), page_index) - S::WRITE_SIZE as u32;
    let mut read_buffer_start_index_into_page = 0;

    flash
        .read(
            page_data_start_address,
            &mut read_buffer[used_read_buffer
                ..MAX_STORAGE_ITEM_SIZE
                    .min((page_data_end_address - page_data_start_address) as usize)],
        )
        .map_err(MapError::Storage)?;

    Ok(core::iter::from_fn(move || {
        // Now we deserialize the items from the buffer one by one
        // Every time we proceed, we remove the bytes we used and fill the buffer back up

        macro_rules! replenish_read_buffer {
            () => {{
                read_buffer.copy_within(used_read_buffer.., 0);
                // We need to replenish the used_bytes at the end of the buffer
                let replenish_slice = &mut read_buffer[MAX_STORAGE_ITEM_SIZE - used_read_buffer..];

                let replenish_start_address = page_data_start_address
                    + read_buffer_start_index_into_page as u32
                    + MAX_STORAGE_ITEM_SIZE as u32
                    - used_read_buffer as u32;

                let unread_bytes_left_in_page =
                    page_data_end_address.saturating_sub(replenish_start_address);

                let (read_slice, fill_slice) = replenish_slice
                    .split_at_mut((unread_bytes_left_in_page as usize).min(replenish_slice.len()));

                if !read_slice.is_empty() {
                    if let Err(e) = flash
                        .read(replenish_start_address, read_slice)
                        .map_err(MapError::Storage)
                    {
                        return Some(Err(e.into()));
                    }
                }
                fill_slice.fill(0xFF);
                used_read_buffer = 0;
            }};
        }

        if used_read_buffer == read_buffer.len() {
            replenish_read_buffer!();
        }

        if read_buffer[used_read_buffer..].iter().all(|b| *b == 0xFF) {
            // The entire buffer is in the erased state, so we know that the rest is empty
            return None;
        }

        loop {
            match I::deserialize_from(&read_buffer[used_read_buffer..]) {
                Ok((item, mut used_bytes)) => {
                    // We can only write in whole words, so we round up the used bytes so the math works
                    if used_bytes % S::WRITE_SIZE > 0 {
                        used_bytes += S::WRITE_SIZE - (used_bytes % S::WRITE_SIZE);
                    }

                    let return_item = Ok((
                        item,
                        page_data_start_address + read_buffer_start_index_into_page as u32,
                        used_bytes,
                    ));

                    read_buffer_start_index_into_page += used_bytes;
                    used_read_buffer += used_bytes;

                    break Some(return_item);
                }
                Err(e) if e.is_buffer_too_small() && used_read_buffer > 0 => {
                    replenish_read_buffer!();
                }
                Err(e) => {
                    // We can't deserialize an item, so something must have gone wrong.
                    // We shouldn't ever get here.
                    // To recover, we erase the flash.
                    if let Err(e) = flash
                        .erase(flash_range.start, flash_range.end)
                        .map_err(MapError::Storage)
                    {
                        return Some(Err(e));
                    }
                    return Some(Err(MapError::Item(e)));
                }
            }
        }
    }))
}

/// A way of serializing and deserializing items in the storage.
///
/// A serialized byte pattern of all `0xFF` is invalid and must never be the result of the `serialize_into` function
/// and `deserialize_from` must always return an error for it.
///
/// The given buffer to serialize in and deserialize from is never bigger than [MAX_STORAGE_ITEM_SIZE] bytes, so make sure the item is
/// smaller than that.
pub trait StorageItem {
    /// The key type of the key-value pair
    type Key: Eq;
    /// The error type for serialization and deserialization
    type Error: StorageItemError;

    /// Serialize the key-value item into the given buffer.
    /// Returns the number of bytes the buffer was filled with or an error.
    ///
    /// The serialized bytes must not all be `0xFF`. One way to prevent this is to serialize an extra 0 byte at the end if that is the case.
    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error>;
    /// Deserialize the key-value item from the given buffer.
    /// The buffer is likely bigger than the size of the item.
    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), Self::Error>
    where
        Self: Sized;

    /// The key of the key-value item. It is used by the storage to know what the key of this item is.
    fn key(&self) -> Self::Key;
}

/// The maximum size in bytes that a storage item can be
pub const MAX_STORAGE_ITEM_SIZE: usize = 512;

/// A trait that the storage item error needs to implement
pub trait StorageItemError: Debug {
    /// Returns true if the error indicates that the buffer is too small to contain the storage item
    fn is_buffer_too_small(&self) -> bool;
}

/// The main error type
#[non_exhaustive]
#[derive(Debug, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum MapError<I, S> {
    /// A storage item error
    Item(I),
    /// An error in the storage (flash)
    Storage(S),
    /// The item cannot be stored anymore because the storage is full.
    /// If you get this error some data may be lost.
    FullStorage,
    /// It's been detected that the memory is likely corrupted.
    /// You may want to erase the memory to recover.
    Corrupted,
}

impl<S, I> From<super::Error<S>> for MapError<I, S> {
    fn from(value: super::Error<S>) -> Self {
        match value {
            Error::Storage(e) => Self::Storage(e),
            Error::FullStorage => Self::FullStorage,
            Error::Corrupted => Self::Corrupted,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

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
    fn store_and_fetch() {
        let mut flash = MockFlashBig::new();
        let flash_range = 0x000..0x1000;

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 0).unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 60).unwrap();
        assert_eq!(item, None);

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 0xFF).unwrap();
        assert_eq!(item, None);

        store_item::<_, _, 1024>(
            &mut flash,
            flash_range.clone(),
            MockStorageItem { key: 0, value: 5 },
        )
        .unwrap();
        store_item::<_, _, 1024>(
            &mut flash,
            flash_range.clone(),
            MockStorageItem { key: 0, value: 6 },
        )
        .unwrap();

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 0)
            .unwrap()
            .unwrap();
        assert_eq!(item.key, 0);
        assert_eq!(item.value, 6);

        store_item::<_, _, 1024>(
            &mut flash,
            flash_range.clone(),
            MockStorageItem { key: 1, value: 2 },
        )
        .unwrap();

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 0)
            .unwrap()
            .unwrap();
        assert_eq!(item.key, 0);
        assert_eq!(item.value, 6);

        let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), 1)
            .unwrap()
            .unwrap();
        assert_eq!(item.key, 1);
        assert_eq!(item.value, 2);

        for index in 0..4000 {
            store_item::<_, _, 1024>(
                &mut flash,
                flash_range.clone(),
                MockStorageItem {
                    key: (index % 10) as u8,
                    value: (index % 10) as u8 * 2,
                },
            )
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), i)
                .unwrap()
                .unwrap();
            assert_eq!(item.key, i);
            assert_eq!(item.value, i * 2);
        }

        for _ in 0..4000 {
            store_item::<_, _, 1024>(
                &mut flash,
                flash_range.clone(),
                MockStorageItem { key: 11, value: 0 },
            )
            .unwrap();
        }

        for i in 0..10 {
            let item = fetch_item::<MockStorageItem, _>(&mut flash, flash_range.clone(), i)
                .unwrap()
                .unwrap();
            assert_eq!(item.key, i);
            assert_eq!(item.value, i * 2);
        }

        println!(
            "Erases: {}, reads: {}, writes: {}",
            flash.erases, flash.reads, flash.writes
        );
    }

    #[test]
    fn store_too_many_items() {
        let mut tiny_flash = MockFlashTiny::new();

        for i in 0..30 {
            store_item::<_, _, 32>(
                &mut tiny_flash,
                0x00..0x40,
                MockStorageItem {
                    key: i as u8,
                    value: i as u8,
                },
            )
            .unwrap();
        }

        assert_eq!(
            store_item::<_, _, 32>(
                &mut tiny_flash,
                0x00..0x40,
                MockStorageItem {
                    key: 31 as u8,
                    value: 31 as u8,
                },
            ),
            Err(MapError::FullStorage)
        );

        for i in 0..30 {
            fetch_item::<MockStorageItem, _>(&mut tiny_flash, 0x00..0x40, i as u8)
                .unwrap()
                .unwrap();
        }
    }
}
