#![cfg_attr(not(test), no_std)]

// Assumptions made in this crate:
//
// - flash erase size is quite big, aka, this is a paged flash
// - flash write size is quite small, so it writes words an not full pages
// - flash read size is 1, so the flash is byte addressable

use core::{fmt::Debug, ops::Range};
use embedded_storage::nor_flash::NorFlash;

#[cfg(test)]
mod mock_flash;

pub fn fetch_item<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    search_key: I::Key,
) -> Result<Option<I>, Error<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 3);
    assert_eq!(S::READ_SIZE, 1);

    // We need to find the page we were last using. This should be the only partial open page.
    let mut last_used_page =
        find_first_page::<I, S>(flash, flash_range.clone(), 0, PageState::PartialOpen)?;

    if last_used_page.is_none() {
        // In the event that all pages are still open or the last used page was just closed, we search for the first open page.
        // If the page one before that is closed, then that's the last used page.
        if let Some(first_open_page) =
            find_first_page::<I, S>(flash, flash_range.clone(), 0, PageState::Open)?
        {
            let previous_page = previous_page::<S>(flash_range.clone(), first_open_page);
            if get_page_state::<I, S>(flash, flash_range.clone(), previous_page)?
                == PageState::Closed
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

        if get_page_state::<I, S>(flash, flash_range.clone(), previous_page)? != PageState::Closed {
            // We've looked through all the pages with data and couldn't find the item
            return Ok(None);
        }

        current_page_to_check = previous_page;
    }

    Ok(newest_found_item)
}

pub fn store_item<I: StorageItem, S: NorFlash, const PAGE_BUFFER_SIZE: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
    item: I,
) -> Result<(), Error<I::Error, S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 3);
    assert_eq!(S::READ_SIZE, 1);

    assert_eq!(PAGE_BUFFER_SIZE, S::ERASE_SIZE);

    let mut next_page_to_use = None;

    // If there is a partial open page, we try to write in that first if there is enough space
    if let Some(partial_open_page) =
        find_first_page::<I, S>(flash, flash_range.clone(), 0, PageState::PartialOpen)?
    {
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
        match item.serialize_into(&mut buffer[..MAX_STORAGE_ITEM_SIZE.min(available_bytes_in_page)])
        {
            Ok(mut used_bytes) => {
                // The item fits, so let's write it to flash
                // We must round up the used size because we can only write with full words
                if used_bytes % S::WRITE_SIZE > 0 {
                    used_bytes += S::WRITE_SIZE - (used_bytes % S::WRITE_SIZE);
                }

                flash
                    .write(last_start_address, &buffer[..used_bytes])
                    .map_err(Error::Storage)?;
                return Ok(());
            }
            Err(e) if e.is_buffer_too_small() => {
                // The item doesn't fit here, so we need to close this page and move to the next
                close_page::<I, S>(flash, flash_range.clone(), partial_open_page)?;
                next_page_to_use = Some(next_page::<S>(flash_range.clone(), partial_open_page));
            }
            Err(e) => {
                return Err(Error::Item(e));
            }
        }
    }

    // If we get here, there was no partial page found or the partial page has now been closed because the item didn't fit.
    // If there was a partial page, then we need to look at the next page. If it's open we just use it and if it's closed we must erase it.
    // If there was no partial page, we just use the first open page.

    match next_page_to_use {
        Some(next_page_to_use) => {
            let next_page_state =
                get_page_state::<I, S>(flash, flash_range.clone(), next_page_to_use)?;

            if next_page_state == PageState::Open {
                partial_close_page::<I, S>(flash, flash_range.clone(), next_page_to_use)?;
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

                partial_close_page::<I, S>(flash, flash_range.clone(), next_page_to_use)?;

                // Now add back any messages we now miss
                // Because the page is already cleared, we can just search for the message keys through the normal API
                // And also because partial page writes go before this, we can just write the items through the normal API

                let mut old_data_slice =
                    &page_cache_buffer[S::WRITE_SIZE..S::ERASE_SIZE - S::WRITE_SIZE];

                while !old_data_slice.iter().all(|b| *b == 0xFF) {
                    let (item, mut used_bytes) =
                        I::deserialize_from(old_data_slice).map_err(Error::Item)?;

                    if fetch_item::<I, S>(flash, flash_range.clone(), item.key())?.is_none() {
                        store_item::<I, S, PAGE_BUFFER_SIZE>(flash, flash_range.clone(), item)?;
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
                match find_first_page::<I, S>(flash, flash_range.clone(), 0, PageState::Open)? {
                    Some(first_open_page) => first_open_page,
                    None => {
                        // Uh oh, no open pages.
                        // Something has gone wrong.
                        // We should never get here.
                        // Let's recover
                        flash
                            .erase(flash_range.start, flash_range.end)
                            .map_err(Error::Storage)?;

                        0
                    }
                };

            partial_close_page::<I, S>(flash, flash_range.clone(), first_open_page)?;
        }
    }

    // If we get here, we just freshly partially closed a new page, so this should succeed
    store_item::<I, S, PAGE_BUFFER_SIZE>(flash, flash_range, item)
}

fn find_first_page<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    starting_page_index: usize,
    page_state: PageState,
) -> Result<Option<usize>, Error<I::Error, S::Error>> {
    for page_index in get_pages::<S>(flash_range.clone(), starting_page_index) {
        if page_state == get_page_state::<I, S>(flash, flash_range.clone(), page_index)? {
            return Ok(Some(page_index));
        }
    }

    Ok(None)
}

/// Get all pages in the flash range from the given start to end (that might wrap back to 0)
fn get_pages<S: NorFlash>(
    flash_range: Range<u32>,
    starting_page_index: usize,
) -> impl Iterator<Item = usize> {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    flash_range
        .step_by(S::ERASE_SIZE)
        .enumerate()
        .map(|(index, _)| index)
        .cycle()
        .skip(starting_page_index)
        .take(page_count)
}

fn next_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;
    (page_index + 1) % page_count
}

fn previous_page<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> usize {
    let page_count = flash_range.len() / S::ERASE_SIZE;

    match page_index.checked_sub(1) {
        Some(new_page_index) => new_page_index,
        None => page_count - 1,
    }
}

fn calculate_page_address<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> u32 {
    flash_range.start + (S::ERASE_SIZE * page_index) as u32
}
fn calculate_page_end_address<S: NorFlash>(flash_range: Range<u32>, page_index: usize) -> u32 {
    flash_range.start + (S::ERASE_SIZE * (page_index + 1)) as u32
}

fn get_page_state<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<PageState, Error<I::Error, S::Error>> {
    let page_address = calculate_page_address::<S>(flash_range, page_index);

    let mut buffer = [0; 16];
    flash
        .read(page_address, &mut buffer[..S::READ_SIZE])
        .map_err(Error::Storage)?;
    let start_marker = buffer[0];

    if start_marker != MARKER {
        // The page start is not marked, so it is unused
        return Ok(PageState::Open);
    }

    // The page start is marked, so it can be full or partially full
    // We need to look at the end marker to know

    flash
        .read(
            page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
            &mut buffer[..S::READ_SIZE],
        )
        .map_err(Error::Storage)?;
    let end_marker = buffer[S::READ_SIZE - 1];

    if end_marker != MARKER {
        // The page end is not marked, so it is only partially filled and thus open
        return Ok(PageState::PartialOpen);
    }

    // Both start and end are marked, so this page is closed
    Ok(PageState::Closed)
}

fn read_page_items<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<
    impl Iterator<Item = Result<(I, u32, usize), Error<I::Error, S::Error>>> + '_,
    Error<I::Error, S::Error>,
> {
    let mut read_buffer = [0xFF; MAX_STORAGE_ITEM_SIZE];
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), page_index) + S::WRITE_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), page_index) - S::WRITE_SIZE as u32;
    let mut read_buffer_start_index_into_page = 0;

    flash
        .read(
            page_data_start_address,
            &mut read_buffer[0..MAX_STORAGE_ITEM_SIZE
                .min((page_data_end_address - page_data_start_address) as usize)],
        )
        .map_err(Error::Storage)?;

    Ok(core::iter::from_fn(move || {
        // Now we deserialize the items from the buffer one by one
        // Every time we proceed, we remove the bytes we used and fill the buffer back up

        if read_buffer.iter().all(|b| *b == 0xFF) {
            // The entire buffer is in the erased state, so we know that the rest is empty
            return None;
        }

        match I::deserialize_from(&read_buffer) {
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
                read_buffer.copy_within(used_bytes.., 0);
                // We need to replenish the used_bytes at the end of the buffer
                let replenish_slice = &mut read_buffer[MAX_STORAGE_ITEM_SIZE - used_bytes..];

                let replenish_start_address = page_data_start_address
                    + read_buffer_start_index_into_page as u32
                    + MAX_STORAGE_ITEM_SIZE as u32
                    - used_bytes as u32;

                let unread_bytes_left_in_page =
                    page_data_end_address.saturating_sub(replenish_start_address);

                let (read_slice, fill_slice) = replenish_slice
                    .split_at_mut((unread_bytes_left_in_page as usize).min(replenish_slice.len()));

                if !read_slice.is_empty() {
                    if let Err(e) = flash
                        .read(replenish_start_address, read_slice)
                        .map_err(Error::Storage)
                    {
                        return Some(Err(e));
                    }
                }
                fill_slice.fill(0xFF);

                Some(return_item)
            }
            Err(e) => {
                // We can't deserialize an item, so something must have gone wrong.
                // We shouldn't ever get here.
                // To recover, we erase the flash.
                if let Err(e) = flash
                    .erase(flash_range.start, flash_range.end)
                    .map_err(Error::Storage)
                {
                    return Some(Err(e));
                }
                Some(Err(Error::Item(e)))
            }
        }
    }))
}

/// Fully closes a page by writing both the start and end marker
fn close_page<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<(), Error<I::Error, S::Error>> {
    partial_close_page::<I, S>(flash, flash_range.clone(), page_index)?;

    let current_state = get_page_state::<I, S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::PartialOpen {
        return Ok(());
    }

    let buffer = [MARKER; 16];
    // Close the end marker
    flash
        .write(
            calculate_page_end_address::<S>(flash_range, page_index) - S::WRITE_SIZE as u32,
            &buffer[..S::WRITE_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(())
}

/// Partially close a page by writing the start marker
fn partial_close_page<I: StorageItem, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> Result<(), Error<I::Error, S::Error>> {
    let current_state = get_page_state::<I, S>(flash, flash_range.clone(), page_index)?;

    if current_state != PageState::Open {
        return Ok(());
    }

    let buffer = [MARKER; 16];
    // Close the start marker
    flash
        .write(
            calculate_page_address::<S>(flash_range, page_index),
            &buffer[..S::WRITE_SIZE],
        )
        .map_err(Error::Storage)?;

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PageState {
    Closed,
    PartialOpen,
    Open,
}

const MARKER: u8 = 0;

/// A way of serializing and deserializing items in the storage.
///
/// A serialized byte pattern of all `0xFF` is invalid and must never be the result of the `serialize_into` function
/// and `deserialize_from` must always return an error for it.
///
/// The given buffer to serialize in and deserialize from is never bigger than [MAX_STORAGE_ITEM_SIZE] bytes, so make sure the item is
/// smaller than that.
pub trait StorageItem {
    type Key: Eq;
    type Error: StorageItemError;

    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error>;
    fn deserialize_from(buffer: &[u8]) -> Result<(Self, usize), Self::Error>
    where
        Self: Sized;

    fn key(&self) -> Self::Key;
}

pub const MAX_STORAGE_ITEM_SIZE: usize = 512;

pub trait StorageItemError: Debug {
    fn is_buffer_too_small(&self) -> bool;
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
    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;

    #[derive(Debug, PartialEq, Eq)]
    struct MockStorageItem {
        key: u8,
        value: u8,
    }

    #[derive(Debug)]
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
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 0, PageState::Open)
                .unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(
                &mut flash,
                0x000..0x400,
                0,
                PageState::PartialOpen
            )
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(
                &mut flash,
                0x000..0x400,
                1,
                PageState::PartialOpen
            )
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(
                &mut flash,
                0x000..0x400,
                2,
                PageState::PartialOpen
            )
            .unwrap(),
            Some(2)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 3, PageState::Open)
                .unwrap(),
            Some(3)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(
                &mut flash,
                0x000..0x200,
                0,
                PageState::PartialOpen
            )
            .unwrap(),
            None
        );

        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 0, PageState::Closed)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 1, PageState::Closed)
                .unwrap(),
            Some(1)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 2, PageState::Closed)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x000..0x400, 3, PageState::Closed)
                .unwrap(),
            Some(0)
        );
        assert_eq!(
            find_first_page::<MockStorageItem, _>(&mut flash, 0x200..0x400, 0, PageState::Closed)
                .unwrap(),
            None
        );
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
    }
}
