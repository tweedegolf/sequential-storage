//! A queue (fifo) implementation for storing arbitrary data in flash memory.
//!
//! Use [push] to add data to the fifo and use [peek] and [pop] to get the data back.

use crate::item::{find_next_free_item_spot, read_item_headers, Item, ItemHeader};

use super::*;
use embedded_storage::nor_flash::MultiwriteNorFlash;

/// Push data into the queue in the given flash memory with the given range.
/// The data can only be taken out with the [pop] function.
///
/// `data` must not be empty and must fit on a single page.
///
/// Old data will not be overwritten unless `allow_overwrite_old_data` is true.
/// If it is, then if the queue is full, the oldest data is removed to make space for the new data.
///
/// *Note: If a page is already used and you push more data than the remaining capacity of the page,
/// the entire remaining capacity will go unused because the data is stored on the next page.*
pub fn push<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &[u8],
    allow_overwrite_old_data: bool,
) -> Result<(), Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    if data.is_empty() {
        return Err(Error::BufferTooSmall);
    }

    // Data must fit in a single page. We use two write words for page markings and
    // at least 2 bytes or a word for length encoding
    if data.len()
        > ItemHeader::available_data_bytes::<S>((S::ERASE_SIZE - S::WORD_SIZE * 2) as u32).unwrap()
            as usize
    // Length must be smaller than 0x7FFE so we can store an extra recognition bit
    {
        return Err(Error::BufferTooBig);
    }

    let current_page = find_youngest_page(flash, flash_range.clone())?;

    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), current_page) - S::WORD_SIZE as u32;

    partial_close_page(flash, flash_range.clone(), current_page)?;

    // Find the last item on the page so we know where we need to write

    let mut next_address =
        find_next_free_item_spot(flash, page_data_start_address, page_data_end_address)?
            .unwrap_or(page_data_end_address);

    let data_cap_left =
        ItemHeader::available_data_bytes::<S>(page_data_end_address.saturating_sub(next_address))
            .unwrap_or(0);

    if data.len() > data_cap_left as usize {
        // No cap left on this page, move to the next page
        let next_page = next_page::<S>(flash_range.clone(), current_page);
        match get_page_state(flash, flash_range.clone(), next_page)? {
            PageState::Open => {
                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address = calculate_page_address::<S>(flash_range.clone(), next_page)
                    + S::WORD_SIZE as u32;
            }
            PageState::Closed => {
                if !allow_overwrite_old_data {
                    return Err(Error::FullStorage);
                }

                flash
                    .erase(
                        calculate_page_address::<S>(flash_range.clone(), next_page),
                        calculate_page_end_address::<S>(flash_range.clone(), next_page),
                    )
                    .map_err(Error::Storage)?;

                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address = calculate_page_address::<S>(flash_range.clone(), next_page)
                    + S::WORD_SIZE as u32;
            }
            PageState::PartialOpen => {
                // This should never happen
                #[cfg(feature = "defmt")]
                defmt::error!("Corrupted: A we expected an open or closed page, but found a partial open page");
                return Err(Error::Corrupted);
            }
        }

        close_page(flash, flash_range.clone(), current_page)?;
    }

    Item::write_new(flash, next_address, data)?;

    Ok(())
}

/// Peek at the oldest data.
///
/// If you also want to remove the data use [pop].
///
/// The data is written to the given data buffer and the part that was written is returned.
/// If the data buffer is not big enough an error is returned.
pub fn peek<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d [u8]>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let oldest_page = find_oldest_page(flash, flash_range.clone())?;

    for current_page in get_pages::<S>(flash_range.clone(), oldest_page) {
        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), current_page)
                - S::WORD_SIZE as u32;

        if let Some((found_item_header, found_item_address)) = read_item_headers(
            flash,
            page_data_start_address,
            page_data_end_address,
            |_, item_header, item_address| {
                if item_header.crc.is_some() {
                    ControlFlow::Break((item_header, item_address))
                } else {
                    ControlFlow::Continue(())
                }
            },
        )? {
            let (header, data_buffer) = found_item_header
                .read_item(
                    flash,
                    data_buffer,
                    found_item_address,
                    page_data_end_address,
                )?
                .unwrap()?
                .destruct();

            return Ok(Some(&data_buffer[..header.length.get() as usize]));
        }
    }

    Ok(None)
}

/// Pop the oldest data from the queue.
///
/// If you don't want to remove the data use [peek].
///
/// The given `CAP` determines the buffer size with which is read.
/// An error is returned if the oldest data is longer than `CAP`.
pub fn pop<'d, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d [u8]>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let oldest_page = find_oldest_page(flash, flash_range.clone())?;

    for current_page in get_pages::<S>(flash_range.clone(), oldest_page) {
        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), current_page)
                - S::WORD_SIZE as u32;

        if let Some((found_item_header, found_item_address)) = read_item_headers(
            flash,
            page_data_start_address,
            page_data_end_address,
            |_, item_header, item_address| {
                if item_header.crc.is_some() {
                    ControlFlow::Break((item_header, item_address))
                } else {
                    ControlFlow::Continue(())
                }
            },
        )? {
            let (header, data_buffer) = found_item_header
                .read_item(
                    flash,
                    data_buffer,
                    found_item_address,
                    page_data_end_address,
                )?
                .unwrap()?
                .destruct();

            let header = header.erase_data(flash, found_item_address)?;

            if current_page != oldest_page {
                // The oldest page didn't yield an item, so we can now erase it
                flash
                    .erase(
                        calculate_page_address::<S>(flash_range.clone(), oldest_page),
                        calculate_page_end_address::<S>(flash_range.clone(), oldest_page),
                    )
                    .map_err(Error::Storage)?;
            }

            return Ok(Some(&data_buffer[..header.length.get() as usize]));
        }
    }

    Ok(None)
}

fn find_youngest_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<usize, Error<S::Error>> {
    let last_used_page = find_first_page(flash, flash_range.clone(), 0, PageState::PartialOpen)?;

    if let Some(last_used_page) = last_used_page {
        return Ok(last_used_page);
    }

    // We have no partial open page. Search for an open page to start in
    let first_open_page = find_first_page(flash, flash_range, 0, PageState::Open)?;

    if let Some(first_open_page) = first_open_page {
        return Ok(first_open_page);
    }

    // All pages are closed... This is not correct.
    #[cfg(feature = "defmt")]
    defmt::error!("Corrupted: All pages are closed");

    Err(Error::Corrupted)
}

fn find_oldest_page<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<usize, Error<S::Error>> {
    let youngest_page = find_youngest_page(flash, flash_range.clone())?;

    // The oldest page is the first non-open page after the youngest page
    let oldest_closed_page = find_first_page(flash, flash_range, youngest_page, PageState::Closed)?;

    Ok(oldest_closed_page.unwrap_or(youngest_page))
}

#[cfg(test)]
mod tests {
    use super::*;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    fn peek_and_overwrite_old_data() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;
        let mut data_buffer = [0; 1024];

        assert_eq!(
            peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
            None
        );

        push(&mut flash, flash_range.clone(), &[0xAA; 26], false).unwrap();
        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xAA; 26]
        );
        push(&mut flash, flash_range.clone(), &[0xBB; 26], false).unwrap();
        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xAA; 26]
        );

        // Flash is full, this should fail
        push(&mut flash, flash_range.clone(), &[0xCC; 26], false).unwrap_err();
        // Now we allow overwrite, so it should work
        push(&mut flash, flash_range.clone(), &[0xDD; 26], true).unwrap();

        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xBB; 26]
        );
        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xBB; 26]
        );

        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xDD; 26]
        );
        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xDD; 26]
        );

        assert_eq!(
            peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
            None
        );
        assert_eq!(
            pop(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
            None
        );
    }

    #[test]
    fn push_pop() {
        let mut flash = MockFlashBig::new();
        let flash_range = 0x000..0x1000;
        let mut data_buffer = [0; 1024];

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 244 + 1];

            push(&mut flash, flash_range.clone(), &data, true).unwrap();
            assert_eq!(
                &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    fn push_pop_tiny() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;
        let mut data_buffer = [0; 1024];

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            push(&mut flash, flash_range.clone(), &data, true).unwrap();
            assert_eq!(
                &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    fn push_lots_then_pop_lots() {
        let mut flash = MockFlashBig::new();
        let flash_range = 0x000..0x1000;
        let mut data_buffer = [0; 1024];

        for _ in 0..100 {
            for i in 0..20 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
            }

            for i in 0..5 {
                let data = vec![i as u8; 50];
                assert_eq!(
                    &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                        .unwrap()
                        .unwrap()[..],
                    &data,
                    "At {i}"
                );
            }

            for i in 20..25 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
            }

            for i in 5..25 {
                let data = vec![i as u8; 50];
                assert_eq!(
                    &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                        .unwrap()
                        .unwrap()[..],
                    &data,
                    "At {i}"
                );
            }
        }
    }

    #[test]
    fn pop_with_empty_section() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;
        let mut data_buffer = [0; 1024];

        push(&mut flash, flash_range.clone(), &[0xAA; 20], false).unwrap();
        push(&mut flash, flash_range.clone(), &[0xBB; 20], false).unwrap();

        // There's now an unused gap at the end of the first page

        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xAA; 20]
        );
        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xBB; 20]
        );
    }
}
