//! A queue (fifo) implementation for storing arbitrary data in flash memory.
//!
//! Use [push] to add data to the fifo and use [peek] and [pop] to get the data back.

use super::*;
use arrayvec::ArrayVec;
use embedded_storage::nor_flash::MultiwriteNorFlash;

/// Push data into the queue in the given flash memory with the given range.
/// The data can only be taken out with the [pop] function.
///
/// `data` must not be empty and can be at most 0x7FFE bytes long and must fit on a single page.
///
/// Old data will not be overwritten unless `allow_overwrite_old_data` is true.
/// If it is, then if the queue is full, the oldest data is removed to make space for the new data.
///
/// *Note: If a page is already used and you push more data than the remaining capacity of the page,
/// the entire remaining capacity will go unused because the data is stored on the next page.*
pub fn push<S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &[u8],
    allow_overwrite_old_data: bool,
) -> Result<(), Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 4);
    assert_eq!(S::READ_SIZE, 1);
    assert!(S::WRITE_SIZE <= 16);

    if data.is_empty() {
        return Err(Error::BufferTooSmall);
    }

    // Data must fit in a single page. We use two write words for page markings and
    // at least 2 bytes or a word for length encoding
    if data.len() > S::ERASE_SIZE - S::WRITE_SIZE * 2 - S::WRITE_SIZE.max(2) || data.len() > 0x7FFE
    // Length must be smaller than 0x7FFE so we can store an extra recognition bit
    {
        return Err(Error::BufferTooBig);
    }

    let current_page = find_youngest_page(flash, flash_range.clone())?;

    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), current_page) + S::WRITE_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), current_page) - S::WRITE_SIZE as u32;

    partial_close_page(flash, flash_range.clone(), current_page)?;

    // Find the last item on the page so we know where we need to write

    let mut next_address = match page_item_adresses_iter(flash, flash_range.clone(), current_page)
        .last()
        .transpose()?
    {
        Some(ItemAddress::Empty { address }) => address,
        Some(ItemAddress::Filled { .. }) => page_data_end_address,
        None => page_data_start_address,
    };

    let data_cap_left = page_data_end_address.saturating_sub(next_address);

    if data.len() + S::WRITE_SIZE.max(2) > data_cap_left as usize {
        // No cap left on this page, move to the next page
        let next_page = next_page::<S>(flash_range.clone(), current_page);
        match get_page_state(flash, flash_range.clone(), next_page)? {
            PageState::Open => {
                close_page(flash, flash_range.clone(), current_page)?;
                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address =
                    calculate_page_address::<S>(flash_range, next_page) + S::WRITE_SIZE as u32;
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

                close_page(flash, flash_range.clone(), current_page)?;
                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address =
                    calculate_page_address::<S>(flash_range, next_page) + S::WRITE_SIZE as u32;
            }
            PageState::PartialOpen => {
                // This should never happen
                #[cfg(feature = "defmt")]
                defmt::error!("Corrupted: A we expected an open or closed page, but found a partial open page");
                return Err(Error::Corrupted);
            }
        }
    }

    // Support write word size up to 16 bytes
    let mut buffer = [0; 16];
    // Write the length of the item
    buffer[0..2].copy_from_slice(&((data.len() as u16) | 0x1000).to_be_bytes());
    flash
        .write(next_address, &buffer[..S::WRITE_SIZE.max(2)])
        .map_err(Error::Storage)?;

    // Write all data that fits in the write words
    let aligned_data_len = (data.len() / S::WRITE_SIZE) * S::WRITE_SIZE;
    flash
        .write(
            next_address + S::WRITE_SIZE.max(2) as u32,
            &data[..aligned_data_len],
        )
        .map_err(Error::Storage)?;

    // Check if we have non-aligned data left over
    let left_over_data = &data[aligned_data_len..];
    if !left_over_data.is_empty() {
        buffer[..left_over_data.len()].copy_from_slice(left_over_data);
        buffer[left_over_data.len()..].fill(0);
        flash
            .write(
                next_address + S::WRITE_SIZE.max(2) as u32 + aligned_data_len as u32,
                &buffer[..S::WRITE_SIZE],
            )
            .map_err(Error::Storage)?;
    }

    Ok(())
}

/// Peek at the oldest data.
///
/// If you also want to remove the data use [pop].
///
/// The given `CAP` determines the buffer size with which is read.
/// An error is returned if the oldest data is longer than `CAP`.
pub fn peek<S: MultiwriteNorFlash, const CAP: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<Option<ArrayVec<u8, CAP>>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 4);
    assert_eq!(S::READ_SIZE, 1);
    assert!(S::WRITE_SIZE <= 16);

    let oldest_page = find_oldest_page(flash, flash_range.clone())?;

    let Some(ItemAddress::Filled { address, length }) =
        get_pages::<S>(flash_range.clone(), oldest_page)
            .filter_map(|page| {
                page_item_adresses_iter(flash, flash_range.clone(), page).find(|address| {
                    address.is_err() || matches!(address, Ok(ItemAddress::Filled { .. }))
                })
            })
            .next()
            .transpose()?
    else {
        return Ok(None);
    };

    if length as usize > CAP {
        return Err(Error::BufferTooBig);
    }

    let mut buffer = [0; CAP];
    // Read the data (at address + skip the length)
    flash
        .read(
            address + S::WRITE_SIZE.max(2) as u32,
            &mut buffer[..length as usize],
        )
        .map_err(Error::Storage)?;

    let mut return_data: ArrayVec<_, CAP> = buffer.into();
    return_data.truncate(length as usize);

    Ok(Some(return_data))
}

/// Pop the oldest data from the queue.
///
/// If you don't want to remove the data use [peek].
///
/// The given `CAP` determines the buffer size with which is read.
/// An error is returned if the oldest data is longer than `CAP`.
pub fn pop<S: MultiwriteNorFlash, const CAP: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<Option<ArrayVec<u8, CAP>>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WRITE_SIZE * 4);
    assert_eq!(S::READ_SIZE, 1);
    assert!(S::WRITE_SIZE <= 16);

    let oldest_page = find_oldest_page(flash, flash_range.clone())?;

    let Some(ItemAddress::Filled { address, length }) =
        get_pages::<S>(flash_range.clone(), oldest_page)
            .filter_map(|page| {
                page_item_adresses_iter(flash, flash_range.clone(), page).find(|address| {
                    address.is_err() || matches!(address, Ok(ItemAddress::Filled { .. }))
                })
            })
            .next()
            .transpose()?
    else {
        return Ok(None);
    };

    if length as usize > CAP {
        return Err(Error::BufferTooBig);
    }

    let mut buffer = [0; CAP];
    // Read the data (at address + skip the length)
    flash
        .read(
            address + S::WRITE_SIZE.max(2) as u32,
            &mut buffer[..length as usize],
        )
        .map_err(Error::Storage)?;

    let mut return_data: ArrayVec<_, CAP> = buffer.into();
    return_data.truncate(length as usize);

    // Disable the length
    let buffer = [0; 64];
    flash
        .write(address, &buffer[..S::WRITE_SIZE.max(2)])
        .map_err(Error::Storage)?;

    // Disable the data
    let full_data_length = next_multiple_of(length as u32, S::WRITE_SIZE as u32);
    let mut remaining_length = full_data_length;
    while remaining_length > 0 {
        flash
            .write(
                address + S::WRITE_SIZE.max(2) as u32 + full_data_length - remaining_length,
                &buffer[..buffer.len().min(remaining_length as usize)],
            )
            .map_err(Error::Storage)?;

        remaining_length -= buffer.len().min(remaining_length as usize) as u32;
    }

    Ok(Some(return_data))
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

fn page_item_adresses_iter<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> impl Iterator<Item = Result<ItemAddress, Error<S::Error>>> + '_ {
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), page_index) + S::WRITE_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range, page_index) - S::WRITE_SIZE as u32;

    let mut current_address = page_data_start_address;
    let mut done = false;

    core::iter::from_fn(move || {
        while !done
            && current_address < page_data_end_address
            && page_data_end_address - current_address > 1
        {
            // Read the length
            let mut length = [0; 2];
            if let Err(e) = flash.read(current_address, &mut length) {
                // Error. Make this the last thing this iterator yields
                done = true;
                return Some(Err(Error::Storage(e)));
            }
            let mut length = u16::from_be_bytes(length);

            if length == 0xFFFF {
                // Not programmed yet, we're done
                let address = ItemAddress::Empty {
                    address: current_address,
                };
                done = true;
                return Some(Ok(address));
            }

            if length == 0 {
                // Probably a removed entry
                current_address += S::WRITE_SIZE as u32;
                continue;
            }

            if length & 0x1000 == 0 {
                // This length does not have the recognition bit set, so we're probably reading half of it
                current_address += S::WRITE_SIZE as u32;
                continue;
            }

            // Strip off the recognition bit
            length ^= 0x1000;

            let data_remaining = page_data_end_address - current_address;

            if length as u32 > data_remaining {
                // All data must fit in a page and this seems like it's not.
                // Something is wrong. Make this the last thing this iterator yields
                #[cfg(feature = "defmt")]
                defmt::error!("Corrupted: A page item was found at 0x{:X} with a seemingly longer length than logical of {}", current_address, length);

                current_address = page_data_end_address;
                return Some(Err(Error::Corrupted));
            }

            let return_value = ItemAddress::Filled {
                address: current_address,
                length,
            };

            current_address +=
                S::WRITE_SIZE.max(2) as u32 + next_multiple_of(length as u32, S::WRITE_SIZE as u32);

            return Some(Ok(return_value));
        }

        if !done {
            done = true;
            Some(Ok(ItemAddress::Empty {
                address: page_data_end_address,
            }))
        } else {
            None
        }
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ItemAddress {
    Filled { address: u32, length: u16 },
    Empty { address: u32 },
}

const fn next_multiple_of(value: u32, multiple: u32) -> u32 {
    match value % multiple {
        0 => value,
        r => value + (multiple - r),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    type MockFlashBig = mock_flash::MockFlashBase<4, 4, 256>;
    type MockFlashTiny = mock_flash::MockFlashBase<2, 1, 32>;

    #[test]
    fn push_layout() {
        let mut flash = MockFlashBig::new();
        let flash_range = 0x000..0x1000;

        push(&mut flash, flash_range.clone(), &[0xAA; 6], false).unwrap();

        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 0),
            Ok(PageState::PartialOpen)
        );
        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 1),
            Ok(PageState::Open)
        );

        assert_eq!(
            &flash.as_bytes()[4..20],
            &[16, 6, 0, 0, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0xAA, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF]
        );

        push(&mut flash, flash_range.clone(), &[0xBB; 1], false).unwrap();

        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 0),
            Ok(PageState::PartialOpen)
        );
        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 1),
            Ok(PageState::Open)
        );

        assert_eq!(
            &flash.as_bytes()[16..28],
            &[16, 1, 0, 0, 0xBB, 0, 0, 0, 0xFF, 0xFF, 0xFF, 0xFF]
        );

        assert_eq!(
            &page_item_adresses_iter(&mut flash, flash_range.clone(), 0).collect::<Vec<_>>(),
            &[
                Ok(ItemAddress::Filled {
                    address: 4,
                    length: 6
                }),
                Ok(ItemAddress::Filled {
                    address: 16,
                    length: 1
                }),
                Ok(ItemAddress::Empty { address: 24 })
            ]
        );

        // Would fit on an empty page, but doesn't here
        assert_eq!(
            push(&mut flash, flash_range.clone(), &[0xCC; 1024 - 8], false),
            Err(Error::BufferTooBig)
        );

        // Barely fits
        push(
            &mut flash,
            flash_range.clone(),
            &[0xCC; 1024 - 8 - 28],
            false,
        )
        .unwrap();

        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 0),
            Ok(PageState::PartialOpen)
        );
        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 1),
            Ok(PageState::Open)
        );

        // Should use the new page
        push(&mut flash, flash_range.clone(), &[0xDD, 1], false).unwrap();

        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 0),
            Ok(PageState::Closed)
        );
        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 1),
            Ok(PageState::PartialOpen)
        );
        assert_eq!(
            get_page_state(&mut flash, flash_range.clone(), 2),
            Ok(PageState::Open)
        );
    }

    #[test]
    fn peek_and_overwrite_old_data() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;

        assert_eq!(
            peek::<_, 28>(&mut flash, flash_range.clone()).unwrap(),
            None
        );

        push(&mut flash, flash_range.clone(), &[0xAA; 28], false).unwrap();
        assert_eq!(
            &peek::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xAA; 28]
        );
        push(&mut flash, flash_range.clone(), &[0xBB; 28], false).unwrap();
        assert_eq!(
            &peek::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xAA; 28]
        );

        // Flash is full, this should fail
        push(&mut flash, flash_range.clone(), &[0xCC; 28], false).unwrap_err();
        // Now we allow overwrite, so it should work
        push(&mut flash, flash_range.clone(), &[0xDD; 28], true).unwrap();

        assert_eq!(
            flash.as_bytes(),
            &[
                0, // Partial open page 0
                16, 28, // LE length 28 | 0x1000
                // Data of last write that overwrote 0xAA
                0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
                0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
                0xFF, // Partial open page 0
                0,    // Closed page 1
                16, 28, // LE length 28 | 0x1000
                // Data of second write
                0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB,
                0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBB,
                0 // Closed page 1
            ]
        );

        assert_eq!(
            &peek::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xBB; 28]
        );
        assert_eq!(
            &pop::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xBB; 28]
        );

        assert_eq!(
            flash.as_bytes(),
            &[
                0, // Partial open page 0
                16, 28, // BE length 28 | 0x1000
                // Data of last write that overwrote 0xAA
                0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
                0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD, 0xDD,
                0xFF, // Partial open page 0
                0,    // Closed page 1
                0, 0, // BE length 0 (erased)
                // Data of second write
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0 // Closed page 1
            ]
        );

        assert_eq!(
            &peek::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xDD; 28]
        );
        assert_eq!(
            &pop::<_, 28>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xDD; 28]
        );

        assert_eq!(
            flash.as_bytes(),
            &[
                0, // Partial open page 0
                0, 0, // BE length 0 (erased)
                // Data of last write that overwrote 0xAA
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0xFF, // Partial open page 0
                0,    // Closed page 1
                0, 0, // BE length 0 (erased)
                // Data of second write
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0 // Closed page 1
            ]
        );

        assert_eq!(
            peek::<_, 28>(&mut flash, flash_range.clone()).unwrap(),
            None
        );
        assert_eq!(pop::<_, 28>(&mut flash, flash_range.clone()).unwrap(), None);
    }

    #[test]
    fn push_pop() {
        let mut flash = MockFlashBig::new();
        let flash_range = 0x000..0x1000;

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 244 + 1];

            push(&mut flash, flash_range.clone(), &data, true).unwrap();
            assert_eq!(
                &peek::<_, 244>(&mut flash, flash_range.clone())
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                &pop::<_, 244>(&mut flash, flash_range.clone())
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                peek::<_, 244>(&mut flash, flash_range.clone()).unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    fn push_pop_tiny() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            push(&mut flash, flash_range.clone(), &data, true).unwrap();
            assert_eq!(
                &peek::<_, 20>(&mut flash, flash_range.clone())
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                &pop::<_, 20>(&mut flash, flash_range.clone())
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            assert_eq!(
                peek::<_, 20>(&mut flash, flash_range.clone()).unwrap(),
                None,
                "At {i}"
            );
        }
    }

    #[test]
    fn pop_with_empty_section() {
        let mut flash = MockFlashTiny::new();
        let flash_range = 0x00..0x40;

        push(&mut flash, flash_range.clone(), &[0xAA; 20], false).unwrap();
        push(&mut flash, flash_range.clone(), &[0xBB; 20], false).unwrap();

        // There's now an unused gap at the end of the first page

        assert_eq!(
            &pop::<_, 20>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xAA; 20]
        );
        assert_eq!(
            &pop::<_, 20>(&mut flash, flash_range.clone())
                .unwrap()
                .unwrap()[..],
            &[0xBB; 20]
        );
    }
}
