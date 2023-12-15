//! A queue (fifo) implementation for storing arbitrary data in flash memory.
//!
//! Use [push] to add data to the fifo and use [peek] and [pop] to get the data back.
//!
//! ```rust
//! # use sequential_storage::queue::{push, peek, pop};
//! # use mock_flash::MockFlashBase;
//! # type Flash = MockFlashBase<10, 1, 4096>;
//! # mod mock_flash {
//! #   include!("mock_flash.rs");
//! # }
//! // Initialize the flash. This can be internal or external
//! let mut flash = Flash::default();
//! // These are the flash addresses in which the crate will operate.
//! // The crate will not read, write or erase outside of this range.
//! let flash_range = 0x1000..0x3000;
//! // We need to give the crate a buffer to work with.
//! // It must be big enough to serialize the biggest value of your storage type in.
//! let mut data_buffer = [0; 100];
//!
//! let my_data = [10, 47, 29];
//!
//! // We can push some data to the queue
//!
//! push(&mut flash, flash_range.clone(), &my_data, false).unwrap();
//!
//! // We can peek at the oldest data
//!
//! assert_eq!(
//!     &peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // With popping we get back the oldest data, but that data is now also removed
//!
//! assert_eq!(
//!     &pop(&mut flash, flash_range.clone(), &mut data_buffer).unwrap().unwrap()[..],
//!     &my_data[..]
//! );
//!
//! // If we pop again, we find there's no data anymore
//!
//! assert_eq!(
//!     pop(&mut flash, flash_range.clone(), &mut data_buffer),
//!     Ok(None)
//! );
//! ```

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

    // Data must fit in a single page
    if data.len()
        > ItemHeader::available_data_bytes::<S>((S::ERASE_SIZE - S::WORD_SIZE * 2) as u32).unwrap()
            as usize
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

    let mut next_address = find_next_free_item_spot(
        flash,
        page_data_start_address,
        page_data_end_address,
        data.len() as u32,
    )?;

    if next_address.is_none() {
        // No cap left on this page, move to the next page
        let next_page = next_page::<S>(flash_range.clone(), current_page);
        match get_page_state(flash, flash_range.clone(), next_page)? {
            PageState::Open => {
                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address = Some(
                    calculate_page_address::<S>(flash_range.clone(), next_page)
                        + S::WORD_SIZE as u32,
                );
            }
            PageState::Closed => {
                let next_page_data_start_address =
                    calculate_page_address::<S>(flash_range.clone(), next_page)
                        + S::WORD_SIZE as u32;
                let next_page_data_end_address =
                    calculate_page_end_address::<S>(flash_range.clone(), next_page)
                        - S::WORD_SIZE as u32;

                if !allow_overwrite_old_data {
                    let next_page_empty = read_item_headers(
                        flash,
                        next_page_data_start_address,
                        next_page_data_end_address,
                        |_, header, _| match header.crc {
                            Some(_) => ControlFlow::Break(()),
                            None => ControlFlow::Continue(()),
                        },
                    )?
                    .is_none();

                    if !next_page_empty {
                        return Err(Error::FullStorage);
                    }
                }

                flash
                    .erase(
                        calculate_page_address::<S>(flash_range.clone(), next_page),
                        calculate_page_end_address::<S>(flash_range.clone(), next_page),
                    )
                    .map_err(Error::Storage)?;

                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address = Some(next_page_data_start_address);
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

    Item::write_new(flash, next_address.unwrap(), data)?;

    Ok(())
}

/// Peek at the data from oldest to newest.
///
/// If you also want to remove the data use [pop_many].
///
/// Returns an iterator-like type that can be used to peek into the data.
pub fn peek_many<'d, S: NorFlash>(flash: &'d mut S, flash_range: Range<u32>) -> Peeker<'d, S> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    Peeker {
        flash,
        flash_range,
        oldest_page: None,
        current_page: 0,
        start_address: 0,
    }
}

/// An iterator-like interface for peeking into events stored in flash.
pub struct Peeker<'d, S: NorFlash> {
    flash: &'d mut S,
    flash_range: Range<u32>,
    oldest_page: Option<usize>,
    current_page: usize,
    start_address: u32,
}

impl<'d, S: NorFlash> Peeker<'d, S> {
    fn next_page(&mut self, current: usize) -> Option<usize> {
        let next = next_page::<S>(self.flash_range.clone(), current);
        let oldest = self.oldest_page.unwrap();
        if next == oldest {
            None
        } else {
            Some(next)
        }
    }

    /// Peek at the next event.
    ///
    /// The data is written to the given `data_buffer`` and the part that was written is returned.
    /// It is valid to only use the length of the returned slice and use the original `data_buffer`.
    /// The `data_buffer` may contain extra data on ranges after the returned slice.
    /// You should not depend on that data.
    ///
    /// If the data buffer is not big enough an error is returned.
    pub fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<&'m mut [u8]>, Error<S::Error>> {
        if self.oldest_page.is_none() {
            let oldest_page = find_oldest_page(self.flash, self.flash_range.clone())?;
            self.oldest_page.replace(oldest_page);
            self.current_page = oldest_page;
            self.start_address = calculate_page_address::<S>(self.flash_range.clone(), oldest_page)
                + S::WORD_SIZE as u32;
        }

        let mut data_buffer = Some(data_buffer);
        loop {
            let page_data_end_address =
                calculate_page_end_address::<S>(self.flash_range.clone(), self.current_page)
                    - S::WORD_SIZE as u32;
            if let Some((found_item_header, found_item_address)) = read_item_headers(
                self.flash,
                self.start_address,
                page_data_end_address,
                |_, item_header, item_address| {
                    if item_header.crc.is_some() {
                        ControlFlow::Break((item_header, item_address))
                    } else {
                        ControlFlow::Continue(())
                    }
                },
            )? {
                let maybe_item = found_item_header.read_item(
                    self.flash,
                    data_buffer.take().unwrap(),
                    found_item_address,
                    page_data_end_address,
                )?;

                match maybe_item {
                    item::MaybeItem::Corrupted(_, db) => {
                        self.start_address += found_item_address + S::WORD_SIZE as u32;
                        data_buffer.replace(db);
                        continue;
                    }
                    item::MaybeItem::Erased(_) => unreachable!("Item is already erased"),
                    item::MaybeItem::Present(item) => {
                        self.start_address = item.header.next_item_address::<S>(self.start_address);
                        let (header, data_buffer) = item.destruct();
                        return Ok(Some(&mut data_buffer[..header.length as usize]));
                    }
                }
            } else {
                match self.next_page(self.current_page) {
                    Some(next) => {
                        self.current_page = next;
                        self.start_address =
                            calculate_page_address::<S>(self.flash_range.clone(), next)
                                + S::WORD_SIZE as u32;
                    }
                    None => {
                        // No more items left!
                        return Ok(None);
                    }
                }
            }
        }
    }
    //let page_count = flash_range.len() / S::ERASE_SIZE;
    //flash_range
    //    .step_by(S::ERASE_SIZE)
    //    .enumerate()
    //    .map(move |(index, _)| (index + starting_page_index) % page_count)
    //}
}

/// Peek at the oldest data.
///
/// If you also want to remove the data use [pop].
///
/// The data is written to the given `data_buffer`` and the part that was written is returned.
/// It is valid to only use the length of the returned slice and use the original `data_buffer`.
/// The `data_buffer` may contain extra data on ranges after the returned slice.
/// You should not depend on that data.
///
/// If the data buffer is not big enough an error is returned.
pub fn peek<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    peek_many(flash, flash_range).next(data_buffer)
}

/// Pop the oldest data from the queue.
///
/// If you don't want to remove the data use [peek].
///
/// The data is written to the given `data_buffer`` and the part that was written is returned.
/// It is valid to only use the length of the returned slice and use the original `data_buffer`.
/// The `data_buffer` may contain extra data on ranges after the returned slice.
/// You should not depend on that data.
///
/// If the data buffer is not big enough an error is returned.
pub fn pop<'d, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let oldest_page = find_oldest_page(flash, flash_range.clone())?;
    let mut data_buffer = Some(data_buffer);

    for current_page in get_pages::<S>(flash_range.clone(), oldest_page) {
        let page_data_start_address =
            calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
        let page_data_end_address =
            calculate_page_end_address::<S>(flash_range.clone(), current_page)
                - S::WORD_SIZE as u32;

        let mut start_address = page_data_start_address;

        while let Some((found_item_header, found_item_address)) = read_item_headers(
            flash,
            start_address,
            page_data_end_address,
            |_, item_header, item_address| {
                if item_header.crc.is_some() {
                    ControlFlow::Break((item_header, item_address))
                } else {
                    ControlFlow::Continue(())
                }
            },
        )? {
            let maybe_item = found_item_header.read_item(
                flash,
                data_buffer.take().unwrap(),
                found_item_address,
                page_data_end_address,
            )?;

            match maybe_item {
                item::MaybeItem::Corrupted(_, db) => {
                    start_address += found_item_address + S::WORD_SIZE as u32;
                    data_buffer.replace(db);
                    continue;
                }
                item::MaybeItem::Erased(_) => unreachable!("Item is already erased"),
                item::MaybeItem::Present(item) => {
                    let (header, data_buffer) = item.destruct();
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

                    return Ok(Some(&mut data_buffer[..header.length as usize]));
                }
            };
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
        let mut flash = MockFlashTiny::default();
        let flash_range = 0x00..0x40;
        let mut data_buffer = [0; 1024];
        const DATA_SIZE: usize = 24;

        assert_eq!(
            peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap(),
            None
        );

        push(&mut flash, flash_range.clone(), &[0xAA; DATA_SIZE], false).unwrap();
        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xAA; DATA_SIZE]
        );
        push(&mut flash, flash_range.clone(), &[0xBB; DATA_SIZE], false).unwrap();
        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xAA; DATA_SIZE]
        );

        // Flash is full, this should fail
        push(&mut flash, flash_range.clone(), &[0xCC; DATA_SIZE], false).unwrap_err();
        // Now we allow overwrite, so it should work
        push(&mut flash, flash_range.clone(), &[0xDD; DATA_SIZE], true).unwrap();

        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xBB; DATA_SIZE]
        );
        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xBB; DATA_SIZE]
        );

        assert_eq!(
            &peek(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xDD; DATA_SIZE]
        );
        assert_eq!(
            &pop(&mut flash, flash_range.clone(), &mut data_buffer)
                .unwrap()
                .unwrap()[..],
            &[0xDD; DATA_SIZE]
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
        let mut flash = MockFlashBig::default();
        let flash_range = 0x000..0x1000;
        let mut data_buffer = [0; 1024];

        for i in 0..2000 {
            println!("{i}");
            let data = vec![i as u8; i % 512 + 1];

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
        let mut flash = MockFlashTiny::default();
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
        let mut flash = MockFlashBig::default();
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
        let mut flash = MockFlashTiny::default();
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

    #[test]
    fn recover_from_bitflips() {
        // We can't really recover, but we can at least ignore and continue

        const TOTAL_TRIES: usize = 10000;
        const DATA_SIZE: usize = 32;
        const BITFLIP_CHANCE: f32 = 0.00001;
        const EFFECTIVE_SIZE: usize = ItemHeader::LENGTH + DATA_SIZE;
        // Note: Times 10 because... well it seems the actual chance is 10x this calculation. Idk why
        let chance_item_bad: f32 =
            (1.0 - (1.0 - BITFLIP_CHANCE).powf(EFFECTIVE_SIZE as f32 * 8.0)) * 10.0;
        let average_tries_bad: f32 = TOTAL_TRIES as f32 * chance_item_bad;

        assert!(average_tries_bad > 10.0);
        println!("Chance item bad: {chance_item_bad}");
        println!("Expecting {average_tries_bad} bad tries");

        let mut flash = MockFlashBig::new(BITFLIP_CHANCE, false);
        let flash_range = 0x000..0x1000;

        let mut bad_tries = 0;

        for i in 0..TOTAL_TRIES {
            push(
                &mut flash,
                flash_range.clone(),
                &[i as u8; DATA_SIZE],
                false,
            )
            .unwrap();
            let mut data_buffer = [0; DATA_SIZE];
            match peek(&mut flash, flash_range.clone(), &mut data_buffer).unwrap() {
                Some(data) => {
                    assert_eq!(data, &[i as u8; DATA_SIZE]);
                    pop(&mut flash, flash_range.clone(), &mut data_buffer).unwrap();
                }
                None => {
                    bad_tries += 1;
                }
            }
        }

        println!("Bad total: {bad_tries}");

        assert!(bad_tries <= (average_tries_bad * 2.0) as usize);
    }
}
