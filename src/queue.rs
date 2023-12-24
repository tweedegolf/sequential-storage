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

use crate::item::{find_next_free_item_spot, is_page_empty, read_item_headers, Item, ItemHeader};

use super::*;
use embedded_storage::nor_flash::MultiwriteNorFlash;

/// Push data into the queue in the given flash memory with the given range.
/// The data can only be taken out with the [pop] function.
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
            state @ PageState::Closed => {
                let next_page_data_start_address =
                    calculate_page_address::<S>(flash_range.clone(), next_page)
                        + S::WORD_SIZE as u32;

                if !allow_overwrite_old_data
                    && !is_page_empty(flash, flash_range.clone(), next_page, Some(state))?
                {
                    return Err(Error::FullStorage);
                }

                flash
                    .erase(
                        calculate_page_address::<S>(flash_range.clone(), next_page),
                        calculate_page_end_address::<S>(flash_range.clone(), next_page),
                    )
                    .map_err(|e| Error::Storage {
                        value: e,
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    })?;

                partial_close_page(flash, flash_range.clone(), next_page)?;
                next_address = Some(next_page_data_start_address);
            }
            PageState::PartialOpen => {
                // This should never happen
                #[cfg(feature = "defmt")]
                defmt::error!("Corrupted: A we expected an open or closed page, but found a partial open page");
                return Err(Error::Corrupted {
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                });
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
pub fn peek_many<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<PeekIterator<'_, S>, Error<S::Error>> {
    Ok(PeekIterator {
        iter: QueueIterator::new(flash, flash_range)?,
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
pub fn peek<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    peek_many(flash, flash_range)?.next(data_buffer)
}

/// Pop the data from oldest to newest.
///
/// If you don't want to remove the data use [peek_many].
///
/// Returns an iterator-like type that can be used to pop the data.
pub fn pop_many<S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<PopIterator<'_, S>, Error<S::Error>> {
    Ok(PopIterator {
        iter: QueueIterator::new(flash, flash_range)?,
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
pub fn pop<'d, S: MultiwriteNorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data_buffer: &'d mut [u8],
) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
    pop_many(flash, flash_range)?.next(data_buffer)
}

/// Iterator for pop'ing elements in the queue.
pub struct PopIterator<'d, S: MultiwriteNorFlash> {
    iter: QueueIterator<'d, S>,
}

impl<'d, S: MultiwriteNorFlash> PopIterator<'d, S> {
    /// Pop the next data.
    ///
    /// The data is written to the given `data_buffer` and the part that was written is returned.
    /// It is valid to only use the length of the returned slice and use the original `data_buffer`.
    /// The `data_buffer` may contain extra data on ranges after the returned slice.
    /// You should not depend on that data.
    ///
    /// If the data buffer is not big enough an error is returned.
    pub fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<&'m mut [u8]>, Error<S::Error>> {
        if let Some((item, item_address)) = self.iter.next(data_buffer)? {
            let (header, data_buffer) = item.destruct();
            let ret = &mut data_buffer[..header.length as usize];

            header.erase_data(self.iter.flash, item_address)?;

            Ok(Some(ret))
        } else {
            Ok(None)
        }
    }
}

/// Iterator for peek'ing elements in the queue.
pub struct PeekIterator<'d, S: NorFlash> {
    iter: QueueIterator<'d, S>,
}

impl<'d, S: NorFlash> PeekIterator<'d, S> {
    /// Peek at the next data.
    ///
    /// The data is written to the given `data_buffer` and the part that was written is returned.
    /// It is valid to only use the length of the returned slice and use the original `data_buffer`.
    /// The `data_buffer` may contain extra data on ranges after the returned slice.
    /// You should not depend on that data.
    ///
    /// If the data buffer is not big enough an error is returned.
    pub fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<&'m mut [u8]>, Error<S::Error>> {
        Ok(self.iter.next(data_buffer)?.map(|(item, _)| {
            let (header, data_buffer) = item.destruct();
            &mut data_buffer[..header.length as usize]
        }))
    }
}

/// An iterator-like interface for peeking into data stored in flash.
struct QueueIterator<'d, S: NorFlash> {
    flash: &'d mut S,
    flash_range: Range<u32>,
    current_address: CurrentAddress,
}

#[derive(Debug)]
enum CurrentAddress {
    Address(u32),
    PageAfter(usize),
}

impl<'d, S: NorFlash> QueueIterator<'d, S> {
    fn new(flash: &'d mut S, flash_range: Range<u32>) -> Result<Self, Error<S::Error>> {
        assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
        assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

        assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
        assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

        // We start at the start of the oldest page
        let current_address = calculate_page_address::<S>(
            flash_range.clone(),
            find_oldest_page(flash, flash_range.clone())?,
        ) + S::WORD_SIZE as u32;

        Ok(Self {
            flash,
            flash_range,
            current_address: CurrentAddress::Address(current_address),
        })
    }

    fn next<'m>(
        &mut self,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<(Item<'m>, u32)>, Error<S::Error>> {
        let mut data_buffer = Some(data_buffer);

        loop {
            // Get the current page and address based on what was stored
            let (current_page, current_address) = match self.current_address {
                CurrentAddress::PageAfter(previous_page) => {
                    let next_page = next_page::<S>(self.flash_range.clone(), previous_page);
                    if get_page_state(self.flash, self.flash_range.clone(), next_page)?.is_open()
                        || next_page == find_oldest_page(self.flash, self.flash_range.clone())?
                    {
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
            if let Some((found_item_header, found_item_address)) = read_item_headers(
                self.flash,
                current_address,
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
                        let next_address = found_item_address + S::WORD_SIZE as u32;
                        self.current_address = if next_address >= page_data_end_address {
                            CurrentAddress::PageAfter(current_page)
                        } else {
                            CurrentAddress::Address(next_address)
                        };
                        data_buffer.replace(db);
                        continue;
                    }
                    item::MaybeItem::Erased(_) => unreachable!("Item is already erased"),
                    item::MaybeItem::Present(item) => {
                        let next_address = item.header.next_item_address::<S>(found_item_address);
                        self.current_address = if next_address >= page_data_end_address {
                            CurrentAddress::PageAfter(current_page)
                        } else {
                            CurrentAddress::Address(next_address)
                        };
                        // Return the item we found
                        return Ok(Some((item, found_item_address)));
                    }
                }
            } else {
                self.current_address = CurrentAddress::PageAfter(current_page);
            }
        }
    }
}

/// Find the largest size of data that can be stored.
///
/// This will read through the entire flash to find the largest chunk of
/// data that can be stored, taking alignment requirements of the item into account.
///
/// If there is no space left, `None` is returned.
pub fn find_max_fit<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<Option<usize>, Error<S::Error>> {
    assert_eq!(flash_range.start % S::ERASE_SIZE as u32, 0);
    assert_eq!(flash_range.end % S::ERASE_SIZE as u32, 0);

    assert!(S::ERASE_SIZE >= S::WORD_SIZE * 4);
    assert!(S::WORD_SIZE <= MAX_WORD_SIZE);

    let current_page = find_youngest_page(flash, flash_range.clone())?;

    // Check if we have space on the next page
    let next_page = next_page::<S>(flash_range.clone(), current_page);
    match get_page_state(flash, flash_range.clone(), next_page)? {
        state @ PageState::Closed => {
            if is_page_empty(flash, flash_range.clone(), next_page, Some(state))? {
                return Ok(Some(S::ERASE_SIZE - (2 * S::WORD_SIZE)));
            }
        }
        PageState::Open => {
            return Ok(Some(S::ERASE_SIZE - (2 * S::WORD_SIZE)));
        }
        PageState::PartialOpen => {
            // This should never happen
            return Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        }
    };

    // See how much space we can ind in the current page.
    let mut max_free: Option<usize> = None;
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), current_page) + S::WORD_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range.clone(), current_page) - S::WORD_SIZE as u32;

    let mut current_address = page_data_start_address;
    let end_address = page_data_end_address;

    while current_address < end_address {
        let result = ItemHeader::read_new(flash, current_address, end_address)?;
        match result {
            Some(header) => current_address = header.next_item_address::<S>(current_address),
            None => {
                let data_address =
                    round_up_to_alignment_usize::<S>(current_address as usize + ItemHeader::LENGTH);
                if data_address <= end_address as usize {
                    let free = round_down_to_alignment_usize::<S>(
                        end_address as usize - data_address as usize,
                    );
                    max_free = max_free.map(|current| current.max(free)).or(Some(free));
                }

                break;
            }
        }
    }

    Ok(max_free)
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

    Err(Error::Corrupted {
        #[cfg(feature = "_test")]
        backtrace: std::backtrace::Backtrace::capture(),
    })
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
        const DATA_SIZE: usize = 22;

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
    /// Same as [push_lots_then_pop_lots], except with added peeking and using the iterator style
    fn push_peek_pop_many() {
        let mut flash = MockFlashBig::default();
        let flash_range = 0x000..0x1000;
        let mut data_buffer = [0; 1024];

        let mut push_ops = (0, 0, 0, 0);
        let mut peek_ops = (0, 0, 0, 0);
        let mut pop_ops = (0, 0, 0, 0);

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
                add_ops(&mut flash, &mut push_ops);
            }

            let mut peeker = peek_many(&mut flash, flash_range.clone()).unwrap();
            for i in 0..5 {
                let mut data = vec![i as u8; 50];
                assert_eq!(
                    peeker.next(&mut data_buffer).unwrap(),
                    Some(&mut data[..]),
                    "At {i}"
                );
                add_ops(peeker.iter.flash, &mut peek_ops);
            }

            let mut popper = pop_many(&mut flash, flash_range.clone()).unwrap();
            for i in 0..5 {
                let data = vec![i as u8; 50];
                assert_eq!(
                    &popper.next(&mut data_buffer).unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                add_ops(popper.iter.flash, &mut pop_ops);
            }

            for i in 20..25 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
                add_ops(&mut flash, &mut push_ops);
            }

            let mut peeker = peek_many(&mut flash, flash_range.clone()).unwrap();
            for i in 5..25 {
                let data = vec![i as u8; 50];
                assert_eq!(
                    &peeker.next(&mut data_buffer).unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                add_ops(peeker.iter.flash, &mut peek_ops);
            }

            let mut popper = pop_many(&mut flash, flash_range.clone()).unwrap();
            for i in 5..25 {
                let data = vec![i as u8; 50];
                assert_eq!(
                    &popper.next(&mut data_buffer).unwrap().unwrap()[..],
                    &data,
                    "At {i}"
                );
                add_ops(popper.iter.flash, &mut pop_ops);
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        // Format = (writes, reads, erases, num operations)
        println!("Asserting push ops:");
        assert_avg_ops(&push_ops, (3.1252, 17.902, 0.0612));
        println!("Asserting peek ops:");
        assert_avg_ops(&peek_ops, (0.0, 8.0188, 0.0));
        println!("Asserting pop ops:");
        assert_avg_ops(&pop_ops, (1.0, 8.0188, 0.0));
    }

    #[test]
    fn push_lots_then_pop_lots() {
        let mut flash = MockFlashBig::default();
        let flash_range = 0x000..0x1000;
        let mut data_buffer = [0; 1024];

        let mut push_ops = (0, 0, 0, 0);
        let mut pop_ops = (0, 0, 0, 0);

        for loop_index in 0..100 {
            println!("Loop index: {loop_index}");

            for i in 0..20 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
                add_ops(&mut flash, &mut push_ops);
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
                add_ops(&mut flash, &mut pop_ops);
            }

            for i in 20..25 {
                let data = vec![i as u8; 50];
                push(&mut flash, flash_range.clone(), &data, false).unwrap();
                add_ops(&mut flash, &mut push_ops);
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
                add_ops(&mut flash, &mut pop_ops);
            }
        }

        // Assert the performance. These numbers can be changed if acceptable.
        // Format = (writes, reads, erases, num operations)
        println!("Asserting push ops:");
        assert_avg_ops(&push_ops, (3.1252, 17.902, 0.0612));
        println!("Asserting pop ops:");
        assert_avg_ops(&pop_ops, (1.0, 82.618, 0.0));
    }

    fn add_ops(flash: &mut MockFlashBig, ops: &mut (u32, u32, u32, u32)) {
        ops.0 += core::mem::replace(&mut flash.writes, 0);
        ops.1 += core::mem::replace(&mut flash.reads, 0);
        ops.2 += core::mem::replace(&mut flash.erases, 0);
        ops.3 += 1;
    }

    #[track_caller]
    fn assert_avg_ops(ops: &(u32, u32, u32, u32), expected_averages: (f32, f32, f32)) {
        let averages = (
            ops.0 as f32 / ops.3 as f32,
            ops.1 as f32 / ops.3 as f32,
            ops.2 as f32 / ops.3 as f32,
        );

        println!(
            "Average writes: {}, expected: {}",
            averages.0, expected_averages.0
        );
        println!(
            "Average reads: {}, expected: {}",
            averages.1, expected_averages.1
        );
        println!(
            "Average erases: {}, expected: {}",
            averages.2, expected_averages.2
        );
        approx::assert_relative_eq!(averages.0, expected_averages.0);
        approx::assert_relative_eq!(averages.1, expected_averages.1);
        approx::assert_relative_eq!(averages.2, expected_averages.2);
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
    fn search_pages() {
        let mut flash = MockFlashBig::default();

        const FLASH_RANGE: Range<u32> = 0x000..0x1000;

        close_page(&mut flash, FLASH_RANGE, 0).unwrap();
        close_page(&mut flash, FLASH_RANGE, 1).unwrap();
        partial_close_page(&mut flash, FLASH_RANGE, 2).unwrap();

        assert_eq!(find_youngest_page(&mut flash, FLASH_RANGE).unwrap(), 2);
        assert_eq!(find_oldest_page(&mut flash, FLASH_RANGE).unwrap(), 0);
    }
}
