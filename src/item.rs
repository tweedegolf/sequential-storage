//! Module that implements storing raw items in flash.
//! This module is page-unaware.
//!
//! Memory layout of item:
//! ```text
//! ┌──────┬──────┬──────┬──────┬──────┬──────┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┐
//! │      :      │      :      │      :      │  :  :  :  :  :  │  :  :  :  :  :  :  :  :  :  │  :  :  :  :  :  │
//! │   Length    │   Length'   │     CRC     │Pad to word align│            Data             │Pad to word align│
//! │      :      │      :      │      :      │  :  :  :  :  :  │  :  :  :  :  :   :  :  :  : │  :  :  :  :  :  │
//! └──────┴──────┴──────┴──────┴──────┴──────┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴───┴──┴──┴──┴─┴──┴──┴──┴──┴──┴──┘
//! 0      1      2      3      4      5      6                 6+padding                     6+padding+length  6+padding+length+endpadding
//! ```
//!
//! An item consists of an [ItemHeader] and some data.
//! The header has a length field that encodes the length of the data, a crc of the length (`Length'`)
//! and a crc field that encodes the checksum of the data.
//!
//! If the crc is 0, then the item is counted as being erased.
//! The crc is calculated by [crc16] which never produces a 0 or 0xFFFF value on its own.
//!

use core::{num::NonZeroU16, ops::ControlFlow};

use embedded_storage::nor_flash::{MultiwriteNorFlash, NorFlash};

use crate::{
    round_down_to_alignment, round_down_to_alignment_usize, round_up_to_alignment,
    round_up_to_alignment_usize, Error, NorFlashExt, MAX_WORD_SIZE,
};

#[derive(Debug)]
pub struct ItemHeader {
    /// Length of the item payload (so not including the header and not including word alignment)
    pub length: u16,
    pub crc: Option<NonZeroU16>,
}

impl ItemHeader {
    pub(crate) const LENGTH: usize = 6;

    pub fn read_new<S: NorFlash>(
        flash: &mut S,
        address: u32,
        end_address: u32,
    ) -> Result<Option<Self>, Error<S::Error>> {
        let mut buffer = [0; MAX_WORD_SIZE];
        let header_slice = &mut buffer[..round_up_to_alignment_usize::<S>(Self::LENGTH)];

        if address + header_slice.len() as u32 > end_address {
            return Ok(None);
        }

        flash.read(address, header_slice).map_err(Error::Storage)?;

        if header_slice.iter().all(|b| *b == 0xFF) {
            // What we read was fully erased bytes, so there's no header here
            return Ok(None);
        }

        let length_crc = u16::from_le_bytes(header_slice[2..4].try_into().unwrap());
        let calculated_length_crc = crc16(&header_slice[0..2]).get();

        if calculated_length_crc != length_crc {
            return Err(Error::Corrupted);
        }

        Ok(Some(Self {
            length: u16::from_le_bytes(header_slice[0..2].try_into().unwrap()),
            crc: {
                match u16::from_le_bytes(header_slice[4..6].try_into().unwrap()) {
                    0 => None,
                    value => Some(NonZeroU16::new(value).unwrap()),
                }
            },
        }))
    }

    pub fn read_item<'d, S: NorFlash>(
        self,
        flash: &mut S,
        data_buffer: &'d mut [u8],
        address: u32,
        end_address: u32,
    ) -> Result<MaybeItem<'d>, Error<S::Error>> {
        match self.crc {
            None => Ok(MaybeItem::Erased(self)),
            Some(header_crc) => {
                let data_address = ItemHeader::data_address::<S>(address);
                let read_len = round_up_to_alignment_usize::<S>(self.length as usize);
                if data_buffer.len() < read_len {
                    return Err(Error::BufferTooSmall(read_len));
                }
                if data_address + read_len as u32 > end_address {
                    return Ok(MaybeItem::Corrupted(self));
                }

                flash
                    .read(data_address, &mut data_buffer[..read_len])
                    .map_err(Error::Storage)?;

                let data = &data_buffer[..self.length as usize];
                let data_crc = crc16(data);

                if data_crc == header_crc {
                    Ok(MaybeItem::Present(Item {
                        header: self,
                        data_buffer,
                    }))
                } else {
                    return Ok(MaybeItem::Corrupted(self));
                }
            }
        }
    }

    fn write<S: NorFlash>(&self, flash: &mut S, address: u32) -> Result<(), Error<S::Error>> {
        let mut buffer = [0xFF; MAX_WORD_SIZE];

        buffer[0..2].copy_from_slice(&self.length.to_le_bytes());
        buffer[2..4].copy_from_slice(&crc16(&self.length.to_le_bytes()).get().to_le_bytes());
        buffer[4..6].copy_from_slice(&self.crc.map(|crc| crc.get()).unwrap_or(0).to_le_bytes());

        flash
            .write(
                address,
                &buffer[..round_up_to_alignment_usize::<S>(Self::LENGTH)],
            )
            .map_err(Error::Storage)
    }

    pub fn erase_data<S: MultiwriteNorFlash>(
        mut self,
        flash: &mut S,
        address: u32,
    ) -> Result<Self, Error<S::Error>> {
        self.crc = None;
        self.write(flash, address)?;
        Ok(self)
    }

    pub fn data_address<S: NorFlash>(address: u32) -> u32 {
        address + round_up_to_alignment::<S>(Self::LENGTH as u32)
    }

    pub fn next_item_address<S: NorFlash>(&self, address: u32) -> u32 {
        let data_address = ItemHeader::data_address::<S>(address);
        data_address + round_up_to_alignment::<S>(self.length as u32)
    }

    /// Calculates the amount of bytes available for data.
    /// Essentially, it's the given amount minus the header and minus some alignment padding.
    pub fn available_data_bytes<S: NorFlash>(total_available: u32) -> Option<u32> {
        let data_start = Self::data_address::<S>(0);
        let data_end = round_down_to_alignment::<S>(total_available);

        data_end.checked_sub(data_start)
    }
}

pub struct Item<'d> {
    pub header: ItemHeader,
    data_buffer: &'d mut [u8],
}

impl<'d> Item<'d> {
    pub fn data(&'d self) -> &'d [u8] {
        &self.data_buffer[..self.header.length as usize]
    }

    /// Destruct the item to get back the full data buffer
    pub fn destruct(self) -> (ItemHeader, &'d mut [u8]) {
        (self.header, self.data_buffer)
    }

    pub fn write_new<S: NorFlash>(
        flash: &mut S,
        address: u32,
        data: &'d [u8],
    ) -> Result<ItemHeader, Error<S::Error>> {
        let header = ItemHeader {
            length: data.len() as u16,
            crc: Some(crc16(data)),
        };

        Self::write_raw(&header, data, flash, address)?;

        Ok(header)
    }

    fn write_raw<S: NorFlash>(
        header: &ItemHeader,
        data: &[u8],
        flash: &mut S,
        address: u32,
    ) -> Result<(), Error<S::Error>> {
        header.write(flash, address)?;

        let (data_block, data_left) = data.split_at(round_down_to_alignment_usize::<S>(data.len()));

        let data_address = ItemHeader::data_address::<S>(address);
        flash
            .write(data_address, data_block)
            .map_err(Error::Storage)?;

        if !data_left.is_empty() {
            let mut buffer = [0; MAX_WORD_SIZE];
            buffer[..data_left.len()].copy_from_slice(data_left);
            flash
                .write(
                    data_address + data_block.len() as u32,
                    &buffer[..round_up_to_alignment_usize::<S>(data_left.len())],
                )
                .map_err(Error::Storage)?;
        }

        Ok(())
    }

    pub fn write<S: NorFlash>(&self, flash: &mut S, address: u32) -> Result<(), Error<S::Error>> {
        Self::write_raw(&self.header, self.data(), flash, address)
    }
}

impl<'d> core::fmt::Debug for Item<'d> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Item")
            .field("header", &self.header)
            .field(
                "data_buffer",
                &&self.data_buffer[..self.header.length as usize],
            )
            .finish()
    }
}

pub fn read_item_headers<S: NorFlash, R>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
    mut callback: impl FnMut(&mut S, ItemHeader, u32) -> ControlFlow<R, ()>,
) -> Result<Option<R>, Error<S::Error>> {
    let mut current_address = start_address;

    loop {
        if current_address >= end_address {
            return Ok(None);
        }

        match ItemHeader::read_new(flash, current_address, end_address) {
            Ok(Some(header)) => {
                let next_address = header.next_item_address::<S>(current_address);

                match callback(flash, header, current_address) {
                    ControlFlow::Continue(_) => {}
                    ControlFlow::Break(r) => return Ok(Some(r)),
                }

                current_address = next_address;
            }
            Ok(None) => return Ok(None),
            Err(Error::Corrupted) => {
                #[cfg(feature = "defmt")]
                defmt::error!(
                    "Found a corrupted item header at {:X}. Skipping...",
                    current_address
                );
                current_address += S::WORD_SIZE as u32;
            }
            Err(e) => return Err(e),
        };
    }
}

pub fn read_items<S: NorFlash, R>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
    data_buffer: &mut [u8],
    mut callback: impl FnMut(&mut S, Item<'_>, u32) -> ControlFlow<R, ()>,
) -> Result<Option<R>, Error<S::Error>> {
    read_item_headers(
        flash,
        start_address,
        end_address,
        |flash, header, address| match header.read_item(flash, data_buffer, address, end_address) {
            Ok(MaybeItem::Corrupted(_)) => {
                #[cfg(feature = "defmt")]
                defmt::error!(
                    "Found a corrupted item at {:X}. Skipping...",
                    current_address
                );
                ControlFlow::Continue(())
            }
            Ok(MaybeItem::Erased(_)) => ControlFlow::Continue(()),
            Ok(MaybeItem::Present(item)) => match callback(flash, item, address) {
                ControlFlow::Continue(_) => ControlFlow::Continue(()),
                ControlFlow::Break(r) => ControlFlow::Break(Ok(r)),
            },
            Err(e) => ControlFlow::Break(Err(e)),
        },
    )?
    .transpose()
}

/// Scans through the items to find the first spot that is free to store a new item.
///
/// - `end_address` is exclusive.
pub fn find_next_free_item_spot<S: NorFlash>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
    data_length: u32,
) -> Result<Option<u32>, Error<S::Error>> {
    let mut current_address = start_address;
    let mut corruption_detected = false;

    while current_address + data_length < end_address {
        match ItemHeader::read_new(flash, current_address, end_address) {
            Ok(Some(header)) => current_address = header.next_item_address::<S>(current_address),
            Ok(None) => {
                if ItemHeader::data_address::<S>(current_address)
                    + round_up_to_alignment::<S>(data_length)
                    >= end_address
                {
                    // Items does not fit anymore between the current address and the end address
                    return Ok(None);
                } else {
                    if corruption_detected {
                        // We need to read ahead to see if the data portion is clear
                        let data_start = ItemHeader::data_address::<S>(current_address);
                        let data_end = data_start + round_up_to_alignment::<S>(data_length);
                        let mut buffer = [0; MAX_WORD_SIZE];

                        for address in (data_start..data_end).step_by(MAX_WORD_SIZE) {
                            let buffer_slice =
                                &mut buffer[..((data_end - address) as usize).min(MAX_WORD_SIZE)];
                            flash.read(address, buffer_slice).map_err(Error::Storage)?;

                            if buffer_slice.iter().any(|byte| *byte != 0xFF) {
                                current_address = address + MAX_WORD_SIZE as u32;
                                continue;
                            }
                        }
                    }

                    return Ok(Some(current_address));
                }
            }
            Err(Error::Corrupted) => {
                current_address += S::WORD_SIZE as u32;
                corruption_detected = true;
            }
            Err(e) => return Err(e),
        }
    }

    Ok(None)
}

#[derive(Debug)]
pub enum MaybeItem<'d> {
    Corrupted(ItemHeader),
    Erased(ItemHeader),
    Present(Item<'d>),
}

impl<'d> MaybeItem<'d> {
    pub fn unwrap<E>(self) -> Result<Item<'d>, Error<E>> {
        match self {
            MaybeItem::Corrupted(_) => Err(Error::Corrupted),
            MaybeItem::Erased(_) => panic!("Cannot unwrap an erased item"),
            MaybeItem::Present(item) => Ok(item),
        }
    }
}

/// A crc that never returns 0 or 0xFFFF
fn crc16(data: &[u8]) -> NonZeroU16 {
    let mut crc = 0xffff;
    for byte in data.iter() {
        crc ^= *byte as u16;
        for _ in 0..8 {
            if crc & 1 == 1 {
                crc = (crc >> 1) ^ 0x1a2e; // CRC-16F/4.2 @ https://users.ece.cmu.edu/~koopman/crc/crc16.html
            } else {
                crc >>= 1;
            }
        }
    }
    crc ^= 0xffff;
    match crc {
        0 => NonZeroU16::new(1).unwrap(),
        0xFFFF => NonZeroU16::new(0xFFFE).unwrap(),
        non_zero => NonZeroU16::new(non_zero).unwrap(),
    }
}
