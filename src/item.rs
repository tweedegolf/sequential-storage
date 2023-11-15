use core::num::NonZeroU16;

use embedded_storage::nor_flash::{MultiwriteNorFlash, NorFlash};

use crate::{
    round_down_to_alignment, round_down_to_alignment_usize, round_up_to_alignment,
    round_up_to_alignment_usize, Error, MAX_WORD_SIZE,
};

pub struct ItemHeader {
    /// Length of the item payload (so not including the header and not including word alignment)
    pub length: NonZeroU16,
    pub crc: Option<NonZeroU16>,
}

impl ItemHeader {
    const LENGTH: usize = 4;

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

        if header_slice[..Self::LENGTH].iter().all(|b| *b == 0xFF) {
            // What we read was fully erased bytes, so there's no header here
            return Ok(None);
        }

        Ok(Some(Self {
            length: match u16::from_le_bytes(header_slice[0..2].try_into().unwrap()) {
                0xFFFF => return Err(Error::Corrupted),
                val => NonZeroU16::new(val + 1).unwrap(),
            },
            crc: {
                match u16::from_le_bytes(header_slice[2..4].try_into().unwrap()) {
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
    ) -> Result<Option<MaybeItem<'d>>, Error<S::Error>> {
        match self.crc {
            None => Ok(Some(MaybeItem::Erased(self))),
            Some(header_crc) => {
                let data_address = ItemHeader::data_address::<S>(address);
                let read_len = round_up_to_alignment_usize::<S>(self.length.get() as usize);
                if data_buffer.len() < read_len {
                    return Err(Error::BufferTooSmall);
                }
                if data_address + read_len as u32 > end_address {
                    return Ok(Some(MaybeItem::Corrupted(self)));
                }

                flash
                    .read(data_address, &mut data_buffer[..read_len])
                    .map_err(Error::Storage)?;

                let data = &data_buffer[..self.length.get() as usize];
                let data_crc = crc16(data);

                if data_crc == header_crc {
                    Ok(Some(MaybeItem::Present(Item {
                        header: self,
                        data_buffer,
                    })))
                } else {
                    Err(Error::CrcError)
                }
            }
        }
    }

    fn write<S: NorFlash>(&self, flash: &mut S, address: u32) -> Result<(), Error<S::Error>> {
        let mut buffer = [0xFF; MAX_WORD_SIZE];

        buffer[0..2].copy_from_slice(&(self.length.get() - 1).to_le_bytes());
        buffer[2..4].copy_from_slice(&self.crc.map(|crc| crc.get()).unwrap_or(0).to_le_bytes());

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
        data_address + round_up_to_alignment::<S>(self.length.get() as u32)
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
        &self.data_buffer[..self.header.length.get() as usize]
    }

    /// Destruct the item to get back the full data buffer
    pub fn destruct(self) -> (ItemHeader, &'d mut [u8]) {
        (self.header, self.data_buffer)
    }

    /// Read the item from the flash
    ///
    /// `data_buffer` must be long enough to hold the data and some padding
    pub fn read_new<S: NorFlash>(
        flash: &mut S,
        data_buffer: &'d mut [u8],
        address: u32,
        end_address: u32,
    ) -> Result<Option<MaybeItem<'d>>, Error<S::Error>> {
        let Some(header) = ItemHeader::read_new(flash, address, end_address)? else {
            return Ok(None);
        };

        header.read_item(flash, data_buffer, address, end_address)
    }

    pub fn write_new<S: NorFlash>(
        flash: &mut S,
        address: u32,
        data: &'d [u8],
    ) -> Result<ItemHeader, Error<S::Error>> {
        let data_crc = crc16(data);
        let data_len = match data.len() {
            0 => return Err(Error::ZeroLengthData),
            len @ 1..=0xFFFF => NonZeroU16::new(len as u16).unwrap(),
            0x10000.. => return Err(Error::BufferTooBig),
            _ => unreachable!(),
        };

        let header = ItemHeader {
            length: data_len,
            crc: Some(data_crc),
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

pub fn read_items<'d, S: NorFlash, R>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
    data_buffer: &mut [u8],
    mut callback: impl FnMut(&mut S, Result<(Item<'_>, u32), Error<S::Error>>) -> Result<(), R>,
) -> Result<(), R> {
    let mut current_address = start_address;

    loop {
        if current_address >= end_address {
            return Ok(());
        }

        let value = match Item::read_new(flash, data_buffer, current_address, end_address) {
            Ok(Some(maybe_item)) => {
                let next_address = maybe_item.header().next_item_address::<S>(current_address);
                let value = match maybe_item {
                    MaybeItem::Corrupted(_) => {
                        #[cfg(feature = "defmt")]
                        defmt::error!("Found a corrupted item header at {:X}", current_address);
                        continue;
                    }
                    MaybeItem::Erased(_) => continue,
                    MaybeItem::Present(item) => Some(Ok((item, current_address))),
                };

                current_address = next_address;

                value
            }
            Ok(None) => None,
            Err(e) => Some(Err(e)),
        };

        match value {
            Some(value) => match callback(flash, value) {
                Err(r) => return Err(r),
                Ok(()) => {}
            },
            None => return Ok(()),
        }
    }
}

pub fn find_next_free_item_spot<S: NorFlash>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
) -> Result<Option<u32>, Error<S::Error>> {
    let mut current_address = start_address;

    while current_address < end_address {
        match ItemHeader::read_new(flash, current_address, end_address)? {
            Some(header) => current_address = header.next_item_address::<S>(current_address),
            None => return Ok(Some(current_address)),
        }
    }

    Ok(None)
}

pub enum MaybeItem<'d> {
    Corrupted(ItemHeader),
    Erased(ItemHeader),
    Present(Item<'d>),
}

impl<'d> MaybeItem<'d> {
    pub fn header(&self) -> &ItemHeader {
        match self {
            MaybeItem::Corrupted(header) => header,
            MaybeItem::Erased(header) => header,
            MaybeItem::Present(item) => &item.header,
        }
    }

    pub fn unwrap<E>(self) -> Result<Item<'d>, Error<E>> {
        match self {
            MaybeItem::Corrupted(_) => Err(Error::Corrupted),
            MaybeItem::Erased(_) => panic!("Cannot unwrap an erased item"),
            MaybeItem::Present(item) => Ok(item),
        }
    }
}

/// A crc that never returns 0
fn crc16(data: &[u8]) -> NonZeroU16 {
    let mut crc = 0xffff;
    for byte in data.iter() {
        crc ^= *byte as u16;
        for _ in 0..8 {
            if crc & 1 == 1 {
                crc = (crc >> 1) ^ 0x8D95; // CRC-16F/3 @ https://users.ece.cmu.edu/~koopman/crc/crc16.html
            } else {
                crc >>= 1;
            }
        }
    }
    crc ^= 0xffff;
    if crc == 0 {
        NonZeroU16::new(1).unwrap()
    } else {
        NonZeroU16::new(crc).unwrap()
    }
}
