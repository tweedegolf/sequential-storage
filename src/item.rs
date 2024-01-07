//! Module that implements storing raw items in flash.
//! This module is page-unaware. This means that start and end addresses should be the actual
//! start and end addresses that don't include the page markers.
//!
//! Memory layout of item:
//! ```text
//! ┌──────┬──────┬──────┬──────┬──────┬──────┬──────┬──────┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┬──┐
//! │      :      :      :      │      :      │      :      │  :  :  :  :  :  │  :  :  :  :  :  :  :  :  :  │  :  :  :  :  :  │
//! │            CRC            │   Length    │   Length'   │Pad to word align│            Data             │Pad to word align│
//! │      :      :      :      │      :      │      :      │  :  :  :  :  :  │  :  :  :  :  :   :  :  :  : │  :  :  :  :  :  │
//! └──────┴──────┴──────┴──────┴──────┴──────┴──────┴──────┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴──┴───┴──┴──┴──┴─┴──┴──┴──┴──┴──┴──┘
//! 0      1      2      3      4      5      6      7      8                 8+padding                     8+padding+length  8+padding+length+endpadding
//! ```
//!
//! An item consists of an [ItemHeader] and some data.
//! The header has a length field that encodes the length of the data, a [crc16] of the length (`Length'`)
//! and a crc field that encodes the checksum of the data.
//!
//! If the crc is 0, then the item is counted as being erased.
//! The crc is calculated by [adapted_crc32] which never produces a 0 value on its own
//! and has some other modifications to make corruption less likely to happen.
//!

use core::num::NonZeroU32;
use core::ops::ControlFlow;
use core::ops::Range;

use embedded_storage_async::nor_flash::{MultiwriteNorFlash, NorFlash};

use crate::{
    calculate_page_address, calculate_page_end_address, get_page_state, round_down_to_alignment,
    round_down_to_alignment_usize, round_up_to_alignment, round_up_to_alignment_usize, AlignedBuf,
    Error, NorFlashExt, PageState, MAX_WORD_SIZE,
};

#[derive(Debug)]
pub struct ItemHeader {
    /// Length of the item payload (so not including the header and not including word alignment)
    pub length: u16,
    pub crc: Option<NonZeroU32>,
}

impl ItemHeader {
    const LENGTH: usize = 8;

    const DATA_CRC_FIELD: Range<usize> = 0..4;
    const LENGTH_FIELD: Range<usize> = 4..6;
    const LENGTH_CRC_FIELD: Range<usize> = 6..8;

    pub async fn read_new<S: NorFlash>(
        flash: &mut S,
        address: u32,
        end_address: u32,
    ) -> Result<Option<Self>, Error<S::Error>> {
        let mut buffer = [0; MAX_WORD_SIZE];
        let header_slice = &mut buffer[..round_up_to_alignment_usize::<S>(Self::LENGTH)];

        if address + header_slice.len() as u32 > end_address {
            return Ok(None);
        }

        flash
            .read(address, header_slice)
            .await
            .map_err(|e| Error::Storage {
                value: e,
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })?;

        if header_slice.iter().all(|b| *b == 0xFF) {
            // What we read was fully erased bytes, so there's no header here
            return Ok(None);
        }

        let length_crc =
            u16::from_le_bytes(header_slice[Self::LENGTH_CRC_FIELD].try_into().unwrap());
        let calculated_length_crc = crc16(&header_slice[Self::LENGTH_FIELD]);

        if calculated_length_crc != length_crc {
            return Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            });
        }

        Ok(Some(Self {
            length: u16::from_le_bytes(header_slice[Self::LENGTH_FIELD].try_into().unwrap()),
            crc: {
                match u32::from_le_bytes(header_slice[Self::DATA_CRC_FIELD].try_into().unwrap()) {
                    0 => None,
                    value => Some(NonZeroU32::new(value).unwrap()),
                }
            },
        }))
    }

    pub async fn read_item<'d, S: NorFlash>(
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
                    return Ok(MaybeItem::Corrupted(self, data_buffer));
                }

                flash
                    .read(data_address, &mut data_buffer[..read_len])
                    .await
                    .map_err(|e| Error::Storage {
                        value: e,
                        #[cfg(feature = "_test")]
                        backtrace: std::backtrace::Backtrace::capture(),
                    })?;

                let data = &data_buffer[..self.length as usize];
                let data_crc = adapted_crc32(data);

                if data_crc == header_crc {
                    Ok(MaybeItem::Present(Item {
                        header: self,
                        data_buffer,
                    }))
                } else {
                    return Ok(MaybeItem::Corrupted(self, data_buffer));
                }
            }
        }
    }

    async fn write<S: NorFlash>(&self, flash: &mut S, address: u32) -> Result<(), Error<S::Error>> {
        let mut buffer = AlignedBuf([0xFF; MAX_WORD_SIZE]);

        buffer[Self::DATA_CRC_FIELD]
            .copy_from_slice(&self.crc.map(|crc| crc.get()).unwrap_or(0).to_le_bytes());
        buffer[Self::LENGTH_FIELD].copy_from_slice(&self.length.to_le_bytes());
        buffer[Self::LENGTH_CRC_FIELD]
            .copy_from_slice(&crc16(&self.length.to_le_bytes()).to_le_bytes());

        flash
            .write(
                address,
                &buffer[..round_up_to_alignment_usize::<S>(Self::LENGTH)],
            )
            .await
            .map_err(|e| Error::Storage {
                value: e,
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })
    }

    pub async fn erase_data<S: MultiwriteNorFlash>(
        mut self,
        flash: &mut S,
        address: u32,
    ) -> Result<Self, Error<S::Error>> {
        self.crc = None;
        self.write(flash, address).await?;
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

    pub async fn write_new<S: NorFlash>(
        flash: &mut S,
        address: u32,
        data: &'d [u8],
    ) -> Result<ItemHeader, Error<S::Error>> {
        let header = ItemHeader {
            length: data.len() as u16,
            crc: Some(adapted_crc32(data)),
        };

        Self::write_raw(&header, data, flash, address).await?;

        Ok(header)
    }

    async fn write_raw<S: NorFlash>(
        header: &ItemHeader,
        data: &[u8],
        flash: &mut S,
        address: u32,
    ) -> Result<(), Error<S::Error>> {
        header.write(flash, address).await?;

        let (data_block, data_left) = data.split_at(round_down_to_alignment_usize::<S>(data.len()));

        let data_address = ItemHeader::data_address::<S>(address);
        flash
            .write(data_address, data_block)
            .await
            .map_err(|e| Error::Storage {
                value: e,
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })?;

        if !data_left.is_empty() {
            let mut buffer = AlignedBuf([0; MAX_WORD_SIZE]);
            buffer[..data_left.len()].copy_from_slice(data_left);
            flash
                .write(
                    data_address + data_block.len() as u32,
                    &buffer[..round_up_to_alignment_usize::<S>(data_left.len())],
                )
                .await
                .map_err(|e| Error::Storage {
                    value: e,
                    #[cfg(feature = "_test")]
                    backtrace: std::backtrace::Backtrace::capture(),
                })?;
        }

        Ok(())
    }

    pub async fn write<S: NorFlash>(
        &self,
        flash: &mut S,
        address: u32,
    ) -> Result<(), Error<S::Error>> {
        Self::write_raw(&self.header, self.data(), flash, address).await
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

/// Scans through the items to find the first spot that is free to store a new item.
///
/// - `end_address` is exclusive.
pub async fn find_next_free_item_spot<S: NorFlash>(
    flash: &mut S,
    start_address: u32,
    end_address: u32,
    data_length: u32,
) -> Result<Option<u32>, Error<S::Error>> {
    let (_, free_item_address) = HeaderIter::new(start_address, end_address)
        .traverse(flash, |_, _| ControlFlow::Continue(()))
        .await?;
    if let Some(available) = ItemHeader::available_data_bytes::<S>(end_address - free_item_address)
    {
        if available >= data_length {
            Ok(Some(free_item_address))
        } else {
            Ok(None)
        }
    } else {
        Ok(None)
    }
}

pub enum MaybeItem<'d> {
    Corrupted(ItemHeader, &'d mut [u8]),
    Erased(ItemHeader),
    Present(Item<'d>),
}

impl<'d> core::fmt::Debug for MaybeItem<'d> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Corrupted(arg0, arg1) => f
                .debug_tuple("Corrupted")
                .field(arg0)
                .field(&arg1.get(..arg0.length as usize))
                .finish(),
            Self::Erased(arg0) => f.debug_tuple("Erased").field(arg0).finish(),
            Self::Present(arg0) => f.debug_tuple("Present").field(arg0).finish(),
        }
    }
}

impl<'d> MaybeItem<'d> {
    pub fn unwrap<E>(self) -> Result<Item<'d>, Error<E>> {
        match self {
            MaybeItem::Corrupted(_, _) => Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            }),
            MaybeItem::Erased(_) => panic!("Cannot unwrap an erased item"),
            MaybeItem::Present(item) => Ok(item),
        }
    }
}

/// A crc that never returns 0xFFFF
fn crc16(data: &[u8]) -> u16 {
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
        0xFFFF => 0xFFFE,
        other => other,
    }
}

/// Calculate the crc32 of the data as used by the crate.
fn adapted_crc32(data: &[u8]) -> NonZeroU32 {
    match crc32(data) {
        // CRC may not be 0 as that already means 'erased'
        0 => NonZeroU32::new(1).unwrap(),
        // To aid in early shutoff/cancellation, we make sure that if the first byte of
        // the crc is erased, it has to be wrong already.
        // Also, if the first byte is written, it must not be all 0xFF.
        value if value.to_le_bytes()[0] == 0 || value.to_le_bytes()[0] == 0xFF => {
            NonZeroU32::new(value ^ 1).unwrap()
        }
        value => NonZeroU32::new(value).unwrap(),
    }
}

fn crc32(data: &[u8]) -> u32 {
    // We use a modified initial value because the normal 0xFFFFFFF does not pass
    // the `crc32_all_ones_resistant` test
    crc32_with_initial(data, 0xEEEEEEEE)
}

fn crc32_with_initial(data: &[u8], initial: u32) -> u32 {
    const POLY: u32 = 0x82f63b78; // Castagnoli

    let mut crc = initial;

    for byte in data {
        crc ^= *byte as u32;

        for _ in 0..8 {
            let lowest_bit_set = crc & 1 > 0;
            crc >>= 1;
            if lowest_bit_set {
                crc ^= POLY;
            }
        }
    }

    !crc
}

/// Checks if the page is open or closed with all items erased.
/// By definition a partial-open page is not empty since it can still be written.
///
/// The page state can optionally be given if it's already known.
/// In that case the state will not be checked again.
pub async fn is_page_empty<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
    page_state: Option<PageState>,
) -> Result<bool, Error<S::Error>> {
    let page_state = match page_state {
        Some(page_state) => page_state,
        None => get_page_state::<S>(flash, flash_range.clone(), page_index).await?,
    };

    match page_state {
        PageState::Closed => {
            let page_data_start_address =
                calculate_page_address::<S>(flash_range.clone(), page_index) + S::WORD_SIZE as u32;
            let page_data_end_address =
                calculate_page_end_address::<S>(flash_range.clone(), page_index)
                    - S::WORD_SIZE as u32;

            let mut it = HeaderIter::new(page_data_start_address, page_data_end_address);
            Ok(it
                .traverse(flash, |header, _| match header.crc {
                    Some(_) => ControlFlow::Break(()),
                    None => ControlFlow::Continue(()),
                })
                .await?
                .0
                .is_none())
        }
        PageState::PartialOpen => Ok(false),
        PageState::Open => Ok(true),
    }
}

pub struct ItemIter {
    header: HeaderIter,
}

impl ItemIter {
    pub fn new(start_address: u32, end_address: u32) -> Self {
        Self {
            header: HeaderIter::new(start_address, end_address),
        }
    }

    pub async fn next<'m, S: NorFlash>(
        &mut self,
        flash: &mut S,
        data_buffer: &'m mut [u8],
    ) -> Result<Option<(Item<'m>, u32)>, Error<S::Error>> {
        while let (Some(header), address) = self.header.next(flash).await? {
            let data_buffer = unsafe {
                core::slice::from_raw_parts_mut(data_buffer.as_mut_ptr(), data_buffer.len())
            };

            match header
                .read_item(flash, data_buffer, address, self.header.end_address)
                .await?
            {
                MaybeItem::Corrupted { .. } => {
                    #[cfg(feature = "defmt")]
                    defmt::error!(
                        "Found a corrupted item at {:X}. Skipping...",
                        self.header.current_address
                    );
                    continue;
                }
                MaybeItem::Erased(_) => {}
                MaybeItem::Present(item) => {
                    return Ok(Some((item, address)));
                }
            }
        }
        Ok(None)
    }
}

pub struct HeaderIter {
    current_address: u32,
    end_address: u32,
}

impl HeaderIter {
    pub fn new(start_address: u32, end_address: u32) -> Self {
        Self {
            current_address: start_address,
            end_address,
        }
    }

    /// Fetch next item
    pub async fn next<S: NorFlash>(
        &mut self,
        flash: &mut S,
    ) -> Result<(Option<ItemHeader>, u32), Error<S::Error>> {
        self.traverse(flash, |_, _| ControlFlow::Break(())).await
    }

    /// Traverse all headers until the callback determines the next element.
    ///
    /// If the end of the headers is reached, a `None` item header is returned.
    pub async fn traverse<S: NorFlash>(
        &mut self,
        flash: &mut S,
        callback: impl Fn(&ItemHeader, u32) -> ControlFlow<(), ()>,
    ) -> Result<(Option<ItemHeader>, u32), Error<S::Error>> {
        if self.current_address >= self.end_address {
            return Ok((None, self.current_address));
        }

        loop {
            match ItemHeader::read_new(flash, self.current_address, self.end_address).await {
                Ok(Some(header)) => {
                    let next_address = header.next_item_address::<S>(self.current_address);
                    match callback(&header, self.current_address) {
                        ControlFlow::Continue(_) => {
                            self.current_address = next_address;
                            continue;
                        }
                        ControlFlow::Break(_) => {
                            let current_address = self.current_address;
                            self.current_address = next_address;
                            return Ok((Some(header), current_address));
                        }
                    }
                }
                Ok(None) => {
                    return Ok((None, self.current_address));
                }
                Err(Error::Corrupted { .. }) => {
                    #[cfg(feature = "defmt")]
                    defmt::error!(
                        "Found a corrupted item header at {:X}. Skipping...",
                        self.current_address
                    );
                    self.current_address += S::WORD_SIZE as u32;
                }
                Err(e) => return Err(e),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crc32_all_ones_resistant() {
        const DATA: [u8; 1024] = [0xFF; 1024];

        // Note: This should hold for all lengths up to the max item length
        // We do not test that because it takes too long.
        // Instead we only test the first couple because those are most likely to go bad.
        for length in 0..DATA.len() {
            let crc = crc32(&DATA[..length]);

            // println!("Num 0xFF bytes: {length}, crc: {crc:08X}");

            assert_ne!(crc, u32::MAX);
        }
    }
}
