use core::ops::Range;
use embedded_storage_async::nor_flash::{
    ErrorType, MultiwriteNorFlash, NorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash,
};

/// State of a word in the flash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Writable {
    /// Twice
    T,
    /// Once (can only convert 1 bits to 0
    O,
    /// Never (must be cleared before being writable again)
    N,
}

use Writable::*;

/// Base type for in memory flash that can be used for mocking.
#[derive(Debug, Clone)]
pub struct MockFlashBase<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> {
    writable: Vec<Writable>,
    data: Vec<u8>,
    /// Number of erases done.
    pub erases: u32,
    /// Number of reads done.
    pub reads: u32,
    /// Number of writes done.
    pub writes: u32,
    /// Check that all write locations are writeable.
    pub write_count_check: WriteCountCheck,
    /// A countdown to shutoff. When some and 0, an early shutoff will happen.
    pub bytes_until_shutoff: Option<u32>,
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> Default
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    fn default() -> Self {
        Self::new(WriteCountCheck::OnceOnly, None)
    }
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize>
    MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    const CAPACITY_WORDS: usize = PAGES * PAGE_WORDS;
    const CAPACITY_BYTES: usize = Self::CAPACITY_WORDS * BYTES_PER_WORD;

    const PAGE_BYTES: usize = PAGE_WORDS * BYTES_PER_WORD;

    /// The full address range of this flash
    pub const FULL_FLASH_RANGE: Range<u32> = 0..(PAGES * PAGE_WORDS * BYTES_PER_WORD) as u32;

    /// Create a new flash instance.
    pub fn new(write_count_check: WriteCountCheck, bytes_until_shutoff: Option<u32>) -> Self {
        Self {
            writable: vec![T; Self::CAPACITY_WORDS],
            data: vec![u8::MAX; Self::CAPACITY_BYTES],
            erases: 0,
            reads: 0,
            writes: 0,
            write_count_check,
            bytes_until_shutoff,
        }
    }

    /// Get a reference to the underlying data.
    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    /// Get a mutable reference to the underlying data.
    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    fn validate_operation(offset: u32, length: usize) -> Result<Range<usize>, MockFlashError> {
        let offset = offset as usize;
        if (offset % Self::READ_SIZE) != 0 {
            Err(MockFlashError::NotAligned)
        } else if offset > Self::CAPACITY_BYTES || offset + length > Self::CAPACITY_BYTES {
            Err(MockFlashError::OutOfBounds)
        } else {
            Ok(offset..(offset + length))
        }
    }

    fn check_shutoff(&mut self, address: u32, _operation: &str) -> Result<(), MockFlashError> {
        if let Some(bytes_until_shutoff) = self.bytes_until_shutoff.as_mut() {
            if let Some(next) = bytes_until_shutoff.checked_sub(1) {
                *bytes_until_shutoff = next;
                Ok(())
            } else {
                #[cfg(fuzzing_repro)]
                eprintln!("!!! Shutoff at {address} while doing '{_operation}' !!!");
                self.bytes_until_shutoff = None;
                Err(MockFlashError::EarlyShutoff(address))
            }
        } else {
            Ok(())
        }
    }

    #[cfg(feature = "_test")]
    /// Print all items in flash to the returned string
    pub fn print_items(&mut self) -> String {
        use crate::NorFlashExt;
        use futures::executor::block_on;
        use std::fmt::Write;

        let mut buf = [0; 1024 * 16];

        let mut s = String::new();

        writeln!(s, "Items in flash:").unwrap();
        writeln!(s, "  Bytes until shutoff: {:?}", self.bytes_until_shutoff).unwrap();

        for page_index in 0..PAGES {
            writeln!(
                s,
                "  Page {page_index} ({}):",
                match block_on(crate::get_page_state(
                    self,
                    Self::FULL_FLASH_RANGE,
                    page_index
                )) {
                    Ok(value) => format!("{value:?}"),
                    Err(e) => format!("Error ({e:?})"),
                }
            )
            .unwrap();
            let page_data_start =
                crate::calculate_page_address::<Self>(Self::FULL_FLASH_RANGE, page_index)
                    + Self::WORD_SIZE as u32;
            let page_data_end =
                crate::calculate_page_end_address::<Self>(Self::FULL_FLASH_RANGE, page_index)
                    - Self::WORD_SIZE as u32;

            let mut it = crate::item::HeaderIter::new(page_data_start, page_data_end);
            while let (Some(header), item_address) =
                block_on(it.traverse(self, |_, _| core::ops::ControlFlow::Break(()))).unwrap()
            {
                let next_item_address = header.next_item_address::<Self>(item_address);
                let maybe_item =
                    block_on(header.read_item(self, &mut buf, item_address, page_data_end))
                        .unwrap();
                writeln!(
                    s,
                    "   Item {maybe_item:?} at {item_address}..{next_item_address}"
                )
                .unwrap();
            }
        }

        s
    }

    #[cfg(feature = "_test")]
    /// Get the presence of the item at the given address.
    ///
    /// - If some, the item is there.
    /// - If true, the item is present and fine.
    /// - If false, the item is corrupt or erased.
    pub fn get_item_presence(&mut self, target_item_address: u32) -> Option<bool> {
        use core::ops::ControlFlow;

        use crate::NorFlashExt;
        use futures::executor::block_on;

        if !Self::FULL_FLASH_RANGE.contains(&target_item_address) {
            return None;
        }

        let mut buf = [0; 1024 * 16];

        let page_index =
            crate::calculate_page_index::<Self>(Self::FULL_FLASH_RANGE, target_item_address);

        let page_data_start =
            crate::calculate_page_address::<Self>(Self::FULL_FLASH_RANGE, page_index)
                + Self::WORD_SIZE as u32;
        let page_data_end =
            crate::calculate_page_end_address::<Self>(Self::FULL_FLASH_RANGE, page_index)
                - Self::WORD_SIZE as u32;

        let mut found_item = None;
        let mut it = crate::item::HeaderIter::new(page_data_start, page_data_end);
        while let (Some(header), item_address) =
            block_on(it.traverse(self, |_, _| ControlFlow::Break(()))).unwrap()
        {
            let next_item_address = header.next_item_address::<Self>(item_address);

            if (item_address..next_item_address).contains(&target_item_address) {
                let maybe_item =
                    block_on(header.read_item(self, &mut buf, item_address, page_data_end))
                        .unwrap();

                match maybe_item {
                    crate::item::MaybeItem::Corrupted(_, _) | crate::item::MaybeItem::Erased(_) => {
                        found_item.replace(false);
                        break;
                    }
                    crate::item::MaybeItem::Present(_) => {
                        found_item.replace(true);
                        break;
                    }
                }
            }
        }

        found_item
    }
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> ErrorType
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    type Error = MockFlashError;
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> ReadNorFlash
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    const READ_SIZE: usize = BYTES_PER_WORD;

    async fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
        self.reads += 1;

        if bytes.len() % Self::READ_SIZE != 0 {
            panic!("any read must be a multiple of Self::READ_SIZE bytes");
        }

        let range = Self::validate_operation(offset, bytes.len())?;

        bytes.copy_from_slice(&self.as_bytes()[range]);

        Ok(())
    }

    fn capacity(&self) -> usize {
        Self::CAPACITY_BYTES
    }
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> MultiwriteNorFlash
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> NorFlash
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    const WRITE_SIZE: usize = BYTES_PER_WORD;

    const ERASE_SIZE: usize = Self::PAGE_BYTES;

    async fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
        self.erases += 1;

        let from = from as usize;
        let to = to as usize;

        assert!(from <= to);

        if to > Self::CAPACITY_BYTES {
            return Err(MockFlashError::OutOfBounds);
        }

        if from % Self::PAGE_BYTES != 0 || to % Self::PAGE_BYTES != 0 {
            return Err(MockFlashError::NotAligned);
        }

        for index in from..to {
            self.check_shutoff(index as u32, "erase")?;
            self.as_bytes_mut()[index] = u8::MAX;

            if index % BYTES_PER_WORD == 0 {
                self.writable[index / BYTES_PER_WORD] = T;
            }
        }

        Ok(())
    }

    async fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        self.writes += 1;

        let range = Self::validate_operation(offset, bytes.len())?;

        if bytes.as_ptr() as usize % Self::WRITE_SIZE != 0 {
            panic!("write buffer must be aligned to Self::WRITE_SIZE bytes");
        }

        if bytes.len() % Self::WRITE_SIZE != 0 {
            panic!("any write must be a multiple of Self::WRITE_SIZE bytes");
        }

        for (source_word, address) in bytes
            .chunks_exact(BYTES_PER_WORD)
            .zip(range.step_by(BYTES_PER_WORD))
        {
            for (byte_index, byte) in source_word.iter().enumerate() {
                self.check_shutoff((address + byte_index) as u32, "write")?;

                if byte_index == 0 {
                    let word_writable = &mut self.writable[address / BYTES_PER_WORD];
                    *word_writable = match (*word_writable, self.write_count_check) {
                        (v, WriteCountCheck::Disabled) => v,
                        (Writable::T, _) => Writable::O,
                        (Writable::O, WriteCountCheck::Twice) => Writable::N,
                        (Writable::O, WriteCountCheck::TwiceDifferent)
                            if source_word == &self.data[address..][..BYTES_PER_WORD] =>
                        {
                            Writable::O
                        }
                        (Writable::O, WriteCountCheck::TwiceDifferent) => Writable::N,
                        (Writable::O, WriteCountCheck::TwiceWithZero)
                            if source_word.iter().all(|b| *b == 0) =>
                        {
                            Writable::N
                        }
                        _ => return Err(MockFlashError::NotWritable(address as u32)),
                    };
                }

                self.as_bytes_mut()[address + byte_index] &= byte;
            }
        }

        Ok(())
    }
}

/// Errors reported by mock flash.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MockFlashError {
    /// Operation out of bounds.
    OutOfBounds,
    /// Offset or data not aligned.
    NotAligned,
    /// Location not writeable.
    NotWritable(u32),
    /// We got a shutoff
    EarlyShutoff(u32),
}

impl NorFlashError for MockFlashError {
    fn kind(&self) -> NorFlashErrorKind {
        match self {
            MockFlashError::OutOfBounds => NorFlashErrorKind::OutOfBounds,
            MockFlashError::NotAligned => NorFlashErrorKind::NotAligned,
            MockFlashError::NotWritable(_) => NorFlashErrorKind::Other,
            MockFlashError::EarlyShutoff(_) => NorFlashErrorKind::Other,
        }
    }
}

/// The mode the write counter works in
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WriteCountCheck {
    /// A word may only be written once
    OnceOnly,
    /// A word may be written twice, but it only counts when it actually changes
    TwiceDifferent,
    /// A word may be written twice
    Twice,
    /// A work may be written twice, but the second time has to be all zeroes. (STM32 does this)
    TwiceWithZero,
    /// No check at all
    Disabled,
}
