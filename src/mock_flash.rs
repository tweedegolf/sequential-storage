use core::ops::Range;
use embedded_storage::nor_flash::{
    ErrorType, MultiwriteNorFlash, NorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash,
};

/// State of a word in the flash.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Writable {
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
    pub use_strict_write_count: bool,
    /// A countdown to shutoff. When some and 0, an early shutoff will happen.
    pub bytes_until_shutoff: Option<u32>,
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> Default
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    fn default() -> Self {
        Self::new(true, None)
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
    pub fn new(use_strict_write_count: bool, bytes_until_shutoff: Option<u32>) -> Self {
        Self {
            writable: vec![T; Self::CAPACITY_WORDS],
            data: vec![u8::MAX; Self::CAPACITY_BYTES],
            erases: 0,
            reads: 0,
            writes: 0,
            use_strict_write_count,
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

    fn check_shutoff(&mut self, _address: u32, _operation: &str) -> Result<(), MockFlashError> {
        if let Some(bytes_until_shutoff) = self.bytes_until_shutoff.as_mut() {
            if let Some(next) = bytes_until_shutoff.checked_sub(1) {
                *bytes_until_shutoff = next;
                Ok(())
            } else {
                #[cfg(fuzzing_repro)]
                eprintln!("!!! Shutoff at {_address} while doing '{_operation}' !!!");
                self.bytes_until_shutoff = None;
                Err(MockFlashError::EarlyShutoff)
            }
        } else {
            Ok(())
        }
    }

    #[cfg(feature = "_test")]
    /// Print all items in flash to the returned string
    pub fn print_items(&mut self) -> String {
        use crate::NorFlashExt;
        use std::fmt::Write;

        let mut buf = [0; 1024 * 16];

        let mut s = String::new();

        writeln!(s, "Items in flash:").unwrap();
        writeln!(s, "  Bytes until shutoff: {:?}", self.bytes_until_shutoff).unwrap();

        for page_index in 0..PAGES {
            writeln!(
                s,
                "  Page {page_index} ({}):",
                match crate::get_page_state(self, Self::FULL_FLASH_RANGE, page_index) {
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

            crate::item::read_item_headers(
                self,
                page_data_start,
                page_data_end,
                |flash, header, item_address| {
                    let next_item_address = header.next_item_address::<Self>(item_address);
                    let maybe_item = header
                        .read_item(flash, &mut buf, item_address, page_data_end)
                        .unwrap();
                    writeln!(
                        s,
                        "   Item {maybe_item:?} at {item_address}..{next_item_address}"
                    )
                    .unwrap();
                    core::ops::ControlFlow::<(), ()>::Continue(())
                },
            )
            .unwrap();
        }

        s
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

    fn read(&mut self, offset: u32, bytes: &mut [u8]) -> Result<(), Self::Error> {
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

    fn erase(&mut self, from: u32, to: u32) -> Result<(), Self::Error> {
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

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        self.writes += 1;

        let range = Self::validate_operation(offset, bytes.len())?;

        if bytes.len() % Self::WRITE_SIZE != 0 {
            panic!("any write must be a multiple of Self::WRITE_SIZE bytes");
        }

        for (index, source) in range.zip(bytes.iter()) {
            let source = *source;

            self.check_shutoff(index as u32, "write")?;

            self.as_bytes_mut()[index] &= source;

            if index % BYTES_PER_WORD == 0 {
                let word_writable = &mut self.writable[index / BYTES_PER_WORD];
                *word_writable = match *word_writable {
                    Writable::T => Writable::O,
                    Writable::O => Writable::N,
                    Writable::N if self.use_strict_write_count => {
                        return Err(MockFlashError::NotWritable(index as u32))
                    }
                    Writable::N => Writable::N,
                };
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
    EarlyShutoff,
}

impl NorFlashError for MockFlashError {
    fn kind(&self) -> NorFlashErrorKind {
        match self {
            MockFlashError::OutOfBounds => NorFlashErrorKind::OutOfBounds,
            MockFlashError::NotAligned => NorFlashErrorKind::NotAligned,
            MockFlashError::NotWritable(_) => NorFlashErrorKind::Other,
            MockFlashError::EarlyShutoff => NorFlashErrorKind::Other,
        }
    }
}
