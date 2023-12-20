#![allow(missing_docs)]
use core::ops::Range;
use embedded_storage::nor_flash::{
    ErrorType, MultiwriteNorFlash, NorFlash, NorFlashError, NorFlashErrorKind, ReadNorFlash,
};

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

#[derive(Debug, Clone)]
pub struct MockFlashBase<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> {
    writable: Vec<Writable>,
    data: Vec<u8>,
    pub erases: u32,
    pub reads: u32,
    pub writes: u32,
    pub write_bit_flip_chance: f32,
    pub use_strict_write_count: bool,
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> Default
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    fn default() -> Self {
        Self::new(0.0, true)
    }
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize>
    MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    const CAPACITY_WORDS: usize = PAGES * PAGE_WORDS;
    const CAPACITY_BYTES: usize = Self::CAPACITY_WORDS * BYTES_PER_WORD;

    const PAGE_BYTES: usize = PAGE_WORDS * BYTES_PER_WORD;

    pub fn new(write_bit_flip_chance: f32, use_strict_write_count: bool) -> Self {
        Self {
            writable: vec![T; Self::CAPACITY_WORDS],
            data: vec![u8::MAX; Self::CAPACITY_BYTES],
            erases: 0,
            reads: 0,
            writes: 0,
            write_bit_flip_chance,
            use_strict_write_count,
        }
    }

    pub fn as_bytes(&self) -> &[u8] {
        &self.data
    }

    pub fn as_bytes_mut(&mut self) -> &mut [u8] {
        &mut self.data
    }

    fn validate_read_operation(offset: u32, length: usize) -> Result<Range<usize>, MockFlashError> {
        let offset = offset as usize;
        if (offset % Self::READ_SIZE) != 0 {
            Err(MockFlashError::NotAligned)
        } else if offset > Self::CAPACITY_BYTES || offset + length > Self::CAPACITY_BYTES {
            Err(MockFlashError::OutOfBounds)
        } else {
            Ok(offset..(offset + length))
        }
    }

    fn validate_write_operation(
        &self,
        offset: u32,
        length: usize,
    ) -> Result<Range<usize>, MockFlashError> {
        let range = Self::validate_read_operation(offset, length)?;

        if self.use_strict_write_count {
            for address in range.start..range.end {
                if self.writable[address / BYTES_PER_WORD] == Writable::N {
                    return Err(MockFlashError::NotWritable(address as u32));
                }
            }
        }

        Ok(range)
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

        let range = Self::validate_read_operation(offset, bytes.len())?;

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

        for byte in self.as_bytes_mut()[from..to].iter_mut() {
            *byte = u8::MAX;
        }

        let range = from / BYTES_PER_WORD..to / BYTES_PER_WORD;
        for word_writable in self.writable[range].iter_mut() {
            *word_writable = T;
        }

        Ok(())
    }

    fn write(&mut self, offset: u32, bytes: &[u8]) -> Result<(), Self::Error> {
        self.writes += 1;

        let range = self.validate_write_operation(offset, bytes.len())?;

        if bytes.len() % Self::WRITE_SIZE != 0 {
            panic!("any write must be a multiple of Self::WRITE_SIZE bytes");
        }

        let start_word = range.start / BYTES_PER_WORD;
        let end_word = (range.end + BYTES_PER_WORD - 1) / BYTES_PER_WORD;

        let write_bit_flip_chance = self.write_bit_flip_chance;

        for (target, source) in self.as_bytes_mut()[range].iter_mut().zip(bytes.iter()) {
            let mut source = *source;

            if write_bit_flip_chance > 0.0 {
                for bit in 0..8 {
                    if rand::random::<f32>() < write_bit_flip_chance {
                        source ^= 1 << bit;
                    }
                }
            }

            *target &= source;
        }

        for word_writable in self.writable[start_word..end_word].iter_mut() {
            *word_writable = match *word_writable {
                Writable::T => Writable::O,
                Writable::O => Writable::N,
                Writable::N => Writable::N,
            };
        }

        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MockFlashError {
    OutOfBounds,
    NotAligned,
    NotWritable(u32),
}

impl NorFlashError for MockFlashError {
    fn kind(&self) -> NorFlashErrorKind {
        match self {
            MockFlashError::OutOfBounds => NorFlashErrorKind::OutOfBounds,
            MockFlashError::NotAligned => NorFlashErrorKind::NotAligned,
            MockFlashError::NotWritable(_) => NorFlashErrorKind::Other,
        }
    }
}
