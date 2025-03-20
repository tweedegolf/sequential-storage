use core::ops::{Add, AddAssign, Range};
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
    current_stats: FlashStatsSnapshot,
    /// Check that all write locations are writeable.
    pub write_count_check: WriteCountCheck,
    /// A countdown to shutoff. When some and 0, an early shutoff will happen.
    pub bytes_until_shutoff: Option<u32>,
    /// When true, write buffers have to be aligned
    pub alignment_check: bool,
}

impl<const PAGES: usize, const BYTES_PER_WORD: usize, const PAGE_WORDS: usize> Default
    for MockFlashBase<PAGES, BYTES_PER_WORD, PAGE_WORDS>
{
    fn default() -> Self {
        Self::new(WriteCountCheck::OnceOnly, None, true)
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
    pub fn new(
        write_count_check: WriteCountCheck,
        bytes_until_shutoff: Option<u32>,
        alignment_check: bool,
    ) -> Self {
        Self {
            writable: vec![T; Self::CAPACITY_WORDS],
            data: vec![u8::MAX; Self::CAPACITY_BYTES],
            current_stats: FlashStatsSnapshot {
                erases: 0,
                reads: 0,
                writes: 0,
                bytes_read: 0,
                bytes_written: 0,
            },
            write_count_check,
            bytes_until_shutoff,
            alignment_check,
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

    /// Get a snapshot of the performance counters
    pub fn stats_snapshot(&self) -> FlashStatsSnapshot {
        self.current_stats
    }

    #[cfg(any(test, feature = "_test"))]
    /// Print all items in flash to the returned string
    pub async fn print_items(&mut self) -> String {
        use crate::NorFlashExt;
        use crate::cache::NoCache;
        use std::fmt::Write;

        let mut buf = [0; 1024 * 16];

        let mut s = String::new();

        writeln!(s, "Items in flash:").unwrap();
        writeln!(s, "  Bytes until shutoff: {:?}", self.bytes_until_shutoff).unwrap();

        for page_index in 0..PAGES {
            writeln!(
                s,
                "  Page {page_index} ({}):",
                match crate::get_page_state(
                    self,
                    Self::FULL_FLASH_RANGE,
                    &mut NoCache::new(),
                    page_index
                )
                .await
                {
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

            let mut it = crate::item::ItemHeaderIter::new(page_data_start, page_data_end);
            while let (Some(header), item_address) = it.traverse(self, |_, _| false).await.unwrap()
            {
                let next_item_address = header.next_item_address::<Self>(item_address);
                let maybe_item = match header
                    .read_item(self, &mut buf, item_address, page_data_end)
                    .await
                {
                    Ok(maybe_item) => maybe_item,
                    Err(e) => {
                        writeln!(
                            s,
                            "   Item COULD NOT BE READ at {item_address}..{next_item_address}"
                        )
                        .unwrap();

                        println!("{s}");
                        panic!("{e:?}");
                    }
                };

                writeln!(
                    s,
                    "   Item {maybe_item:?} at {item_address}..{next_item_address}"
                )
                .unwrap();
            }
        }

        s
    }

    #[cfg(any(test, feature = "_test"))]
    /// Get the presence of the item at the given address.
    ///
    /// - If some, the item is there.
    /// - If true, the item is present and fine.
    /// - If false, the item is corrupt or erased.
    pub async fn get_item_presence(&mut self, target_item_address: u32) -> Option<bool> {
        use crate::NorFlashExt;

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
        let mut it = crate::item::ItemHeaderIter::new(page_data_start, page_data_end);
        while let (Some(header), item_address) = it.traverse(self, |_, _| false).await.unwrap() {
            let next_item_address = header.next_item_address::<Self>(item_address);

            if (item_address..next_item_address).contains(&target_item_address) {
                let maybe_item = header
                    .read_item(self, &mut buf, item_address, page_data_end)
                    .await
                    .unwrap();

                match maybe_item {
                    crate::item::MaybeItem::Corrupted(_, _)
                    | crate::item::MaybeItem::Erased(_, _) => {
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
        self.current_stats.reads += 1;
        self.current_stats.bytes_read += bytes.len() as u64;

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
        self.current_stats.erases += 1;

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
        self.current_stats.writes += 1;

        let range = Self::validate_operation(offset, bytes.len())?;

        // Check alignment. Some flash types are strict about the alignment of the input buffer. This ensures
        // that the mock flash is also strict to catch bugs and avoid regressions.
        if self.alignment_check && bytes.as_ptr() as usize % 4 != 0 {
            panic!("write buffer must be aligned to 4 bytes");
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

                self.current_stats.bytes_written += 1;

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

/// A snapshot of the flash performance statistics
#[derive(Debug, Clone, Copy)]
pub struct FlashStatsSnapshot {
    erases: u64,
    reads: u64,
    writes: u64,
    bytes_read: u64,
    bytes_written: u64,
}

impl FlashStatsSnapshot {
    /// Compare the snapshot to another snapshot.
    ///
    /// The oldest snapshot goes first, so it's `old.compare_to(new)`.
    pub fn compare_to(&self, other: Self) -> FlashStatsResult {
        FlashStatsResult {
            erases: other
                .erases
                .checked_sub(self.erases)
                .expect("Order is old compare to new"),
            reads: other
                .reads
                .checked_sub(self.reads)
                .expect("Order is old compare to new"),
            writes: other
                .writes
                .checked_sub(self.writes)
                .expect("Order is old compare to new"),
            bytes_read: other
                .bytes_read
                .checked_sub(self.bytes_read)
                .expect("Order is old compare to new"),
            bytes_written: other
                .bytes_written
                .checked_sub(self.bytes_written)
                .expect("Order is old compare to new"),
        }
    }
}

/// The performance stats of everything between two snapshots
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct FlashStatsResult {
    /// The amount of times a page has been erased
    pub erases: u64,
    /// The amount of times a read operation was started
    pub reads: u64,
    /// The amount of times a write operation was started
    pub writes: u64,
    /// The total amount of bytes that were read
    pub bytes_read: u64,
    /// The total amount of bytes that were written
    pub bytes_written: u64,
}

impl FlashStatsResult {
    /// Take the average of the stats
    pub fn take_average(&self, divider: u64) -> FlashAverageStatsResult {
        FlashAverageStatsResult {
            avg_erases: self.erases as f64 / divider as f64,
            avg_reads: self.reads as f64 / divider as f64,
            avg_writes: self.writes as f64 / divider as f64,
            avg_bytes_read: self.bytes_read as f64 / divider as f64,
            avg_bytes_written: self.bytes_written as f64 / divider as f64,
        }
    }
}

impl AddAssign for FlashStatsResult {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Add for FlashStatsResult {
    type Output = FlashStatsResult;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            erases: self.erases + rhs.erases,
            reads: self.reads + rhs.reads,
            writes: self.writes + rhs.writes,
            bytes_read: self.bytes_read + rhs.bytes_read,
            bytes_written: self.bytes_written + rhs.bytes_written,
        }
    }
}

/// The averaged performance stats of everything between two snapshots
#[derive(Debug, Clone, Copy, PartialEq, Default)]
pub struct FlashAverageStatsResult {
    /// The amount of times a page has been erased
    pub avg_erases: f64,
    /// The amount of times a read operation was started
    pub avg_reads: f64,
    /// The amount of times a write operation was started
    pub avg_writes: f64,
    /// The total amount of bytes that were read
    pub avg_bytes_read: f64,
    /// The total amount of bytes that were written
    pub avg_bytes_written: f64,
}

impl approx::AbsDiffEq for FlashAverageStatsResult {
    type Epsilon = f64;

    fn default_epsilon() -> Self::Epsilon {
        f64::EPSILON
    }

    fn abs_diff_eq(&self, other: &Self, epsilon: Self::Epsilon) -> bool {
        self.avg_erases.abs_diff_eq(&other.avg_erases, epsilon)
            && self.avg_reads.abs_diff_eq(&other.avg_reads, epsilon)
            && self.avg_writes.abs_diff_eq(&other.avg_writes, epsilon)
            && self
                .avg_bytes_read
                .abs_diff_eq(&other.avg_bytes_read, epsilon)
            && self
                .avg_bytes_written
                .abs_diff_eq(&other.avg_bytes_written, epsilon)
    }
}

impl approx::RelativeEq for FlashAverageStatsResult {
    fn default_max_relative() -> Self::Epsilon {
        f64::default_max_relative()
    }

    fn relative_eq(
        &self,
        other: &Self,
        epsilon: Self::Epsilon,
        max_relative: Self::Epsilon,
    ) -> bool {
        self.avg_erases
            .relative_eq(&other.avg_erases, epsilon, max_relative)
            && self
                .avg_reads
                .relative_eq(&other.avg_reads, epsilon, max_relative)
            && self
                .avg_writes
                .relative_eq(&other.avg_writes, epsilon, max_relative)
            && self
                .avg_bytes_read
                .relative_eq(&other.avg_bytes_read, epsilon, max_relative)
            && self
                .avg_bytes_written
                .relative_eq(&other.avg_bytes_written, epsilon, max_relative)
    }
}
