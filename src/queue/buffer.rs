//! RAM-buffered wrapper for [`QueueStorage`].
//!
//! NOR flash writes are slow and erases are very slow. If a producer emits data faster than the
//! flash interface can commit it, [`BufferedQueue`] accepts items into a fixed-size RAM ring
//! buffer via the synchronous [`enqueue`][BufferedQueue::enqueue] call (no flash I/O) and
//! asynchronously drains them to flash via [`drain_one`][BufferedQueue::drain_one] or
//! [`drain_all`][BufferedQueue::drain_all].
//!
//! # Overflow policy
//!
//! When the RAM ring is full, [`enqueue`][BufferedQueue::enqueue] behaviour is controlled by
//! [`OverflowPolicy`]: either return `Err(())` or silently evict the oldest buffered item.
//!
//! # Ordering
//!
//! FIFO ordering is preserved: flash items are always older than RAM items.
//! [`pop`][BufferedQueue::pop] and [`peek`][BufferedQueue::peek] read from flash first,
//! falling back to the oldest RAM item if flash is empty.
//!
//! # Power-fail note
//!
//! Items that are in the RAM ring and have not yet been drained to flash **will be lost** on
//! power loss. Items that have been drained follow the power-fail safety guarantees of
//! sequential-storage.
//!
//! # Embassy / ISR-safe use
//!
//! Enable the `shared-ram-ring` feature for [`SharedRamRing`], which wraps the ring in a
//! critical-section mutex so it can be enqueued to from an interrupt handler, and signals
//! a drain task the moment data arrives.

use embedded_storage_async::nor_flash::{MultiwriteNorFlash, NorFlash};

use super::QueueStorage;
use crate::{Error, cache::CacheImpl};

// ── RamRing ──────────────────────────────────────────────────────────────────

/// A compact, fixed-capacity ring buffer for variable-length byte items.
///
/// Each item is stored as a 2-byte little-endian length prefix followed by the item's bytes,
/// so the usable capacity for data is `N - 2` bytes per item at most.
pub struct RamRing<const N: usize> {
    buf: [u8; N],
    read_pos: usize,
    write_pos: usize,
    /// Total bytes occupied (length prefixes + data).
    used: usize,
    item_count: usize,
}

impl<const N: usize> RamRing<N> {
    /// Create a new empty ring.
    pub const fn new() -> Self {
        Self {
            buf: [0u8; N],
            read_pos: 0,
            write_pos: 0,
            used: 0,
            item_count: 0,
        }
    }

    /// Number of items currently buffered.
    pub fn len(&self) -> usize {
        self.item_count
    }

    /// Returns `true` if the ring contains no items.
    pub fn is_empty(&self) -> bool {
        self.item_count == 0
    }

    /// Bytes currently occupied (including length prefixes).
    pub fn bytes_used(&self) -> usize {
        self.used
    }

    /// Byte length of the oldest buffered item, or `None` if the ring is empty.
    pub fn oldest_len(&self) -> Option<usize> {
        if self.item_count == 0 {
            return None;
        }
        let lo = self.buf[self.read_pos] as usize;
        let hi = self.buf[(self.read_pos + 1) % N] as usize;
        Some(lo | (hi << 8))
    }

    /// Push an item into the ring.
    ///
    /// Returns `Err(())` if there is insufficient space or the item exceeds `u16::MAX` bytes.
    #[allow(clippy::result_unit_err)]
    pub fn push(&mut self, data: &[u8]) -> Result<(), ()> {
        let len = data.len();
        if len > u16::MAX as usize {
            return Err(());
        }
        let total = 2 + len;
        if self.used + total > N {
            return Err(());
        }
        self.write_raw(data);
        Ok(())
    }

    /// Push an item, discarding the oldest item(s) to make room if necessary.
    ///
    /// Returns `Err(())` only if the item is larger than the entire ring capacity.
    #[allow(clippy::result_unit_err)]
    pub fn push_overwriting(&mut self, data: &[u8]) -> Result<(), ()> {
        let len = data.len();
        if len > u16::MAX as usize {
            return Err(());
        }
        let total = 2 + len;
        if total > N {
            return Err(());
        }
        while self.used + total > N {
            self.discard_oldest();
        }
        self.write_raw(data);
        Ok(())
    }

    /// Copy the oldest item into `buf` and return a slice of the written bytes.
    ///
    /// Returns `None` if the ring is empty or `buf` is smaller than [`oldest_len`][Self::oldest_len].
    pub fn peek_into<'b>(&self, buf: &'b mut [u8]) -> Option<&'b [u8]> {
        let len = self.oldest_len()?;
        if buf.len() < len {
            return None;
        }
        let mut pos = (self.read_pos + 2) % N;
        for b in buf[..len].iter_mut() {
            *b = self.buf[pos];
            pos = (pos + 1) % N;
        }
        Some(&buf[..len])
    }

    /// Discard the oldest item without copying it. Does nothing if the ring is empty.
    pub fn discard_oldest(&mut self) {
        if let Some(len) = self.oldest_len() {
            self.read_pos = (self.read_pos + 2 + len) % N;
            self.used -= 2 + len;
            self.item_count -= 1;
        }
    }

    fn write_raw(&mut self, data: &[u8]) {
        let len = data.len();
        self.write_byte(len as u8);
        self.write_byte((len >> 8) as u8);
        for &b in data {
            self.write_byte(b);
        }
        self.used += 2 + len;
        self.item_count += 1;
    }

    fn write_byte(&mut self, b: u8) {
        self.buf[self.write_pos] = b;
        self.write_pos = (self.write_pos + 1) % N;
    }
}

impl<const N: usize> Default for RamRing<N> {
    fn default() -> Self {
        Self::new()
    }
}

// ── OverflowPolicy ────────────────────────────────────────────────────────────

/// Controls what happens when [`enqueue`][BufferedQueue::enqueue] is called on a full RAM ring.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum OverflowPolicy {
    /// Return `Err(())` — the caller decides whether to drop the item or drain first.
    Err,
    /// Silently discard the oldest buffered item(s) to make room for the new one.
    ///
    /// The new item is always accepted as long as it physically fits in the ring
    /// (i.e. `data.len() + 2 <= RAM_BYTES`).
    DiscardOldest,
}

// ── BufferedQueue ─────────────────────────────────────────────────────────────

/// A write-buffered queue that accepts items into a RAM ring and drains them to NOR flash.
///
/// ## Type parameters
///
/// - `S`: NOR flash driver implementing [`NorFlash`].
/// - `C`: Cache implementation from [`crate::cache`].
/// - `RAM_BYTES`: Capacity of the RAM ring buffer in bytes (includes 2-byte per-item overhead).
///
/// ## Usage pattern
///
/// ```ignore
/// // Fast path — called from a tight loop:
/// queue.enqueue(&sample, OverflowPolicy::Err)?;
///
/// // Slow path — called from a lower-priority task or on a timer:
/// queue.drain_all(&mut scratch, false).await?;
///
/// // Read path — flash items are popped first, then RAM items:
/// if let Some(data) = queue.pop(&mut buf).await? {
///     // process data
/// }
/// ```
///
/// For ISR-safe use, enable the `shared-ram-ring` feature and use [`SharedRamRing`] instead.
pub struct BufferedQueue<S: NorFlash, C: CacheImpl, const RAM_BYTES: usize> {
    storage: QueueStorage<S, C>,
    ram: RamRing<RAM_BYTES>,
}

impl<S: NorFlash, C: CacheImpl, const RAM_BYTES: usize> BufferedQueue<S, C, RAM_BYTES> {
    /// Wrap an existing [`QueueStorage`] with a RAM ring buffer.
    pub fn new(storage: QueueStorage<S, C>) -> Self {
        Self {
            storage,
            ram: RamRing::new(),
        }
    }

    /// Enqueue an item into the RAM ring buffer.
    ///
    /// This is **synchronous and never touches flash**. When the ring is full the behaviour
    /// is determined by `policy`: return `Err(())` or evict the oldest item.
    #[allow(clippy::result_unit_err)]
    pub fn enqueue(&mut self, data: &[u8], policy: OverflowPolicy) -> Result<(), ()> {
        match policy {
            OverflowPolicy::Err => self.ram.push(data),
            OverflowPolicy::DiscardOldest => self.ram.push_overwriting(data),
        }
    }

    /// Drain one item from the RAM ring to flash.
    ///
    /// `scratch` is caller-provided temporary storage; it must be at least as large as the
    /// oldest pending item.
    ///
    /// Returns `Ok(true)` if an item was committed to flash, `Ok(false)` if the ring was empty.
    pub async fn drain_one(
        &mut self,
        scratch: &mut [u8],
        allow_overwrite: bool,
    ) -> Result<bool, Error<S::Error>> {
        let Some(data) = self.ram.peek_into(scratch) else {
            return Ok(false);
        };
        let len = data.len();
        self.storage.push(&scratch[..len], allow_overwrite).await?;
        self.ram.discard_oldest();
        Ok(true)
    }

    /// Drain all RAM-buffered items to flash.
    ///
    /// `scratch` must be large enough for the largest pending item.
    pub async fn drain_all(
        &mut self,
        scratch: &mut [u8],
        allow_overwrite: bool,
    ) -> Result<(), Error<S::Error>> {
        while self.drain_one(scratch, allow_overwrite).await? {}
        Ok(())
    }

    /// Pop the oldest item from the queue.
    ///
    /// Flash items are always older than RAM items, so flash is read first. If flash is
    /// empty the oldest item is taken directly from the RAM ring without writing to flash.
    pub async fn pop<'d>(
        &mut self,
        data_buffer: &'d mut [u8],
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        // Reborrow so we can reuse data_buffer if flash returns None.
        let flash_len = self.storage.pop(&mut *data_buffer).await?.map(|s| s.len());
        if let Some(len) = flash_len {
            return Ok(Some(&mut data_buffer[..len]));
        }
        let len = self.ram.peek_into(data_buffer).map(|s| s.len());
        if let Some(len) = len {
            self.ram.discard_oldest();
            return Ok(Some(&mut data_buffer[..len]));
        }
        Ok(None)
    }

    /// Peek at the oldest item without removing it.
    ///
    /// Flash items are always older than RAM items, so flash is read first. If flash is
    /// empty the oldest item is read directly from the RAM ring without writing to flash.
    pub async fn peek<'d>(
        &mut self,
        data_buffer: &'d mut [u8],
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>>
    where
        S: MultiwriteNorFlash,
    {
        // Reborrow so we can reuse data_buffer if flash returns None.
        let flash_len = self.storage.peek(&mut *data_buffer).await?.map(|s| s.len());
        if let Some(len) = flash_len {
            return Ok(Some(&mut data_buffer[..len]));
        }
        let len = self.ram.peek_into(data_buffer).map(|s| s.len());
        if let Some(len) = len {
            return Ok(Some(&mut data_buffer[..len]));
        }
        Ok(None)
    }

    /// Total capacity of the RAM ring in bytes (including 2-byte per-item length prefixes).
    pub const fn ram_capacity_bytes() -> usize {
        RAM_BYTES
    }

    /// Free bytes remaining in the RAM ring.
    pub fn ram_free_bytes(&self) -> usize {
        RAM_BYTES - self.ram.bytes_used()
    }

    /// Number of items currently buffered in RAM (not yet committed to flash).
    pub fn ram_pending_count(&self) -> usize {
        self.ram.len()
    }

    /// Bytes currently occupied in the RAM ring (including 2-byte per-item length prefixes).
    pub fn ram_bytes_used(&self) -> usize {
        self.ram.bytes_used()
    }

    /// Consume this [`BufferedQueue`] and return the inner [`QueueStorage`].
    ///
    /// **Any items still in the RAM ring are discarded.**
    pub fn into_storage(self) -> QueueStorage<S, C> {
        self.storage
    }
}

// ── SharedRamRing ─────────────────────────────────────────────────────────────

/// An ISR-safe RAM ring buffer with an Embassy [`Signal`][embassy_sync::signal::Signal] that
/// wakes a drain task on enqueue.
///
/// Designed to be placed in a `static`:
/// ```ignore
/// static RING: SharedRamRing<256> = SharedRamRing::new();
/// ```
///
/// The [`enqueue`][SharedRamRing::enqueue] method is synchronous and interrupt-safe.
/// Drain and read methods (`drain_one`, `drain_all`, `pop`, `peek`) are `async` and intended
/// for task context; they take a `&mut QueueStorage` so flash access remains exclusive to
/// one task.
///
/// ## Typical wiring
///
/// ```ignore
/// static RING: SharedRamRing<256> = SharedRamRing::new();
///
/// // In an interrupt handler (or anywhere, no async needed):
/// RING.enqueue(&sensor_sample, OverflowPolicy::DiscardOldest);
///
/// // In the drain task:
/// #[embassy_executor::task]
/// async fn drain(mut storage: QueueStorage<Flash, NoCache>) {
///     let mut scratch = [0u8; 64];
///     loop {
///         RING.wait_and_drain_all(&mut storage, &mut scratch, false).await.unwrap();
///     }
/// }
/// ```
#[cfg(feature = "shared-ram-ring")]
pub struct SharedRamRing<const N: usize> {
    ring: embassy_sync::blocking_mutex::Mutex<
        embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex,
        core::cell::RefCell<RamRing<N>>,
    >,
    signal: embassy_sync::signal::Signal<
        embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex,
        (),
    >,
}

#[cfg(feature = "shared-ram-ring")]
impl<const N: usize> SharedRamRing<N> {
    /// Create a new `SharedRamRing`. Suitable for `static` initialisation.
    pub const fn new() -> Self {
        Self {
            ring: embassy_sync::blocking_mutex::Mutex::new(
                core::cell::RefCell::new(RamRing::new()),
            ),
            signal: embassy_sync::signal::Signal::new(),
        }
    }

    // ── Producer API (sync, ISR-safe) ─────────────────────────────────────────

    /// Enqueue an item. Safe to call from any context, including interrupt handlers.
    ///
    /// Signals the drain task after a successful enqueue so it wakes without polling.
    /// Returns `Err(())` if the ring is full and `policy` is [`OverflowPolicy::Err`].
    #[allow(clippy::result_unit_err)]
    pub fn enqueue(&self, data: &[u8], policy: OverflowPolicy) -> Result<(), ()> {
        let result = self.ring.lock(|r| match policy {
            OverflowPolicy::Err => r.borrow_mut().push(data),
            OverflowPolicy::DiscardOldest => r.borrow_mut().push_overwriting(data),
        });
        if result.is_ok() {
            self.signal.signal(());
        }
        result
    }

    // ── Task-context API (async) ──────────────────────────────────────────────

    /// Wait until at least one item has been enqueued since the last `wait`.
    pub async fn wait(&self) {
        self.signal.wait().await;
    }

    /// Drain one item from the ring to flash.
    ///
    /// `scratch` must be at least [`oldest_ram_item_len`][Self::oldest_ram_item_len] bytes.
    /// Returns `Ok(true)` if an item was written, `Ok(false)` if the ring was empty.
    ///
    /// The critical section is held only for the brief ring peek/discard; the slow flash
    /// write runs outside it.
    pub async fn drain_one<S: NorFlash, C: CacheImpl>(
        &self,
        storage: &mut QueueStorage<S, C>,
        scratch: &mut [u8],
        allow_overwrite: bool,
    ) -> Result<bool, Error<S::Error>> {
        let len = self
            .ring
            .lock(|r| r.borrow().peek_into(scratch).map(|s| s.len()));
        let Some(len) = len else {
            return Ok(false);
        };
        storage.push(&scratch[..len], allow_overwrite).await?;
        self.ring.lock(|r| r.borrow_mut().discard_oldest());
        Ok(true)
    }

    /// Drain all ring items to flash.
    ///
    /// `scratch` must be large enough for the largest pending item.
    pub async fn drain_all<S: NorFlash, C: CacheImpl>(
        &self,
        storage: &mut QueueStorage<S, C>,
        scratch: &mut [u8],
        allow_overwrite: bool,
    ) -> Result<(), Error<S::Error>> {
        while self.drain_one(storage, scratch, allow_overwrite).await? {}
        Ok(())
    }

    /// Wait for the signal, then drain all ring items to flash.
    ///
    /// This is the recommended drain-task body:
    /// ```ignore
    /// loop {
    ///     ring.wait_and_drain_all(&mut storage, &mut scratch, false).await.unwrap();
    /// }
    /// ```
    pub async fn wait_and_drain_all<S: NorFlash, C: CacheImpl>(
        &self,
        storage: &mut QueueStorage<S, C>,
        scratch: &mut [u8],
        allow_overwrite: bool,
    ) -> Result<(), Error<S::Error>> {
        self.wait().await;
        self.drain_all(storage, scratch, allow_overwrite).await
    }

    /// Pop the oldest item (drains ring to flash first to preserve ordering).
    pub async fn pop<'d, S: MultiwriteNorFlash, C: CacheImpl>(
        &self,
        storage: &mut QueueStorage<S, C>,
        data_buffer: &'d mut [u8],
        allow_overwrite: bool,
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
        if self.ram_pending_count() > 0 {
            self.drain_all(storage, data_buffer, allow_overwrite)
                .await?;
        }
        storage.pop(data_buffer).await
    }

    /// Peek at the oldest item without removing it (drains ring to flash first).
    pub async fn peek<'d, S: MultiwriteNorFlash, C: CacheImpl>(
        &self,
        storage: &mut QueueStorage<S, C>,
        data_buffer: &'d mut [u8],
        allow_overwrite: bool,
    ) -> Result<Option<&'d mut [u8]>, Error<S::Error>> {
        if self.ram_pending_count() > 0 {
            self.drain_all(storage, data_buffer, allow_overwrite)
                .await?;
        }
        storage.peek(data_buffer).await
    }

    // ── Introspection ─────────────────────────────────────────────────────────

    /// Total capacity of the ring in bytes (including 2-byte per-item length prefixes).
    pub const fn ram_capacity_bytes() -> usize {
        N
    }

    /// Free bytes remaining in the ring.
    pub fn ram_free_bytes(&self) -> usize {
        self.ring.lock(|r| N - r.borrow().bytes_used())
    }

    /// Number of items currently buffered in the ring.
    pub fn ram_pending_count(&self) -> usize {
        self.ring.lock(|r| r.borrow().len())
    }

    /// Byte length of the oldest item in the ring, or `None` if the ring is empty.
    pub fn oldest_ram_item_len(&self) -> Option<usize> {
        self.ring.lock(|r| r.borrow().oldest_len())
    }
}

#[cfg(feature = "shared-ram-ring")]
impl<const N: usize> Default for SharedRamRing<N> {
    fn default() -> Self {
        Self::new()
    }
}

// ── Unit tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_peek_discard() {
        let mut ring: RamRing<64> = RamRing::new();
        assert!(ring.is_empty());

        ring.push(b"hello").unwrap();
        ring.push(b"world").unwrap();
        assert_eq!(ring.len(), 2);
        assert_eq!(ring.oldest_len(), Some(5));

        let mut buf = [0u8; 32];
        assert_eq!(ring.peek_into(&mut buf), Some(b"hello".as_ref()));
        assert_eq!(ring.len(), 2); // peek does not consume

        ring.discard_oldest();
        assert_eq!(ring.len(), 1);
        assert_eq!(ring.peek_into(&mut buf), Some(b"world".as_ref()));

        ring.discard_oldest();
        assert!(ring.is_empty());
        assert_eq!(ring.peek_into(&mut buf), None);
    }

    #[test]
    fn wrap_around() {
        // Use a tight buffer: 2 items of 3 bytes each = 2*(2+3)=10 bytes
        let mut ring: RamRing<10> = RamRing::new();
        ring.push(b"abc").unwrap();
        ring.push(b"def").unwrap();
        // Full — no room for another
        assert!(ring.push(b"x").is_err());

        let mut buf = [0u8; 8];
        ring.discard_oldest();
        ring.push(b"ghi").unwrap(); // wraps around
        assert_eq!(ring.peek_into(&mut buf), Some(b"def".as_ref()));
        ring.discard_oldest();
        assert_eq!(ring.peek_into(&mut buf), Some(b"ghi".as_ref()));
    }

    #[test]
    fn push_overwriting_evicts_oldest() {
        // 10-byte ring fits exactly 2 items of 3 bytes (2*(2+3)=10)
        let mut ring: RamRing<10> = RamRing::new();
        ring.push(b"aaa").unwrap();
        ring.push(b"bbb").unwrap();

        // Overwriting push evicts "aaa" to make room for "ccc"
        ring.push_overwriting(b"ccc").unwrap();
        assert_eq!(ring.len(), 2);

        let mut buf = [0u8; 8];
        assert_eq!(ring.peek_into(&mut buf), Some(b"bbb".as_ref()));
        ring.discard_oldest();
        assert_eq!(ring.peek_into(&mut buf), Some(b"ccc".as_ref()));
    }

    // ── Integration tests (require mock flash via _test feature) ─────────────

    #[cfg(feature = "_test")]
    mod integration {
        use super::*;
        use crate::cache::NoCache;
        use crate::mock_flash::MockFlashBase;
        use crate::queue::{QueueConfig, QueueStorage};
        use futures::executor::block_on;

        // 4 pages × 64 words × 4 bytes/word = 1 KiB flash
        type MockFlash = MockFlashBase<4, 4, 64>;

        fn make_storage() -> QueueStorage<MockFlash, NoCache> {
            let flash = MockFlash::new(crate::mock_flash::WriteCountCheck::Twice, None, true);
            let config = QueueConfig::new(MockFlash::FULL_FLASH_RANGE);
            QueueStorage::new(flash, config, NoCache::new())
        }

        fn make_queue() -> BufferedQueue<MockFlash, NoCache, 256> {
            BufferedQueue::new(make_storage())
        }

        #[test]
        fn enqueue_drain_pop() {
            block_on(async {
                let mut queue = make_queue();
                let mut scratch = [0u8; 64];
                let mut out = [0u8; 64];

                // Enqueue two items into RAM — no flash I/O yet.
                queue.enqueue(b"hello", OverflowPolicy::Err).unwrap();
                queue.enqueue(b"world", OverflowPolicy::Err).unwrap();
                assert_eq!(queue.ram_pending_count(), 2);

                // Drain RAM → flash.
                queue.drain_all(&mut scratch, false).await.unwrap();
                assert_eq!(queue.ram_pending_count(), 0);

                // Pop from flash in FIFO order.
                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"hello");

                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"world");

                assert!(queue.pop(&mut out).await.unwrap().is_none());
            });
        }

        #[test]
        fn pop_reads_flash_before_ram() {
            block_on(async {
                // Push "first" directly to flash, then wrap in a BufferedQueue with "second" in RAM.
                // The mock flash requires write buffers aligned to BYTES_PER_WORD = 4 bytes.
                let mut storage = make_storage();
                let mut aligned = [0u8; 8];
                aligned[..5].copy_from_slice(b"first");
                storage.push(&aligned[..5], false).await.unwrap();

                let mut queue: BufferedQueue<MockFlash, NoCache, 256> =
                    BufferedQueue::new(storage);
                let mut out = [0u8; 64];

                // Buffer "second" in RAM only.
                queue.enqueue(b"second", OverflowPolicy::Err).unwrap();

                // pop returns flash items (older) before RAM items.
                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"first");

                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"second");

                assert!(queue.pop(&mut out).await.unwrap().is_none());
            });
        }

        #[test]
        fn overflow_policy_err() {
            // 16-byte ring: each item costs 2 (prefix) + data.len() bytes.
            // 3 items of 4 bytes = 3*6 = 18 bytes — won't all fit.
            let flash = MockFlash::new(crate::mock_flash::WriteCountCheck::Twice, None, true);
            let config = QueueConfig::new(MockFlash::FULL_FLASH_RANGE);
            let storage = QueueStorage::new(flash, config, NoCache::new());
            let mut queue: BufferedQueue<MockFlash, NoCache, 16> = BufferedQueue::new(storage);

            queue.enqueue(b"aaaa", OverflowPolicy::Err).unwrap(); // 6 bytes used
            queue.enqueue(b"bbbb", OverflowPolicy::Err).unwrap(); // 12 bytes used
            assert!(queue.enqueue(b"cccc", OverflowPolicy::Err).is_err()); // 18 > 16
        }

        #[test]
        fn overflow_policy_discard_oldest() {
            let flash = MockFlash::new(crate::mock_flash::WriteCountCheck::Twice, None, true);
            let config = QueueConfig::new(MockFlash::FULL_FLASH_RANGE);
            let storage = QueueStorage::new(flash, config, NoCache::new());
            let mut queue: BufferedQueue<MockFlash, NoCache, 16> = BufferedQueue::new(storage);

            queue.enqueue(b"aaaa", OverflowPolicy::Err).unwrap();
            queue.enqueue(b"bbbb", OverflowPolicy::Err).unwrap();
            // "aaaa" is evicted to make room for "cccc"
            queue
                .enqueue(b"cccc", OverflowPolicy::DiscardOldest)
                .unwrap();

            assert_eq!(queue.ram_pending_count(), 2);

            // Drain to flash and pop to verify FIFO order with "aaaa" evicted.
            block_on(async {
                let mut out = [0u8; 64];
                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"bbbb");
                let data = queue.pop(&mut out).await.unwrap().unwrap();
                assert_eq!(data, b"cccc");
            });
        }

        #[test]
        fn capacity_helpers() {
            let queue = make_queue();
            assert_eq!(
                BufferedQueue::<MockFlash, NoCache, 256>::ram_capacity_bytes(),
                256
            );
            assert_eq!(queue.ram_free_bytes(), 256);
            assert_eq!(queue.ram_bytes_used(), 0);
        }
    }
}
