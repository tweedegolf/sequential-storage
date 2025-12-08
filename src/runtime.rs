//! Implementation for sequential-storage [Runtime]

use core::marker::PhantomData;
use core::ops::Range;

use embedded_storage_async::nor_flash::NorFlash;

use crate::MAX_WORD_SIZE;
use crate::NorFlashExt;
use crate::cache::CacheImpl;

/// Map typestate object
pub struct Map<Key>(PhantomData<Key>);
/// Queue typestate object
pub struct Queue(PhantomData<()>);

/// Runtime data for sequential-storage
pub struct Runtime<'data, Cache: CacheImpl, Storage, Type> {
    pub(crate) flash_range: Range<u32>,
    pub(crate) cache: Cache,
    pub(crate) data_buffer: &'data mut [u8],
    _phantom: PhantomData<(Type, Storage)>,
}

impl<'data, Cache: CacheImpl, Storage: NorFlash, Key> Runtime<'data, Cache, Storage, Map<Key>> {
    /// Create a runtime for a map
    pub const fn new_map(
        flash_range: Range<u32>,
        cache: Cache,
        data_buffer: &'data mut [u8],
    ) -> Self {
        assert!(
            flash_range.start % Storage::ERASE_SIZE as u32 == 0,
            "Flash range start must be aligned to a sector"
        );
        assert!(
            flash_range.end % Storage::ERASE_SIZE as u32 == 0,
            "Flash range end must be aligned to a sector"
        );
        assert!(
            flash_range.end - flash_range.start >= Storage::ERASE_SIZE as u32 * 2,
            "Flash range must contain at least 2 sectors"
        );

        assert!(
            Storage::ERASE_SIZE
                >= Storage::WORD_SIZE * 2
                    + crate::item::ItemHeader::data_address::<Storage>(0) as usize,
            "A sector must be at least 2 words + 1 item header in size"
        );
        assert!(
            Storage::WORD_SIZE <= MAX_WORD_SIZE,
            "Word size must be smaller (or equal) to the max supported word size"
        );

        Self {
            flash_range,
            cache,
            data_buffer,
            _phantom: PhantomData,
        }
    }
}

impl<'data, Cache: CacheImpl, Storage: NorFlash> Runtime<'data, Cache, Storage, Queue> {
    /// Create a runtime for a queue
    pub const fn new_queue<S: NorFlash>(
        flash_range: Range<u32>,
        cache: Cache,
        data: &'data mut [u8],
    ) -> Self {
        assert!(
            flash_range.start % Storage::ERASE_SIZE as u32 == 0,
            "Flash range start must be aligned to a sector"
        );
        assert!(
            flash_range.end % Storage::ERASE_SIZE as u32 == 0,
            "Flash range end must be aligned to a sector"
        );

        assert!(
            Storage::ERASE_SIZE
                >= Storage::WORD_SIZE * 2
                    + crate::item::ItemHeader::data_address::<Storage>(0) as usize,
            "A sector must be at least 2 words + 1 item header in size"
        );
        assert!(
            Storage::WORD_SIZE <= MAX_WORD_SIZE,
            "Word size must be smaller (or equal) to the max supported word size"
        );

        Self {
            flash_range,
            cache,
            data_buffer: data,
            _phantom: PhantomData,
        }
    }
}

impl<'data, Cache: CacheImpl, Storage, Type> Runtime<'data, Cache, Storage, Type> {
    /// Free the runtime cache
    pub fn free(self) -> Cache {
        self.cache
    }

    /// Get the used flash range used by the runtime
    pub const fn flash_range(&self) -> &Range<u32> {
        &self.flash_range
    }
}
