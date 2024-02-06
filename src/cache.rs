//! Module implementing all things cache related

use crate::PageState;

/// Trait implemented by all cache types
#[allow(private_bounds)]
pub trait CacheImpl: PrivateCacheImpl {}

impl<T: CacheImpl> CacheImpl for &mut T {}

impl<PSC: PageStatesCache> CacheImpl for Cache<PSC> {}

pub(crate) trait PrivateCacheImpl {
    type PSC: PageStatesCache;

    fn inner(&mut self) -> &mut Cache<Self::PSC>;
}

impl<T: PrivateCacheImpl> PrivateCacheImpl for &mut T {
    type PSC = T::PSC;

    fn inner(&mut self) -> &mut Cache<Self::PSC> {
        T::inner(self)
    }
}

impl<PSC: PageStatesCache> PrivateCacheImpl for Cache<PSC> {
    type PSC = PSC;

    fn inner(&mut self) -> &mut Cache<Self::PSC> {
        self
    }
}

/// A cache object implementing no cache.
///
/// This type of cache doesn't have to be kept around and may be constructed on every api call.
/// You could simply pass `&mut NoCache::new()` every time.
pub struct NoCache(Cache<UncachedPageSates>);

impl NoCache {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self(Cache::new(UncachedPageSates))
    }
}

impl PrivateCacheImpl for NoCache {
    type PSC = UncachedPageSates;

    fn inner(&mut self) -> &mut Cache<Self::PSC> {
        &mut self.0
    }
}

impl CacheImpl for NoCache {}

/// A cache object that keeps track of the page states.
///
/// This cache has to be kept around and passed to *every* api call to the same memory region until the cache gets discarded.
///
/// Valid usecase:  
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:  
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
pub struct PageStateCache<const PAGE_COUNT: usize>(Cache<CachedPageStates<PAGE_COUNT>>);

impl<const PAGE_COUNT: usize> PageStateCache<PAGE_COUNT> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self(Cache::new(CachedPageStates::new()))
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PageStateCache<PAGE_COUNT> {
    type PSC = CachedPageStates<PAGE_COUNT>;

    fn inner(&mut self) -> &mut Cache<Self::PSC> {
        &mut self.0
    }
}

impl<const PAGE_COUNT: usize> CacheImpl for PageStateCache<PAGE_COUNT> {}

#[derive(Debug)]
pub(crate) struct Cache<PSC: PageStatesCache> {
    dirty: bool,
    page_states: PSC,
}

impl<PSC: PageStatesCache> Cache<PSC> {
    pub(crate) const fn new(page_states: PSC) -> Self {
        Self {
            dirty: false,
            page_states,
        }
    }

    pub(crate) fn is_dirty(&self) -> bool {
        self.dirty
    }

    pub(crate) fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    pub(crate) fn unmark_dirty(&mut self) {
        self.dirty = false;
    }

    pub(crate) fn invalidate_cache_state(&mut self) {
        self.dirty = false;
        self.page_states.invalidate_cache_state();
    }

    pub(crate) fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        self.page_states.get_page_state(page_index)
    }

    pub(crate) fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.mark_dirty();
        self.page_states.notice_page_state(page_index, new_state)
    }
}

pub(crate) trait PageStatesCache {
    fn get_page_state(&self, page_index: usize) -> Option<PageState>;
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

#[derive(Debug)]
pub(crate) struct CachedPageStates<const PAGE_COUNT: usize> {
    pages: [Option<PageState>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> CachedPageStates<PAGE_COUNT> {
    pub const fn new() -> Self {
        Self {
            pages: [None; PAGE_COUNT],
        }
    }
}

impl<const PAGE_COUNT: usize> PageStatesCache for CachedPageStates<PAGE_COUNT> {
    fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        self.pages[page_index]
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.pages[page_index] = Some(new_state);
    }

    fn invalidate_cache_state(&mut self) {
        *self = Self::new();
    }
}

#[derive(Debug, Default)]
pub(crate) struct UncachedPageSates;

impl PageStatesCache for UncachedPageSates {
    fn get_page_state(&self, _page_index: usize) -> Option<PageState> {
        None
    }

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {}

    fn invalidate_cache_state(&mut self) {}
}

#[cfg(test)]
mod queue_tests {
    use core::ops::Range;

    use crate::{
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
        queue::{peek, pop, push},
        AlignedBuf,
    };

    use super::*;
    use futures_test::test;

    const NUM_PAGES: usize = 4;
    const LOOP_COUNT: usize = 2000;

    #[test]
    async fn no_cache() {
        assert_eq!(
            run_test(&mut NoCache::new()).await,
            FlashStatsResult {
                erases: 146,
                reads: 594934,
                writes: 6299,
                bytes_read: 2766058,
                bytes_written: 53299
            }
        );
    }

    #[test]
    async fn page_state_cache() {
        assert_eq!(
            run_test(&mut PageStateCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 146,
                reads: 308740,
                writes: 6299,
                bytes_read: 2479864,
                bytes_written: 53299
            }
        );
    }

    async fn run_test(mut cache: impl CacheImpl) -> FlashStatsResult {
        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None, true);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 1024]);

        let start_snapshot = flash.stats_snapshot();

        for i in 0..LOOP_COUNT {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            println!("PUSH");
            push(&mut flash, FLASH_RANGE, &mut cache, &data, true)
                .await
                .unwrap();
            assert_eq!(
                &peek(&mut flash, FLASH_RANGE, &mut cache, &mut data_buffer)
                    .await
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            println!("POP");
            assert_eq!(
                &pop(&mut flash, FLASH_RANGE, &mut cache, &mut data_buffer)
                    .await
                    .unwrap()
                    .unwrap()[..],
                &data,
                "At {i}"
            );
            println!("PEEK");
            assert_eq!(
                peek(&mut flash, FLASH_RANGE, &mut cache, &mut data_buffer)
                    .await
                    .unwrap(),
                None,
                "At {i}"
            );
            println!("DONE");
        }

        start_snapshot.compare_to(flash.stats_snapshot())
    }
}

#[cfg(test)]
mod map_tests {
    use core::ops::Range;

    use crate::{
        map::{fetch_item, store_item, StorageItem},
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
        AlignedBuf,
    };

    use super::*;
    use futures_test::test;

    const NUM_PAGES: usize = 4;

    #[test]
    async fn no_cache() {
        assert_eq!(
            run_test(&mut NoCache::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 224161,
                writes: 5201,
                bytes_read: 1770974,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn page_state_cache() {
        assert_eq!(
            run_test(&mut PageStateCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 172831,
                writes: 5201,
                bytes_read: 1719644,
                bytes_written: 50401
            }
        );
    }

    #[derive(Debug, PartialEq, Eq)]
    struct MockStorageItem {
        key: u8,
        value: Vec<u8>,
    }

    #[derive(Debug, PartialEq, Eq)]
    enum MockStorageItemError {
        BufferTooSmall,
        InvalidKey,
        BufferTooBig,
    }

    impl StorageItem for MockStorageItem {
        type Key = u8;

        type Error = MockStorageItemError;

        fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
            if buffer.len() < 2 + self.value.len() {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            if self.value.len() > 255 {
                return Err(MockStorageItemError::BufferTooBig);
            }

            // The serialized value must not be all 0xFF
            if self.key == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            buffer[0] = self.key;
            buffer[1] = self.value.len() as u8;
            buffer[2..][..self.value.len()].copy_from_slice(&self.value);

            Ok(2 + self.value.len())
        }

        fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error>
        where
            Self: Sized,
        {
            if buffer.len() < 2 {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            if buffer[0] == 0xFF {
                return Err(MockStorageItemError::InvalidKey);
            }

            let len = buffer[1];

            if buffer.len() < 2 + len as usize {
                return Err(MockStorageItemError::BufferTooSmall);
            }

            Ok(Self {
                key: buffer[0],
                value: buffer[2..][..len as usize].to_vec(),
            })
        }

        fn key(&self) -> Self::Key {
            self.key
        }
    }

    async fn run_test(mut cache: impl CacheImpl) -> FlashStatsResult {
        let mut cache = cache.inner();

        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None, true);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 128]);

        const LENGHT_PER_KEY: [usize; 24] = [
            11, 13, 6, 13, 13, 10, 2, 3, 5, 36, 1, 65, 4, 6, 1, 15, 10, 7, 3, 15, 9, 3, 4, 5,
        ];

        let start_snapshot = flash.stats_snapshot();

        for _ in 0..100 {
            for i in 0..24 {
                let item = MockStorageItem {
                    key: i as u8,
                    value: vec![i as u8; LENGHT_PER_KEY[i]],
                };

                store_item::<_, _>(&mut flash, FLASH_RANGE, &mut cache, &mut data_buffer, &item)
                    .await
                    .unwrap();
            }

            for i in 0..24 {
                let item = fetch_item::<MockStorageItem, _>(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                    &mut data_buffer,
                    i as u8,
                )
                .await
                .unwrap()
                .unwrap();

                println!("Fetched {item:?}");

                assert_eq!(item.value, vec![i as u8; LENGHT_PER_KEY[i]]);
            }
        }

        start_snapshot.compare_to(flash.stats_snapshot())
    }
}
