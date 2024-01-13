use core::ops::Range;

use embedded_storage_async::nor_flash::NorFlash;

use crate::{calculate_page_address, Error, PageState, MAX_WORD_SIZE};

#[allow(private_bounds)]
pub trait Cache: StateQuery {}

impl<T: StateQuery> Cache for T {}

pub(crate) trait StateQuery {
    fn invalidate_cache_state(&mut self);
    fn mark_dirty(&mut self);
    fn unmark_dirty(&mut self);
    fn is_dirty(&self) -> bool;

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {}

    /// Get the state of the page located at the given index
    async fn get_page_state<S: NorFlash>(
        &mut self,
        flash: &mut S,
        flash_range: Range<u32>,
        page_index: usize,
    ) -> Result<PageState, Error<S::Error>> {
        let page_address = calculate_page_address::<S>(flash_range, page_index);
        /// We only care about the data in the first byte to aid shutdown/cancellation.
        /// But we also don't want it to be too too definitive because we want to survive the occasional bitflip.
        /// So only half of the byte needs to be zero.
        const HALF_MARKER_BITS: u32 = 4;

        let mut buffer = [0; MAX_WORD_SIZE];
        flash
            .read(page_address, &mut buffer[..S::READ_SIZE])
            .await
            .map_err(|e| Error::Storage {
                value: e,
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })?;
        let start_marked = buffer[..S::READ_SIZE]
            .iter()
            .map(|marker_byte| marker_byte.count_zeros())
            .sum::<u32>()
            >= HALF_MARKER_BITS;

        flash
            .read(
                page_address + (S::ERASE_SIZE - S::READ_SIZE) as u32,
                &mut buffer[..S::READ_SIZE],
            )
            .await
            .map_err(|e| Error::Storage {
                value: e,
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            })?;
        let end_marked = buffer[..S::READ_SIZE]
            .iter()
            .map(|marker_byte| marker_byte.count_zeros())
            .sum::<u32>()
            >= HALF_MARKER_BITS;

        match (start_marked, end_marked) {
            (true, true) => Ok(PageState::Closed),
            (true, false) => Ok(PageState::PartialOpen),
            // Probably an interrupted erase
            (false, true) => Err(Error::Corrupted {
                #[cfg(feature = "_test")]
                backtrace: std::backtrace::Backtrace::capture(),
            }),
            (false, false) => Ok(PageState::Open),
        }
    }
}

pub struct NoCache;

impl StateQuery for NoCache {
    fn invalidate_cache_state(&mut self) {}

    fn mark_dirty(&mut self) {}

    fn unmark_dirty(&mut self) {}

    fn is_dirty(&self) -> bool {
        false
    }
}

struct DirtyCache {
    dirty: bool,
}

impl StateQuery for DirtyCache {
    fn invalidate_cache_state(&mut self) {
        self.dirty = false;
    }

    fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    fn unmark_dirty(&mut self) {
        self.dirty = false;
    }

    fn is_dirty(&self) -> bool {
        self.dirty
    }
}

pub struct PageStateCache<const PAGE_COUNT: usize> {
    dirty_cache: DirtyCache,
    pages: [Option<PageState>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> PageStateCache<PAGE_COUNT> {
    pub const fn new() -> Self {
        Self {
            dirty_cache: DirtyCache { dirty: false },
            pages: [None; PAGE_COUNT],
        }
    }
}

impl<const PAGE_COUNT: usize> Default for PageStateCache<PAGE_COUNT> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_COUNT: usize> StateQuery for PageStateCache<PAGE_COUNT> {
    fn invalidate_cache_state(&mut self) {
        self.dirty_cache.invalidate_cache_state();
        self.pages = [None; PAGE_COUNT];
    }

    fn mark_dirty(&mut self) {
        self.dirty_cache.mark_dirty();
    }

    fn unmark_dirty(&mut self) {
        self.dirty_cache.unmark_dirty();
    }

    fn is_dirty(&self) -> bool {
        self.dirty_cache.is_dirty()
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.mark_dirty();
        self.pages[page_index] = Some(new_state);
    }

    async fn get_page_state<S: NorFlash>(
        &mut self,
        flash: &mut S,
        flash_range: Range<u32>,
        page_index: usize,
    ) -> Result<PageState, Error<S::Error>> {
        match self.pages[page_index] {
            Some(state) => Ok(state),
            None => {
                let state = NoCache
                    .get_page_state(flash, flash_range, page_index)
                    .await?;
                self.pages[page_index] = Some(state);
                Ok(state)
            }
        }
    }
}

#[cfg(test)]
mod queue_tests {
    use crate::{
        mock_flash::{self, WriteCountCheck},
        queue::{peek, pop, push},
        AlignedBuf,
    };

    use super::*;
    use futures_test::test;

    const NUM_PAGES: usize = 4;
    const LOOP_COUNT: usize = 2000;

    #[test]
    async fn no_cache() {
        assert_eq!(run_test(NoCache).await, (594934, 6299, 146));
    }

    #[test]
    async fn page_state_cache() {
        assert_eq!(
            run_test(PageStateCache::<NUM_PAGES>::new()).await,
            (308740, 6299, 146)
        );
    }

    async fn run_test(mut cache: impl Cache) -> (u32, u32, u32) {
        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 1024]);

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

        (flash.reads, flash.writes, flash.erases)
    }
}

#[cfg(test)]
mod map_tests {
    use crate::{
        map::{fetch_item, store_item, StorageItem},
        mock_flash::{self, WriteCountCheck},
        AlignedBuf,
    };

    use super::*;
    use futures_test::test;

    const NUM_PAGES: usize = 4;

    #[test]
    async fn no_cache() {
        assert_eq!(run_test(NoCache).await, (224161, 5201, 198));
    }

    #[test]
    async fn page_state_cache() {
        assert_eq!(
            run_test(PageStateCache::<NUM_PAGES>::new()).await,
            (171543, 5201, 198)
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

    async fn run_test(mut cache: impl Cache) -> (u32, u32, u32) {
        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 128]);

        const LENGHT_PER_KEY: [usize; 24] = [
            11, 13, 6, 13, 13, 10, 2, 3, 5, 36, 1, 65, 4, 6, 1, 15, 10, 7, 3, 15, 9, 3, 4, 5,
        ];

        for _ in 0..100 {
            for i in 0..24 {
                let item = MockStorageItem {
                    key: i as u8,
                    value: vec![i as u8; LENGHT_PER_KEY[i]],
                };

                store_item::<_, _>(&mut flash, FLASH_RANGE, &mut cache, &mut data_buffer, item)
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

        (flash.reads, flash.writes, flash.erases)
    }
}
