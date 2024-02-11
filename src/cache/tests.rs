#[cfg(test)]
mod queue_tests {
    use core::ops::Range;

    use crate::{
        cache::{CacheImpl, NoCache, PagePointerCache, PageStateCache},
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
        queue::{peek, pop, push},
        AlignedBuf,
    };

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

    #[test]
    async fn page_pointer_cache() {
        assert_eq!(
            run_test(&mut PagePointerCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 146,
                reads: 211172,
                writes: 6299,
                bytes_read: 1699320,
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
        cache::{KeyCacheImpl, KeyPointerCache, NoCache, PagePointerCache, PageStateCache},
        map::{fetch_item, store_item, StorageItem},
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
        AlignedBuf,
    };

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
                reads: 171543,
                writes: 5201,
                bytes_read: 1718356,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn page_pointer_cache() {
        assert_eq!(
            run_test(&mut PagePointerCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 153667,
                writes: 5201,
                bytes_read: 1575348,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn key_pointer_cache_half() {
        assert_eq!(
            run_test(&mut KeyPointerCache::<NUM_PAGES, u8, 12>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 130523,
                writes: 5201,
                bytes_read: 1318479,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn key_pointer_cache_full() {
        assert_eq!(
            run_test(&mut KeyPointerCache::<NUM_PAGES, u8, 24>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 14506,
                writes: 5201,
                bytes_read: 150566,
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

    async fn run_test(mut cache: impl KeyCacheImpl<u8>) -> FlashStatsResult {
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
