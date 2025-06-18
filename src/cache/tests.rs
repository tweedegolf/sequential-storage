#[cfg(test)]
mod queue_tests {
    use core::ops::Range;

    use crate::{
        AlignedBuf,
        cache::{CacheImpl, NoCache, PagePointerCache, PageStateCache},
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
        queue::{peek, pop, push},
    };

    use futures_test::test;

    const NUM_PAGES: usize = 4;
    const LOOP_COUNT: usize = 2000;

    #[test]
    async fn no_cache() {
        assert_eq!(
            run_test(&mut NoCache::new()).await,
            FlashStatsResult {
                erases: 149,
                reads: 165009,
                writes: 6299,
                bytes_read: 651212,
                bytes_written: 53299
            }
        );
    }

    #[test]
    async fn page_state_cache() {
        assert_eq!(
            run_test(&mut PageStateCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 149,
                reads: 68037,
                writes: 6299,
                bytes_read: 554240,
                bytes_written: 53299
            }
        );
    }

    #[test]
    async fn page_pointer_cache() {
        assert_eq!(
            run_test(&mut PagePointerCache::<NUM_PAGES>::new()).await,
            FlashStatsResult {
                erases: 149,
                reads: 9959,
                writes: 6299,
                bytes_read: 89616,
                bytes_written: 53299
            }
        );
    }

    async fn run_test(cache: &mut impl CacheImpl) -> FlashStatsResult {
        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None, true);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 1024]);

        let start_snapshot = flash.stats_snapshot();

        for i in 0..LOOP_COUNT {
            println!("{i}");
            let data = vec![i as u8; i % 20 + 1];

            println!("PUSH");
            push(&mut flash, FLASH_RANGE, cache, &data, true)
                .await
                .unwrap();
            assert_eq!(
                peek(&mut flash, FLASH_RANGE, cache, &mut data_buffer)
                    .await
                    .unwrap()
                    .unwrap(),
                &data,
                "At {i}"
            );
            println!("POP");
            assert_eq!(
                pop(&mut flash, FLASH_RANGE, cache, &mut data_buffer)
                    .await
                    .unwrap()
                    .unwrap(),
                &data,
                "At {i}"
            );
            println!("PEEK");
            assert_eq!(
                peek(&mut flash, FLASH_RANGE, cache, &mut data_buffer)
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
        AlignedBuf,
        cache::{KeyCacheImpl, KeyPointerCache, NoCache, PagePointerCache, PageStateCache},
        map::{fetch_item, store_item},
        mock_flash::{self, FlashStatsResult, WriteCountCheck},
    };

    use futures_test::test;

    const NUM_PAGES: usize = 4;

    #[test]
    async fn no_cache() {
        assert_eq!(
            run_test(&mut NoCache::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 233786,
                writes: 5201,
                bytes_read: 1837101,
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
                reads: 181162,
                writes: 5201,
                bytes_read: 1784477,
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
                reads: 163273,
                writes: 5201,
                bytes_read: 1641365,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn key_pointer_cache_half() {
        assert_eq!(
            run_test(&mut KeyPointerCache::<NUM_PAGES, u16, 12>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 131503,
                writes: 5201,
                bytes_read: 1299275,
                bytes_written: 50401
            }
        );
    }

    #[test]
    async fn key_pointer_cache_full() {
        assert_eq!(
            run_test(&mut KeyPointerCache::<NUM_PAGES, u16, 24>::new()).await,
            FlashStatsResult {
                erases: 198,
                reads: 14510,
                writes: 5201,
                bytes_read: 150592,
                bytes_written: 50401
            }
        );
    }

    async fn run_test(cache: &mut impl KeyCacheImpl<u16>) -> FlashStatsResult {
        let mut flash =
            mock_flash::MockFlashBase::<NUM_PAGES, 1, 256>::new(WriteCountCheck::Twice, None, true);
        const FLASH_RANGE: Range<u32> = 0x00..0x400;
        let mut data_buffer = AlignedBuf([0; 128]);

        const LENGHT_PER_KEY: [usize; 24] = [
            11, 13, 6, 13, 13, 10, 2, 3, 5, 36, 1, 65, 4, 6, 1, 15, 10, 7, 3, 15, 9, 3, 4, 5,
        ];

        let start_snapshot = flash.stats_snapshot();

        for _ in 0..100 {
            const WRITE_ORDER: [usize; 24] = [
                15, 0, 4, 22, 18, 11, 19, 8, 14, 23, 5, 1, 16, 10, 6, 12, 20, 17, 3, 9, 7, 13, 21,
                2,
            ];

            for i in WRITE_ORDER {
                store_item(
                    &mut flash,
                    FLASH_RANGE,
                    cache,
                    &mut data_buffer,
                    &(i as u16),
                    &vec![i as u8; LENGHT_PER_KEY[i]].as_slice(),
                )
                .await
                .unwrap();
            }

            const READ_ORDER: [usize; 24] = [
                8, 22, 21, 11, 16, 23, 13, 15, 19, 7, 6, 2, 12, 1, 17, 4, 20, 14, 10, 5, 9, 3, 18,
                0,
            ];

            for i in READ_ORDER {
                let item = fetch_item::<u16, &[u8], _>(
                    &mut flash,
                    FLASH_RANGE,
                    cache,
                    &mut data_buffer,
                    &(i as u16),
                )
                .await
                .unwrap()
                .unwrap();

                // println!("Fetched {item:?}");

                assert_eq!(item, vec![i as u8; LENGHT_PER_KEY[i]]);
            }
        }

        start_snapshot.compare_to(flash.stats_snapshot())
    }
}
