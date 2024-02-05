#![no_main]

use futures::executor::block_on;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use sequential_storage::{
    map::{MapError, StorageItem},
    mock_flash::{MockFlashBase, MockFlashError, WriteCountCheck},
};
use std::{collections::HashMap, ops::Range};

fuzz_target!(|data: Input| fuzz(data));

#[derive(Arbitrary, Debug, Clone)]
struct Input {
    seed: u64,
    fuel: u16,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug, Clone)]
enum Op {
    Store(StoreOp),
    Fetch(u8),
}

#[derive(Arbitrary, Debug, Clone)]
struct StoreOp {
    key: u8,
    value_len: u8,
}

impl StoreOp {
    fn into_test_item(self, rng: &mut impl rand::Rng) -> TestItem {
        TestItem {
            key: self.key,
            value: (0..(self.value_len % 8) as usize)
                .map(|_| rng.gen())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestItem {
    key: u8,
    value: Vec<u8>,
}

impl StorageItem for TestItem {
    type Key = u8;

    type Error = ();

    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
        if buffer.len() < 1 + self.value.len() {
            return Err(());
        }

        buffer[0] = self.key;
        buffer[1..][..self.value.len()].copy_from_slice(&self.value);

        Ok(1 + self.value.len())
    }

    fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        Ok(Self {
            key: buffer[0],
            value: buffer[1..].to_vec(),
        })
    }

    fn key(&self) -> Self::Key {
        self.key
    }

    fn deserialize_key_only(buffer: &[u8]) -> Result<Self::Key, Self::Error>
    where
        Self: Sized,
    {
        Ok(buffer[0])
    }
}

fn fuzz(ops: Input) {
    const PAGES: usize = 4;
    const WORD_SIZE: usize = 4;
    const WORDS_PER_PAGE: usize = 256;

    let mut flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(
        WriteCountCheck::OnceOnly,
        Some(ops.fuel as u32),
        true,
    );
    const FLASH_RANGE: Range<u32> = 0x000..0x1000;

    let mut cache = sequential_storage::cache::NoCache::new();

    let mut map = HashMap::new();
    #[repr(align(4))]
    struct AlignedBuf([u8; 260]);
    let mut buf = AlignedBuf([0; 260]); // Max length of test item serialized, rounded up to align to flash word.

    let mut rng = rand_pcg::Pcg32::seed_from_u64(ops.seed);

    #[cfg(fuzzing_repro)]
    eprintln!("\n=== START ===\n");

    for op in ops.ops.into_iter() {
        let mut retry = true;
        let mut corruption_repaired = false;

        while std::mem::replace(&mut retry, false) {
            #[cfg(fuzzing_repro)]
            eprintln!("{}", flash.print_items());
            #[cfg(fuzzing_repro)]
            eprintln!("=== OP: {op:?} ===");

            match op.clone() {
                Op::Store(op) => {
                    let item = op.into_test_item(&mut rng);
                    match block_on(sequential_storage::map::store_item(
                        &mut flash,
                        FLASH_RANGE,
                        &mut cache,
                        &mut buf.0,
                        &item,
                    )) {
                        Ok(_) => {
                            map.insert(item.key, item.value);
                        }
                        Err(MapError::FullStorage) => {}
                        Err(MapError::Storage {
                            value: MockFlashError::EarlyShutoff(_),
                            backtrace: _backtrace,
                        }) => {
                            match block_on(sequential_storage::map::fetch_item::<TestItem, _>(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                                &mut buf.0,
                                item.key,
                            )) {
                                Ok(Some(check_item))
                                    if check_item.key == item.key
                                        && check_item.value == item.value =>
                                {
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when storing {item:?}! (but it still stored fully). Originated from:\n{_backtrace:#}");
                                    // Even though we got a shutoff, it still managed to store well
                                    map.insert(item.key, item.value);
                                }
                                _ => {
                                    // Could not fetch the item we stored...
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when storing {item:?}! Originated from:\n{_backtrace:#}");
                                }
                            }
                        }
                        Err(MapError::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while storing! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            block_on(sequential_storage::map::try_repair::<TestItem, _>(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                                &mut buf.0,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("{e:?}"),
                    }
                }
                Op::Fetch(key) => {
                    match block_on(sequential_storage::map::fetch_item::<TestItem, _>(
                        &mut flash,
                        FLASH_RANGE,
                        &mut cache,
                        &mut buf.0,
                        key,
                    )) {
                        Ok(Some(fetch_result)) => {
                            let map_value = map
                                .get(&key)
                                .expect(&format!("Map doesn't contain: {fetch_result:?}"));
                            assert_eq!(key, fetch_result.key, "Mismatching keys");
                            assert_eq!(map_value, &fetch_result.value, "Mismatching values");
                        }
                        Ok(None) => {
                            assert_eq!(None, map.get(&key));
                        }
                        Err(MapError::Storage {
                            value: MockFlashError::EarlyShutoff(_),
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "Early shutoff when fetching! Originated from:\n{_backtrace:#}"
                            );
                        }
                        Err(MapError::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while fetching! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            block_on(sequential_storage::map::try_repair::<TestItem, _>(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                                &mut buf.0,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("{e:?}"),
                    }
                }
            }
        }
    }
}
