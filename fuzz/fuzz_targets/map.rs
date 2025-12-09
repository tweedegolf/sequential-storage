#![no_main]

use futures::executor::block_on;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rand::SeedableRng;
use sequential_storage::{
    cache::{
        HeapKeyPointerCache, HeapPagePointerCache, HeapPageStateCache, KeyCacheImpl,
        KeyPointerCache, NoCache, PagePointerCache, PageStateCache,
    },
    map::MapConfig,
    mock_flash::{MockFlashBase, MockFlashError, WriteCountCheck},
    Error, Storage,
};
use std::{collections::HashMap, fmt::Debug};

const PAGES: usize = 4;
const WORD_SIZE: usize = 4;
const WORDS_PER_PAGE: usize = 256;

fuzz_target!(|data: Input| match data.cache_type {
    CacheType::NoCache => fuzz(data, NoCache::new()),
    CacheType::PageStateCache => fuzz(data, PageStateCache::<PAGES>::new()),
    CacheType::PagePointerCache => fuzz(data, PagePointerCache::<PAGES>::new()),
    CacheType::KeyPointerCache => fuzz(data, KeyPointerCache::<PAGES, u8, 64>::new()),
    CacheType::HeapPageStateCache => fuzz(data, HeapPageStateCache::new(PAGES)),
    CacheType::HeapPagePointerCache => fuzz(data, HeapPagePointerCache::new(PAGES)),
    CacheType::HeapKeyPointerCache => fuzz(data, HeapKeyPointerCache::<u8>::new(PAGES, 64)),
});

#[derive(Arbitrary, Debug, Clone)]
struct Input {
    seed: u64,
    fuel: u16,
    ops: Vec<Op>,
    cache_type: CacheType,
}

#[derive(Arbitrary, Debug, Clone)]
enum Op {
    Store(StoreOp),
    Fetch(u8),
    Remove(u8),
    RemoveAll,
    Iter,
}

#[derive(Arbitrary, Debug, Clone)]
struct StoreOp {
    key: u8,
    value_len: u8,
}

impl StoreOp {
    fn into_test_item(self, rng: &mut impl rand::Rng) -> (u8, Vec<u8>) {
        (
            self.key,
            (0..(self.value_len % 8) as usize)
                .map(|_| rng.random())
                .collect(),
        )
    }
}

#[derive(Arbitrary, Debug, Clone)]
enum CacheType {
    NoCache,
    PageStateCache,
    PagePointerCache,
    KeyPointerCache,
    HeapPageStateCache,
    HeapPagePointerCache,
    HeapKeyPointerCache,
}

fn fuzz(ops: Input, cache: impl KeyCacheImpl<u8> + Debug) {
    let flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(
        if ops
            .ops
            .iter()
            .any(|op| matches!(op, Op::Remove(_) | Op::RemoveAll))
        {
            WriteCountCheck::Twice
        } else {
            WriteCountCheck::OnceOnly
        },
        Some(ops.fuel as u32),
        true,
    );

    let mut storage = Storage::new_map(flash, const { MapConfig::new(0x000..0x1000) }, cache);

    let mut map = HashMap::new();
    #[repr(align(4))]
    struct AlignedBuf([u8; 260]);
    let mut buf = AlignedBuf([0; 260]); // Max length of test item serialized, rounded up to align to flash word.

    let mut rng = rand_pcg::Pcg32::seed_from_u64(ops.seed);

    #[cfg(fuzzing_repro)]
    eprintln!("\n=== START ===\n");

    for op in ops.ops.into_iter() {
        #[cfg(fuzzing_repro)]
        eprintln!("{}", block_on(flash.print_items()));
        #[cfg(fuzzing_repro)]
        eprintln!("{:?}", cache);
        #[cfg(fuzzing_repro)]
        eprintln!("=== OP: {op:?} ===");

        match op.clone() {
            Op::Store(op) => {
                let (key, value) = op.into_test_item(&mut rng);
                match block_on(storage.store_item(&mut buf.0, &key, &value.as_slice())) {
                    Ok(_) => {
                        map.insert(key, value);
                    }
                    Err(Error::FullStorage) => {}
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(_, _),
                        backtrace: _backtrace,
                    }) => {
                        match block_on(storage.fetch_item::<&[u8]>(&mut buf.0, &key)) {
                            Ok(Some(check_item)) if check_item == value => {
                                #[cfg(fuzzing_repro)]
                                eprintln!("Early shutoff when storing key: {key}, value: {value:?}! (but it still stored fully). Originated from:\n{_backtrace:#}");
                                // Even though we got a shutoff, it still managed to store well
                                map.insert(key, value);
                            }
                            _ => {
                                // Could not fetch the item we stored...
                                #[cfg(fuzzing_repro)]
                                eprintln!("Early shutoff when storing key: {key}, value: {value:?}! Originated from:\n{_backtrace:#}");
                            }
                        }
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!("Corrupted when storing! Originated from:\n{_backtrace:#}");
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
            Op::Fetch(key) => match block_on(storage.fetch_item::<&[u8]>(&mut buf.0, &key)) {
                Ok(Some(fetch_result)) => {
                    let map_value = map
                        .get(&key)
                        .unwrap_or_else(|| panic!("Map doesn't contain: {fetch_result:?}"));
                    assert_eq!(map_value, &fetch_result, "Mismatching values");
                }
                Ok(None) => {
                    assert_eq!(None, map.get(&key));
                }
                Err(Error::Storage {
                    value: MockFlashError::EarlyShutoff(_, _),
                    backtrace: _backtrace,
                }) => {
                    #[cfg(fuzzing_repro)]
                    eprintln!("Early shutoff when fetching! Originated from:\n{_backtrace:#}");
                }
                Err(Error::Corrupted {
                    backtrace: _backtrace,
                }) => {
                    #[cfg(fuzzing_repro)]
                    eprintln!("Corrupted when fetching! Originated from:\n{_backtrace:#}");
                    panic!("Corrupted!");
                }
                Err(e) => panic!("{e:#?}"),
            },
            Op::Remove(key) => {
                match block_on(storage.remove_item(&mut buf.0, &key)) {
                    Ok(()) => {
                        map.remove(&key);
                    }
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(_, _),
                        backtrace: _backtrace,
                    }) => {
                        // Check if the item is still there. It might or it might not and either is fine
                        match block_on(storage.fetch_item::<&[u8]>(&mut buf.0, &key)) {
                            Ok(Some(_)) => {
                                #[cfg(fuzzing_repro)]
                                eprintln!("Early shutoff when removing item {key}! Originated from:\n{_backtrace:#}");
                            }
                            _ => {
                                // Could not fetch the item we stored...
                                #[cfg(fuzzing_repro)]
                                eprintln!("Early shutoff when removing item {key}! (but it still removed fully). Originated from:\n{_backtrace:#}");
                                // Even though we got a shutoff, it still managed to store well
                                map.remove(&key);
                            }
                        }
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!("Corrupted when removing! Originated from:\n{_backtrace:#}");
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
            Op::RemoveAll => {
                match block_on(storage.remove_all_items(&mut buf.0)) {
                    Ok(()) => {
                        map.clear();
                    }
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(_, _),
                        backtrace: _backtrace,
                    }) => {
                        for key in map.keys().copied().collect::<Vec<_>>() {
                            // Check if the item is still there. It might or it might not and either is fine
                            match block_on(storage.fetch_item::<&[u8]>(&mut buf.0, &key)) {
                                Ok(Some(_)) => {
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when removing item {key}! Originated from:\n{_backtrace:#}");
                                }
                                _ => {
                                    // Could not fetch the item we stored...
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when removing item {key}! (but it still removed fully). Originated from:\n{_backtrace:#}");
                                    // Even though we got a shutoff, it still managed to store well
                                    map.remove(&key);
                                }
                            }
                        }
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!("Corrupted when removing! Originated from:\n{_backtrace:#}");
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("{e:?}"),
                }
            }
            Op::Iter => {
                let mut iter = block_on(storage.fetch_all_items(&mut buf.0)).unwrap();

                let mut seen_items = HashMap::new();

                loop {
                    match block_on(iter.next::<&[u8]>(&mut buf.0)) {
                        Ok(None) => break,
                        Ok(Some((key, val))) => {
                            seen_items.insert(key, val.to_vec());
                        }
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!("Corrupted when removing! Originated from:\n{_backtrace:#}");
                            panic!("Corrupted!");
                        }
                        Err(e) => panic!("{e:?}"),
                    }
                }

                assert_eq!(seen_items, map);
            }
        }
    }
}
