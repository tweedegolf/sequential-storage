#![no_main]

use futures::executor::block_on;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rand::{Rng, SeedableRng};
use sequential_storage::{
    cache::{
        CacheImpl, HeapPagePointerCache, HeapPageStateCache, NoCache, PagePointerCache,
        PageStateCache,
    },
    mock_flash::{MockFlashBase, MockFlashError, Operation, WriteCountCheck},
    Error,
};
use std::{collections::VecDeque, fmt::Debug, ops::Range};
const MAX_VALUE_SIZE: usize = u8::MAX as usize;

const PAGES: usize = 4;
const WORD_SIZE: usize = 4;
const WORDS_PER_PAGE: usize = 256;

fuzz_target!(|data: Input| match data.cache_type {
    CacheType::NoCache => fuzz(data, NoCache::new()),
    CacheType::PageStateCache => fuzz(data, PageStateCache::<PAGES>::new()),
    CacheType::PagePointerCache => fuzz(data, PagePointerCache::<PAGES>::new()),
    CacheType::HeapPageStateCache => fuzz(data, HeapPageStateCache::new(PAGES)),
    CacheType::HeapPagePointerCache => fuzz(data, HeapPagePointerCache::new(PAGES)),
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
    Push(PushOp),
    Iterate(Vec<bool>),
    Peek,
    Pop,
}

#[derive(Arbitrary, Debug, Clone)]
struct PushOp {
    value_len: u8,
}

#[derive(Arbitrary, Debug, Clone)]
enum CacheType {
    NoCache,
    PageStateCache,
    PagePointerCache,
    HeapPageStateCache,
    HeapPagePointerCache,
}

#[repr(align(4))]
struct AlignedBuf([u8; MAX_VALUE_SIZE + 1]);

fn fuzz(ops: Input, mut cache: impl CacheImpl + Debug) {
    let mut flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(
        WriteCountCheck::Twice,
        Some(ops.fuel as u32),
        true,
    );
    const FLASH_RANGE: Range<u32> = 0x000..0x1000;

    let mut order = VecDeque::new();
    let mut buf = AlignedBuf([0; MAX_VALUE_SIZE + 1]);

    let mut rng = rand_pcg::Pcg32::seed_from_u64(ops.seed);

    #[cfg(fuzzing_repro)]
    eprintln!("\n=== START ===\n");

    for mut op in ops.ops.into_iter() {
        #[cfg(fuzzing_repro)]
        eprintln!("{}", block_on(flash.print_items()));
        #[cfg(fuzzing_repro)]
        eprintln!("{:?}", cache);
        #[cfg(fuzzing_repro)]
        eprintln!("\n=== OP: {op:?} ===\n");

        match &mut op {
            Op::Push(op) => {
                let val: Vec<u8> = (0..op.value_len as usize % 16)
                    .map(|_| rng.random())
                    .collect();

                let max_fit = match block_on(sequential_storage::queue::find_max_fit(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                )) {
                    Ok(val) => val,
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!("Corrupted when finding max! Originated from:\n{_backtrace:#}");
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("Error while finding max fit: {e:?}"),
                };

                buf.0[..val.len()].copy_from_slice(&val);
                match block_on(sequential_storage::queue::push(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                    &buf.0[..val.len()],
                    false,
                )) {
                    Ok(_) => {
                        if let Some(max_fit) = max_fit {
                            if val.len() > max_fit as usize {
                                panic!("Pushing succeeded while value was bigger than max fit");
                            }
                        } else {
                            panic!("Pushing succeeded while there was no fit");
                        }

                        order.push_back(val);
                    }
                    Err(Error::FullStorage) => {
                        if let Some(max_fit) = max_fit {
                            if val.len() <= max_fit as usize {
                                panic!("Got a wrong full storage");
                            }
                        }
                    }
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(address, _),
                        backtrace: _backtrace,
                    }) => {
                        // We need to check if it managed to write
                        if let Some(true) = block_on(flash.get_item_presence(address)) {
                            #[cfg(fuzzing_repro)]
                            eprintln!("Early shutoff when pushing {val:?}! (but it still stored fully). Originated from:\n{_backtrace:#}");
                            order.push_back(val);
                        } else {
                            #[cfg(fuzzing_repro)]
                            eprintln!("Early shutoff when pushing {val:?}! Originated from:\n{_backtrace:#}");
                        }
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!("Corrupted when pushing! Originated from:\n{_backtrace:#}");
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("Error pushing to queue: {e:?}"),
                }
            }
            Op::Pop => {
                match block_on(sequential_storage::queue::pop(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                    &mut buf.0,
                )) {
                    Ok(value) => {
                        assert_eq!(
                            value,
                            order
                                .pop_front()
                                .as_mut()
                                .map(|target| target.as_mut_slice())
                        );
                    }
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(address, operation),
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!(
                            "Early shutoff when popping (single)! Originated from:\n{_backtrace:#}"
                        );

                        if operation != Operation::Erase {
                            if !matches!(block_on(flash.get_item_presence(address)), Some(true)) {
                                // The item is no longer readable here
                                order.pop_front();
                            }
                        }
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!(
                            "Corrupted when popping single! Originated from:\n{_backtrace:#}"
                        );
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                }
            }
            Op::Peek => {
                match block_on(sequential_storage::queue::peek(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                    &mut buf.0,
                )) {
                    Ok(value) => {
                        assert_eq!(
                            value.map(|b| &b[..]),
                            order.front().as_ref().map(|target| target.as_slice())
                        );
                    }
                    Err(Error::Storage {
                        value: MockFlashError::EarlyShutoff(_, Operation::Erase),
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!(
                                "Early shutoff when getting next iterator entry! Originated from:\n{_backtrace:#}"
                            );

                        break;
                    }
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!(
                            "Corrupted when peeking single! Originated from:\n{_backtrace:#}"
                        );
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                }
            }
            Op::Iterate(pop_sequence) => {
                let mut iterator = match block_on(sequential_storage::queue::iter(
                    &mut flash,
                    FLASH_RANGE,
                    &mut cache,
                )) {
                    Ok(val) => val,
                    Err(Error::Corrupted {
                        backtrace: _backtrace,
                    }) => {
                        #[cfg(fuzzing_repro)]
                        eprintln!(
                            "Corrupted when creating iterator! Originated from:\n{_backtrace:#}"
                        );
                        panic!("Corrupted!");
                    }
                    Err(e) => panic!("Error while creating iterator: {e:?}"),
                };

                let mut popped_items = 0;
                for (i, do_pop) in pop_sequence.iter().enumerate() {
                    match block_on(iterator.next(&mut buf.0)) {
                        Ok(Some(value)) => {
                            assert_eq!(
                                &*value,
                                order.get(i as usize - popped_items).unwrap().as_slice()
                            );

                            if *do_pop {
                                #[cfg(fuzzing_repro)]
                                eprintln!("Popping item at address: {}", value.address());

                                let popped = block_on(value.pop());

                                match popped {
                                    Ok(value) => {
                                        assert_eq!(
                                            value,
                                            order
                                                .get(i as usize - popped_items)
                                                .unwrap()
                                                .as_slice()
                                        );

                                        order.remove(i - popped_items).unwrap();
                                        popped_items += 1;
                                    }
                                    Err(Error::Corrupted {
                                        backtrace: _backtrace,
                                    }) => {
                                        #[cfg(fuzzing_repro)]
                                        eprintln!(
                                            "Corrupted when popping interator entry! Originated from:\n{_backtrace:#}"
                                        );
                                        panic!("Corrupted!");
                                    }
                                    Err(Error::Storage {
                                        value: MockFlashError::EarlyShutoff(address, operation),
                                        backtrace: _backtrace,
                                    }) => {
                                        #[cfg(fuzzing_repro)]
                                        eprintln!(
                                            "Early shutoff when popping iterator entry! Originated from:\n{_backtrace:#}"
                                        );

                                        if operation != Operation::Erase {
                                            if !matches!(
                                                block_on(flash.get_item_presence(address)),
                                                Some(true)
                                            ) {
                                                // The item is no longer readable here
                                                order.remove(i - popped_items).unwrap();
                                            }
                                        }

                                        break;
                                    }
                                    Err(e) => panic!("Error popping iterator entry: {e:?}"),
                                }
                            }
                        }
                        Ok(None) => {
                            assert_eq!(None, order.get(i as usize - popped_items));
                        }
                        Err(Error::Storage {
                            value: MockFlashError::EarlyShutoff(address, operation),
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "Early shutoff when getting next iterator entry! Originated from:\n{_backtrace:#}"
                            );

                            if operation != Operation::Erase {
                                if !matches!(block_on(flash.get_item_presence(address)), Some(true))
                                {
                                    // The item is no longer readable here
                                    order.remove(i - popped_items).unwrap();
                                }
                            }

                            break;
                        }
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "Corrupted when interating! Originated from:\n{_backtrace:#}"
                            );
                            panic!("Corrupted!");
                        }
                        Err(e) => panic!("Error iterating queue: {e:#?}"),
                    }
                }
            }
        }
    }
}
