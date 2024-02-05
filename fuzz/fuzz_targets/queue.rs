#![no_main]

use futures::executor::block_on;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rand::{Rng, SeedableRng};
use sequential_storage::{
    mock_flash::{MockFlashBase, MockFlashError, WriteCountCheck},
    Error,
};
use std::{collections::VecDeque, ops::Range};
const MAX_VALUE_SIZE: usize = u8::MAX as usize;

fuzz_target!(|data: Input| fuzz(data));

#[derive(Arbitrary, Debug, Clone)]
struct Input {
    seed: u64,
    fuel: u16,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug, Clone)]
enum Op {
    Push(PushOp),
    PopMany(u8),
    PeekMany(u8),
    Peek,
    Pop,
}

#[derive(Arbitrary, Debug, Clone)]
struct PushOp {
    value_len: u8,
}

#[repr(align(4))]
struct AlignedBuf([u8; MAX_VALUE_SIZE + 1]);

fn fuzz(ops: Input) {
    const PAGES: usize = 4;
    const WORD_SIZE: usize = 4;
    const WORDS_PER_PAGE: usize = 256;

    let mut flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(
        WriteCountCheck::Twice,
        Some(ops.fuel as u32),
        true,
    );
    const FLASH_RANGE: Range<u32> = 0x000..0x1000;

    let mut cache = sequential_storage::NoCache::new();

    let mut order = VecDeque::new();
    let mut buf = AlignedBuf([0; MAX_VALUE_SIZE + 1]);

    let mut rng = rand_pcg::Pcg32::seed_from_u64(ops.seed);

    #[cfg(fuzzing_repro)]
    eprintln!("\n=== START ===\n");

    for mut op in ops.ops.into_iter() {
        let mut retry = true;
        let mut corruption_repaired = false;

        while std::mem::replace(&mut retry, false) {
            #[cfg(fuzzing_repro)]
            eprintln!("{}", flash.print_items());
            #[cfg(fuzzing_repro)]
            eprintln!("=== OP: {op:?} ===");

            match &mut op {
                Op::Push(op) => {
                    let val: Vec<u8> = (0..op.value_len as usize % 16).map(|_| rng.gen()).collect();

                    let max_fit = match block_on(sequential_storage::queue::find_max_fit(
                        &mut flash,
                        FLASH_RANGE,
                        &mut cache,
                    )) {
                        Ok(val) => val,
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                    "### Encountered curruption while finding max fit! Repairing now. Originated from:\n{_backtrace:#}"
                                );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                            continue;
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
                            value: MockFlashError::EarlyShutoff(address),
                            backtrace: _backtrace,
                        }) => {
                            // We need to check if it managed to write
                            if let Some(true) = flash.get_item_presence(address) {
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
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while pushing! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
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
                            value: MockFlashError::EarlyShutoff(address),
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "Early shutoff when popping (single)! Originated from:\n{_backtrace:#}"
                            );

                            if !matches!(flash.get_item_presence(address), Some(true)) {
                                // The item is no longer readable here
                                order.pop_front();
                            }
                        }
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while popping (single)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                    }
                }
                Op::PopMany(n) => {
                    let mut popper = match block_on(sequential_storage::queue::pop_many(
                        &mut flash,
                        FLASH_RANGE,
                        &mut cache,
                    )) {
                        Ok(val) => val,
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                        "### Encountered curruption while creating popper! Repairing now. Originated from:\n{_backtrace:#}"
                                    );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                            continue;
                        }
                        Err(e) => panic!("Error while creating popper: {e:?}"),
                    };

                    for i in 0..*n {
                        match block_on(popper.next(&mut buf.0)) {
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
                                value: MockFlashError::EarlyShutoff(address),
                                backtrace: _backtrace,
                            }) => {
                                #[cfg(fuzzing_repro)]
                                eprintln!(
                                    "Early shutoff when popping (many)! Originated from:\n{_backtrace:#}"
                                );

                                if !matches!(flash.get_item_presence(address), Some(true)) {
                                    // The item is no longer readable here
                                    order.pop_front();
                                }

                                retry = true;
                                *n -= i;
                                break;
                            }
                            Err(Error::Corrupted {
                                backtrace: _backtrace,
                            }) if !corruption_repaired => {
                                #[cfg(fuzzing_repro)]
                                eprintln!(
                                "### Encountered curruption while popping (many)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                                block_on(sequential_storage::queue::try_repair(
                                    &mut flash,
                                    FLASH_RANGE,
                                    &mut cache,
                                ))
                                .unwrap();
                                corruption_repaired = true;
                                retry = true;
                                *n -= i;
                                break;
                            }
                            Err(e) => panic!("Error popping (many) from queue: {e:?}"),
                        }
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
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while peeking (single)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                    }
                }
                Op::PeekMany(n) => {
                    let mut peeker = match block_on(sequential_storage::queue::peek_many(
                        &mut flash,
                        FLASH_RANGE,
                        &mut cache,
                    )) {
                        Ok(val) => val,
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                        "### Encountered curruption while creating peeker! Repairing now. Originated from:\n{_backtrace:#}"
                                    );

                            block_on(sequential_storage::queue::try_repair(
                                &mut flash,
                                FLASH_RANGE,
                                &mut cache,
                            ))
                            .unwrap();
                            corruption_repaired = true;
                            retry = true;
                            continue;
                        }
                        Err(e) => panic!("Error while creating peeker: {e:?}"),
                    };

                    for i in 0..*n {
                        match block_on(peeker.next(&mut buf.0)) {
                            Ok(value) => {
                                assert_eq!(
                                    value.map(|b| &b[..]),
                                    order
                                        .get(i as usize)
                                        .as_ref()
                                        .map(|target| target.as_slice())
                                );
                            }
                            Err(Error::Corrupted {
                                backtrace: _backtrace,
                            }) if !corruption_repaired => {
                                #[cfg(fuzzing_repro)]
                                eprintln!(
                                "### Encountered curruption while peeking (many)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                                block_on(sequential_storage::queue::try_repair(
                                    &mut flash,
                                    FLASH_RANGE,
                                    &mut cache,
                                ))
                                .unwrap();
                                corruption_repaired = true;
                                retry = true;
                                *n -= i;
                                break;
                            }
                            Err(e) => panic!("Error peeking (many) from queue: {e:?}"),
                        }
                    }
                }
            }
        }
    }
}
