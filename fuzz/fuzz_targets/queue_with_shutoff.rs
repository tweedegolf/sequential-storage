#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use rand::{Rng, SeedableRng};
use sequential_storage::{
    mock_flash::{MockFlashBase, MockFlashError},
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

fn fuzz(ops: Input) {
    const PAGES: usize = 4;
    const WORD_SIZE: usize = 4;
    const WORDS_PER_PAGE: usize = 256;

    // TODO: Turn on strict write count again
    let mut flash =
        MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(false, Some(ops.fuel as u32));
    const FLASH_RANGE: Range<u32> = 0x000..0x1000;

    let mut order = VecDeque::new();
    let mut buf = [0; MAX_VALUE_SIZE + 1];

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

                    let max_fit =
                        sequential_storage::queue::find_max_fit(&mut flash, FLASH_RANGE).unwrap();

                    match sequential_storage::queue::push(&mut flash, FLASH_RANGE, &val, false) {
                        Ok(_) => {
                            if let Some(max_fit) = max_fit {
                                if val.len() > max_fit {
                                    panic!("Pushing succeeded while value was bigger than max fit");
                                }
                            } else {
                                panic!("Pushing succeeded while there was no fit");
                            }

                            order.push_back(val);
                        }
                        Err(Error::FullStorage) => {
                            if let Some(max_fit) = max_fit {
                                if val.len() <= max_fit {
                                    panic!("Got a wrong full storage");
                                }
                            }
                        }
                        Err(Error::Storage {
                            value: MockFlashError::EarlyShutoff,
                            backtrace: _backtrace,
                        }) => {
                            let mut peeker =
                                sequential_storage::queue::peek_many(&mut flash, FLASH_RANGE)
                                    .unwrap();

                            let mut last_item = None;
                            let mut count = 0;

                            while let Ok(Some(data)) = peeker.next(&mut buf) {
                                last_item = Some(data.to_vec());
                                count += 1;
                            }

                            if let Some(last_item) = last_item {
                                if order.get(count).is_none() && last_item == val {
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when pushing {val:?}! (but it still stored fully). Originated from:\n{_backtrace:#}");
                                    order.push_back(val);
                                } else {
                                    #[cfg(fuzzing_repro)]
                                    eprintln!("Early shutoff when pushing {val:?}! Originated from:\n{_backtrace:#}");
                                }
                            }
                        }
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while pushing! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            sequential_storage::queue::try_repair(&mut flash, FLASH_RANGE).unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("Error pushing to queue: {e:?}"),
                    }
                }
                Op::Pop => {
                    match sequential_storage::queue::pop(&mut flash, FLASH_RANGE, &mut buf) {
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
                            value: MockFlashError::EarlyShutoff,
                            backtrace: _backtrace,
                        }) => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "Early shutoff when popping (single)! Originated from:\n{_backtrace:#}"
                            );

                            retry = true;
                        }
                        Err(Error::Corrupted {
                            backtrace: _backtrace,
                        }) if !corruption_repaired => {
                            #[cfg(fuzzing_repro)]
                            eprintln!(
                                "### Encountered curruption while popping (single)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                            sequential_storage::queue::try_repair(&mut flash, FLASH_RANGE).unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                    }
                }
                Op::PopMany(n) => {
                    let mut popper =
                        sequential_storage::queue::pop_many(&mut flash, FLASH_RANGE).unwrap();

                    for i in 0..*n {
                        match popper.next(&mut buf) {
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
                                value: MockFlashError::EarlyShutoff,
                                backtrace: _backtrace,
                            }) => {
                                #[cfg(fuzzing_repro)]
                                eprintln!(
                                    "Early shutoff when popping (many)! Originated from:\n{_backtrace:#}"
                                );
                            }
                            Err(Error::Corrupted {
                                backtrace: _backtrace,
                            }) if !corruption_repaired => {
                                #[cfg(fuzzing_repro)]
                                eprintln!(
                                "### Encountered curruption while popping (many)! Repairing now. Originated from:\n{_backtrace:#}"
                            );

                                sequential_storage::queue::try_repair(&mut flash, FLASH_RANGE)
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
                    match sequential_storage::queue::peek(&mut flash, FLASH_RANGE, &mut buf) {
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

                            sequential_storage::queue::try_repair(&mut flash, FLASH_RANGE).unwrap();
                            corruption_repaired = true;
                            retry = true;
                        }
                        Err(e) => panic!("Error popping (single) from queue: {e:?}"),
                    }
                }
                Op::PeekMany(n) => {
                    let mut peeker =
                        sequential_storage::queue::peek_many(&mut flash, FLASH_RANGE).unwrap();

                    for i in 0..*n {
                        match peeker.next(&mut buf) {
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

                                sequential_storage::queue::try_repair(&mut flash, FLASH_RANGE)
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
