#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sequential_storage::mock_flash::{MockFlashBase, MockFlashError};
use std::collections::VecDeque;
const MAX_VALUE_SIZE: usize = u8::MAX as usize;

fuzz_target!(|data: Input| fuzz(data));

#[derive(Arbitrary, Debug)]
struct Input {
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Push(PushOp),
    PopMany(u8),
    PeekMany(u8),
    Peek,
    Pop,
}

#[derive(Arbitrary, Debug)]
struct PushOp {
    value_len: u8,
}

fn fuzz(ops: Input) {
    const PAGES: usize = 4;
    const WORD_SIZE: usize = 4;
    const WORDS_PER_PAGE: usize = 256;

    let mut flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::default();
    let flash_range = 0x000..0x1000;

    let mut order = VecDeque::new();
    let mut buf = [0; MAX_VALUE_SIZE + 1];

    for op in ops.ops.into_iter() {
        println!(
            "==================================================== op: {:?}",
            op,
        );
        match op {
            Op::Push(op) => {
                let val: Vec<u8> = (0..op.value_len as usize)
                    .map(|_| rand::random::<u8>())
                    .collect();

                let max_fit =
                    sequential_storage::queue::find_max_fit(&mut flash, flash_range.clone())
                        .unwrap();

                let result: Result<(), sequential_storage::Error<MockFlashError>> =
                    sequential_storage::queue::push(&mut flash, flash_range.clone(), &val, false);

                if let Some(max_fit) = max_fit {
                    if val.len() <= max_fit {
                        result.unwrap();
                        order.push_back(val.to_vec());
                    } else {
                        assert!(result.is_err());
                    }
                } else {
                    assert!(result.is_err());
                }
            }
            Op::Pop => {
                if let Some(expected) = order.pop_front() {
                    let result =
                        sequential_storage::queue::pop(&mut flash, flash_range.clone(), &mut buf);
                    assert!(result.is_ok());
                    assert_eq!(result.unwrap().unwrap(), expected);
                } else {
                    assert!(sequential_storage::queue::pop(
                        &mut flash,
                        flash_range.clone(),
                        &mut buf
                    )
                    .unwrap()
                    .is_none());
                }
            }
            Op::PopMany(n) => {
                let mut popper =
                    sequential_storage::queue::pop_many(&mut flash, flash_range.clone());
                for _i in 0..n {
                    if let Some(expected) = order.pop_front() {
                        let result = popper.next(&mut buf);
                        assert!(result.is_ok());
                        assert_eq!(result.unwrap().unwrap(), expected);
                    } else {
                        assert!(popper.next(&mut buf).unwrap().is_none());
                    }
                }
            }

            Op::Peek => {
                if let Some(expected) = order.get(0) {
                    let result =
                        sequential_storage::queue::peek(&mut flash, flash_range.clone(), &mut buf);
                    assert!(result.is_ok());
                    assert_eq!(result.unwrap().unwrap(), expected);
                } else {
                    assert!(sequential_storage::queue::peek(
                        &mut flash,
                        flash_range.clone(),
                        &mut buf
                    )
                    .unwrap()
                    .is_none());
                }
            }
            Op::PeekMany(n) => {
                let mut peeker =
                    sequential_storage::queue::peek_many(&mut flash, flash_range.clone());
                for i in 0..n {
                    if let Some(expected) = order.get(i as usize) {
                        let result = peeker.next(&mut buf);
                        assert!(result.is_ok());
                        assert_eq!(result.unwrap().unwrap(), expected);
                    } else {
                        assert!(peeker.next(&mut buf).unwrap().is_none());
                    }
                }
            }
        }
    }
}
