#![no_main]

use embedded_storage::nor_flash::ReadNorFlash;
use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sequential_storage::mock_flash::MockFlashBase;
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
    Pop,
}

#[derive(Arbitrary, Debug)]
struct PushOp {
    value_len: u8,
}

fn fuzz(ops: Input) {
    let mut flash = MockFlashBase::<4, 4, 256>::default();
    let flash_range = 0x000..0x1000;

    let mut order = VecDeque::new();
    let mut buf = [0; MAX_VALUE_SIZE + 1];

    let mut used = 0;
    let capacity = (0.75 * flash.capacity() as f32) as usize;
    for op in ops.ops.into_iter() {
        println!(
            "==================================================== op: {:?} (used {}/{})",
            op, used, capacity,
        );
        match op {
            Op::Push(op) => {
                let val: Vec<u8> = (0..op.value_len as usize)
                    .map(|_| rand::random::<u8>())
                    .collect();

                let result =
                    sequential_storage::queue::push(&mut flash, flash_range.clone(), &val, false);
                println!("Item size: {}. Used: {}/{}", val.len(), used, capacity);
                if used + val.len() > capacity {
                    assert!(result.is_err());
                } else {
                    result.unwrap();
                    used += val.len();
                    order.push_back(val.to_vec());
                }
            }
            Op::Pop => {
                if let Some(expected) = order.pop_front() {
                    let result =
                        sequential_storage::queue::pop(&mut flash, flash_range.clone(), &mut buf);
                    assert!(result.is_ok());
                    assert_eq!(result.unwrap().unwrap(), expected);
                    used -= expected.len();
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
                        used -= expected.len();
                    } else {
                        assert!(popper.next(&mut buf).unwrap().is_none());
                    }
                }
            }
        }
    }
}
