#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sequential_storage::mock_flash::MockFlashBase;
const MAX_VALUE_SIZE: usize = 255;

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
    key: u16,
    value_len: u8,
}

fn fuzz(ops: Input) {
    let mut flash = MockFlashBase::<4, 4, 131072>::default();
    let flash_range = 0x000..0x200000;

    let mut order = Vec::new();
    let mut buf = [0; MAX_VALUE_SIZE + 64];

    for (i, op) in ops.ops.into_iter().enumerate() {
        println!(
            "==================================================== op: {:?}",
            op
        );
        match op {
            Op::Push(mut op) => {
                op.value_len %= MAX_VALUE_SIZE as u8;

                let key = op.key.to_be_bytes();
                let mut val = vec![0; op.value_len as usize];
                let val_num = i.to_be_bytes();
                let n = val_num.len().min(val.len());
                val[..n].copy_from_slice(&val_num[..n]);

                sequential_storage::queue::push(&mut flash, flash_range.clone(), &val, false)
                    .unwrap();
                order.push(key.to_vec());
            }
            Op::Pop => {
                if let Some(_key) = order.pop() {
                    assert!(sequential_storage::queue::pop(
                        &mut flash,
                        flash_range.clone(),
                        &mut buf
                    )
                    .unwrap()
                    .is_some());
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
                    if let Some(_key) = order.pop() {
                        assert!(popper.next(&mut buf).unwrap().is_some());
                    } else {
                        assert!(popper.next(&mut buf).unwrap().is_none());
                    }
                }
            }
        }
    }
}
