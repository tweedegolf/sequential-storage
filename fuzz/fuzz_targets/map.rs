#![no_main]

use libfuzzer_sys::arbitrary::Arbitrary;
use libfuzzer_sys::fuzz_target;
use sequential_storage::{
    map::{MapError, StorageItem},
    mock_flash::MockFlashBase,
};
use std::{collections::HashMap, ops::Range};

fuzz_target!(|data: Input| fuzz(data));

#[derive(Arbitrary, Debug)]
struct Input {
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    Store(StoreOp),
    Fetch(u16),
}

#[derive(Arbitrary, Debug)]
struct StoreOp {
    key: u16,
    value_len: u8,
}

impl StoreOp {
    fn into_test_item(self) -> TestItem {
        TestItem {
            key: self.key,
            value: (0..self.value_len as usize)
                .map(|_| rand::random::<u8>())
                .collect(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TestItem {
    key: u16,
    value: Vec<u8>,
}

impl StorageItem for TestItem {
    type Key = u16;

    type Error = ();

    fn serialize_into(&self, buffer: &mut [u8]) -> Result<usize, Self::Error> {
        if buffer.len() < 2 + self.value.len() {
            return Err(());
        }

        buffer[0..2].copy_from_slice(&self.key.to_ne_bytes());
        buffer[2..][..self.value.len()].copy_from_slice(&self.value);

        Ok(2 + self.value.len())
    }

    fn deserialize_from(buffer: &[u8]) -> Result<Self, Self::Error>
    where
        Self: Sized,
    {
        Ok(Self {
            key: u16::from_ne_bytes(buffer[0..2].try_into().unwrap()),
            value: buffer[2..].to_vec(),
        })
    }

    fn key(&self) -> Self::Key {
        self.key
    }

    fn deserialize_key_only(buffer: &[u8]) -> Result<Self::Key, Self::Error>
    where
        Self: Sized,
    {
        Ok(u16::from_ne_bytes(buffer[0..2].try_into().unwrap()))
    }
}

fn fuzz(ops: Input) {
    const PAGES: usize = 4;
    const WORD_SIZE: usize = 4;
    const WORDS_PER_PAGE: usize = 256;

    let mut flash = MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::default();
    const FLASH_RANGE: Range<u32> = 0x000..0x1000;

    let mut map = HashMap::new();
    let mut buf = [0; 260]; // Max length of test item serialized, rounded up to align to flash word.

    for op in ops.ops.into_iter() {
        // println!(
        //     "==================================================== op: {:?}",
        //     op,
        // );
        match op {
            Op::Store(op) => {
                let item = op.into_test_item();
                match sequential_storage::map::store_item(
                    &mut flash,
                    FLASH_RANGE,
                    &mut buf,
                    item.clone(),
                ) {
                    Ok(_) => {
                        map.insert(item.key, item.value);
                    }
                    Err(MapError::FullStorage) => {}
                    Err(e) => panic!("{e:?}"),
                }
            }
            Op::Fetch(key) => {
                let fetch_result = sequential_storage::map::fetch_item::<TestItem, _>(
                    &mut flash,
                    FLASH_RANGE,
                    &mut buf,
                    key,
                )
                .unwrap();

                if let Some(existing_value) = map.get(&key) {
                    assert_eq!(
                        fetch_result.as_ref().map(|item| &item.key),
                        Some(&key),
                        "Mismatching keys"
                    );
                    assert_eq!(
                        fetch_result.as_ref().map(|item| &item.value),
                        Some(existing_value),
                        "Mismatching values"
                    );
                } else {
                    assert_eq!(fetch_result, None)
                }
            }
        }
    }
}
