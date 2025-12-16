#![no_main]

extern crate libfuzzer_sys;

use futures::executor::block_on;
use libfuzzer_sys::fuzz_target;
use sequential_storage::{
    cache::NoCache,
    mock_flash::{MockFlashBase, WriteCountCheck},
    queue::{QueueConfig, QueueStorage},
};

fuzz_target!(|data: &[u8]| fuzz(data));

const PAGES: usize = 4;
const WORD_SIZE: usize = 4;
const WORDS_PER_PAGE: usize = 256;

fn fuzz(random_data: &[u8]) {
    let mut flash =
        MockFlashBase::<PAGES, WORD_SIZE, WORDS_PER_PAGE>::new(WriteCountCheck::Twice, None, false);

    let len = random_data.len().min(flash.as_bytes().len());
    flash.as_bytes_mut()[..len].copy_from_slice(&random_data[..len]);

    let mut storage = QueueStorage::new(
        flash,
        const { QueueConfig::new(0..(PAGES * WORD_SIZE * WORDS_PER_PAGE) as u32) },
        NoCache::new(),
    );
    block_on(storage.print_items());
}
