#![no_main]

use futures::executor::block_on;
use libfuzzer_sys::fuzz_target;
use sequential_storage::{
    cache::Cache,
    map::{MapConfig, MapStorage},
    mock_flash::{MockFlashBase, MockFlashError, WriteCountCheck},
    Error,
};

const ERASE_SIZE: usize = 128;
const CAPACITY: usize = ERASE_SIZE * 2;
const VALUE_SIZE: usize = 8;

type Flash = MockFlashBase<2, 1, ERASE_SIZE>;

fn config() -> MapConfig<Flash> {
    const { MapConfig::new(0..CAPACITY as u32) }
}

fn fetch(flash: Flash, buffer: &mut [u8]) -> (Flash, Option<[u8; VALUE_SIZE]>) {
    let mut storage = MapStorage::<u8, _, _>::new(flash, config(), Cache::new_uncached());
    let value = block_on(storage.fetch_item::<[u8; VALUE_SIZE]>(buffer, &0)).unwrap();
    (storage.destroy().0, value)
}

fuzz_target!(|input: &[u8]| {
    let mut flash = Flash::new(WriteCountCheck::OnceOnly, None, false);
    let mut expected = None;
    let mut buffer = [0; 256];

    for offset in (0..input.len().saturating_sub(2)).step_by(3).take(512) {
        let command = &input[offset..offset + 3];
        let next = [command[1]; VALUE_SIZE];
        if command[0] & 1 != 0 {
            flash.bytes_until_shutoff = Some(u32::from(command[2]));
        }

        let mut storage = MapStorage::<u8, _, _>::new(flash, config(), Cache::new_uncached());
        let result = block_on(storage.store_item(&mut buffer, &0, &next));
        (flash, _) = storage.destroy();

        // A reboot restores power and discards all cache state while keeping
        // every byte that reached the flash before the shutdown.
        flash.bytes_until_shutoff = None;
        let recovered;
        (flash, recovered) = fetch(flash, &mut buffer);

        match result {
            Ok(()) => {
                assert_eq!(recovered, Some(next));
                expected = Some(next);
            }
            Err(Error::Storage {
                value: MockFlashError::EarlyShutoff(_, _),
                ..
            }) => {
                assert!(recovered == expected || recovered == Some(next));
                expected = recovered;
            }
            Err(error) => panic!("unexpected store error: {error:?}"),
        }

        let loaded;
        (flash, loaded) = fetch(flash, &mut buffer);
        assert_eq!(loaded, expected);
    }
});
