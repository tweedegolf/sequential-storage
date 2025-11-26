#![no_std]
#![no_main]

use core::ops::Range;

use defmt::unwrap;
use embassy_executor::Spawner;
use embedded_storage_async::nor_flash::MultiwriteNorFlash;
use sequential_storage::cache::{KeyPointerCache, PagePointerCache};
use {defmt_rtt as _, panic_probe as _};

#[embassy_executor::main]
async fn main(_spawner: Spawner) {
    let p = embassy_nrf::init(Default::default());

    let flash = embassy_nrf::nvmc::Nvmc::new(p.NVMC);
    let mut flash = embassy_embedded_hal::adapter::BlockingAsync::new(flash);

    const QUEUE_FLASH_RANGE: Range<u32> = 0xF8000..0xFC000;
    const MAP_FLASH_RANGE: Range<u32> = 0xFC000..0x100000;

    run_queue(&mut flash, QUEUE_FLASH_RANGE).await;
    run_map(&mut flash, MAP_FLASH_RANGE).await;

    defmt::info!("All went ok!");
    cortex_m::asm::bkpt();
}

async fn run_queue<E: defmt::Format>(
    flash: &mut impl MultiwriteNorFlash<Error = E>,
    flash_range: Range<u32>,
) {
    unwrap!(sequential_storage::erase_all(flash, flash_range.clone()).await);

    let mut data_buffer = [0; 32];
    let mut ppc = PagePointerCache::<4>::new();

    unwrap!(
        sequential_storage::queue::push(flash, flash_range.clone(), &mut ppc, &[0, 0, 0, 0], false)
            .await
    );

    let peeked = unwrap!(
        sequential_storage::queue::peek(flash, flash_range.clone(), &mut ppc, &mut data_buffer,)
            .await
    );

    defmt::assert_eq!(peeked, Some(&mut [0u8, 0, 0, 0][..]));

    let popped = unwrap!(
        sequential_storage::queue::pop(flash, flash_range.clone(), &mut ppc, &mut data_buffer,)
            .await
    );

    defmt::assert_eq!(popped, Some(&mut [0u8, 0, 0, 0][..]));

    let peeked = unwrap!(
        sequential_storage::queue::peek(flash, flash_range.clone(), &mut ppc, &mut data_buffer,)
            .await
    );

    defmt::assert!(peeked.is_none());
}

async fn run_map<E: defmt::Format>(
    flash: &mut impl MultiwriteNorFlash<Error = E>,
    flash_range: Range<u32>,
) {
    unwrap!(sequential_storage::erase_all(flash, flash_range.clone()).await);

    let mut data_buffer = [0; 32];
    let mut kpc = KeyPointerCache::<4, u8, 8>::new();

    unwrap!(
        sequential_storage::map::store_item(
            flash,
            flash_range.clone(),
            &mut kpc,
            &mut data_buffer,
            &0u8,
            &0u8,
        )
        .await
    );

    unwrap!(
        sequential_storage::map::store_item(
            flash,
            flash_range.clone(),
            &mut kpc,
            &mut data_buffer,
            &1u8,
            &123u32,
        )
        .await
    );

    unwrap!(
        sequential_storage::map::store_item(
            flash,
            flash_range.clone(),
            &mut kpc,
            &mut data_buffer,
            &2u8,
            &0.123f32,
        )
        .await
    );

    let fetched = unwrap!(
        sequential_storage::map::fetch_item::<u8, u32, _>(
            flash,
            flash_range.clone(),
            &mut kpc,
            &mut data_buffer,
            &3,
        )
        .await
    );

    defmt::assert!(fetched.is_none());

    let fetched = unwrap!(
        sequential_storage::map::fetch_item::<u8, u32, _>(
            flash,
            flash_range.clone(),
            &mut kpc,
            &mut data_buffer,
            &1,
        )
        .await
    );

    defmt::assert_eq!(fetched, Some(123));
}
