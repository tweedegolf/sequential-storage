# Sequential-storage

[![crates.io](https://img.shields.io/crates/v/sequential-storage.svg)](https://crates.io/crates/sequential-storage) [![Documentation](https://docs.rs/sequential-storage/badge.svg)](https://docs.rs/sequential-storage)

A crate for storing key-value pairs in flash with minimal erase cycles.

Basic API:

```rust,ignore
enum MyCustomType {
    X,
    Y,
    // ...
}

impl StorageItem for MyCustomType {
    // ...
}

let mut flash = SomeFlashChip::new();
let flash_range = 0x1000..0x2000; // These are the flash addresses in which the crate will operate

assert_eq!(
    fetch_item::<MyCustomType, SomeFlashChip>(
        &mut flash,
        flash_range.clone(),
        0
    ).unwrap(),
    None
);

store_item::<MyCustomType, SomeFlashChip, SomeFlashChip::ERASE_SIZE>(
    &mut flash,
    flash_range.clone(),
    MyCustomType::X
).unwrap();

assert_eq!(
    fetch_item::<MyCustomType, SomeFlashChip>(
        &mut flash,
        flash_range.clone(),
        0
    ).unwrap(),
    Some(MyCustomType::X)
);
```
