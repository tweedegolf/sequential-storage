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

## TODO

- Find a way to support removing items. You can do this manually now by reading all keys,
  erasing all flash manually and then storing the items you want to keep again.

## Inner workings

The idea behind this crate it to save on flash erase cycles by storing every item in an append-only way.
Only the most recent value of a key-value item is 'active'.

This is more efficient because we don't have to erase a page every time we want to update a value.

Every item has to fit in a page. Once an item is too big to fit on the current page will be closed
and the item will be stored on the next page.

Once all pages have been closed, the next page will be erased to open it up again.
There is the possibility that the erased page contains the only copy of a key, so the crate checks if that happens and
if it does add that key-value item back in. In principle you will never lose any data.

## Changelog

### 0.2.2 - 11-05-23

- Optimized reading items from flash which reduces the amount of reads by ~30% for small items.

### 0.2.1 - 19-01-23

- Added defmt behind a feature flag. When enabled, the error type implements Format

### 0.2.0 - 13-01-23

- Fixed a scenario where an infinite recursion could lead to a stackoverflow.
  If there's no more space to fit all items, you'll now get an error instead.
- Made the error non-exhaustive so that next time this update wouldn't be a breaking one.
