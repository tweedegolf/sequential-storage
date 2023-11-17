# Sequential-storage

[![crates.io](https://img.shields.io/crates/v/sequential-storage.svg)](https://crates.io/crates/sequential-storage) [![Documentation](https://docs.rs/sequential-storage/badge.svg)](https://docs.rs/sequential-storage)

A crate for storing data in flash with minimal erase cycles.

There are two datastructures:

- Map: An key-value pair store
- Queue: A fifo store

Each live in their own module. See the module documentation for more info and examples.

Make sure not to mix the datastructures in flash!
You can't fetch a key-value item from a flash region where you pushed to the queue.

## TODO

- Map: Find a way to support removing items. You can do this manually now by reading all keys,
  erasing all flash manually and then storing the items you want to keep again.

## Inner workings for map

The idea behind this crate it to save on flash erase cycles by storing every item in an append-only way.
Only the most recent value of a key-value item is 'active'.

This is more efficient because we don't have to erase a page every time we want to update a value.

Every item has to fit in a page. Once an item is too big to fit on the current page will be closed
and the item will be stored on the next page.

Once all but one pages have been closed, a new page will be erased to open it up again.
There is the possibility that the erased page contains the only copy of a key, so the crate checks if that happens and
if it does add that key-value item back in. In principle you will never lose any data.

## Inner workings for queue

Pages work in the same way as for the map.

All data is stored as u16 BE length + data. Push appends the data at the next spot.
If there's no more room, a push can erase the oldest page to make space, but only does so when configured.

Peeking and popping look at the oldest data it can find.
When popping, the data is also erased by writing all 0's over it.

## Changelog

### Unreleased

- *Breaking* Internal overhaul of the code. Both map and queue now use the same `item` module to store and read their data with.
- *Breaking* Map serialization is no longer done in a stack buffer, but in the buffer provided by the user.
- Added CRC protection of the user data. If user data is corrupted, it will now be skipped as if it wasn't stored.
- Read word size is no longer required to be 1. It can now be 1-32.

### 0.5.0 - 13-11-23

- *Breaking* Map `store_item` item no longer uses a ram buffer to temporarily store erased items in.
  Instead it keeps an extra open page so it can copy from one page to another page directly.
  This means the minimum page count for map is now 2.

### 0.4.2 - 13-11-23

- Map no longer erases the flash when corrupted to self-recover. It now just returns an error so the user can choose what to do.

### 0.4.1 - 26-09-23

- Flipped one of the error messages in `queue::pop` and `queue::peek` from `BufferTooBig` to `BufferTooSmall` because that's a lot clearer
- Massive performance bug fixed for the queue. Before it had to read all pages from the start until the first pop or peek data was found.
  Now empty pages are erased which solves this issue.

### 0.4.0 - 04-07-23

- Fixed the queue implementation for devices with a write size of 1
- *Breaking:* The internal storage format for queue has changed, so is incompatible with existing stored memory. The max size has come down to 0x7FFE.

### 0.3.0 - 30-06-23

- Added new queue implementation with `push`, `peek` and `pop` which requires multiwrite flash
- *Breaking:* the map implementation now moved to its own module. You'll need to change your imports.

### 0.2.2 - 11-05-23

- Optimized reading items from flash which reduces the amount of reads by ~30% for small items.

### 0.2.1 - 19-01-23

- Added defmt behind a feature flag. When enabled, the error type implements Format

### 0.2.0 - 13-01-23

- Fixed a scenario where an infinite recursion could lead to a stackoverflow.
  If there's no more space to fit all items, you'll now get an error instead.
- Made the error non-exhaustive so that next time this update wouldn't be a breaking one.
