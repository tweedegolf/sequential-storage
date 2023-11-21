# Sequential-storage

[![crates.io](https://img.shields.io/crates/v/sequential-storage.svg)](https://crates.io/crates/sequential-storage) [![Documentation](https://docs.rs/sequential-storage/badge.svg)](https://docs.rs/sequential-storage)

A crate for storing data in flash with minimal erase cycles.

There are two datastructures:

- Map: An key-value pair store
- Queue: A fifo store

Each live in their own module. See the module documentation for more info and examples.

Make sure not to mix the datastructures in flash!
You can't fetch a key-value item from a flash region where you pushed to the queue.

To search for data, the crate first searches for the flash page that is likeliest to contain it and
then performs a linear scan over the data, skipping data blocks where it can.

All data is crc protected, so if there is corruption of the data, you should not read back corrupted data unless there's
a perfect storm of unfortunate bitflips. But this chance is very low.
Corrupted data is ignored. This means you will lose the corrupted data, but not any other data.

If you're looking for an alternative with different tradeoffs, take a look at [ekv](https://github.com/embassy-rs/ekv).

## Inner workings

To save on erase cycles, this crate only really appends data to the pages. Exactly how this is done depends
on whether you use the map or the queue.

To do all this there are two concepts:

### Page & page state

The flash is divided up in multiple pages.
A page can be in three states:

1. Open - This page is in the erased state
2. Partial open - This page has been written to, but is not full yet
3. Closed - This page has been fully written to

The state of a page is encoded into the first and the last word of a page.
If both words are `FF` (erased), then the page is open.
If the first word is written with the marker, then the page is partial open.
If both words are written, then the page is closed.

### Items

All data is stored as an item.

An item consists of a header containing the data length, a CRC for that length, a data CRC, and some data.
An item is considered erased when its data CRC field is 0.

*NOTE: This means the data itself is still stored on the flash when it's considered erased.*
*Depending on your usecase, this might not be secure*

The length is a u16, so any item cannot be longer than 0xFFFF.

### Inner workings for map

The map stores every key-value as an item. Every new value is appended at the last partial open page
or the first open after the last closed page.

Once a page is full it will be closed and the next page will need to store the item.
However, we need to erase an old page at some point. Because we don't want to lose any data,
all items on the to-be-erased page are checked. If an item does not have a newer value than what is found on
the page, it will be copied over from the to-be-erased page to the current partial-open page.
This way no data is lost (as long as the flash is big enough to contain all data).

## Inner workings for queue

When pushing, the youngest spot to place the item is searched for.
If it doesn't fit, it will return an error or erase an old page if you specified it could.
You should only lose data when you give permission.

Peeking and popping look at the oldest data it can find.
When popping, the item is also erased.

## Changelog

### 0.6.0 - 21-11-23

- *Breaking* Internal overhaul of the code. Both map and queue now use the same `item` module to store and read their data with.
- *Breaking* Map serialization is no longer done in a stack buffer, but in the buffer provided by the user.
- *Breaking* Map StorageItemError trait has been removed.
- Added CRC protection of the user data. If user data is corrupted, it will now be skipped as if it wasn't stored.
  If you think it should be reported to the user, let me know and propose an API for that!
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
