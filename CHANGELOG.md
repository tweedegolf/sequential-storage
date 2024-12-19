# Changelog

(DD-MM-YY)

## Unreleased

- Added item iterator for map.
- *Breaking:* Added `Value` impls for `bool`, `Option<T: Value>`, and `[T: Value; N]`.
  *This can break existing code because it changes type inference, be mindfull of that!*

## 3.0.1 25-07-24

- Add `defmt` attributes to cache types.

## 3.0.0 17-07-24

- *Breaking:* Map keys are now always passed by reference. This avoids extra cloning and memory use for bigger keys.
- Added `space_left` function for queue
- Added a new `map::remove_all_items()` API to remove all stored items in flash.

This release is 'disk'-compatible with 2.0

## 2.0.2 07-05-24

- Added check for too big items that won't ever fit in flash so it returns a good clear error.

## 2.0.1 06-05-24

- Implemented the `get_len` function for all built-in key types

## 2.0.0 06-05-24

- *Breaking:* Made the cache API a bit more strict. Caches now always have to be passed as a mutable reference.
  The API before would lead to a lot of extra unncesessary binary size.
- *Breaking:* Removed the `StorageItem` trait in favor of two separate `Key` and `Value` traits. This helps cut
  binary size and is closer to what users of the map APIs were expecting.
- *Breaking:* The error type is no longer generic over the Item error. That error variant has been renamed `SerializationError`
  and carries a predefined error subtype.
- Added `erase_all` function as a helper to erase the flash in a region.
- *Breaking:* Changed the way that queue iteration works. Now there's an `iter` function instead of two separate `peek_many` and `pop_many` functions. The new iter returns an entry from which you can get the data that was just peeked. If you want to pop it, then call the pop function on the entry.
- Added `arrayvec` feature that when activated impls the `Key` trait for `ArrayVec` and `ArrayString`.

## 1.0.0 01-03-24

- *Breaking:* Corruption repair is automatic now! The repair functions have been made private.
- *Breaking:* There's now only one error type. `MapError` has been retired and the main error type now carries
  the Item error as well. The queue uses `Infallable` as the item error type.
- *Breaking:* The feature `defmt` has been renamed `defmt-03` to avoid a future breaking change.
- Added `std` feature that implements the error trait for the error enum
- This release is flash compatible downto version 0.7

## 0.9.1 13-02-24

- Added `remove_item` to map

## 0.9.0 11-02-24

- *Breaking:* Storage item key must now also be clone
- Added KeyPointerCache which significantly helps out the map

## 0.8.1 07-02-24

- Added new PagePointerCache that caches more than the PageStateCache. See the readme for more details.

## 0.8.0 05-12-24

- *Breaking:* The item to store is now passed by reference to Map `store_item`
- *Breaking:* Added cache options to the functions to speed up reading the state of the flash.
  To retain the old behaviour you can pass the `NoCache` type as the cache parameter.
- Removed defmt logging since that wasn't being maintained. The format impl for the errors remain.

## 0.7.0 10-01-24

- *Breaking:* Data CRC has been upgraded to 32-bit from 16-bit. Turns out 16-bit has too many collisions.
  This increases the item header size from 6 to 8. The CRC was also moved to the front of the header to
  aid with shutdown/cancellation issues.
- When the state is corrupted, many issues can now be repaired with the repair functions in the map and queue modules
- Made changes to the entire crate to better survive shutoffs
- *Breaking:* Convert API to async first supporting the traits from embedded-storage-async. Flash
  drivers supporting `sequential-storage` can be wrapped using
  [BlockingAsync](https://docs.embassy.dev/embassy-embedded-hal/git/default/adapter/struct.BlockingAsync.html), and a 
  simple [blocking executor](https://docs.rs/futures/0.3.30/futures/executor/fn.block_on.html) can be used to call the 
  API from a non-async function.

## 0.6.2 - 22-12-23

- Small bug fixes and refactorings including an off-by-one error. Found with added fuzzing from ([#13](https://github.com/tweedegolf/sequential-storage/pull/13))

## 0.6.1 - 16-12-23

- Added queue peek_many and pop_many ([#12](https://github.com/tweedegolf/sequential-storage/pull/12))

## 0.6.0 - 21-11-23

- *Breaking:* Internal overhaul of the code. Both map and queue now use the same `item` module to store and read their data with.
- *Breaking:* Map serialization is no longer done in a stack buffer, but in the buffer provided by the user.
- *Breaking:* Map StorageItemError trait has been removed.
- Added CRC protection of the user data. If user data is corrupted, it will now be skipped as if it wasn't stored.
  If you think it should be reported to the user, let me know and propose an API for that!
- Read word size is no longer required to be 1. It can now be 1-32.

## 0.5.0 - 13-11-23

- *Breaking:* Map `store_item` item no longer uses a ram buffer to temporarily store erased items in.
  Instead it keeps an extra open page so it can copy from one page to another page directly.
  This means the minimum page count for map is now 2.

## 0.4.2 - 13-11-23

- Map no longer erases the flash when corrupted to self-recover. It now just returns an error so the user can choose what to do.

## 0.4.1 - 26-09-23

- Flipped one of the error messages in `queue::pop` and `queue::peek` from `BufferTooBig` to `BufferTooSmall` because that's a lot clearer
- Massive performance bug fixed for the queue. Before it had to read all pages from the start until the first pop or peek data was found.
  Now empty pages are erased which solves this issue.

## 0.4.0 - 04-07-23

- Fixed the queue implementation for devices with a write size of 1
- *Breaking:* The internal storage format for queue has changed, so is incompatible with existing stored memory. The max size has come down to 0x7FFE.

## 0.3.0 - 30-06-23

- Added new queue implementation with `push`, `peek` and `pop` which requires multiwrite flash
- *Breaking:* the map implementation now moved to its own module. You'll need to change your imports.

## 0.2.2 - 11-05-23

- Optimized reading items from flash which reduces the amount of reads by ~30% for small items.

## 0.2.1 - 19-01-23

- Added defmt behind a feature flag. When enabled, the error type implements Format

## 0.2.0 - 13-01-23

- Fixed a scenario where an infinite recursion could lead to a stackoverflow.
  If there's no more space to fit all items, you'll now get an error instead.
- Made the error non-exhaustive so that next time this update wouldn't be a breaking one.

## 0.1.0 - 12-01-23

- Initial release
