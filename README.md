# Sequential-storage

[![crates.io](https://img.shields.io/crates/v/sequential-storage.svg)](https://crates.io/crates/sequential-storage) [![Documentation](https://docs.rs/sequential-storage/badge.svg)](https://docs.rs/sequential-storage)

A crate for storing data in flash with minimal erase cycles.

There are two datastructures:

- Map: A key-value pair store
- Queue: A fifo store

Each are implemented on the `Storage` struct. See the [documentation](https://docs.rs/sequential-storage) for examples and API docs.

To search for data, the crate first searches for the flash page that is likeliest to contain it and
then performs a linear scan over the data, skipping data blocks where it can.

## Status

This crate is used in production in multiple projects inside and outside of Tweede golf.

The in-flash representation is not (yet?) stable. This too follows semver.

- A breaking change to the in-flash representation will lead to a major version bump
- A feature addition will lead to a minor version bump
  - This is always backward-compatible. So data created by e.g. `1.0.0` can be used by `1.1.0`.
  - This may not be forward-compatible. So data created by e.g. `1.0.1` may not be usable by `1.0.0`.
- After 1.0, patch releases only fix bugs and don't change the in-flash representation

For any update, consult the changelog to see what changed. Any externally noticable changes are recorded there.

The `_test` feature of the crate is considered private. It and anything it enables is not covered by semver.

The performance of any of the cache types is not covered by semver either. If you use this crate in a
performance sensitive application, then make sure that everything remains working even when no cache is used.
That way you've covered the worst-case execution time for that part of your application.

A cache performance regression might be a bug though. Open an issue to discus your situation if you find a regression.

## MSRV

This crate has no further guarantees other than being able to run on the latest stable compiler.\
Increasing the MSRV is not seen as a breaking change semver-wise.\
If you find yourself in trouble with this, feel free to open an issue.

## Example

See the `map` and `queue` module level documentation for examples.

## Features

- Key value datastore (Map)
  - User defined key and value types
  - Great for creating configs
- Fifo queue datastore (Queue)
  - Store byte slices in memory
  - Great for caching data
- Simple APIs:
  - Initialize the storage struct and use its functions
  - No need to worry about anything else
- Item header CRC protected
- Item data CRC protected
- Power-fail safe
  - The system is always fine or fully recoverable
- Corrupted items are ignored
- Optional caching to speed things up
- Wear leveling
  - Pages are used cyclically, so all pages get erased an equal amount
- Built on [`embedded-storage`](https://github.com/rust-embedded-community/embedded-storage)
  - This is the only required dependency

If you're looking for an alternative with different tradeoffs, take a look at [ekv](https://github.com/embassy-rs/ekv).

***Note:** The crate uses futures for its operations. These futures write to flash. If a future is cancelled, this can lead*
*to a corrupted flash state, so cancelling is at your own risc. If this happens, the state will be repaired.*
*In any case, the thing you tried to store or erase might or might not have fully happened.*

### Corruption repair

When corruption is found while an operation is going on, the crate will automatically try to repair it.
Some corruption leads to unrecoverable data and sadly that cannot be repaired.
However, the repair will make sure that the flash state is recovered so any next operation should succeed.

If any function still returns the corrupted error, that means that a repair wasn't able to fix the state.
In that case please open an issue!

### Caching

There are various cache options that speed up the operations.
By default (no cache) all state is stored in flash and the state has to be fully read every time.
Instead, we can optionally store some state in ram.

These numbers are taken from the test cases in the cache module:

|             Name |                                    RAM bytes | Map # flash reads | Map flash bytes read | Queue # flash reads | Queue flash bytes read |
| ---------------: | -------------------------------------------: | ----------------: | -------------------: | ------------------: | ---------------------: |
|          `NoCache` |                                            0 |              100% |                 100% |                100% |                   100% |
|   `PageStateCache` |                                1 * num pages |               77% |                  97% |                 41% |                    85% |
| `PagePointerCache` |                                9 * num pages |               70% |                  89% |                  6% |                    14% |
|  `KeyPointerCache` | 9 * num pages + (sizeof(KEY) + 4) * num keys |              6.2% |                 8.2% |                   - |                      - |

#### Takeaways

- `PageStateCache`
  - Mostly tackles number of reads
  - Very cheap in RAM, so easy win
- `PagePointerCache`
  - Very efficient for the queue
  - Minimum cache level that makes a dent in the map
- `KeyPointerCache`
  - Awesome savings!
  - Numbers are less good if there are more keys than the cache can store
  - Same as `PagePointerCache` when used for queue

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

The length is a u16, so any item cannot be longer than 0xFFFF or `page size - the item header (padded to word boundary) - page state (2 words)`.

### Inner workings for map

The map stores every key-value as an item. Every new value is appended at the last partial open page
or the first open after the last closed page.

Once a page is full it will be closed and the next page will need to store the item.
However, we need to erase an old page at some point. Because we don't want to lose any data,
all items on the to-be-erased page are checked. If an item does not have a newer value than what is found on
the page, it will be copied over from the to-be-erased page to the current partial-open page.
This way no data is lost (as long as the flash is big enough to contain all data).

### Inner workings for queue

When pushing, the youngest spot to place the item is searched for.
If it doesn't fit, it will return an error or erase an old page if you specified it could.
You should only lose data when you give permission.

Peeking and popping look at the oldest data it can find.
When popping, the item is also erased.

When using `peek_many`, you can look at all data from oldest to newest.
