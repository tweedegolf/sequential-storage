extern crate alloc;

use alloc::{vec, vec::Vec};
use core::num::NonZeroU32;

use crate::{
    PageState,
    cache::{
        CacheImpl, DirtTracker, Invalidate, KeyCacheImpl, PagePointersCache, PageStatesCache,
        PrivateCacheImpl, PrivateKeyCacheImpl,
        key_pointers::{CachedKeyPointers, KeyPointersCache, UncachedKeyPointers},
        page_pointers::{CachedPagePointers, UncachedPagePointers},
        page_states::CachedPageStates,
    },
    map::Key,
};

/// A cache object that keeps track of the page states.
///
/// This cache has to be kept around and passed to *every* api call to the same memory region until the cache gets discarded.
///
/// Valid usecase:  
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:  
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct HeapPageStateCache {
    dirt_tracker: DirtTracker,
    page_states: Vec<Option<PageState>>,
}

impl HeapPageStateCache {
    /// Construct a new instance
    pub fn new(pages: usize) -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: vec![None; pages],
        }
    }
}

impl PrivateCacheImpl for HeapPageStateCache {
    type PSC<'a>
        = CachedPageStates<'a>
    where
        Self: 'a;
    type PPC<'a>
        = UncachedPagePointers
    where
        Self: 'a;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> Self::PSC<'_> {
        CachedPageStates::new(&mut self.page_states)
    }

    fn page_pointers(&mut self) -> Self::PPC<'_> {
        UncachedPagePointers
    }
}

impl CacheImpl for HeapPageStateCache {}
impl<KEY: Key> KeyCacheImpl<KEY> for HeapPageStateCache {}

impl Invalidate for HeapPageStateCache {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
    }
}

impl<KEY: Key> PrivateKeyCacheImpl<KEY> for HeapPageStateCache {
    type KPC<'a>
        = UncachedKeyPointers
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_> {
        UncachedKeyPointers
    }
}

/// A cache object that keeps track of the page states and some pointers to the items in the page.
///
/// This cache has to be kept around and passed to *every* api call to the same memory region until the cache gets discarded.
///
/// Valid usecase:  
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:  
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct HeapPagePointerCache {
    dirt_tracker: DirtTracker,
    page_states: Vec<Option<PageState>>,
    after_erased_pointers: Vec<Option<NonZeroU32>>,
    after_written_pointers: Vec<Option<NonZeroU32>>,
}

impl HeapPagePointerCache {
    /// Construct a new instance
    pub fn new(pages: usize) -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: vec![None; pages],
            after_erased_pointers: vec![None; pages],
            after_written_pointers: vec![None; pages],
        }
    }
}

impl PrivateCacheImpl for HeapPagePointerCache {
    type PSC<'a>
        = CachedPageStates<'a>
    where
        Self: 'a;
    type PPC<'a>
        = CachedPagePointers<'a>
    where
        Self: 'a;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> Self::PSC<'_> {
        CachedPageStates::new(&mut self.page_states)
    }

    fn page_pointers(&mut self) -> Self::PPC<'_> {
        CachedPagePointers::new(
            &mut self.after_erased_pointers,
            &mut self.after_written_pointers,
        )
    }
}

impl CacheImpl for HeapPagePointerCache {}
impl<KEY: Key> KeyCacheImpl<KEY> for HeapPagePointerCache {}

impl Invalidate for HeapPagePointerCache {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
    }
}

impl<KEY: Key> PrivateKeyCacheImpl<KEY> for HeapPagePointerCache {
    type KPC<'a>
        = UncachedKeyPointers
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_> {
        UncachedKeyPointers
    }
}

/// An object that caches the location of the newest item with a given key.
/// This cache also caches pages states and page pointers.
///
/// This cache has to be kept around and passed to *every* api call to the same memory region until the cache gets discarded.
///
/// Valid usecase:  
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:  
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
///
/// The number of key slots can be lower than the total amount of possible keys used, but this will lower
/// the chance of a cache hit.
/// The keys are cached in a fifo and any time its location is updated in cache it's added to the front.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct HeapKeyPointerCache<KEY: Key> {
    dirt_tracker: DirtTracker,
    page_states: Vec<Option<PageState>>,
    after_erased_pointers: Vec<Option<NonZeroU32>>,
    after_written_pointers: Vec<Option<NonZeroU32>>,
    key_pointers: Vec<Option<(KEY, NonZeroU32)>>,
}

impl<KEY: Key> HeapKeyPointerCache<KEY> {
    /// Construct a new instance
    pub fn new(pages: usize, keys: usize) -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: vec![None; pages],
            after_erased_pointers: vec![None; pages],
            after_written_pointers: vec![None; pages],
            key_pointers: vec![const { None }; keys],
        }
    }
}

impl<KEY: Key> PrivateCacheImpl for HeapKeyPointerCache<KEY> {
    type PSC<'a>
        = CachedPageStates<'a>
    where
        Self: 'a;
    type PPC<'a>
        = CachedPagePointers<'a>
    where
        Self: 'a;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> Self::PSC<'_> {
        CachedPageStates::new(&mut self.page_states)
    }

    fn page_pointers(&mut self) -> Self::PPC<'_> {
        CachedPagePointers::new(
            &mut self.after_erased_pointers,
            &mut self.after_written_pointers,
        )
    }
}

impl<KEY: Key> CacheImpl for HeapKeyPointerCache<KEY> {}
impl<KEY: Key> KeyCacheImpl<KEY> for HeapKeyPointerCache<KEY> {}

impl<KEY: Key> Invalidate for HeapKeyPointerCache<KEY> {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
        self.key_pointers().invalidate_cache_state();
    }
}

impl<KEY: Key> PrivateKeyCacheImpl<KEY> for HeapKeyPointerCache<KEY> {
    type KPC<'a>
        = CachedKeyPointers<'a, KEY>
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_> {
        CachedKeyPointers::new(&mut self.key_pointers)
    }
}
