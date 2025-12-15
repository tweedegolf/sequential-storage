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
/// Valid usecase:\
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:\
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PageStateCache<const PAGE_COUNT: usize> {
    dirt_tracker: DirtTracker,
    page_states: [Option<PageState>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> PageStateCache<PAGE_COUNT> {
    /// Construct a new instance
    #[must_use]
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: [None; PAGE_COUNT],
        }
    }
}

impl<const PAGE_COUNT: usize> Default for PageStateCache<PAGE_COUNT> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PageStateCache<PAGE_COUNT> {
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

impl<const PAGE_COUNT: usize> CacheImpl for PageStateCache<PAGE_COUNT> {}
impl<KEY: Key, const PAGE_COUNT: usize> KeyCacheImpl<KEY> for PageStateCache<PAGE_COUNT> {}

impl<const PAGE_COUNT: usize> Invalidate for PageStateCache<PAGE_COUNT> {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
    }
}

impl<KEY: Key, const PAGE_COUNT: usize> PrivateKeyCacheImpl<KEY> for PageStateCache<PAGE_COUNT> {
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
/// Valid usecase:\
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:\
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct PagePointerCache<const PAGE_COUNT: usize> {
    dirt_tracker: DirtTracker,
    page_states: [Option<PageState>; PAGE_COUNT],
    after_erased_pointers: [Option<NonZeroU32>; PAGE_COUNT],
    after_written_pointers: [Option<NonZeroU32>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> PagePointerCache<PAGE_COUNT> {
    /// Construct a new instance
    #[must_use]
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: [None; PAGE_COUNT],
            after_erased_pointers: [None; PAGE_COUNT],
            after_written_pointers: [None; PAGE_COUNT],
        }
    }
}

impl<const PAGE_COUNT: usize> Default for PagePointerCache<PAGE_COUNT> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PagePointerCache<PAGE_COUNT> {
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

impl<const PAGE_COUNT: usize> CacheImpl for PagePointerCache<PAGE_COUNT> {}
impl<KEY: Key, const PAGE_COUNT: usize> KeyCacheImpl<KEY> for PagePointerCache<PAGE_COUNT> {}

impl<const PAGE_COUNT: usize> Invalidate for PagePointerCache<PAGE_COUNT> {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
    }
}

impl<KEY: Key, const PAGE_COUNT: usize> PrivateKeyCacheImpl<KEY> for PagePointerCache<PAGE_COUNT> {
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
/// Valid usecase:\
/// `Create cache 1` -> `use 1` -> `use 1` -> `create cache 2` -> `use 2` -> `use 2`
///
/// Invalid usecase:\
/// `Create cache 1` -> `use 1` -> `create cache 2` -> `use 2` -> `❌ use 1 ❌`
///
/// Make sure the page count is correct. If the number is lower than the actual amount, the code will panic at some point.
///
/// The number of key slots can be lower than the total amount of possible keys used, but this will lower
/// the chance of a cache hit.
/// The keys are cached in a fifo and any time its location is updated in cache it's added to the front.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct KeyPointerCache<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> {
    dirt_tracker: DirtTracker,
    page_states: [Option<PageState>; PAGE_COUNT],
    after_erased_pointers: [Option<NonZeroU32>; PAGE_COUNT],
    after_written_pointers: [Option<NonZeroU32>; PAGE_COUNT],
    key_pointers: [Option<(KEY, NonZeroU32)>; KEYS],
}

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> KeyPointerCache<PAGE_COUNT, KEY, KEYS> {
    /// Construct a new instance
    #[must_use]
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: [None; PAGE_COUNT],
            after_erased_pointers: [None; PAGE_COUNT],
            after_written_pointers: [None; PAGE_COUNT],
            key_pointers: [const { None }; KEYS],
        }
    }
}

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> Default
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> PrivateCacheImpl
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
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

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> CacheImpl
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
}
impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> KeyCacheImpl<KEY>
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
}

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> Invalidate
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states().invalidate_cache_state();
        self.page_pointers().invalidate_cache_state();
        self.key_pointers().invalidate_cache_state();
    }
}

impl<const PAGE_COUNT: usize, KEY: Key, const KEYS: usize> PrivateKeyCacheImpl<KEY>
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    type KPC<'a>
        = CachedKeyPointers<'a, KEY>
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_> {
        CachedKeyPointers::new(&mut self.key_pointers)
    }
}
