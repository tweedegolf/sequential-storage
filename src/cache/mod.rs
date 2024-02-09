//! Module implementing all things cache related

use core::{fmt::Debug, ops::Range};

use embedded_storage_async::nor_flash::NorFlash;

use crate::{item::ItemHeader, PageState};

use self::{
    key_pointers::{CachedKeyPointers, KeyPointersCache, UncachedKeyPointers},
    page_pointers::{CachedPagePointers, UncachedPagePointers},
    page_states::{CachedPageStates, UncachedPageStates},
};

pub(crate) mod key_pointers;
pub(crate) mod page_pointers;
pub(crate) mod page_states;
mod tests;

pub(crate) use page_pointers::PagePointersCache;
pub(crate) use page_states::PageStatesCache;

/// Trait implemented by all cache types
#[allow(private_bounds)]
pub trait CacheImpl: PrivateCacheImpl {}
impl<T: CacheImpl> CacheImpl for &mut T {}
/// Trait implemented by all cache types that know about keys
#[allow(private_bounds)]
pub trait KeyCacheImpl<KEY: Eq>: CacheImpl + PrivateKeyCacheImpl<KEY> {}
impl<KEY: Eq, T: KeyCacheImpl<KEY>> KeyCacheImpl<KEY> for &mut T {}

pub(crate) trait Invalidate {
    fn invalidate_cache_state(&mut self);
}

impl<T: Invalidate> Invalidate for &mut T {
    fn invalidate_cache_state(&mut self) {
        T::invalidate_cache_state(self)
    }
}

pub(crate) trait PrivateCacheImpl: Invalidate {
    type PSC: PageStatesCache;
    type PPC: PagePointersCache;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R>;
    fn page_states(&mut self) -> &mut Self::PSC;
    fn page_pointers(&mut self) -> &mut Self::PPC;

    /// True if the cache might be inconsistent
    fn is_dirty(&mut self) -> bool {
        self.dirt_tracker(|d| d.is_dirty()).unwrap_or_default()
    }

    /// Mark the cache as potentially inconsistent with reality
    fn mark_dirty(&mut self) {
        self.dirt_tracker(|d| d.mark_dirty());
    }

    /// Mark the cache as being consistent with reality
    fn unmark_dirty(&mut self) {
        self.dirt_tracker(|d| d.unmark_dirty());
    }

    /// Get the cache state of the requested page
    fn get_page_state(&mut self, page_index: usize) -> Option<PageState> {
        self.page_states().get_page_state(page_index)
    }

    /// Let the cache know a page state changed
    ///
    /// The dirty flag should be true if the page state is actually going to be changed.
    /// Keep it false if we're only discovering the state.
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState, dirty: bool) {
        if dirty {
            self.mark_dirty();
        }
        self.page_states().notice_page_state(page_index, new_state);
        self.page_pointers()
            .notice_page_state(page_index, new_state);
    }

    /// Get the cached address of the first non-erased item in the requested page.
    ///
    /// This is purely for the items that get erased from start to end.
    fn first_item_after_erased(&mut self, page_index: usize) -> Option<u32> {
        self.page_pointers().first_item_after_erased(page_index)
    }

    /// Get the cached address of the first free unwritten item in the requested page.
    fn first_item_after_written(&mut self, page_index: usize) -> Option<u32> {
        self.page_pointers().first_item_after_written(page_index)
    }

    /// Let the cache know that an item has been written to flash
    fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.mark_dirty();
        self.page_pointers()
            .notice_item_written::<S>(flash_range, item_address, item_header)
    }

    /// Let the cache know that an item has been erased from flash
    fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.mark_dirty();
        self.page_pointers()
            .notice_item_erased::<S>(flash_range, item_address, item_header)
    }
}

impl<T: PrivateCacheImpl> PrivateCacheImpl for &mut T {
    type PSC = T::PSC;
    type PPC = T::PPC;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        T::dirt_tracker(self, f)
    }

    fn page_states(&mut self) -> &mut Self::PSC {
        T::page_states(self)
    }

    fn page_pointers(&mut self) -> &mut Self::PPC {
        T::page_pointers(self)
    }
}

pub(crate) trait PrivateKeyCacheImpl<KEY: Eq>: PrivateCacheImpl {
    type KPC: KeyPointersCache<KEY>;

    fn key_pointers(&mut self) -> &mut Self::KPC;

    fn key_location(&mut self, key: &KEY) -> Option<u32> {
        self.key_pointers().key_location(key)
    }

    fn notice_key_location(&mut self, key: KEY, item_address: u32, dirty: bool) {
        if dirty {
            self.mark_dirty();
        }
        self.key_pointers().notice_key_location(key, item_address)
    }
    #[allow(unused)]
    fn notice_key_erased(&mut self, key: &KEY) {
        self.mark_dirty();
        self.key_pointers().notice_key_erased(key)
    }
}

impl<KEY: Eq, T: PrivateKeyCacheImpl<KEY>> PrivateKeyCacheImpl<KEY> for &mut T {
    type KPC = T::KPC;

    fn key_pointers(&mut self) -> &mut Self::KPC {
        T::key_pointers(self)
    }
}

#[derive(Debug)]
pub(crate) struct DirtTracker {
    /// Managed from the library code.
    ///
    /// When true, the cache and/or flash has changed and things might not be fully
    /// consistent if there's an early return due to error.
    dirty: bool,
}

impl DirtTracker {
    pub const fn new() -> Self {
        DirtTracker { dirty: false }
    }

    /// True if the cache might be inconsistent
    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Mark the cache as potentially inconsistent with reality
    pub fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Mark the cache as being consistent with reality
    pub fn unmark_dirty(&mut self) {
        self.dirty = false;
    }
}

/// A cache object implementing no cache.
///
/// This type of cache doesn't have to be kept around and may be constructed on every api call.
/// You could simply pass `&mut NoCache::new()` every time.
#[derive(Debug)]
pub struct NoCache {
    page_states: UncachedPageStates,
    page_pointers: UncachedPagePointers,
    key_pointers: UncachedKeyPointers,
}

impl NoCache {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self {
            page_states: UncachedPageStates,
            page_pointers: UncachedPagePointers,
            key_pointers: UncachedKeyPointers,
        }
    }
}

impl PrivateCacheImpl for NoCache {
    type PSC = UncachedPageStates;
    type PPC = UncachedPagePointers;

    fn dirt_tracker<R>(&mut self, _f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        // We have no state, so no need to track dirtyness
        None
    }

    fn page_states(&mut self) -> &mut Self::PSC {
        &mut self.page_states
    }

    fn page_pointers(&mut self) -> &mut Self::PPC {
        &mut self.page_pointers
    }
}

impl CacheImpl for NoCache {}
impl<KEY: Eq> KeyCacheImpl<KEY> for NoCache {}

impl Invalidate for NoCache {
    fn invalidate_cache_state(&mut self) {}
}

impl<KEY: Eq> PrivateKeyCacheImpl<KEY> for NoCache {
    type KPC = UncachedKeyPointers;

    fn key_pointers(&mut self) -> &mut Self::KPC {
        &mut self.key_pointers
    }
}

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
pub struct PageStateCache<const PAGE_COUNT: usize> {
    dirt_tracker: DirtTracker,
    page_states: CachedPageStates<PAGE_COUNT>,
    page_pointers: UncachedPagePointers,
    key_pointers: UncachedKeyPointers,
}

impl<const PAGE_COUNT: usize> PageStateCache<PAGE_COUNT> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: CachedPageStates::new(),
            page_pointers: UncachedPagePointers,
            key_pointers: UncachedKeyPointers,
        }
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PageStateCache<PAGE_COUNT> {
    type PSC = CachedPageStates<PAGE_COUNT>;
    type PPC = UncachedPagePointers;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> &mut Self::PSC {
        &mut self.page_states
    }

    fn page_pointers(&mut self) -> &mut Self::PPC {
        &mut self.page_pointers
    }
}

impl<const PAGE_COUNT: usize> CacheImpl for PageStateCache<PAGE_COUNT> {}
impl<KEY: Eq, const PAGE_COUNT: usize> KeyCacheImpl<KEY> for PageStateCache<PAGE_COUNT> {}

impl<const PAGE_COUNT: usize> Invalidate for PageStateCache<PAGE_COUNT> {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states.invalidate_cache_state();
        self.page_pointers.invalidate_cache_state();
    }
}

impl<KEY: Eq, const PAGE_COUNT: usize> PrivateKeyCacheImpl<KEY> for PageStateCache<PAGE_COUNT> {
    type KPC = UncachedKeyPointers;

    fn key_pointers(&mut self) -> &mut Self::KPC {
        &mut self.key_pointers
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
pub struct PagePointerCache<const PAGE_COUNT: usize> {
    dirt_tracker: DirtTracker,
    page_states: CachedPageStates<PAGE_COUNT>,
    page_pointers: CachedPagePointers<PAGE_COUNT>,
    key_pointers: UncachedKeyPointers,
}

impl<const PAGE_COUNT: usize> PagePointerCache<PAGE_COUNT> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: CachedPageStates::new(),
            page_pointers: CachedPagePointers::new(),
            key_pointers: UncachedKeyPointers,
        }
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PagePointerCache<PAGE_COUNT> {
    type PSC = CachedPageStates<PAGE_COUNT>;
    type PPC = CachedPagePointers<PAGE_COUNT>;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> &mut Self::PSC {
        &mut self.page_states
    }

    fn page_pointers(&mut self) -> &mut Self::PPC {
        &mut self.page_pointers
    }
}

impl<const PAGE_COUNT: usize> CacheImpl for PagePointerCache<PAGE_COUNT> {}
impl<KEY: Eq, const PAGE_COUNT: usize> KeyCacheImpl<KEY> for PagePointerCache<PAGE_COUNT> {}

impl<const PAGE_COUNT: usize> Invalidate for PagePointerCache<PAGE_COUNT> {
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states.invalidate_cache_state();
        self.page_pointers.invalidate_cache_state();
    }
}

impl<KEY: Eq, const PAGE_COUNT: usize> PrivateKeyCacheImpl<KEY> for PagePointerCache<PAGE_COUNT> {
    type KPC = UncachedKeyPointers;

    fn key_pointers(&mut self) -> &mut Self::KPC {
        &mut self.key_pointers
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
pub struct KeyPointerCache<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> {
    dirt_tracker: DirtTracker,
    page_states: CachedPageStates<PAGE_COUNT>,
    page_pointers: CachedPagePointers<PAGE_COUNT>,
    key_pointers: CachedKeyPointers<KEY, KEYS>,
}

impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> KeyPointerCache<PAGE_COUNT, KEY, KEYS> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self {
            dirt_tracker: DirtTracker::new(),
            page_states: CachedPageStates::new(),
            page_pointers: CachedPagePointers::new(),
            key_pointers: CachedKeyPointers::new(),
        }
    }
}

impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> PrivateCacheImpl
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    type PSC = CachedPageStates<PAGE_COUNT>;
    type PPC = CachedPagePointers<PAGE_COUNT>;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        Some(f(&mut self.dirt_tracker))
    }

    fn page_states(&mut self) -> &mut Self::PSC {
        &mut self.page_states
    }

    fn page_pointers(&mut self) -> &mut Self::PPC {
        &mut self.page_pointers
    }
}

impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> CacheImpl
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
}
impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> KeyCacheImpl<KEY>
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
}

impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> Invalidate
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    fn invalidate_cache_state(&mut self) {
        self.dirt_tracker.unmark_dirty();
        self.page_states.invalidate_cache_state();
        self.page_pointers.invalidate_cache_state();
        self.key_pointers.invalidate_cache_state();
    }
}

impl<const PAGE_COUNT: usize, KEY: Eq, const KEYS: usize> PrivateKeyCacheImpl<KEY>
    for KeyPointerCache<PAGE_COUNT, KEY, KEYS>
{
    type KPC = CachedKeyPointers<KEY, KEYS>;

    fn key_pointers(&mut self) -> &mut Self::KPC {
        &mut self.key_pointers
    }
}
