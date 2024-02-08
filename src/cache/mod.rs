//! Module implementing all things cache related

use core::{fmt::Debug, ops::Range};

use embedded_storage_async::nor_flash::NorFlash;

use crate::{item::ItemHeader, PageState};

use self::{
    key_pointers::{KeyPointersCache, UncachedKeyPointers},
    page_pointers::{CachedPagePointers, UncachedPagePointers},
    page_states::{CachedPageStates, UncachedPageSates},
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

impl<PSC: PageStatesCache, PPC: PagePointersCache, KPC: KeyPointersCache> CacheImpl
    for Cache<PSC, PPC, KPC>
{
}

pub(crate) trait PrivateCacheImpl {
    type PSC: PageStatesCache;
    type PPC: PagePointersCache;
    type KEY: Eq;
    type KPC: KeyPointersCache<Key = Self::KEY>;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC>;
}

impl<T: PrivateCacheImpl> PrivateCacheImpl for &mut T {
    type PSC = T::PSC;
    type PPC = T::PPC;
    type KEY = T::KEY;
    type KPC = T::KPC;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC> {
        T::inner(self)
    }
}

impl<PSC: PageStatesCache, PPC: PagePointersCache, KPC: KeyPointersCache> PrivateCacheImpl
    for Cache<PSC, PPC, KPC>
{
    type PSC = PSC;
    type PPC = PPC;
    type KEY = KPC::Key;
    type KPC = KPC;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC> {
        self
    }
}

/// A cache object implementing no cache.
///
/// This type of cache doesn't have to be kept around and may be constructed on every api call.
/// You could simply pass `&mut NoCache::new()` every time.
#[derive(Debug)]
pub struct NoCache(Cache<UncachedPageSates, UncachedPagePointers, UncachedKeyPointers>);

impl NoCache {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self(Cache::new(
            UncachedPageSates,
            UncachedPagePointers,
            UncachedKeyPointers,
        ))
    }
}

impl PrivateCacheImpl for NoCache {
    type PSC = UncachedPageSates;
    type PPC = UncachedPagePointers;
    type KEY = ();
    type KPC = UncachedKeyPointers;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC> {
        &mut self.0
    }
}

impl CacheImpl for NoCache {}

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
pub struct PageStateCache<const PAGE_COUNT: usize>(
    Cache<CachedPageStates<PAGE_COUNT>, UncachedPagePointers, UncachedKeyPointers>,
);

impl<const PAGE_COUNT: usize> PageStateCache<PAGE_COUNT> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self(Cache::new(
            CachedPageStates::new(),
            UncachedPagePointers,
            UncachedKeyPointers,
        ))
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PageStateCache<PAGE_COUNT> {
    type PSC = CachedPageStates<PAGE_COUNT>;
    type PPC = UncachedPagePointers;
    type KEY = ();
    type KPC = UncachedKeyPointers;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC> {
        &mut self.0
    }
}

impl<const PAGE_COUNT: usize> CacheImpl for PageStateCache<PAGE_COUNT> {}

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
pub struct PagePointerCache<const PAGE_COUNT: usize>(
    Cache<CachedPageStates<PAGE_COUNT>, CachedPagePointers<PAGE_COUNT>, UncachedKeyPointers>,
);

impl<const PAGE_COUNT: usize> PagePointerCache<PAGE_COUNT> {
    /// Construct a new instance
    pub const fn new() -> Self {
        Self(Cache::new(
            CachedPageStates::new(),
            CachedPagePointers::new(),
            UncachedKeyPointers,
        ))
    }
}

impl<const PAGE_COUNT: usize> PrivateCacheImpl for PagePointerCache<PAGE_COUNT> {
    type PSC = CachedPageStates<PAGE_COUNT>;
    type PPC = CachedPagePointers<PAGE_COUNT>;
    type KEY = ();
    type KPC = UncachedKeyPointers;

    fn inner(&mut self) -> &mut Cache<Self::PSC, Self::PPC, Self::KPC> {
        &mut self.0
    }
}

impl<const PAGE_COUNT: usize> CacheImpl for PagePointerCache<PAGE_COUNT> {}

/// The cache struct that is behind it all.
///
/// It manages the cache state in a generic way. For every field it can be chosen to have it be cached or not.
#[derive(Debug)]
pub(crate) struct Cache<PSC: PageStatesCache, PPC: PagePointersCache, KPC: KeyPointersCache> {
    /// Managed from the library code.
    ///
    /// When true, the cache and/or flash has changed and things might not be fully
    /// consistent if there's an early return due to error.
    dirty: bool,
    page_states: PSC,
    page_pointers: PPC,
    key_pointers: KPC,
}

impl<PSC: PageStatesCache, PPC: PagePointersCache, KPC: KeyPointersCache> Cache<PSC, PPC, KPC> {
    pub(crate) const fn new(page_states: PSC, page_pointers: PPC, key_pointers: KPC) -> Self {
        Self {
            dirty: false,
            page_states,
            page_pointers,
            key_pointers,
        }
    }

    /// True if the cache might be inconsistent
    pub(crate) fn is_dirty(&self) -> bool {
        self.dirty
    }

    /// Mark the cache as potentially inconsistent with reality
    pub(crate) fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Mark the cache as being consistent with reality
    pub(crate) fn unmark_dirty(&mut self) {
        self.dirty = false;
    }

    /// Wipe the cache
    pub(crate) fn invalidate_cache_state(&mut self) {
        self.dirty = false;
        self.page_states.invalidate_cache_state();
        self.page_pointers.invalidate_cache_state();
        self.key_pointers.invalidate_cache_state();
    }

    /// Get the cache state of the requested page
    pub(crate) fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        self.page_states.get_page_state(page_index)
    }

    /// Let the cache know a page state changed
    ///
    /// The dirty flag should be true if the page state is actually going to be changed.
    /// Keep it false if we're only discovering the state.
    pub(crate) fn notice_page_state(
        &mut self,
        page_index: usize,
        new_state: PageState,
        dirty: bool,
    ) {
        if dirty {
            self.mark_dirty();
        }
        self.page_states.notice_page_state(page_index, new_state);
        self.page_pointers.notice_page_state(page_index, new_state);
    }

    /// Get the cached address of the first non-erased item in the requested page.
    ///
    /// This is purely for the items that get erased from start to end.
    pub(crate) fn first_item_after_erased(&self, page_index: usize) -> Option<u32> {
        self.page_pointers.first_item_after_erased(page_index)
    }

    /// Get the cached address of the first free unwritten item in the requested page.
    pub(crate) fn first_item_after_written(&self, page_index: usize) -> Option<u32> {
        self.page_pointers.first_item_after_written(page_index)
    }

    /// Let the cache know that an item has been written to flash
    pub(crate) fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.mark_dirty();
        self.page_pointers
            .notice_item_written::<S>(flash_range, item_address, item_header)
    }

    /// Let the cache know that an item has been erased from flash
    pub(crate) fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.mark_dirty();
        self.page_pointers
            .notice_item_erased::<S>(flash_range, item_address, item_header)
    }

    pub(crate) fn key_location(&self, key: &KPC::Key) -> Option<u32> {
        self.key_pointers.key_location(key)
    }

    pub(crate) fn notice_key_location(&mut self, key: KPC::Key, item_address: u32) {
        self.key_pointers.notice_key_location(key, item_address)
    }
    pub(crate) fn notice_key_erased(&mut self, key: &KPC::Key) {
        self.key_pointers.notice_key_erased(key)
    }
}
