//! Module implementing all things cache related

use core::{fmt::Debug, ops::Range};

use embedded_storage_async::nor_flash::NorFlash;

use crate::{PageState, item::ItemHeader, map::Key};

use self::{
    key_pointers::{KeyPointersCache, UncachedKeyPointers},
    page_pointers::UncachedPagePointers,
    page_states::UncachedPageStates,
};

pub(crate) mod array_impl;
#[cfg(feature = "alloc")]
pub(crate) mod heap_impl;
pub(crate) mod key_pointers;
pub(crate) mod page_pointers;
pub(crate) mod page_states;

mod tests;

pub use array_impl::*;
#[cfg(feature = "alloc")]
pub use heap_impl::*;
pub(crate) use page_pointers::PagePointersCache;
pub(crate) use page_states::PageStatesCache;

/// Trait implemented by all cache types
#[allow(private_bounds)]
pub trait CacheImpl: PrivateCacheImpl {}

/// Trait implemented by all cache types that know about keys
#[allow(private_bounds)]
pub trait KeyCacheImpl<KEY: Key>: CacheImpl + PrivateKeyCacheImpl<KEY> {}

pub(crate) trait Invalidate {
    fn invalidate_cache_state(&mut self);
}

pub(crate) trait PrivateCacheImpl: Invalidate {
    type PSC<'a>: PageStatesCache
    where
        Self: 'a;
    type PPC<'a>: PagePointersCache
    where
        Self: 'a;

    fn dirt_tracker<R>(&mut self, f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R>;
    fn page_states(&mut self) -> Self::PSC<'_>;
    fn page_pointers(&mut self) -> Self::PPC<'_>;

    /// True if the cache might be inconsistent
    fn is_dirty(&mut self) -> bool {
        self.dirt_tracker(|d| d.is_dirty()).unwrap_or_default()
    }

    /// Mark the cache as potentially inconsistent with reality
    fn mark_dirty(&mut self) {
        self.dirt_tracker(DirtTracker::mark_dirty);
    }

    /// Mark the cache as being consistent with reality
    fn unmark_dirty(&mut self) {
        self.dirt_tracker(DirtTracker::unmark_dirty);
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
            .notice_item_written::<S>(flash_range, item_address, item_header);
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
            .notice_item_erased::<S>(flash_range, item_address, item_header);
    }
}

pub(crate) trait PrivateKeyCacheImpl<KEY: Key>: PrivateCacheImpl {
    type KPC<'a>: KeyPointersCache<KEY>
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_>;

    fn key_location(&mut self, key: &KEY) -> Option<u32> {
        self.key_pointers().key_location(key)
    }

    fn notice_key_location(&mut self, key: &KEY, item_address: u32, dirty: bool) {
        if dirty {
            self.mark_dirty();
        }
        self.key_pointers().notice_key_location(key, item_address);
    }
    #[allow(unused)]
    fn notice_key_erased(&mut self, key: &KEY) {
        self.mark_dirty();
        self.key_pointers().notice_key_erased(key);
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
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
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct NoCache;

impl NoCache {
    /// Construct a new instance
    #[must_use]
    pub const fn new() -> Self {
        Self
    }
}

impl Default for NoCache {
    fn default() -> Self {
        Self::new()
    }
}

impl PrivateCacheImpl for NoCache {
    type PSC<'a>
        = UncachedPageStates
    where
        Self: 'a;
    type PPC<'a>
        = UncachedPagePointers
    where
        Self: 'a;

    fn dirt_tracker<R>(&mut self, _f: impl FnOnce(&mut DirtTracker) -> R) -> Option<R> {
        // We have no state, so no need to track dirtyness
        None
    }

    fn page_states(&mut self) -> Self::PSC<'_> {
        UncachedPageStates
    }

    fn page_pointers(&mut self) -> Self::PPC<'_> {
        UncachedPagePointers
    }
}

impl CacheImpl for NoCache {}
impl<KEY: Key> KeyCacheImpl<KEY> for NoCache {}

impl Invalidate for NoCache {
    fn invalidate_cache_state(&mut self) {}
}

impl<KEY: Key> PrivateKeyCacheImpl<KEY> for NoCache {
    type KPC<'a>
        = UncachedKeyPointers
    where
        Self: 'a;

    fn key_pointers(&mut self) -> Self::KPC<'_> {
        UncachedKeyPointers
    }
}
