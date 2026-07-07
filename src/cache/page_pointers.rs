//! Implementation of page pointer caching

#[cfg(feature = "alloc")]
extern crate alloc;

use core::{fmt::Debug, num::NonZeroU32, ops::Range};

use embedded_storage_async::nor_flash::NorFlash;

use crate::{
    NorFlashExt, PageState, calculate_page_address, calculate_page_index, item::ItemHeader,
};

pub(crate) trait SealedPagePointersCache {
    fn first_item_after_erased(&self, page_index: usize) -> Option<u32>;
    fn first_item_after_written(&self, page_index: usize) -> Option<u32>;

    fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    );
    fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    );

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

/// A cache that caches which parts of the pages are written to already
#[allow(private_bounds)]
pub trait PagePointersCache: SealedPagePointersCache {}

/// A cache that stores page pointers in an array.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ArrayPagePointers<const PAGE_COUNT: usize> {
    after_erased_pointers: [Option<NonZeroU32>; PAGE_COUNT],
    after_written_pointers: [Option<NonZeroU32>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> ArrayPagePointers<PAGE_COUNT> {
    /// Create a new empty cache
    pub const fn new() -> Self {
        Self {
            after_erased_pointers: [None; _],
            after_written_pointers: [None; _],
        }
    }

    fn as_tracked_mut(&mut self) -> TrackedPagePointers<'_> {
        TrackedPagePointers {
            after_erased_pointers: &mut self.after_erased_pointers,
            after_written_pointers: &mut self.after_written_pointers,
        }
    }
}

impl<const PAGE_COUNT: usize> Default for ArrayPagePointers<PAGE_COUNT> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const PAGE_COUNT: usize> SealedPagePointersCache for ArrayPagePointers<PAGE_COUNT> {
    fn first_item_after_erased(&self, page_index: usize) -> Option<u32> {
        self.after_erased_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn first_item_after_written(&self, page_index: usize) -> Option<u32> {
        self.after_written_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.as_tracked_mut()
            .notice_item_written::<S>(flash_range, item_address, item_header);
    }

    fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.as_tracked_mut()
            .notice_item_erased::<S>(flash_range, item_address, item_header);
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.as_tracked_mut()
            .notice_page_state(page_index, new_state);
    }

    fn invalidate_cache_state(&mut self) {
        self.as_tracked_mut().invalidate_cache_state();
    }
}
impl<const PAGE_COUNT: usize> PagePointersCache for ArrayPagePointers<PAGE_COUNT> {}

#[cfg(feature = "alloc")]
/// A cache that stores page pointers in a vec.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct HeapPagePointers {
    after_erased_pointers: alloc::vec::Vec<Option<NonZeroU32>>,
    after_written_pointers: alloc::vec::Vec<Option<NonZeroU32>>,
}

#[cfg(feature = "alloc")]
impl HeapPagePointers {
    /// Create a new empty cache
    pub fn new(page_count: usize) -> Self {
        Self {
            after_erased_pointers: alloc::vec![None; page_count],
            after_written_pointers: alloc::vec![None; page_count],
        }
    }

    fn as_tracked(&mut self) -> TrackedPagePointers<'_> {
        TrackedPagePointers {
            after_erased_pointers: &mut self.after_erased_pointers,
            after_written_pointers: &mut self.after_written_pointers,
        }
    }
}

#[cfg(feature = "alloc")]
impl SealedPagePointersCache for HeapPagePointers {
    fn first_item_after_erased(&self, page_index: usize) -> Option<u32> {
        self.after_erased_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn first_item_after_written(&self, page_index: usize) -> Option<u32> {
        self.after_written_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.as_tracked()
            .notice_item_written::<S>(flash_range, item_address, item_header);
    }

    fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        self.as_tracked()
            .notice_item_erased::<S>(flash_range, item_address, item_header);
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.as_tracked().notice_page_state(page_index, new_state);
    }

    fn invalidate_cache_state(&mut self) {
        self.as_tracked().invalidate_cache_state();
    }
}
#[cfg(feature = "alloc")]
impl PagePointersCache for HeapPagePointers {}

// Use NonZeroU32 because we never store 0's in here (because of the first page marker)
// and so Option can make use of the niche so we save bytes
pub(crate) struct TrackedPagePointers<'a> {
    after_erased_pointers: &'a mut [Option<NonZeroU32>],
    after_written_pointers: &'a mut [Option<NonZeroU32>],
}

impl SealedPagePointersCache for TrackedPagePointers<'_> {
    fn first_item_after_erased(&self, page_index: usize) -> Option<u32> {
        self.after_erased_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn first_item_after_written(&self, page_index: usize) -> Option<u32> {
        self.after_written_pointers
            .get(page_index)
            .copied()
            .flatten()
            .map(NonZeroU32::get)
    }

    fn notice_item_written<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        let page_index = calculate_page_index::<S>(flash_range, item_address);

        let next_item_address = item_header.next_item_address::<S>(item_address);

        // We only care about the furthest written item, so discard if this is an earlier item
        if let Some(first_item_after_written) = self.first_item_after_written(page_index) {
            if next_item_address <= first_item_after_written {
                return;
            }
        }

        if let Some(after_written_pointer) = self.after_written_pointers.get_mut(page_index) {
            *after_written_pointer = NonZeroU32::new(next_item_address);
        }
    }

    fn notice_item_erased<S: NorFlash>(
        &mut self,
        flash_range: Range<u32>,
        item_address: u32,
        item_header: &ItemHeader,
    ) {
        let page_index = calculate_page_index::<S>(flash_range.clone(), item_address);

        // Either the item we point to or the first item on the page
        let next_unerased_item = self.first_item_after_erased(page_index).unwrap_or_else(|| {
            calculate_page_address::<S>(flash_range, page_index) + S::WORD_SIZE as u32
        });

        if item_address == next_unerased_item {
            if let Some(after_erased_pointer) = self.after_erased_pointers.get_mut(page_index) {
                *after_erased_pointer =
                    NonZeroU32::new(item_header.next_item_address::<S>(item_address));
            }
        }
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        if new_state.is_open() {
            // This page was erased
            if let Some(after_erased_pointer) = self.after_erased_pointers.get_mut(page_index) {
                *after_erased_pointer = None;
            }
            if let Some(after_written_pointer) = self.after_written_pointers.get_mut(page_index) {
                *after_written_pointer = None;
            }
        }
    }

    fn invalidate_cache_state(&mut self) {
        for pointers in self.after_erased_pointers.iter_mut() {
            *pointers = None;
        }
        for pointers in self.after_written_pointers.iter_mut() {
            *pointers = None;
        }
    }
}
