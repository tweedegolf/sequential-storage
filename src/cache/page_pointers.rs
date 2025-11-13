use core::{fmt::Debug, num::NonZeroU32, ops::Range};

use embedded_storage_async::nor_flash::NorFlash;

use crate::{
    NorFlashExt, PageState, calculate_page_address, calculate_page_index, item::ItemHeader,
};

use super::list::List;

pub(crate) trait PagePointersCache: Debug {
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

// Use NoneZeroU32 because we never store 0's in here (because of the first page marker)
// and so Option can make use of the niche so we save bytes
#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub(crate) struct CachedPagePointers<const PAGE_COUNT: usize> {
    after_erased_pointers: List<Option<NonZeroU32>, PAGE_COUNT>,
    after_written_pointers: List<Option<NonZeroU32>, PAGE_COUNT>,
}

impl<const PAGE_COUNT: usize> Debug for CachedPagePointers<PAGE_COUNT> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{{ after_erased_pointers: [")?;
        for (i, val) in self.after_erased_pointers.as_slice().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            if let Some(val) = val {
                write!(f, "{:?}", val.get())?;
            } else {
                write!(f, "?")?;
            }
        }
        write!(f, "], after_written_pointers: [")?;
        for (i, val) in self.after_written_pointers.as_slice().iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            if let Some(val) = val {
                write!(f, "{:?}", val.get())?;
            } else {
                write!(f, "?")?;
            }
        }
        write!(f, "] }}")?;

        Ok(())
    }
}

impl<const PAGE_COUNT: usize> CachedPagePointers<PAGE_COUNT> {
    pub const fn new() -> Self {
        Self {
            after_erased_pointers: List::from_elem_arr(None),
            after_written_pointers: List::from_elem_arr(None),
        }
    }

    #[cfg(feature = "alloc")]
    pub fn new_heap(n: usize) -> Self {
        Self {
            after_erased_pointers: List::from_elem_vec(None, n),
            after_written_pointers: List::from_elem_vec(None, n),
        }
    }
}

impl<const PAGE_COUNT: usize> PagePointersCache for CachedPagePointers<PAGE_COUNT> {
    fn first_item_after_erased(&self, page_index: usize) -> Option<u32> {
        self.after_erased_pointers[page_index].map(|val| val.get())
    }

    fn first_item_after_written(&self, page_index: usize) -> Option<u32> {
        self.after_written_pointers[page_index].map(|val| val.get())
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

        self.after_written_pointers[page_index] = NonZeroU32::new(next_item_address);
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
            self.after_erased_pointers[page_index] =
                NonZeroU32::new(item_header.next_item_address::<S>(item_address));
        }
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        if new_state.is_open() {
            // This page was erased
            self.after_erased_pointers[page_index] = None;
            self.after_written_pointers[page_index] = None;
        }
    }

    fn invalidate_cache_state(&mut self) {
        self.after_erased_pointers.as_mut_slice().fill(None);
        self.after_written_pointers.as_mut_slice().fill(None);
    }
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub(crate) struct UncachedPagePointers;

impl PagePointersCache for UncachedPagePointers {
    fn first_item_after_erased(&self, _page_index: usize) -> Option<u32> {
        None
    }

    fn first_item_after_written(&self, _page_index: usize) -> Option<u32> {
        None
    }

    fn notice_item_written<S: NorFlash>(
        &mut self,
        _flash_range: Range<u32>,
        _item_address: u32,
        _item_header: &ItemHeader,
    ) {
    }

    fn notice_item_erased<S: NorFlash>(
        &mut self,
        _flash_range: Range<u32>,
        _item_address: u32,
        _item_header: &ItemHeader,
    ) {
    }

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {}

    fn invalidate_cache_state(&mut self) {}
}
