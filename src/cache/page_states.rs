use core::fmt::Debug;

use crate::PageState;

pub(crate) trait PageStatesCache: Debug {
    fn get_page_state(&self, page_index: usize) -> Option<PageState>;
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub(crate) struct CachedPageStates<const PAGE_COUNT: usize> {
    pages: [Option<PageState>; PAGE_COUNT],
}

impl<const PAGE_COUNT: usize> Debug for CachedPageStates<PAGE_COUNT> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for (i, val) in self.pages.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }

            if let Some(val) = val {
                write!(f, "{val:?}")?;
            } else {
                write!(f, "?")?;
            }
        }
        write!(f, "]")?;

        Ok(())
    }
}

impl<const PAGE_COUNT: usize> CachedPageStates<PAGE_COUNT> {
    pub const fn new() -> Self {
        Self {
            pages: [None; PAGE_COUNT],
        }
    }
}

impl<const PAGE_COUNT: usize> PageStatesCache for CachedPageStates<PAGE_COUNT> {
    fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        self.pages[page_index]
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        self.pages[page_index] = Some(new_state);
    }

    fn invalidate_cache_state(&mut self) {
        *self = Self::new();
    }
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub(crate) struct UncachedPageStates;

impl PageStatesCache for UncachedPageStates {
    fn get_page_state(&self, _page_index: usize) -> Option<PageState> {
        None
    }

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {}

    fn invalidate_cache_state(&mut self) {}
}
