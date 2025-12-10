use core::fmt::Debug;

use crate::PageState;

pub(crate) trait PageStatesCache: Debug {
    fn get_page_state(&self, page_index: usize) -> Option<PageState>;
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CachedPageStates<'a> {
    pages: &'a mut [Option<PageState>],
}

impl Debug for CachedPageStates<'_> {
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

impl<'a> CachedPageStates<'a> {
    pub const fn new(pages: &'a mut [Option<PageState>]) -> Self {
        Self { pages }
    }
}

impl PageStatesCache for CachedPageStates<'_> {
    fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        self.pages.get(page_index).copied().flatten()
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        if let Some(page_state) = self.pages.get_mut(page_index) {
            *page_state = Some(new_state);
        }
    }

    fn invalidate_cache_state(&mut self) {
        for page in self.pages.iter_mut() {
            *page = None;
        }
    }
}

#[derive(Debug, Default)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct UncachedPageStates;

impl PageStatesCache for UncachedPageStates {
    fn get_page_state(&self, _page_index: usize) -> Option<PageState> {
        None
    }

    fn notice_page_state(&mut self, _page_index: usize, _new_state: PageState) {}

    fn invalidate_cache_state(&mut self) {}
}
