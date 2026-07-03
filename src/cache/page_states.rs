use core::fmt::Debug;

use crate::PageState;

pub(crate) trait PageStatesCache: Debug {
    fn get_page_state(&self, page_index: usize) -> Option<PageState>;
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
#[derive(Debug)]
struct WrappingRange {
    start: usize,
    end: usize,
}

impl WrappingRange {
    const fn new() -> Self {
        Self { start: 0, end: 0 }
    }

    fn contains(&self, page_index: usize) -> bool {
        if self.start == self.end {
            true
        } else if self.end > self.start {
            page_index >= self.start && page_index < self.end
        } else {
            page_index >= self.start || page_index < self.end
        }
    }

    fn set_start_wrapped(&mut self, start: usize, page_count: usize) {
        self.start = start % page_count;
    }
    fn set_end_wrapped(&mut self, end: usize, page_count: usize) {
        self.end = end % page_count;
    }
}

#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CachedPageStates {
    page_count: usize,
    partial_open_page: Option<usize>,
    closed_pages: Option<WrappingRange>,
    open_pages: Option<WrappingRange>,
}

impl Debug for CachedPageStates {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "[")?;
        for i in 0..self.page_count {
            write!(
                f,
                "{}{i}: {:?}",
                if i == 0 { "" } else { ", " },
                self.get_page_state(i)
            )?;
        }
        write!(f, "]")?;

        Ok(())
    }
}

impl CachedPageStates {
    pub const fn new(page_count: usize) -> Self {
        Self {
            page_count,
            partial_open_page: None,
            closed_pages: None,
            open_pages: None,
        }
    }

    fn fill_gaps(&mut self) {
        if let Some(partial_open_page) = self.partial_open_page {
            if let Some(closed_pages) = self.closed_pages.as_mut() {
                closed_pages.end = partial_open_page;
            }
            if let Some(open_pages) = self.open_pages.as_mut() {
                open_pages.set_start_wrapped(partial_open_page + 1, self.page_count);
            }
        }
    }
}

impl PageStatesCache for CachedPageStates {
    fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        if let Some(closed_pages) = self.closed_pages.as_ref()
            && closed_pages.contains(page_index)
        {
            Some(PageState::Closed)
        } else if Some(page_index) == self.partial_open_page {
            Some(PageState::PartialOpen)
        } else if let Some(open_pages) = self.open_pages.as_ref()
            && open_pages.contains(page_index)
        {
            Some(PageState::Open)
        } else {
            None
        }
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        #[cfg(fuzzing)]
        eprintln!("Noticing page state: {page_index} -> {new_state:?}");
        #[cfg(fuzzing)]
        eprintln!("{self:?}");

        match new_state {
            PageState::Closed => {
                match self.closed_pages.as_mut() {
                    None => {
                        let closed_pages = self.closed_pages.insert(WrappingRange::new());
                        closed_pages.start = page_index;
                        closed_pages.set_end_wrapped(page_index + 1, self.page_count);
                    }
                    Some(closed_pages) => {
                        if page_index == closed_pages.end {
                            closed_pages.set_end_wrapped(page_index + 1, self.page_count);
                        } else if closed_pages.contains(page_index) {
                            // Ignore
                        } else {
                            closed_pages.start = page_index;
                        }
                    }
                }

                if self.partial_open_page == Some(page_index) {
                    self.partial_open_page = None;
                } else if let Some(open_pages) = self.open_pages.as_mut()
                    && page_index == open_pages.start
                {
                    open_pages.set_start_wrapped(page_index + 1, self.page_count);
                    if open_pages.start == open_pages.end {
                        self.open_pages = None;
                    }
                }
            }
            PageState::PartialOpen => {
                self.partial_open_page = Some(page_index);

                if let Some(open_pages) = self.open_pages.as_mut()
                    && open_pages.start == page_index
                {
                    open_pages.set_start_wrapped(page_index + 1, self.page_count);
                    if open_pages.start == open_pages.end {
                        self.open_pages = None;
                    }
                }
            }
            PageState::Open => {
                match self.open_pages.as_mut() {
                    None => {
                        let open_pages = self.open_pages.insert(WrappingRange::new());
                        open_pages.start = page_index;
                        open_pages.set_end_wrapped(page_index + 1, self.page_count);
                    }
                    Some(open_pages) => {
                        if page_index == open_pages.end {
                            open_pages.set_end_wrapped(page_index + 1, self.page_count);
                        } else if open_pages.contains(page_index) {
                            // Ignore
                        } else {
                            open_pages.start = page_index;
                        }
                    }
                }

                if self.partial_open_page == Some(page_index) {
                    self.partial_open_page = None;
                } else if let Some(closed_pages) = self.closed_pages.as_mut()
                    && page_index == closed_pages.start
                {
                    closed_pages.set_start_wrapped(page_index + 1, self.page_count);
                    if closed_pages.start == closed_pages.end {
                        self.closed_pages = None;
                    }
                }
            }
        }

        self.fill_gaps();

        #[cfg(fuzzing)]
        eprintln!("Afterwards {self:?}");
    }

    fn invalidate_cache_state(&mut self) {
        *self = Self {
            page_count: self.page_count,
            ..Self::new(0)
        };
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn page_states_correct_from_erased() {
        let mut page_states = CachedPageStates::new(4);

        assert_eq!(page_states.get_page_state(0), None);
        assert_eq!(page_states.get_page_state(1), None);
        assert_eq!(page_states.get_page_state(2), None);
        assert_eq!(page_states.get_page_state(3), None);

        page_states.notice_page_state(0, PageState::Open);
        page_states.notice_page_state(1, PageState::Open);
        page_states.notice_page_state(2, PageState::Open);
        page_states.notice_page_state(3, PageState::Open);

        assert_eq!(page_states.get_page_state(0), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(1), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));

        page_states.notice_page_state(0, PageState::PartialOpen);

        assert_eq!(page_states.get_page_state(0), Some(PageState::PartialOpen));
        assert_eq!(page_states.get_page_state(1), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));

        page_states.notice_page_state(0, PageState::Closed);

        assert_eq!(page_states.get_page_state(0), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(1), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));

        page_states.notice_page_state(1, PageState::PartialOpen);

        assert_eq!(page_states.get_page_state(0), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(1), Some(PageState::PartialOpen));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));

        page_states.notice_page_state(0, PageState::Open);

        assert_eq!(page_states.get_page_state(0), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(1), Some(PageState::PartialOpen));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));
    }

    #[test]
    fn page_states_correct_from_recover() {
        let mut page_states = CachedPageStates::new(4);

        println!("{page_states:?}");
        page_states.notice_page_state(0, PageState::Open);
        println!("{page_states:?}");
        page_states.notice_page_state(1, PageState::Closed);
        println!("{page_states:?}");
        page_states.notice_page_state(2, PageState::PartialOpen);
        println!("{page_states:?}");
        page_states.notice_page_state(3, PageState::Open);
        println!("{page_states:?}");

        assert_eq!(page_states.get_page_state(0), Some(PageState::Open));
        assert_eq!(page_states.get_page_state(1), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(2), Some(PageState::PartialOpen));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));
    }
}
