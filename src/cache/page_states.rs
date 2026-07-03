use core::fmt::Debug;

use crate::PageState;

pub(crate) trait PageStatesCache: Debug {
    fn get_page_state(&self, page_index: usize) -> Option<PageState>;
    fn notice_page_state(&mut self, page_index: usize, new_state: PageState);
    fn invalidate_cache_state(&mut self);
}

/// A cache that uses knowledge about the typical layout of pages.
/// 
/// The layout is always as follows:
/// - X amount of closed pages
/// - Y amount of open pages
///   - Y is at least 1
///   - One of the open pages may be partial
/// - If a partial page is present, it's in the order ascending page indices: `Closed` -> `Partial` -> `Open`
/// 
/// The idea is to have an anchor which is the first open page (which may be the partial open page)
/// and then keep track of the amount of open pages in front and the amount of closed pages behind it.
/// 
/// We know the anchor for sure when we find a partial open page.
/// Since sequential-storage always iterates going forward and never back, we can have a 'guessed' anchor
/// if we find the first open page. But when the anchor is guessed, we need to be a little pessimistic.
/// 
/// Thus, this cache isn't able to remember every page state in every situation, but this is only the case when
/// the anchor hasn't been found yet. When the cache is fully warm, it does have perfect knowledge.
/// 
/// We don't have to care about corruption, because when corruption is repaired the cache is invalidated.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CachedPageStates {
    page_count: usize,
    anchor: Option<usize>,
    anchor_is_partial: bool,
    anchor_is_guess: bool,
    closed_pages: usize,
    open_pages: usize,
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
            anchor: None,
            anchor_is_partial: false,
            anchor_is_guess: true,
            closed_pages: 0,
            open_pages: 0,
        }
    }

    fn places_in_front_of_anchor(&self, page_index: usize) -> Option<usize> {
        let anchor = self.anchor?;

        if page_index >= anchor {
            Some(page_index - anchor)
        } else {
            Some(self.page_count - anchor + page_index)
        }
    }

    fn places_behind_of_anchor(&self, page_index: usize) -> Option<usize> {
        let anchor = self.anchor?;

        if page_index <= anchor {
            Some(anchor - page_index)
        } else {
            Some(anchor + 1 + self.page_count - page_index)
        }
    }
}

impl PageStatesCache for CachedPageStates {
    fn get_page_state(&self, page_index: usize) -> Option<PageState> {
        if self.anchor == Some(page_index) {
            if self.anchor_is_partial {
                Some(PageState::PartialOpen)
            } else {
                Some(PageState::Open)
            }
        } else if let Some(in_front) = self.places_in_front_of_anchor(page_index)
            && in_front < self.open_pages
        {
            Some(PageState::Open)
        } else if let Some(behind) = self.places_behind_of_anchor(page_index)
            && behind <= self.closed_pages
        {
            Some(PageState::Closed)
        } else {
            None
        }
    }

    fn notice_page_state(&mut self, page_index: usize, new_state: PageState) {
        #[cfg(fuzzing)]
        eprintln!("Noticing page state: {page_index} -> {new_state:?}");
        #[cfg(fuzzing)]
        eprintln!("Before {self:?}");

        match new_state {
            PageState::PartialOpen => {
                // What do we currently think it is?
                match self.get_page_state(page_index) {
                    Some(PageState::PartialOpen) => {
                        // We've rediscovered ourselves and that's great
                    }
                    Some(PageState::Open) => {
                        self.anchor = Some(page_index);
                        self.anchor_is_partial = true;
                    }
                    Some(PageState::Closed) => {
                        unreachable!("Can't partially open a closed page")
                    }
                    None => {
                        // Unknown, so we can just become the anchor
                        self.anchor = Some(page_index);
                        self.anchor_is_partial = true;
                        self.open_pages = 1;
                    }
                }

                self.anchor_is_guess = false;
            }
            PageState::Closed => {
                // What do we currently think it is?
                match self.get_page_state(page_index) {
                    Some(PageState::Closed) => {
                        // We've rediscovered ourselves and that's great
                    }
                    Some(PageState::PartialOpen) => {
                        let anchor = self.anchor.as_mut().unwrap();
                        // The anchor moves one up
                        self.closed_pages += 1;
                        self.open_pages -= 1;
                        *anchor = (*anchor + 1) % self.page_count;
                        self.anchor_is_partial = false;
                    }
                    Some(PageState::Open) => {
                        unreachable!("We never outright close a fully open page")
                    }
                    None => {
                        // If we know the anchor, we can know the minimum amount of closed pages we have
                        if !self.anchor_is_guess {
                            if let Some(behind) = self.places_behind_of_anchor(page_index) {
                                self.closed_pages = self.closed_pages.max(behind);
                            }
                        }
                    }
                }
            }
            PageState::Open => {
                // What do we currently think it is?
                match self.get_page_state(page_index) {
                    Some(PageState::Open) => {
                        // We've rediscovered ourselves and that's great
                    }
                    Some(PageState::PartialOpen) => {
                        // We're opening our anchor
                        self.anchor_is_partial = false;
                    }
                    Some(PageState::Closed) => {
                        if let Some(in_front) = self.places_in_front_of_anchor(page_index) {
                            self.open_pages = self.open_pages.max(in_front + 1);
                        }
                        if let Some(behind) =
                            self.places_behind_of_anchor((page_index + 1) % self.page_count)
                        {
                            self.closed_pages = self.closed_pages.min(behind);
                        }
                    }
                    None => {
                        match self.anchor {
                            Some(anchor) => {
                                if self.anchor_is_guess {
                                    // We're not sure about the anchor, but all open pages are one after each other.
                                    // Our guessed anchor must be the at the start of the open pages,
                                    // so if this open page simply extends that, then we can just add it
                                    if page_index == (anchor + self.open_pages) % self.page_count {
                                        self.open_pages += 1;
                                    }
                                } else {
                                    if let Some(in_front) =
                                        self.places_in_front_of_anchor(page_index)
                                    {
                                        self.open_pages = self.open_pages.max(in_front + 1);
                                    }
                                }
                            }
                            None => {
                                // Become the guessed anchor for now
                                self.anchor = Some(page_index);
                                self.anchor_is_partial = false;
                                self.anchor_is_guess = true;
                                self.open_pages = 1;
                                self.closed_pages = 0;
                            }
                        }
                    }
                }
            }
        }

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
        page_states.notice_page_state(3, PageState::PartialOpen);
        println!("{page_states:?}");
        page_states.notice_page_state(0, PageState::Closed);
        println!("{page_states:?}");
        page_states.notice_page_state(3, PageState::Open);
        println!("{page_states:?}");

        assert_eq!(page_states.get_page_state(0), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(1), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(2), Some(PageState::Closed));
        assert_eq!(page_states.get_page_state(3), Some(PageState::Open));
    }
}
