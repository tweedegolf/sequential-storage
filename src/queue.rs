use super::*;

pub fn push<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &[u8],
) -> Result<(), Error<S::Error>> {
    todo!()
}

pub fn peek<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &'d mut [u8],
) -> Result<&'d [u8], Error<S::Error>> {
    todo!()
}

pub fn pop<'d, S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &'d mut [u8],
) -> Result<&'d [u8], Error<S::Error>> {
    todo!()
}

/// Returns the page and offset in the page to the start of the first (oldest) data
fn find_first_data<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<Option<(usize, u32)>, Error<S::Error>> {
    let first_closed_page = find_first_page(flash, flash_range.clone(), 0, PageState::Closed)?;

    let oldest_page = match first_closed_page {
        Some(first_closed_page) => {
            let mut oldest_page = first_closed_page;
            for older_page_index in get_pages::<S>(flash_range.clone(), first_closed_page).rev() {
                if get_page_state(flash, flash_range.clone(), older_page_index)?.is_closed() {
                    oldest_page = older_page_index;
                } else {
                    break;
                }
            }
            oldest_page
        }
        None => {
            // There is no closed page anywhere, but there might be data in a partially open page
            match find_first_page(flash, flash_range.clone(), 0, PageState::Closed)? {
                Some(oldest_page) => oldest_page,
                None => {
                    // There are only open pages. We don't have data
                    return Ok(None);
                }
            }
        }
    };

    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), oldest_page) + S::WRITE_SIZE as u32;

    todo!()
}
