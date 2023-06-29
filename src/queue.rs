use arrayvec::ArrayVec;

use super::*;

pub fn push<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    data: &[u8],
) -> Result<(), Error<S::Error>> {
    todo!()
}

pub fn peek<S: NorFlash, const CAP: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<ArrayVec<u8, CAP>, Error<S::Error>> {
    todo!()
}

pub fn pop<S: NorFlash, const CAP: usize>(
    flash: &mut S,
    flash_range: Range<u32>,
) -> Result<ArrayVec<u8, CAP>, Error<S::Error>> {
    todo!()
}

fn page_item_adresses_iter<S: NorFlash>(
    flash: &mut S,
    flash_range: Range<u32>,
    page_index: usize,
) -> impl Iterator<Item = Result<(u32, u16), Error<S::Error>>> + '_ {
    let page_data_start_address =
        calculate_page_address::<S>(flash_range.clone(), page_index) + S::WRITE_SIZE as u32;
    let page_data_end_address =
        calculate_page_end_address::<S>(flash_range, page_index) - S::WRITE_SIZE as u32;

    let mut current_address = page_data_start_address;

    core::iter::from_fn(move || {
        while current_address < page_data_end_address {
            // Read the length
            let mut length = [0; 2];
            if let Err(e) = flash.read(current_address, &mut length) {
                // Error. Make this the last thing this iterator yields
                current_address = page_data_end_address;
                return Some(Err(Error::Storage(e)));
            }
            let length = u16::from_le_bytes(length);

            if length == 0xFFFF {
                // Not programmed yet, we're done
                return None;
            }

            if length == 0 {
                // Probably a removed entry
                current_address += 2;
                continue;
            }

            let data_remaining = page_data_end_address - current_address;

            if length as u32 > data_remaining {
                // All data must fit in a page and this seems like it's not.
                // Something is wrong. Make this the last thing this iterator yields
                current_address = page_data_end_address;
                return Some(Err(Error::Corrupted));
            }

            let return_value = (current_address, length);

            current_address += 2 + length as u32;

            return Some(Ok(return_value));
        }

        None
    })
}
