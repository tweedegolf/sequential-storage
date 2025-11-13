use core::{fmt::Debug, num::NonZeroU32};

use crate::map::Key;

use super::list::List;

pub(crate) trait KeyPointersCache<KEY: Key> {
    fn key_location(&self, key: &KEY) -> Option<u32>;

    fn notice_key_location(&mut self, key: &KEY, item_address: u32);
    fn notice_key_erased(&mut self, key: &KEY);

    fn invalidate_cache_state(&mut self);
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CachedKeyPointers<KEY: Eq, const KEYS: usize> {
    key_pointers: List<Option<(KEY, NonZeroU32)>, KEYS>,
}

impl<KEY: Eq, const KEYS: usize> CachedKeyPointers<KEY, KEYS> {
    const ARRAY_REPEAT_VALUE: Option<(KEY, NonZeroU32)> = None;

    pub(crate) const fn new() -> Self {
        Self {
            key_pointers: List::Arr([Self::ARRAY_REPEAT_VALUE; KEYS]),
        }
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn new_heap(n: usize) -> Self
    where
        KEY: Clone,
    {
        Self {
            key_pointers: List::from_elem_vec(Self::ARRAY_REPEAT_VALUE, n),
        }
    }

    fn key_index(&self, key: &KEY) -> Option<usize> {
        self.key_pointers
            .as_slice()
            .iter()
            .enumerate()
            .filter_map(|(index, val)| val.as_ref().map(|val| (index, val)))
            .find_map(
                |(index, (known_key, _))| {
                    if key == known_key { Some(index) } else { None }
                },
            )
    }

    fn insert_front(&mut self, value: (KEY, NonZeroU32)) {
        self.key_pointers[KEYS - 1] = Some(value);
        move_to_front(self.key_pointers.as_mut_slice(), KEYS - 1);
    }
}

impl<KEY: Key, const KEYS: usize> KeyPointersCache<KEY> for CachedKeyPointers<KEY, KEYS> {
    fn key_location(&self, key: &KEY) -> Option<u32> {
        self.key_index(key)
            .map(|index| self.key_pointers[index].as_ref().unwrap().1.get())
    }

    fn notice_key_location(&mut self, key: &KEY, item_address: u32) {
        match self.key_index(key) {
            Some(existing_index) => {
                self.key_pointers[existing_index] =
                    Some((key.clone(), NonZeroU32::new(item_address).unwrap()));
                move_to_front(self.key_pointers.as_mut_slice(), existing_index);
            }
            None => self.insert_front((key.clone(), NonZeroU32::new(item_address).unwrap())),
        }
    }

    fn notice_key_erased(&mut self, key: &KEY) {
        if let Some(existing_index) = self.key_index(key) {
            self.key_pointers[existing_index] = None;
            move_to_back(self.key_pointers.as_mut_slice(), existing_index);
        }
    }

    fn invalidate_cache_state(&mut self) {
        *self = Self::new();
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct UncachedKeyPointers;

impl<KEY: Key> KeyPointersCache<KEY> for UncachedKeyPointers {
    fn key_location(&self, _key: &KEY) -> Option<u32> {
        None
    }

    fn notice_key_location(&mut self, _key: &KEY, _item_address: u32) {}

    fn notice_key_erased(&mut self, _key: &KEY) {}

    fn invalidate_cache_state(&mut self) {}
}

fn move_to_front<T>(data: &mut [Option<T>], index: usize) {
    assert!(index < data.len());

    // Swap the item we're moving into this temporary
    let mut item = None;
    core::mem::swap(&mut item, &mut data[index]);

    unsafe {
        // Move the items until the index back one.
        // This overwrites the None we just put in.
        // This is fine because it's none and no drop has to occur
        let ptr = data.as_mut_ptr();
        ptr.copy_to(ptr.add(1), index);

        // The item in front is now duplicated.
        // Swap back our item into the front.
        core::mem::swap(&mut item, &mut data[0]);
        // The duplicated item must not drop, so just forget it
        core::mem::forget(item);
    }
}

fn move_to_back<T>(data: &mut [Option<T>], index: usize) {
    assert!(index < data.len());

    // Swap the item we're moving into this temporary
    let mut item = None;
    core::mem::swap(&mut item, &mut data[index]);

    unsafe {
        // Move the items until the index back one.
        // This overwrites the None we just put in.
        // This is fine because it's none and no drop has to occur
        let ptr = data.as_mut_ptr();
        ptr.add(index + 1)
            .copy_to(ptr.add(index), data.len() - 1 - index);

        // The item in front is now duplicated.
        // Swap back our item into the back.
        core::mem::swap(&mut item, &mut data[data.len() - 1]);
        // The duplicated item must not drop, so just forget it
        core::mem::forget(item);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_move_to_front() {
        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_front::<String>(&mut array, 0);
        assert_eq!(
            array,
            [
                Some("0".into()),
                Some("1".into()),
                Some("2".into()),
                Some("3".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_front::<String>(&mut array, 1);
        assert_eq!(
            array,
            [
                Some("1".into()),
                Some("0".into()),
                Some("2".into()),
                Some("3".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_front::<String>(&mut array, 2);
        assert_eq!(
            array,
            [
                Some("2".into()),
                Some("0".into()),
                Some("1".into()),
                Some("3".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_front::<String>(&mut array, 3);
        assert_eq!(
            array,
            [
                Some("3".into()),
                Some("0".into()),
                Some("1".into()),
                Some("2".into()),
            ]
        );
    }

    #[test]
    fn test_move_to_back() {
        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_back::<String>(&mut array, 0);
        assert_eq!(
            array,
            [
                Some("1".into()),
                Some("2".into()),
                Some("3".into()),
                Some("0".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_back::<String>(&mut array, 1);
        assert_eq!(
            array,
            [
                Some("0".into()),
                Some("2".into()),
                Some("3".into()),
                Some("1".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_back::<String>(&mut array, 2);
        assert_eq!(
            array,
            [
                Some("0".into()),
                Some("1".into()),
                Some("3".into()),
                Some("2".into()),
            ]
        );

        let mut array = [
            Some("0".into()),
            Some("1".into()),
            Some("2".into()),
            Some("3".into()),
        ];
        move_to_back::<String>(&mut array, 3);
        assert_eq!(
            array,
            [
                Some("0".into()),
                Some("1".into()),
                Some("2".into()),
                Some("3".into()),
            ]
        );
    }
}
