use core::{fmt::Debug, num::NonZeroU32};

use crate::map::Key;

pub(crate) trait KeyPointersCache<KEY: Key> {
    fn key_location(&self, key: &KEY) -> Option<u32>;

    fn notice_key_location(&mut self, key: &KEY, item_address: u32);
    fn notice_key_erased(&mut self, key: &KEY);

    fn invalidate_cache_state(&mut self);
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct CachedKeyPointers<'a, KEY: Eq> {
    key_pointers: &'a mut [Option<(KEY, NonZeroU32)>],
}

impl<'a, KEY: Eq> CachedKeyPointers<'a, KEY> {
    pub const fn new(key_pointers: &'a mut [Option<(KEY, NonZeroU32)>]) -> Self {
        Self { key_pointers }
    }

    fn insert_front(&mut self, value: (KEY, NonZeroU32)) {
        let len = self.key_pointers.len();
        self.key_pointers[len - 1] = Some(value);
        move_to_front(self.key_pointers, len - 1);
    }
}

impl<KEY: Key> KeyPointersCache<KEY> for CachedKeyPointers<'_, KEY> {
    fn key_location(&self, key: &KEY) -> Option<u32> {
        self.key_pointers
            .iter()
            .flatten()
            .find(|(iter_key, _)| key == iter_key)
            .map(|(_, pointer)| pointer.get())
    }

    fn notice_key_location(&mut self, key: &KEY, item_address: u32) {
        let existing_pointer = self
            .key_pointers
            .iter_mut()
            .enumerate()
            .filter_map(|(index, val)| val.as_mut().map(|(key, pointer)| (index, key, pointer)))
            .find(|(_, iter_key, _)| key == *iter_key)
            .map(|(index, _, pointer)| (index, pointer));

        match existing_pointer {
            Some((existing_index, pointer)) => {
                *pointer = NonZeroU32::new(item_address).unwrap();
                move_to_front(self.key_pointers, existing_index);
            }
            None => self.insert_front((key.clone(), NonZeroU32::new(item_address).unwrap())),
        }
    }

    fn notice_key_erased(&mut self, key: &KEY) {
        let existing_pointer = self
            .key_pointers
            .iter_mut()
            .enumerate()
            .find(|(_, val)| val.as_ref().is_some_and(|(iter_key, _)| key == iter_key));

        if let Some((existing_index, val)) = existing_pointer {
            *val = None;
            move_to_back(self.key_pointers, existing_index);
        }
    }

    fn invalidate_cache_state(&mut self) {
        for pointers in self.key_pointers.iter_mut() {
            *pointers = None;
        }
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
    debug_assert!(index < data.len());

    // In an if to get rid of panic. Assert above still panics in debug builds
    if index < data.len() {
        data[..=index].rotate_right(1);
    }
}

fn move_to_back<T>(data: &mut [Option<T>], index: usize) {
    debug_assert!(index < data.len());

    // In an if to get rid of panic. Assert above still panics in debug builds
    if index < data.len() {
        data[index..].rotate_left(1);
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
