//! Implementation of key caching

#[cfg(feature = "alloc")]
extern crate alloc;

use core::{fmt::Debug, num::NonZeroU32};

use crate::map::Key;

pub(crate) trait SealedKeyPointersCache<KEY> {
    fn key_location(&self, key: &KEY) -> Option<u32>;

    fn notice_key_location(&mut self, key: &KEY, item_address: u32);
    fn notice_key_erased(&mut self, key: &KEY);

    fn invalidate_cache_state(&mut self);
}

/// A cache that caches pointers to keys
#[allow(private_bounds)]
pub trait KeyPointersCache<KEY>: SealedKeyPointersCache<KEY> {}

/// A cache that stores keys in an array.
/// The array may be smaller than the amount of keys, but that will reduce performance.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct ArrayKeyPointers<const KEYS: usize, KEY: Key> {
    key_pointers: [Option<(KEY, NonZeroU32)>; KEYS],
}

impl<const KEYS: usize, KEY: Key> ArrayKeyPointers<KEYS, KEY> {
    /// Create a new empty cache
    pub const fn new() -> Self {
        Self {
            key_pointers: [const { None }; _],
        }
    }

    fn as_tracked(&mut self) -> TrackedKeyPointers<'_, KEY> {
        TrackedKeyPointers {
            key_pointers: &mut self.key_pointers,
        }
    }
}

impl<const KEYS: usize, KEY: Key> Default for ArrayKeyPointers<KEYS, KEY> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const KEYS: usize, KEY: Key> SealedKeyPointersCache<KEY> for ArrayKeyPointers<KEYS, KEY> {
    fn key_location(&self, key: &KEY) -> Option<u32> {
        self.key_pointers
            .iter()
            .flatten()
            .find(|(iter_key, _)| key == iter_key)
            .map(|(_, pointer)| pointer.get())
    }

    fn notice_key_location(&mut self, key: &KEY, item_address: u32) {
        self.as_tracked().notice_key_location(key, item_address);
    }

    fn notice_key_erased(&mut self, key: &KEY) {
        self.as_tracked().notice_key_erased(key);
    }

    fn invalidate_cache_state(&mut self) {
        self.as_tracked().invalidate_cache_state();
    }
}
impl<const KEYS: usize, KEY: Key> KeyPointersCache<KEY> for ArrayKeyPointers<KEYS, KEY> {}

#[cfg(feature = "alloc")]
/// A cache that stores keys in a vec.
/// The vec may be smaller than the amount of keys, but that will reduce performance.
#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub struct HeapKeyPointers<KEY: Key> {
    key_pointers: alloc::vec::Vec<Option<(KEY, NonZeroU32)>>,
}

#[cfg(feature = "alloc")]
impl<KEY: Key> HeapKeyPointers<KEY> {
    /// Create a new empty cache for the given amount of keys
    pub fn new(keys: usize) -> Self {
        Self {
            key_pointers: alloc::vec![None; keys],
        }
    }

    fn as_tracked(&mut self) -> TrackedKeyPointers<'_, KEY> {
        TrackedKeyPointers {
            key_pointers: &mut self.key_pointers,
        }
    }
}

#[cfg(feature = "alloc")]
impl<KEY: Key> SealedKeyPointersCache<KEY> for HeapKeyPointers<KEY> {
    fn key_location(&self, key: &KEY) -> Option<u32> {
        self.key_pointers
            .iter()
            .flatten()
            .find(|(iter_key, _)| key == iter_key)
            .map(|(_, pointer)| pointer.get())
    }

    fn notice_key_location(&mut self, key: &KEY, item_address: u32) {
        self.as_tracked().notice_key_location(key, item_address);
    }

    fn notice_key_erased(&mut self, key: &KEY) {
        self.as_tracked().notice_key_erased(key);
    }

    fn invalidate_cache_state(&mut self) {
        self.as_tracked().invalidate_cache_state();
    }
}
#[cfg(feature = "alloc")]
impl<KEY: Key> KeyPointersCache<KEY> for HeapKeyPointers<KEY> {}

#[derive(Debug)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct TrackedKeyPointers<'a, KEY: Eq> {
    key_pointers: &'a mut [Option<(KEY, NonZeroU32)>],
}

impl<'a, KEY: Eq> TrackedKeyPointers<'a, KEY> {
    fn insert_front(&mut self, value: (KEY, NonZeroU32)) {
        let len = self.key_pointers.len();
        self.key_pointers[len - 1] = Some(value);
        move_to_front(self.key_pointers, len - 1);
    }
}

impl<KEY: Key> SealedKeyPointersCache<KEY> for TrackedKeyPointers<'_, KEY> {
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
