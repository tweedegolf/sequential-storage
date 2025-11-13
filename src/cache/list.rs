//! A `List` enum which allows to treat a boxed slice or an array the same way
//! once created.
//!
//! It does this by having a generic usize parameter and discarding that
//! when being used as a vec.
//!
//! BS stands for boxed slice.
//!
//! Obviously when alloc feature is disabled only the array is available.

#[cfg(feature = "alloc")]
use alloc::{boxed::Box, vec, vec::Vec};

pub enum ListKind {
    Arr,
    /// Boxed Slice
    #[cfg(feature = "alloc")]
    BS(usize),
}

#[derive(Debug)]
#[cfg_attr(feature = "defmt-03", derive(defmt::Format))]
pub enum List<T, const N: usize = 0> {
    Arr([T; N]),
    #[cfg(feature = "alloc")]
    BS(Box<[T]>),
}

impl<T, const N: usize> List<T, N> {
    pub fn from_elem(elem: T, list_kind: ListKind) -> Self
    where
        T: Copy,
    {
        match list_kind {
            ListKind::Arr => Self::Arr([elem; N]),
            #[cfg(feature = "alloc")]
            ListKind::BS(n) => Self::BS(vec![elem; n].into()),
        }
    }

    #[cfg(feature = "alloc")]
    pub fn from_elem_vec(elem: T, n: usize) -> Self
    where
        T: Clone,
    {
        Self::BS(vec![elem; n].into())
    }

    pub const fn from_elem_arr(elem: T) -> Self
    where
        T: Copy,
    {
        Self::Arr([elem; N])
    }

    pub fn as_slice(&self) -> &[T] {
        match self {
            Self::Arr(a) => &a[..],
            #[cfg(feature = "alloc")]
            Self::BS(v) => v,
        }
    }

    pub fn as_mut_slice(&mut self) -> &mut [T] {
        match self {
            Self::Arr(a) => &mut a[..],
            #[cfg(feature = "alloc")]
            Self::BS(v) => v,
        }
    }
}

impl<T, const N: usize> core::ops::Index<usize> for List<T, N> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        match self {
            Self::Arr(a) => a.index(index),
            #[cfg(feature = "alloc")]
            Self::BS(v) => v.index(index),
        }
    }
}

impl<T, const N: usize> core::ops::IndexMut<usize> for List<T, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        match self {
            Self::Arr(a) => a.index_mut(index),
            #[cfg(feature = "alloc")]
            Self::BS(v) => v.index_mut(index),
        }
    }
}
