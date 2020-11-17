// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::borrow::{Borrow, BorrowMut};

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use crate::hash_table::LoadFactor;

/// An array of buckets.
pub trait Array<T>: BorrowMut<[T]> + Sized {
    /// Hint to the array that the hash table is about to insert additional elements.
    /// This function can return a new array to tell the hash table to rehash into the new array.
    fn reserve(&mut self, min_capacity: usize) -> Option<Self>;

    /// Hint to shrink the capacity of the array if possible.
    /// This function can return a new array to tell the hash table to rehash into the new array.
    fn shrink_to(&mut self, min_capacity: usize) -> Option<Self>;

    /// Returns the capacity.
    fn capacity(&self) -> usize;
}

impl<T> Array<T> for &'_ mut [T] {
    #[inline(never)]
    fn reserve(&mut self, _new_len: usize) -> Option<Self> {
        None
    }

    #[inline]
    fn shrink_to(&mut self, _new_len: usize) -> Option<Self> {
        None
    }

    #[inline]
    fn capacity(&self) -> usize {
        usize::max_value()
    }
}

#[cfg(feature = "nightly")]
impl<T, const N: usize> Array<T> for [T; N]
where
    [T; N]: BorrowMut<[T]>,
{
    #[inline]
    fn reserve(&mut self, _new_len: usize) -> Option<Self> {
        None
    }

    #[inline]
    fn shrink_to(&mut self, _new_len: usize) -> Option<Self> {
        None
    }

    #[inline]
    fn capacity(&self) -> usize {
        usize::max_value()
    }
}

#[cfg(not(feature = "nightly"))]
macro_rules! array_impls {
    ($($N:literal)+) => {
        $(
            impl<T> Array<T> for [T; $N]
            where
                [T; $N]: BorrowMut<[T]>,
            {
                #[inline]
                fn reserve(&mut self, _new_len: usize) -> Option<Self> {
                    None
                }

                #[inline]
                fn shrink_to(&mut self, _new_len: usize) -> Option<Self> {
                    None
                }

                #[inline]
                fn capacity(&self) -> usize { usize::max_value() }
            }
        )+
    }
}

#[cfg(not(feature = "nightly"))]
array_impls! {
    0  1  2  3  4  5  6  7  8  9
   10 11 12 13 14 15 16 17 18 19
   20 21 22 23 24 25 26 27 28 29
   30 31 32
}

#[cfg(feature = "alloc")]
pub struct DynamicArray<T> {
    inner: Vec<T>,
    capacity: usize,
    load_factor: LoadFactor,
    len: usize,
}

#[cfg(feature = "alloc")]
impl<T> Default for DynamicArray<T> {
    #[inline]
    fn default() -> Self {
        DynamicArray::new()
    }
}

#[cfg(feature = "alloc")]
impl<T> DynamicArray<T> {
    /// Constructs a new, empty`DynamicArray<T>`.
    #[inline]
    pub fn new() -> DynamicArray<T> {
        DynamicArray {
            inner: Vec::new(),
            capacity: 0,
            load_factor: LoadFactor::default(),
            len: 0,
        }
    }
}

#[cfg(feature = "alloc")]
impl<T: Default> DynamicArray<T> {
    /// Constructs a new, empty`DynamicArray<T>` with the specified capacity.
    ///
    /// The dynamic array will be able to hold at least `capacity` elements without reallocating.
    /// If `capacity` is 0, the dynamic array will not allocate.
    #[inline]
    pub fn with_capacity(capacity: usize) -> DynamicArray<T> {
        let bucket_count = min_bucket_count(capacity, LoadFactor::default());

        let mut inner = Vec::with_capacity(bucket_count);
        inner.resize_with(bucket_count, Default::default);

        DynamicArray {
            inner,
            capacity,
            load_factor: LoadFactor::default(),
            len: 0,
        }
    }
}

#[cfg(feature = "alloc")]
impl<T> Borrow<[T]> for DynamicArray<T> {
    #[inline]
    fn borrow(&self) -> &[T] {
        self.inner.borrow()
    }
}

#[cfg(feature = "alloc")]
impl<T> BorrowMut<[T]> for DynamicArray<T> {
    #[inline]
    fn borrow_mut(&mut self) -> &mut [T] {
        self.inner.borrow_mut()
    }
}

#[cfg(feature = "alloc")]
impl<T: Default> Array<T> for DynamicArray<T> {
    #[inline(never)]
    fn reserve(&mut self, new_capacity: usize) -> Option<Self> {
        let new_len = new_capacity;

        if new_len <= self.capacity {
            self.len = new_len;

            return None;
        }

        let old_bucket_count = self.inner.len();

        let new_bucket_count = core::cmp::max(
            core::cmp::max(
                min_bucket_count(new_len, self.load_factor),
                self.load_factor.buckets(),
            ),
            old_bucket_count + (old_bucket_count >> 1),
        );

        if old_bucket_count >= new_bucket_count {
            self.len = new_len;

            return None;
        }

        let mut new_vec = Vec::with_capacity(new_bucket_count);
        new_vec.resize_with(new_bucket_count, Default::default);

        let new_capacity = capacity(new_bucket_count, self.load_factor);

        Some(DynamicArray {
            inner: new_vec,
            capacity: new_capacity,
            load_factor: self.load_factor,
            len: new_len,
        })
    }

    #[inline]
    fn shrink_to(&mut self, new_len: usize) -> Option<Self> {
        if new_len >= self.capacity {
            return None;
        }

        let new_bucket_count = min_bucket_count(new_len, self.load_factor);

        if self.inner.len() <= new_bucket_count {
            return None;
        }

        let mut new_vec = Vec::with_capacity(new_bucket_count);
        new_vec.resize_with(new_bucket_count, Default::default);

        let new_capacity = capacity(new_bucket_count, self.load_factor);

        Some(DynamicArray {
            inner: new_vec,
            capacity: new_capacity,
            load_factor: self.load_factor,
            len: new_len,
        })
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.capacity
    }
}

// TODO: constrain the load factor so that a multiplication does not overflow
#[inline]
fn min_bucket_count(new_len: usize, target: LoadFactor) -> usize {
    (new_len * target.buckets() + target.items().saturating_sub(1)) / target.items()
}

#[inline]
fn capacity(bucket_count: usize, target: LoadFactor) -> usize {
    (bucket_count * target.items() + target.buckets().saturating_sub(1)) / target.buckets()
}
