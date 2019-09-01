// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Dynamically-size arrays for implementing other intrusive data structures (e.g. hash tables).

use crate::array::Array;

//use core::marker::PhantomData;

/// A Dynamic Array.
pub trait DynamicArray: Array {
    /// Returns the capacity.
    fn capacity(&self) -> usize;

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// into `self`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows `usize`.
    fn reserve(&mut self, additional: usize);

    /// Tries to reserve capacity for at least `additional` more elements to be inserted
    /// into `self`. The collection may reserve more space to avoid
    /// frequent reallocations. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    fn try_reserve(&mut self, additional: usize) -> Result<(), DynamicArrayAllocErr>;

    /// Resizes `self` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, `self` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, `self` is simply truncated.
    ///
    /// This method requires [`Clone`] to be able clone the passed value. If
    /// you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`resize_with`].
    fn resize(&mut self, new_len: usize, value: Self::Item)
        where Self::Item: Clone;

    /// Tries to resize `self` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, `self` is extended by the
    /// difference, with each additional slot filled with `value`.
    /// If `new_len` is less than `len`, `self` is simply truncated.
    ///
    /// This method requires [`Clone`] to be able clone the passed value. If
    /// you need more flexibility (or want to rely on [`Default`] instead of
    /// [`Clone`]), use [`resize_with`].
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    fn try_resize(&mut self, new_len: usize, value: Self::Item) -> Result<(), DynamicArrayAllocErr>
        where Self::Item: Clone;

    /// Resizes `self` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, `self` is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in `self` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, `self` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`resize`]. If you want
    /// to use the [`Default`] trait to generate values, you can pass
    /// [`Default::default()`] as the second argument.
    fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Self::Item;

    /// Tries to resize `self` in-place so that `len` is equal to `new_len`.
    ///
    /// If `new_len` is greater than `len`, `self` is extended by the
    /// difference, with each additional slot filled with the result of
    /// calling the closure `f`. The return values from `f` will end up
    /// in `self` in the order they have been generated.
    ///
    /// If `new_len` is less than `len`, `self` is simply truncated.
    ///
    /// This method uses a closure to create new values on every push. If
    /// you'd rather [`Clone`] a given value, use [`resize`]. If you want
    /// to use the [`Default`] trait to generate values, you can pass
    /// [`Default::default()`] as the second argument.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), DynamicArrayAllocErr>
    where
        F: FnMut() -> Self::Item;
}

/// A dynamic array allocation error.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DynamicArrayAllocErr {
    /// Error due to the computed capacity exceeding the collection's maximum.
    CapacityOverflow,
    /// Error due to the allocator.
    AllocErr,
}

#[cfg(any(test, feature = "alloc"))]
impl From<core::alloc::LayoutErr> for DynamicArrayAllocErr {
    #[inline]
    fn from(_: core::alloc::LayoutErr) -> Self {
        DynamicArrayAllocErr::CapacityOverflow
    }
}

#[cfg(any(test, feature = "std", feature = "alloc"))]
impl<T> DynamicArray for alloc::vec::Vec<T> {
    #[inline]
    fn capacity(&self) -> usize {
        alloc::vec::Vec::capacity(self)
    }

    #[inline]
    fn reserve(&mut self, additional: usize) {
        alloc::vec::Vec::reserve(self, additional)
    }

    #[inline]
    fn try_reserve(&mut self, additional: usize) -> Result<(), DynamicArrayAllocErr> {
        self.reserve(additional);
        Ok(())
    }

    #[inline]
    fn resize(&mut self, new_len: usize, value: Self::Item)
    where Self::Item: Clone
    {
        alloc::vec::Vec::resize(self, new_len, value);
    }

    #[inline]
    fn try_resize(&mut self, new_len: usize, value: Self::Item) -> Result<(), DynamicArrayAllocErr>
    where Self::Item: Clone
    {
        DynamicArray::resize(self, new_len, value);
        Ok(())
    }

    #[inline]
    fn resize_with<F>(&mut self, new_len: usize, f: F)
    where
        F: FnMut() -> Self::Item,
    {
        alloc::vec::Vec::resize_with(self, new_len, f)
    }

    #[inline]
    fn try_resize_with<F>(&mut self, new_len: usize, f: F) -> Result<(), DynamicArrayAllocErr>
    where
        F: FnMut() -> Self::Item,
    {
        DynamicArray::resize_with(self, new_len, f);
        Ok(())
    }
}
