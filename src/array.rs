// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Fixed-size arrays for implementing other intrusive data structures (e.g. hash tables).

/// A Fixed-size array.
pub trait Array {
    /// The element of this array.
    type Item;

    /// Returns the number of elements in this array.
    fn len(&self) -> usize;

    /// Returns a slice of the array's contents.
    fn as_slice(&self) -> &[Self::Item];

    /// Returns a mutable slice of the array's contents.
    fn as_mut_slice(&mut self) -> &mut [Self::Item];

    /// Returns a raw pointer to the array's contents.
    fn as_ptr(&self) -> *const Self::Item;

    /// Returns an unsafe mutable pointer to the array's contents.
    fn as_mut_ptr(&mut self) -> *mut Self::Item;
}

// impl for &'a mut [T], Vec, [T; N], &'a mut [T; N],

macro_rules! impl_array(
    ($($size:expr),+) => {
        $(
            impl<T> Array for [T; $size] {
                type Item = T;

                #[inline]
                fn len(&self) -> usize {
                    $size
                }

                #[inline]
                fn as_slice(&self) -> &[Self::Item] {
                    &self[..]
                }

                #[inline]
                fn as_mut_slice(&mut self) -> &mut [Self::Item] {
                    &mut self[..]
                }

                #[inline]
                fn as_ptr(&self) -> *const Self::Item {
                    self as *const [T; $size] as *const T
                }

                #[inline]
                fn as_mut_ptr(&mut self) -> *mut Self::Item {
                    self as *mut [T; $size] as *mut T
                }
            }
        )+
    }
);

impl_array!(
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
    17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32
);

impl_array!(36,
            0x40, 0x80, 0x100, 0x200, 0x400, 0x800, 0x1000, 0x2000, 0x4000, 0x8000,
            0x10000, 0x20000, 0x40000, 0x80000, 0x100000);

#[cfg(any(test, feature = "alloc"))]
impl<T> Array for alloc::vec::Vec<T> {
    type Item = T;

    #[inline]
    fn len(&self) -> usize {
        alloc::vec::Vec::len(self)
    }

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        alloc::vec::Vec::as_slice(self)
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        alloc::vec::Vec::as_mut_slice(self)
    }

    #[inline]
    fn as_ptr(&self) -> *const Self::Item {
        alloc::vec::Vec::as_ptr(self)
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        alloc::vec::Vec::as_mut_ptr(self)
    }
}

impl<'a, T> Array for &'a mut [T] {
    type Item = T;

    #[inline]
    fn len(&self) -> usize {
        <[T]>::len(&*self)
    }

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        &*self
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        &mut *self
    }

    #[inline]
    fn as_ptr(&self) -> *const Self::Item {
        <[T]>::as_ptr(self)
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        <[T]>::as_mut_ptr(self)
    }
}

#[cfg(any(test, feature = "alloc"))]
impl<T> Array for alloc::boxed::Box<[T]> {
    type Item = T;

    #[inline]
    fn len(&self) -> usize {
        <[T]>::len(&*self)
    }

    #[inline]
    fn as_slice(&self) -> &[Self::Item] {
        &*self
    }

    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Self::Item] {
        &mut *self
    }

    #[inline]
    fn as_ptr(&self) -> *const Self::Item {
        (**self).as_ptr()
    }

    #[inline]
    fn as_mut_ptr(&mut self) -> *mut Self::Item {
        (**self).as_mut_ptr()
    }
}
