// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

/// A load factor of a hash table.
#[derive(Clone, Copy, Debug)]
pub struct LoadFactor {
    items: usize,
    buckets: usize,
}

impl Default for LoadFactor {
    #[inline(always)]
    fn default() -> LoadFactor {
        unsafe { LoadFactor::new_unchecked(24, 8) }
    }
}

impl LoadFactor {
    /// Returns a new `LoadFactor`.
    #[inline(always)]
    pub fn new(items: usize, buckets: usize) -> Option<LoadFactor> {
        if items == 0 || buckets == 0 {
            None
        } else {
            unsafe { Some(LoadFactor::new_unchecked(items, buckets)) }
        }
    }

    /// Returns a new `LoadFactor`.
    /// 
    /// # Safety
    /// `items` and `buckets` must be greater than zero.
    #[inline(always)]
    pub const unsafe fn new_unchecked(items: usize, buckets: usize) -> LoadFactor {
        LoadFactor { items, buckets }
    }

    /// Returns the numerator of the load factor.
    #[inline(always)]
    pub fn items(&self) -> usize {
        self.items
    }

    /// Returns the denominator of the load factor.
    #[inline(always)]
    pub fn buckets(&self) -> usize {
        self.buckets
    }
}
