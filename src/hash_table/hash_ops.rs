// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::hash::{BuildHasher, Hash, Hasher};

/// Trait for hash operations.
pub trait HashOps<T: ?Sized> {
    /// Returns the hash value of `value`.
    fn hash(&self, value: &T) -> u64;
}

/// The default implementation of `HashOps`.
#[derive(Default)]
pub struct DefaultHashOps<S: BuildHasher> {
    hasher_builder: S,
}

impl<S: BuildHasher> DefaultHashOps<S> {
    /// Returns a new hash ops instance.
    #[inline]
    pub fn from_hasher_builder(hasher_builder: S) -> DefaultHashOps<S> {
        DefaultHashOps { hasher_builder }
    }
}

impl<S: BuildHasher, T: Hash> HashOps<T> for DefaultHashOps<S> {
    #[inline(never)]
    fn hash(&self, value: &T) -> u64 {
        let mut hasher = self.hasher_builder.build_hasher();
        value.hash(&mut hasher);
        hasher.finish()
    }
}

/// An implementation of `HashOps` that uses value of an integer as its hash.
#[derive(Clone, Copy, Default)]
pub struct IntegerIdentityHashOps;

impl HashOps<u8> for IntegerIdentityHashOps {
    #[inline(always)]
    fn hash(&self, value: &u8) -> u64 {
        *value as u64
    }
}

impl HashOps<u16> for IntegerIdentityHashOps {
    #[inline(always)]
    fn hash(&self, value: &u16) -> u64 {
        *value as u64
    }
}

impl HashOps<u32> for IntegerIdentityHashOps {
    #[inline(always)]
    fn hash(&self, value: &u32) -> u64 {
        *value as u64
    }
}

impl HashOps<u64> for IntegerIdentityHashOps {
    #[inline(always)]
    fn hash(&self, value: &u64) -> u64 {
        *value as u64
    }
}
