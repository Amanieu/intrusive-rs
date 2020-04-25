// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::hash::{BuildHasher, Hash, Hasher};
use core::marker::PhantomData;

pub trait HashOps<T: ?Sized> {
    /// Returns the hash of `value`.
    fn hash(&self, value: &T) -> u64;
}

#[derive(Default)]
pub struct DefaultHashOps<S> {
    hasher_builder: S,
}

impl<S: BuildHasher, T: Hash> HashOps<T> for DefaultHashOps<S> {
    #[inline(never)]
    fn hash(&self, value: &T) -> u64 {
        let mut hasher = self.hasher_builder.build_hasher();
        value.hash(&mut hasher);
        hasher.finish()
    }
}
