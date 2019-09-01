// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![allow(unused_variables)]

use crate::adapter::Adapter;

/// Extension of the Adapter trait to provide a way of extracting a memoized hash code from an object.
/// This hash code can then be used as an index in certain intrusive collections (currently only `ChainedHashTable` uses this).
pub trait HashAdapter: Adapter {
    /// Returns the memoized hash code, if any.
    #[inline]
    fn get_cached_hash(&self, val: &Self::Value) -> Option<u64> {
        None
    }

    /// Assigns the memoized hash code, if any.
    #[inline]
    fn set_cached_hash(&self, val: &Self::Value, hash: Option<u64>) {}
}
