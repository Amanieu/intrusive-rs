// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

pub mod chaining;

use core::cmp;

/// Hash Table Load Factor
#[derive(Clone, Copy, Debug)]
pub enum LoadFactor {
    /// A chaining hash table.
    Chained(ChainedLoadFactor),
    /// An "open addressing" hash table.
    OpenAddressed(OpenAddressedLoadFactor),
}

impl From<ChainedLoadFactor> for LoadFactor {
    #[inline]
    fn from(other: ChainedLoadFactor) -> LoadFactor {
        LoadFactor::Chained(other)
    }
}

impl From<OpenAddressedLoadFactor> for LoadFactor {
    #[inline]
    fn from(other: OpenAddressedLoadFactor) -> LoadFactor {
        LoadFactor::OpenAddressed(other)
    }
}

/// Chaining Hash Table Load Factor
#[derive(Clone, Copy, Debug, Eq)]
pub struct ChainedLoadFactor {
    /// The number of items in the hash table.
    pub size: usize,
    /// The number of buckets in the hash table.
    pub bucket_count: usize,
}

impl ChainedLoadFactor {
    /// Returns a new `ChainedLoadFactor`.
    #[inline]
    pub fn new(size: usize, bucket_count: usize) -> ChainedLoadFactor {
        ChainedLoadFactor { size, bucket_count }
    }
}

impl PartialEq for ChainedLoadFactor {
    #[inline]
    fn eq(&self, rhs: &Self) -> bool {
        self.size * rhs.bucket_count == rhs.size * self.bucket_count
    }
}

impl PartialOrd for ChainedLoadFactor {
    #[inline]
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        (self.size * rhs.bucket_count).partial_cmp(&(rhs.size * self.bucket_count))
    }
}

impl Ord for ChainedLoadFactor {
    #[inline]
    fn cmp(&self, rhs: &Self) -> cmp::Ordering {
        (self.size * rhs.bucket_count).cmp(&(rhs.size * self.bucket_count))
    }
}

/// Open Addressing Hash Table Load Factor
#[derive(Clone, Copy, Debug)]
pub struct OpenAddressedLoadFactor {
    /// The maximum number of items in the hash table.
    pub capacity: usize,
    /// The number of items in the hash table.
    pub size: usize,
}

/// The default load factor of a chaining hash table.
pub const DEFAULT_CHAINED_LOAD_FACTOR: ChainedLoadFactor = ChainedLoadFactor {
    size: 1,
    bucket_count: 1,
};
