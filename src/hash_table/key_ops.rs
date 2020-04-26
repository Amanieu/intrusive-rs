// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

/// Trait for key operations.
pub trait KeyOps<'a, T: ?Sized> {
    /// The key type.
    type Key;

    /// Returns the key of `value`.
    fn key(&self, value: &'a T) -> Self::Key;
}
