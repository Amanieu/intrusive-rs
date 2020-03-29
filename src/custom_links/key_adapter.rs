// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::adapter::Adapter;
use super::pointer_ops::PointerOps;

pub trait KeyAdapter<'a>: Adapter {
    /// Type of the key returned by `get_key`.
    type Key;

    /// Gets the key for the given object.
    fn get_key(&self, value: &'a <Self::PointerOps as PointerOps>::Value) -> Self::Key;
}
