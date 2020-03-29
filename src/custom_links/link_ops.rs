// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

pub trait LinkOps {
    type LinkPtr: Copy + Eq;

    fn is_linked(&self, ptr: Self::LinkPtr) -> bool;

    unsafe fn mark_unlinked(&mut self, ptr: Self::LinkPtr);
}

pub trait DefaultLinkOps {
    type Ops: LinkOps + Default;
}
