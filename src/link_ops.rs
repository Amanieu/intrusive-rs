// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

/// Base trait for link operations.
/// 
/// `LinkPtr` is the representation of a link pointer.
/// Typically this is `NonNull`, but compact representations such 
/// as `u8` or `u16` are possible.
pub trait LinkOps {
    /// The link pointer type.
    type LinkPtr: Copy + Eq;

    /// Returns `true` if `ptr` is currently linked into an intrusive collection.
    fn is_linked(&self, ptr: Self::LinkPtr) -> bool;

    /// Forcibly unlinks `ptr` from an intrusive collection.
    /// 
    /// # Safety
    /// This function should only be used after calling the `fast_clear` method of the intrusive collection 
    /// since `fast_clear` "clears" the collection without unlinking the nodes.
    /// 
    /// Otherwise, it is undefined behavior to call this function while `ptr` is still linked into an intrusive collection.
    unsafe fn mark_unlinked(&mut self, ptr: Self::LinkPtr);
}

/// The default implementation of `LinkOps` associated with a link type.
pub trait DefaultLinkOps {
    /// The default link operations.
    type Ops: LinkOps + Default;
}
