// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::link_ops::LinkOps;
use super::pointer_ops::PointerOps;

/// Trait for a adapter which allows a type to be inserted into an intrusive
/// collection.
/// 
/// `LinkOps` implements the collection-specific operations which
/// allows an object to be inserted into an intrusive collection. This type
/// needs to implement the appropriate trait for the collection type
/// (eg. `LinkedListOps` for inserting into a `LinkedList`).
/// `LinkOps` type may be stateful, allowing custom link types.
///
/// `PointerOps` implements the collection-specific pointer conversions which
/// allow an object to be inserted into an intrusive collection.
/// `PointerOps` type may be stateful, allowing custom pointer types.
/// 
/// A single object type may have multiple adapters, which allows it to be part
/// of multiple intrusive collections simultaneously.
///
/// In most cases you do not need to implement this trait manually: the
/// `intrusive_adapter!` macro will generate the necessary implementation for a
/// given type and its link field. However it is possible to implement it
/// manually if the intrusive link is not a direct field of the object type.
///
/// It is also possible to create stateful adapters.
/// This allows links and containers to be separated and avoids the need for objects to be modified to
/// contain a link.
///
/// # Safety
///
/// It must be possible to get back a reference to the container by passing a
/// pointer returned by `get_link` to `get_container`.
pub unsafe trait Adapter {
    /// Collection-specific link operations which allow an object to be inserted in
    /// an intrusive collection.
    type LinkOps: LinkOps;

    /// Collection-specific pointer conversions which allow an object to
    /// be inserted in an intrusive collection.
    type PointerOps: PointerOps;

    /// Gets a reference to an object from a reference to a link in that object.
    unsafe fn get_value(
        &self,
        link: <Self::LinkOps as LinkOps>::LinkPtr,
    ) -> *const <Self::PointerOps as PointerOps>::Value;

    /// Gets a reference to the link for the given object.
    unsafe fn get_link(
        &self,
        value: *const <Self::PointerOps as PointerOps>::Value,
    ) -> <Self::LinkOps as LinkOps>::LinkPtr;

    /// Returns a reference to the link operations.
    fn link_ops(&self) -> &Self::LinkOps;

    /// Returns a reference to the mutable link operations.
    fn link_ops_mut(&mut self) -> &mut Self::LinkOps;

    /// Returns a reference to the pointer converter.
    fn pointer_ops(&self) -> &Self::PointerOps;
}
