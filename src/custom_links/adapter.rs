// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::link_ops::LinkOps;
use super::pointer_ops::PointerOps;

/// Trait for a adapter which allows a type to be inserted into an intrusive
/// collection. The `Link` type contains the collection-specific metadata which
/// allows an object to be inserted into an intrusive collection. This type
/// needs to match the collection type (eg. `LinkedListLink` for inserting
/// in a `LinkedList`).
///
/// `Value` is the actual object type managed by the collection. This type will
/// typically have an instance of `Link` as a struct field.
///
/// `Pointer` is a pointer type which "owns" an object of type `Value`.
/// Operations which insert an element into an intrusive collection will accept
/// such a pointer and operations which remove an element will return this type.
///
/// `NodeRef` is a value type which represents the "address" of an object within
/// an intrusive collection.
///
/// A single object type may have multiple adapters, which allows it to be part
/// of multiple intrusive collections simultaneously.
///
/// In most cases you do not need to implement this trait manually: the
/// `intrusive_adapter!` macro will generate the necessary implementation for a
/// given type and its link field. However it is possible to implement it
/// manually if the intrusive link is not a direct field of the object type.
///
/// It is also possible to create stateful adapters. This allows links and
/// containers to be separated and avoids the need for objects to be modified to
/// contain a link.
///
/// # Safety
///
/// It must be possible to get back a reference to the container by passing a
/// pointer returned by `get_link` to `get_container`.
pub unsafe trait Adapter {
    /// Link type which allows an object to be inserted into an intrusive collection.
    type LinkOps: LinkOps;

    /// Collection-specific pointer conversions which allow an object to
    /// be inserted in an intrusive collection.
    type PointerOps: PointerOps;

    /// Gets a reference to an object from a reference to a link in that object.
    unsafe fn get_value(&self, link: <Self::LinkOps as LinkOps>::LinkPtr) -> *const <Self::PointerOps as PointerOps>::Value;

    /// Gets a reference to the link for the given object.
    unsafe fn get_link(&self, value: *const <Self::PointerOps as PointerOps>::Value) -> <Self::LinkOps as LinkOps>::LinkPtr;

    fn link_ops(&self) -> &Self::LinkOps;

    fn link_ops_mut(&mut self) -> &mut Self::LinkOps;

    fn pointer_ops(&self) -> &Self::PointerOps;
}
