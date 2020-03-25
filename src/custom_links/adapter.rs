// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

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
/// # Relationship of associated types
/// `Pointer` <-> `NodeRef` <-> `*const Link` <-> `*const Value`
/// 
/// # Safety
///
/// It must be possible to get back a reference to the container by passing a
/// pointer returned by `get_link` to `get_container`.
pub unsafe trait Adapter {
    /// Link type which allows an object to be inserted into an intrusive collection.
    type Link;

    /// Object type which is inserted in an intrusive collection.
    type Value: ?Sized;

    /// Pointer type which owns an instance of a value.
    type Pointer;

    /// Node reference type.
    type NodeRef;

    /// Gets a reference to an object from a reference to a link in that object.
    unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value;

    /// Gets a reference to the link for the given object.
    unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link;

    /// Consumes the owned pointer and returns a node reference to the owned object.
    unsafe fn node_from_pointer(&self, ptr: Self::Pointer) -> Self::NodeRef;

    /// Costructs an owned pointer from a node reference which was previous returned by `node_from_pointer`.
    unsafe fn node_into_pointer(&self, node: Self::NodeRef) -> Self::Pointer;

     /// Converts a node reference into a link reference.
    unsafe fn node_from_link(&self, link: *const Self::Link) -> Self::NodeRef;

    /// Converts a link reference to a node reference.
    unsafe fn node_into_link(&self, node: Self::NodeRef) -> *const Self::Link;
}
