// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use super::link_ops::LinkOps;

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

    /// Object type which is inserted in an intrusive collection.
    type Value: ?Sized;

    /// Pointer type which owns an instance of a value.
    type Pointer;

    /// Gets a reference to an object from a reference to a link in that object.
    unsafe fn get_value(&self, link: <Self::LinkOps as LinkOps>::LinkPtr) -> *const Self::Value;

    /// Gets a reference to the link for the given object.
    unsafe fn get_link(&self, value: *const Self::Value) -> <Self::LinkOps as LinkOps>::LinkPtr;

    fn link_ops(&self) -> &Self::LinkOps;

    fn link_ops_mut(&mut self) -> &mut Self::LinkOps;

    /// Constructs an owned pointer from a raw pointer.
    /// 
    /// # Safety
    /// The raw pointer must have been previously returned by `into_raw`.
    unsafe fn from_raw(&self, value: *const Self::Value) -> Self::Pointer;

    /// Consumes the owned pointer and returns a raw pointer to the owned object.
    fn into_raw(&self, ptr: Self::Pointer) -> *const Self::Value;
}

#[inline]
pub(crate) unsafe fn clone_pointer_from_raw<A: Adapter>(
    adapter: &A,
    pointer: *const A::Value,
) -> A::Pointer
where
    A::Pointer: Clone,
{
    use core::mem::ManuallyDrop;
    use core::ops::Deref;

    /// Guard which converts an pointer back into its raw version
    /// when it gets dropped. This makes sure we also perform a full
    /// `from_raw` and `into_raw` round trip - even in the case of panics.
    struct PointerGuard<'a, A: Adapter> {
        pointer: ManuallyDrop<A::Pointer>,
        adapter: &'a A,
    }

    impl<'a, A: Adapter> Drop for PointerGuard<'a, A> {
        #[inline]
        fn drop(&mut self) {
            // Prevent shared pointers from being released by converting them
            // back into the raw pointers
            let _ = self
                .adapter
                .into_raw(unsafe { ManuallyDrop::take(&mut self.pointer) });
        }
    }

    let holder = PointerGuard {
        pointer: ManuallyDrop::new(adapter.from_raw(pointer)),
        adapter,
    };
    holder.pointer.deref().clone()
}
