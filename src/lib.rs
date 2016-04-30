// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive collections for Rust.
//!
//! Unlike normal colletions, an intrusive collection does not own the objects
//! inside it. Instead it just tracks a set of already-existing objects. Such a
//! collection is called intrusive because it requires explicit support in
//! objects to allow them to be inserted into the collection. However, this
//! allows intrusive collections to work without needed to allocate any memory.
//!
//! Semantically, intrusive collections are roughly equivalent to a standard
//! collection holding a set of `*mut T`. However, since intrusive collections
//! store data in the objects themselves, the pointers to these objects must
//! remain valid as long as they are linked into a collection.
//!
//! # Example
//!
//! ```
//! #[macro_use]
//! extern crate intrusive_collections;
//! use intrusive_collections::{IntrusiveRef, LinkedList, linked_list};
//! use std::cell::Cell;
//!
//! // Define a struct containing an intrusive link, and an adaptor for it
//! struct Test {
//!     link: linked_list::Link,
//!     value: Cell<i32>,
//! }
//! intrusive_adaptor!(TestAdaptor = Test { link: linked_list::Link });
//!
//! fn main() {
//!     // Create a list and some objects
//!     let mut list = LinkedList::new(TestAdaptor);
//!     let a = IntrusiveRef::from_box(Box::new(Test {
//!         link: linked_list::Link::new(),
//!         value: Cell::new(1),
//!     }));
//!     let b = IntrusiveRef::from_box(Box::new(Test {
//!         link: linked_list::Link::new(),
//!         value: Cell::new(2),
//!     }));
//!     let c = IntrusiveRef::from_box(Box::new(Test {
//!         link: linked_list::Link::new(),
//!         value: Cell::new(3),
//!     }));
//!
//!     // Insert the objects at the front of the list. We use clone here to
//!     // send a copy of the IntrusiveRef to the list, rather than completely
//!     // relinquishing ownership.
//!     list.push_front(a.clone());
//!     list.push_front(b.clone());
//!     list.push_front(c.clone());
//!     assert_eq!(list.iter().map(|x| x.value.get()).collect::<Vec<_>>(), [3, 2, 1]);
//!
//!     // We can modify the objects and the changes will be reflected in the
//!     // collection since it references the existing objects.
//!     c.value.set(4);
//!     assert_eq!(list.iter().map(|x| x.value.get()).collect::<Vec<_>>(), [4, 2, 1]);
//!
//!     // Once we remove objects from one collection, we are free to drop them
//!     // or insert them into another collection. Note that this isn't checked
//!     // by the compiler: you need to ensure that an object is not dropped
//!     // while still linked to an intrusive container.
//!     list.back_mut().remove();
//!     unsafe {
//!         drop(a.into_box());
//!     }
//!     assert_eq!(list.iter().map(|x| x.value.get()).collect::<Vec<_>>(), [4, 2]);
//!
//!     // We can drop the collection at any time, even if it still contains
//!     // objects. This is safe because the links in an object are only
//!     // accessed by an intrusive container. However this will leak the
//!     // objects in the list if they are not freed.
//!     drop(list);
//! }
//! ```
//!
//! # Links and adaptors
//!
//! Intrusive collections track objects through links which are embedded within
//! the objects themselves. It also allows a single object to be part of
//! multiple intrusive collections at once by having multiple links in it.
//!
//! The relationship between an object and a link inside it is described by the
//! `Adaptor` trait. Intrusive collections use an implementation of this trait
//! to determine which link in an object should be used by the collection. In
//! most cases you do not need to write an implementation manually: the
//! `intrusive_adaptor!` macro will automatically generate the necessary code.
//!
//! For red-black trees, the adaptor must also implement the `TreeAdaptor` trait
//! which allows a key to be extracted from an object. This key is then used to
//! keep all elements in the tree in ascending order.
//!
//! ```
//! #[macro_use]
//! extern crate intrusive_collections;
//! use intrusive_collections::{IntrusiveRef, linked_list, LinkedList, rbtree, RBTree, TreeAdaptor};
//!
//! // This struct can be inside two lists and one tree simultaneously
//! #[derive(Default)]
//! struct Test {
//!     link: linked_list::Link,
//!     link2: linked_list::Link,
//!     link3: rbtree::Link,
//!     value: i32,
//! }
//!
//! intrusive_adaptor!(MyAdaptor = Test { link: linked_list::Link });
//! intrusive_adaptor!(MyAdaptor2 = Test { link2: linked_list::Link });
//! intrusive_adaptor!(MyAdaptor3 = Test { link3: rbtree::Link });
//! impl<'a> TreeAdaptor<'a> for MyAdaptor3 {
//!     type Key = i32;
//!     fn get_key(&self, x: &'a Test) -> i32 { x.value }
//! }
//!
//! fn main() {
//!     let mut a = LinkedList::new(MyAdaptor);
//!     let mut b = LinkedList::new(MyAdaptor2);
//!     let mut c = RBTree::new(MyAdaptor3);
//!
//!     let test = IntrusiveRef::from_box(Box::new(Test::default()));
//!     a.cursor_mut().insert_after(test.clone());
//!     b.cursor_mut().insert_after(test.clone());
//!     c.insert(test);
//! }
//! ```
//!
//! # Cursors
//!
//! Intrusive collections are manipulated using cursors. A cursor is similar to
//! an iterator, except that it can freely seek back-and-forth, and can safely
//! mutate the list during iteration. This is similar to how a C++ iterator
//! works.
//!
//! A cursor views an intrusive collection as a circular list, with a special
//! null object between the last and first elements of the collection. A cursor
//! will either point to a valid object in the collection or to this special
//! null object.
//!
//! Cursors come in two forms: `Cursor` and `CursorMut`. A `Cursor` gives a
//! read-only view of a collection, but you are allowed to use multiple `Cursor`
//! objects simultaneously on the same collection. On the other hand,
//! `CursorMut` can be used to mutate the collection, but you may only use one
//! of them at a time.
//!
//! # Safety
//!
//! Guaranteeing safety in intrusive collections is tricky becauses they do
//! not integrate well with Rust's ownership system, especially in cases where
//! an object is a member of multiple intrusive collections. This library
//! encapsulates all safety concerns using the `IntrusiveRef` type. An
//! `IntrusiveRef` is a pointer type that provides several guarantees which must
//! be maintained by unsafe code:
//!
//! - An object managed by an `IntrusiveRef` must not be moved, dropped or
//!   accessed through a mutable reference as long as at least one
//!   `IntrusiveRef` is pointing to it.
//!
//! The only safe way to create a `IntrusiveRef` is by using the
//! `IntrusiveRef::from_box` which takes ownership of a boxed object. An
//! `IntrusiveRef` can also be created using the unsafe `IntrusiveRef::from_raw`
//! function, however you must ensure that the invariants listed above are
//! maintained.
//!
//! Destroying an object that is managed by an `IntrusiveRef` can only be done
//! using unsafe code because you must manually ensure that the object is no
//! longer a member of any intrusive collection and that there are no other
//! `IntrusiveRef` pointing to it. The object managed by an `IntrusiveRef` can
//! be retrieved through the `IntrusiveRef::into_box` and
//! `IntrusiveRef::into_raw` functions.
//!
//! Note that while moving an object that is linked into a collection is
//! disallowed, moving the collection itself is perfectly fine. This is possible
//! because the linked objects do not contain any pointers back to the
//! collection object itself.
//!
//! If an intrusive collection is dropped while still containing objects then
//! the links in those objects are not reset. Attempting to insert one of these
//! objects into another intrusive collection will fail unless its link is
//! manually reset by calling `unsafe_unlink` on it.

#![warn(missing_docs)]
#![no_std]
#![cfg_attr(feature = "nightly", feature(const_fn, shared))]
#![cfg_attr(all(feature = "nightly", feature = "box"), feature(alloc))]

#[cfg(test)]
#[macro_use]
extern crate std;

// Re-export core for use by macros
#[doc(hidden)]
pub extern crate core as __core;

/// Trait representing a mapping between an object and an intrusive link type
/// which is a member of that object.
///
/// A single object type may have multiple adaptors, which allows it to be part
/// of multiple intrusive collections simultaneously.
///
/// In most cases you do not need to implement this trait manually: the
/// `intrusive_adaptor!` macro will generate the necessary implementation for a
/// given object and link field. However it is possible to implement it manually
/// if the intrusive link is not a direct field of the object, or if you want
/// to create an adaptor with generic and/or lifetime parameters.
///
/// It is also possible to create stateful adaptors. This allows links and
/// containers to be separated and avoids the need for objects to be modified to
/// contain a link.
///
/// # Safety
///
/// It must be possible to get back a reference to the container by passing a
/// pointer returned by `get_link` to `get_container`.
pub unsafe trait Adaptor<Link> {
    /// Type containing the intrusive link
    type Container: ?Sized;

    /// Gets a reference to the containing object from a reference to a link.
    unsafe fn get_container(&self, link: *const Link) -> *const Self::Container;

    /// Gets a reference to the link for the given container object.
    unsafe fn get_link(&self, container: *const Self::Container) -> *const Link;
}

/// Macro to get the offset of a struct field in bytes from the address of the
/// struct.
///
/// This macro is identical to `offset_of!` but doesn't give a warning about
/// unnecessary unsafe blocks when invoked from unsafe code.
#[macro_export]
macro_rules! offset_of_unsafe {
    ($container:path, $field:ident) => {{
        // Make sure the field actually exists. This line ensures that a
        // compile-time error is generated if $field is accessed through a
        // Deref impl.
        let $container { $field : _, .. };

        // Create an instance of the container and calculate the offset to its
        // field. Although we are creating references to uninitialized data this
        // is fine since we are not dereferencing them.
        let val: $container = $crate::__core::mem::uninitialized();
        let result = &val.$field as *const _ as isize - &val as *const _ as isize;
        $crate::__core::mem::forget(val);
        result
    }};
}

/// Macro to get the offset of a struct field in bytes from the address of the
/// struct.
///
/// This macro will cause a warning if it is invoked in an unsafe block. Use the
/// `offset_of_unsafe` macro instead to avoid this warning.
#[macro_export]
macro_rules! offset_of {
    ($container:path, $field:ident) => {
        unsafe { offset_of_unsafe!($container, $field) }
    };
}

/// Unsafe macro to get a raw pointer to an outer object from a pointer to one
/// of its fields.
///
/// # Examples
///
/// ```
/// # #[macro_use] extern crate intrusive_collections;
/// # fn main() {
/// struct S { x: u32, y: u32 };
/// let container = S { x: 1, y: 2 };
/// let field = &container.x;
/// let container2: *const S = unsafe { container_of!(field, S, x) };
/// assert_eq!(&container as *const _, container2);
/// # }
/// ```
///
/// # Safety
///
/// This is unsafe because it assumes that the given expression is a valid
/// pointer to the specified field of some container type.
#[macro_export]
macro_rules! container_of {
    ($ptr:expr, $container:path, $field:ident) => {
        ($ptr as *const _ as *const u8).offset(-offset_of_unsafe!($container, $field)) as *mut $container
    };
}

/// Macro to generate an empty type implementing the Adaptor trait for the given
/// container object and field.
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate intrusive_collections;
/// use intrusive_collections::{linked_list, rbtree};
///
/// pub struct Test {
///     link: linked_list::Link,
///     link2: rbtree::Link,
/// }
/// intrusive_adaptor!(MyAdaptor = Test { link: linked_list::Link });
/// intrusive_adaptor!(pub MyAdaptor2 = Test { link2: rbtree::Link });
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! intrusive_adaptor {
    ($name:ident = $container:path { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        struct $name;
        intrusive_adaptor!(_impl $name = $container { $field: $link });
    };
    (pub $name:ident = $container:path { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        pub struct $name;
        intrusive_adaptor!(_impl $name = $container { $field: $link });
    };
    (_impl $name:ident = $container:path { $field:ident: $link:ty }) => {
        #[allow(dead_code)]
        unsafe impl $crate::Adaptor<$link> for $name {
            type Container = $container;
            #[inline]
            unsafe fn get_container(&self, link: *const $link) -> *const $container {
                container_of!(link, $container, $field)
            }
            #[inline]
            unsafe fn get_link(&self, container: *const $container) -> *const $link {
                &(*container).$field
            }
        }
    };
    // Versions accepting a trailing comma
    ($name:ident = $container:path { $field:ident: $link:ty, }) => {
        intrusive_adaptor!($name = $container { $field: $link });
    };
    (pub $name:ident = $container:path { $field:ident: $link:ty, }) => {
        intrusive_adaptor!($name = $container { $field: $link });
    };
}

pub mod singly_linked_list;
pub mod linked_list;
pub mod rbtree;
mod intrusive_ref;

pub use singly_linked_list::SinglyLinkedList;
pub use linked_list::LinkedList;
pub use rbtree::{RBTree, TreeAdaptor};
pub use intrusive_ref::IntrusiveRef;

/// An endpoint of a range of keys.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Bound<T> {
    /// An inclusive bound.
    Included(T),
    /// An exclusive bound.
    Excluded(T),
    /// An infinite endpoint. Indicates that there is no bound in this direction.
    Unbounded,
}
