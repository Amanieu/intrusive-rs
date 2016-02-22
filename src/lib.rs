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
//! # #[macro_use] extern crate intrusive_collections;
//! use intrusive_collections::{LinkedList, linked_list};
//!
//! // Define a struct containing an intrusive link, and an adaptor for it
//! struct Test {
//!     link: linked_list::Link,
//!     value: i32,
//! }
//! intrusive_adaptor!(TestAdaptor = Test { link: linked_list::Link });
//!
//! fn main() {
//!     // Create a list and some objects
//!     let mut list = LinkedList::new(TestAdaptor);
//!     let mut a = Test {
//!         link: linked_list::Link::new(),
//!         value: 1,
//!     };
//!     let mut b = Test {
//!         link: linked_list::Link::new(),
//!         value: 2,
//!     };
//!     let mut c = Test {
//!         link: linked_list::Link::new(),
//!         value: 3,
//!     };
//!
//!     // Insert the objects at the front of the list. This is unsafe because
//!     // we need to guarantee that the objects will remain valid as long as
//!     // they are linked in an intrusive collection.
//!     unsafe {
//!         list.cursor_mut().insert_after(&mut a);
//!         list.cursor_mut().insert_after(&mut b);
//!         list.cursor_mut().insert_after(&mut c);
//!     }
//!     assert_eq!(list.iter().map(|x| x.value).collect::<Vec<_>>(), [3, 2, 1]);
//!
//!     // We can modify the objects and the changes will be reflected in the
//!     // collection since it references the existing objects.
//!     c.value = 4;
//!     assert_eq!(list.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 2, 1]);
//!
//!     // Once we remove objects from one collection, we are free to drop them
//!     // or insert them into another collection. Note that this isn't checked
//!     // by the compiler: you need to ensure that an object is not dropped
//!     // while still linked to an intrusive container.
//!     list.back_mut().remove();
//!     drop(a);
//!     assert_eq!(list.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 2]);
//!
//!     // We can drop the collection once it is empty
//!     list.clear();
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
//! use intrusive_collections::{linked_list, LinkedList, rbtree, RBTree, TreeAdaptor};
//!
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
//!     let mut test = Test::default();
//!     unsafe {
//!         a.cursor_mut().insert_after(&mut test);
//!         b.cursor_mut().insert_after(&mut test);
//!         c.insert(&mut test);
//!     }
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
//! Intrusive collections are inherently unsafe because they bypass a large
//! portion of Rust's ownership and lifetime system. To use intrusive
//! collections safely, two rules must be followed:
//!
//! 1. An object must not be moved or dropped while it is linked in an
//!    intrusive collection. This can be checked by calling `is_linked` on the
//!    Link in an object.
//! 2. You must be careful not to violate Rust's reference aliasing rules when
//!    working with intrusive collections. These rules disallow having a
//!    `&mut T` which aliases (points to the same object as) a `&T` or `&mut T`.
//!    This means that you must not be holding a reference (mutable or
//!    otherwise) to an object linked inside a collection while operation on
//!    that collection.
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
//!
//! # Recovering safety
//!
//! If the first rule is violated (an object was moved or dropped while linked
//! in an intrusive collection) then any further use of the intrusive collection
//! that the object was in will result in undefined behavior. At this point only
//! two operations can be done: dropping the collection or resetting it using
//! the `fast_clear` function.
//!
//! The latter will reset the collection to its initial state but will not
//! unlink any of the objects that were previously in the collection. In order
//! to continue using those objects in intrusive collections, their links must
//! be manually reset by calling `unsafe_unlink` on them.

#![warn(missing_docs)]
#![no_std]
#![cfg_attr(feature = "nightly", feature(const_fn))]
#![cfg_attr(all(test, feature = "nightly"), feature(recover))]

#[cfg(test)]
#[macro_use]
extern crate std;

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
/// pointer returned by `get_link` to `get_container` or `get_container_mut`.
pub unsafe trait Adaptor<Link> {
    /// Type containing the intrusive link
    type Container;

    /// Gets a reference to the containing object from a reference to a link.
    unsafe fn get_container(&self, link: *const Link) -> *const Self::Container;

    /// Gets a reference to the link for the given container object.
    unsafe fn get_link(&self, container: *const Self::Container) -> *const Link;
}

/// Macro to get the offset of a struct field in bytes from the address of the
/// struct.
///
/// This macro supports chaining multiple fields together.
///
/// # Safety
///
/// This is unsafe because it assumes that the given expression can be resolved
/// into an offset at compile time. This is usually safe with simple field
/// accesses, but complex expressions that rely on function calls or pointer
/// derefences will result in this macro being compiled into a null pointer
/// dereference, which will crash your program.
#[macro_export]
macro_rules! offset_of {
    (_as_expr $x:expr) => {
        $x
    };
    ($container:ty, $($field:tt)*) => {{
        // Yes, this is technically derefencing a null pointer. However, Rust
        // currently accepts this and reduces it to a constant, even in debug
        // builds!
        &offset_of!(_as_expr (*(0 as *const $container)).$($field)*) as *const _ as isize
    }};
}

/// Unsafe macro to get a raw pointer to an outer object from a pointer to one
/// of its fields.
///
/// This macro supports chaining multiple fields together.
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
    ($ptr:expr, $container:ty, $($field:tt)*) => {
        ($ptr as *const _ as *const u8).offset(-offset_of!($container, $($field)*)) as *mut $container
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
    ($name:ident = $container:ty { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        struct $name;
        intrusive_adaptor!(_impl $name = $container { $field: $link });
    };
    (pub $name:ident = $container:ty { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        pub struct $name;
        intrusive_adaptor!(_impl $name = $container { $field: $link });
    };
    (_impl $name:ident = $container:ty { $field:ident: $link:ty }) => {
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
}

pub mod linked_list;
pub mod rbtree;

pub use linked_list::LinkedList;
pub use rbtree::{RBTree, TreeAdaptor};

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
