// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use IntrusivePointer;

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
    /// Collection-specific link type which allows an object to be inserted in
    /// an intrusive collection.
    type Link;

    /// Object type which is inserted in an intrusive collection.
    type Value: ?Sized;

    /// Pointer type which owns an instance of a value.
    type Pointer: IntrusivePointer<Self::Value>;

    /// Gets a reference to an object from a reference to a link in that object.
    unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value;

    /// Gets a reference to the link for the given object.
    unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link;
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
        let result = &val.$field as *const _ as usize - &val as *const _ as usize;
        $crate::__core::mem::forget(val);
        result as isize
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
/// assert_eq!(&container as *const S, container2);
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

/// Macro to generate an implementation of `Adapter` for a given set of types.
/// In particular this will automatically generate implementations of the
/// `get_value` and `get_link` methods for a given named field in a struct.
///
/// The basic syntax to create an adapter is:
/// ```rust,ignore
/// intrusive_adapter!(Adapter = Pointer: Value { link_field: LinkType });
/// ```
///
/// # Generics
///
/// This macro supports generic arguments, but uses a slightly different syntax
/// from the usual due to limitations in the Rust macro system:
/// ```rust,ignore
/// intrusive_adapter!(Adapter['lifetime, Type, Type2: ?Sized] = Pointer: Value { link_field: LinkType } where Type: Copy, Type2: 'lifetiem);
/// ```
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate intrusive_collections;
/// use intrusive_collections::{LinkedListLink, RBTreeLink};
///
/// pub struct Test {
///     link: LinkedListLink,
///     link2: RBTreeLink,
/// }
/// intrusive_adapter!(MyAdapter = Box<Test>: Test { link: LinkedListLink });
/// intrusive_adapter!(pub MyAdapter2 = Box<Test>: Test { link2: RBTreeLink });
///
/// pub struct Test2<T: ?Sized>
///     where T: Clone
/// {
///     link: LinkedListLink,
///     val: T,
/// }
/// intrusive_adapter!(MyAdapter3['a, T: ?Sized] = &'a Test2<T>: Test2<T> { link: LinkedListLink } where T: Clone + 'a);
/// # fn main() {}
/// ```
#[macro_export]
macro_rules! intrusive_adapter {
    (@impl $name:ident [ $($args:tt $(: ?$bound:tt)*),* ] = $pointer:ty: $value:path { $field:ident: $link:ty } $($where_:tt)*) => {
        unsafe impl<$($args $(: ?$bound)*),*> Send for $name<$($args),*> $($where_)* {}
        unsafe impl<$($args $(: ?$bound)*),*> Sync for $name<$($args),*> $($where_)* {}
        #[allow(dead_code)]
        impl<$($args $(: ?$bound)*),*> $name<$($args),*> $($where_)* {
            pub fn new() -> Self {
                $name($crate::__core::marker::PhantomData)
            }
        }
        #[allow(dead_code, unsafe_code)]
        unsafe impl<$($args $(: ?$bound)*),*> $crate::Adapter for $name<$($args),*> $($where_)* {
            type Link = $link;
            type Value = $value;
            type Pointer = $pointer;
            #[inline]
            unsafe fn get_value(&self, link: *const $link) -> *const $value {
                container_of!(link, $value, $field)
            }
            #[inline]
            unsafe fn get_link(&self, value: *const $value) -> *const $link {
                &(*value).$field
            }
        }
    };
    ($name:ident [ $($args:tt)* ] = $pointer:ty: $value:path { $field:ident: $link:ty } where $($where_:tt)*) => {
        #[derive(Clone, Default)]
        struct $name<$($args)*>($crate::__core::marker::PhantomData<$pointer>) where $($where_)*;
        intrusive_adapter!(@impl $name[$($args)*] = $pointer: $value { $field: $link } where $($where_)*);
    };
    (pub $name:ident [ $($args:tt)* ] = $pointer:ty: $value:path { $field:ident: $link:ty } where $($where_:tt)*) => {
        #[derive(Clone, Default)]
        pub struct $name<$($args)*>($crate::__core::marker::PhantomData<$pointer>) where $($where_)*;
        intrusive_adapter!(@impl $name[$($args)*] = $pointer: $value { $field: $link } where $($where_)*);
    };
    ($name:ident [ $($args:tt)* ] = $pointer:ty: $value:path { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        struct $name<$($args)*>($crate::__core::marker::PhantomData<$pointer>);
        intrusive_adapter!(@impl $name[$($args)*] = $pointer: $value { $field: $link });
    };
    (pub $name:ident [ $($args:tt)* ] = $pointer:ty: $value:path { $field:ident: $link:ty }) => {
        #[derive(Clone, Default)]
        pub struct $name<$($args)*>($crate::__core::marker::PhantomData<$pointer>);
        intrusive_adapter!(@impl $name[$($args)*] = $pointer: $value { $field: $link });
    };
    ($name:ident = $pointer:ty: $value:path { $field:ident: $link:ty }) => {
        intrusive_adapter!($name[] = $pointer: $value { $field: $link });
    };
    (pub $name:ident = $pointer:ty: $value:path { $field:ident: $link:ty }) => {
        intrusive_adapter!($name[] = $pointer: $value { $field: $link });
    };
}
