// Copyright 2016 Amanieu d'Antras
// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::link_ops::LinkOps;
use crate::pointer_ops::PointerOps;

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

/// Macro to get the offset of a struct field in bytes from the address of the
/// struct.
#[macro_export(local_inner_macros)]
macro_rules! offset_of {
    ($($inner:tt)*) => {
        ($crate::__memoffset::offset_of!($($inner)*) as isize)
    }
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
#[macro_export(local_inner_macros)]
macro_rules! container_of {
    ($ptr:expr, $container:path, $field:ident) => {
        #[allow(clippy::cast_ptr_alignment)]
        {
            ($ptr as *const _ as *const u8).offset(-offset_of!($container, $field))
                as *mut $container
        }
    };
}

/// Macro to generate an implementation of `Adapter` for a given set of types.
/// In particular this will automatically generate implementations of the
/// `get_value` and `get_link` methods for a given named field in a struct.
///
/// The basic syntax to create an adapter is:
///
/// ```rust,ignore
/// intrusive_adapter!(Adapter = Pointer: Value { link_field: LinkType });
/// ```
///
/// You can create a new instance of an adapter using the `new` method or the
/// `NEW` associated constant. The adapter also implements the `Default` trait.
///
/// # Generics
///
/// This macro supports generic arguments:
///
/// ```rust,ignore
/// intrusive_adapter!(
///     Adapter<'lifetime, Type, Type2> =
///         Pointer: Value {
///             link_field: LinkType
///         }
///         where
///             Type: Copy,
///             Type2: ?Sized + 'lifetime
///     );
/// ```
///
/// Note that due to macro parsing limitations, `T: Trait` bounds are not
/// supported in the generic argument list. You must list any trait bounds in
/// a separate `where` clause at the end of the macro.
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
/// pub struct Test2<T>
///     where T: Clone + ?Sized
/// {
///     link: LinkedListLink,
///     val: T,
/// }
/// intrusive_adapter!(MyAdapter3<'a, T> = &'a Test2<T>: Test2<T> { link: LinkedListLink } where T: ?Sized + Clone + 'a);
/// # fn main() {}
/// ```
#[macro_export(local_inner_macros)]
macro_rules! intrusive_adapter {
    (@impl
        $(#[$attr:meta])* ($($privacy:tt)*) $name:ident ($($args:tt),*)
        = $pointer:ty: $value:path { $field:ident: $link:ty } $($where_:tt)*
    ) => {
        #[allow(explicit_outlives_requirements)]
        $(#[$attr])*
        $($privacy)* struct $name<$($args),*> $($where_)* {
            link_ops: <$link as $crate::DefaultLinkOps>::Ops,
            pointer_ops: $crate::DefaultPointerOps<$pointer>,
        }
        unsafe impl<$($args),*> Send for $name<$($args),*> $($where_)* {}
        unsafe impl<$($args),*> Sync for $name<$($args),*> $($where_)* {}
        impl<$($args),*> Copy for $name<$($args),*> $($where_)* {}
        impl<$($args),*> Clone for $name<$($args),*> $($where_)* {
            #[inline]
            fn clone(&self) -> Self {
                *self
            }
        }
        impl<$($args),*> Default for $name<$($args),*> $($where_)* {
            #[inline]
            fn default() -> Self {
                Self::NEW
            }
        }
        #[allow(dead_code)]
        impl<$($args),*> $name<$($args),*> $($where_)* {
            pub const NEW: Self = $name {
                link_ops: <$link as $crate::DefaultLinkOps>::NEW,
                pointer_ops: $crate::DefaultPointerOps::<$pointer>::new(),
            };
            #[inline]
            pub fn new() -> Self {
                Self::NEW
            }
        }
        #[allow(dead_code, unsafe_code)]
        unsafe impl<$($args),*> $crate::Adapter for $name<$($args),*> $($where_)* {
            type LinkOps = <$link as $crate::DefaultLinkOps>::Ops;
            type PointerOps = $crate::DefaultPointerOps<$pointer>;

            #[inline]
            unsafe fn get_value(&self, link: <Self::LinkOps as $crate::LinkOps>::LinkPtr) -> *const <Self::PointerOps as $crate::PointerOps>::Value {
                container_of!(link.as_ptr(), $value, $field)
            }
            #[inline]
            unsafe fn get_link(&self, value: *const <Self::PointerOps as $crate::PointerOps>::Value) -> <Self::LinkOps as $crate::LinkOps>::LinkPtr {
                $crate::__core::ptr::NonNull::new_unchecked(&(*value).$field as *const $link as *mut $link)
            }
            #[inline]
            fn link_ops(&self) -> &Self::LinkOps {
                &self.link_ops
            }
            #[inline]
            fn link_ops_mut(&mut self) -> &mut Self::LinkOps {
                &mut self.link_ops
            }
            #[inline]
            fn pointer_ops(&self) -> &Self::PointerOps {
                &self.pointer_ops
            }
        }
    };
    (@find_generic
        $(#[$attr:meta])* ($($privacy:tt)*) $name:ident ($($prev:tt)*) > $($rest:tt)*
    ) => {
        intrusive_adapter!(@impl
            $(#[$attr])* ($($privacy)*) $name ($($prev)*) $($rest)*
        );
    };
    (@find_generic
        $(#[$attr:meta])* ($($privacy:tt)*) $name:ident ($($prev:tt)*) $cur:tt $($rest:tt)*
    ) => {
        intrusive_adapter!(@find_generic
            $(#[$attr])* ($($privacy)*) $name ($($prev)* $cur) $($rest)*
        );
    };
    (@find_if_generic
        $(#[$attr:meta])* ($($privacy:tt)*) $name:ident < $($rest:tt)*
    ) => {
        intrusive_adapter!(@find_generic
            $(#[$attr])* ($($privacy)*) $name () $($rest)*
        );
    };
    (@find_if_generic
        $(#[$attr:meta])* ($($privacy:tt)*) $name:ident $($rest:tt)*
    ) => {
        intrusive_adapter!(@impl
            $(#[$attr])* ($($privacy)*) $name () $($rest)*
        );
    };
    ($(#[$attr:meta])* pub $name:ident $($rest:tt)*) => {
        intrusive_adapter!(@find_if_generic
            $(#[$attr])* (pub) $name $($rest)*
        );
    };
    ($(#[$attr:meta])* $name:ident $($rest:tt)*) => {
        intrusive_adapter!(@find_if_generic
            $(#[$attr])* () $name $($rest)*
        );
    };
}

#[cfg(test)]
mod tests {
    use crate::LinkedListLink;
    use std::rc::Rc;

    struct Obj {
        link: LinkedListLink,
    }

    #[deny(missing_docs)]
    intrusive_adapter! {
        /// Test doc comment
        ObjAdapter1 = Rc<Obj>: Obj { link: LinkedListLink }
    }
}
