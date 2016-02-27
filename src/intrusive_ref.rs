// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

// Use liballoc on nightly to avoid a dependency on libstd
#[cfg(all(not(feature = "nightly"), feature = "box"))]
extern crate std as alloc;
#[cfg(all(feature = "nightly", feature = "box"))]
extern crate alloc;

#[cfg(feature = "box")]
use self::alloc::boxed::Box;
#[cfg(feature = "nightly")]
use core::nonzero::NonZero;
use core::ops::Deref;
use core::borrow::Borrow;

/// Pointer to an object that may be part of one or more intrusive colllections
///
/// This pointer guarantees that an object managed by an `IntrusiveRef` is not
/// moved, dropped or accessed through a mutable reference as long as at least
/// one `IntrusiveRef` is pointing to it.
pub struct IntrusiveRef<T: ?Sized> {
    #[cfg(feature = "nightly")]
    ptr: NonZero<*mut T>,
    #[cfg(not(feature = "nightly"))]
    ptr: *mut T,
}

#[cfg(feature = "nightly")]
impl<T: ?Sized> IntrusiveRef<T> {
    /// Creates an `IntrusiveRef` from a raw pointer
    ///
    /// # Safety
    ///
    /// You must ensure that the `IntrusiveRef` guarantees are upheld.
    #[inline]
    pub unsafe fn from_raw(val: *mut T) -> IntrusiveRef<T> {
        IntrusiveRef { ptr: NonZero::new(val) }
    }

    /// Creates an `IntrusiveRef` from a raw pointer
    ///
    /// # Safety
    ///
    /// This yields a `&mut` reference but makes no guarantee that these
    /// references are not aliased. You must ensure that there are no live
    /// references (mutable or immutable) to this object.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut **self.ptr
    }

    /// Converts an `IntrusiveRef` into a raw pointer
    #[inline]
    pub unsafe fn into_raw(self) -> *mut T {
        *self.ptr
    }
}

#[cfg(not(feature = "nightly"))]
impl<T: ?Sized> IntrusiveRef<T> {
    /// Creates an `IntrusiveRef` from a raw pointer
    ///
    /// # Safety
    ///
    /// You must ensure that the `IntrusiveRef` guarantees are upheld.
    #[inline]
    pub unsafe fn from_raw(val: *mut T) -> IntrusiveRef<T> {
        IntrusiveRef { ptr: val }
    }

    /// Creates an `IntrusiveRef` from a raw pointer
    ///
    /// # Safety
    ///
    /// This yields a `&mut` reference but makes no guarantee that these
    /// references are not aliased. You must ensure that there are no live
    /// references (mutable or immutable) to this object.
    #[inline]
    pub unsafe fn as_mut(&mut self) -> &mut T {
        &mut *self.ptr
    }

    /// Converts an `IntrusiveRef` into a raw pointer
    #[inline]
    pub fn into_raw(self) -> *mut T {
        self.ptr
    }
}

#[cfg(feature = "box")]
impl<T: ?Sized> IntrusiveRef<T> {
    /// Creates an `IntrusiveRef` from a `Box`
    #[inline]
    pub fn from_box(val: Box<T>) -> IntrusiveRef<T> {
        unsafe { IntrusiveRef::from_raw(Box::into_raw(val)) }
    }

    /// Converts an `IntrusiveRef` into a `Box`
    ///
    /// # Safety
    ///
    /// You must ensure that this is the only `IntrusiveRef` managing this
    /// object and that it is not currently a member of any intrusive
    /// collections. This operation is only valid if the `IntrusiveRef` was
    /// created using `IntrusiveRef::from_box`.
    #[inline]
    pub unsafe fn into_box(self) -> Box<T> {
        Box::from_raw(self.into_raw())
    }
}

impl<T: ?Sized> Copy for IntrusiveRef<T> {}
impl<T: ?Sized> Clone for IntrusiveRef<T> {
    #[inline]
    fn clone(&self) -> IntrusiveRef<T> {
        *self
    }
}
impl<T: ?Sized> Deref for IntrusiveRef<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        self.as_ref()
    }
}
impl<T: ?Sized> AsRef<T> for IntrusiveRef<T> {
    #[cfg(feature = "nightly")]
    #[inline]
    fn as_ref(&self) -> &T {
        unsafe { &**self.ptr }
    }

    #[cfg(not(feature = "nightly"))]
    #[inline]
    fn as_ref(&self) -> &T {
        unsafe { &*self.ptr }
    }
}
impl<T: ?Sized> Borrow<T> for IntrusiveRef<T> {
    #[inline]
    fn borrow(&self) -> &T {
        self.as_ref()
    }
}
