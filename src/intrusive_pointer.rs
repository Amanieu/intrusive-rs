// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(feature = "alloc")]
use crate::alloc::boxed::Box;
#[cfg(feature = "alloc")]
use crate::alloc::rc::Rc;
#[cfg(feature = "alloc")]
use crate::alloc::sync::Arc;
use crate::UnsafeRef;
use core::mem;
use core::ops::Deref;

/// Trait representing an owned pointer type which can be converted to and from
/// a raw pointer.
///
/// This trait is automatically implemented for the standard `Box`, `Rc` and
/// `Arc` types. It is also implemented for the `UnsafeRef` pointer type
/// provided by this crate.
///
/// Rust reference types (`&T`) also implement `IntrusivePointer`. This is safe
/// because the lifetime of an intrusive collection is limited to that of the
/// pointer type. This means that a collection of `&'a T` cannot outlive any
/// objects that are inserted into the collection.
pub unsafe trait IntrusivePointer<T: ?Sized>: Deref<Target = T> + Sized {
    /// Consumes the owned pointer and returns a raw pointer to the owned object.
    ///
    /// The returned pointer must be the same as the one returned by `Deref`.
    fn into_raw(self) -> *const T {
        let ptr = self.deref() as *const _;
        mem::forget(self);
        ptr
    }

    /// Constructs an owned pointer from a raw pointer which was previously
    /// returned by `into_raw`.
    unsafe fn from_raw(ptr: *const T) -> Self;
}

unsafe impl<'a, T: ?Sized> IntrusivePointer<T> for &'a T {
    #[inline]
    fn into_raw(self) -> *const T {
        self
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Self {
        &*ptr
    }
}

unsafe impl<T: ?Sized> IntrusivePointer<T> for UnsafeRef<T> {
    #[inline]
    fn into_raw(self) -> *const T {
        UnsafeRef::into_raw(self)
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Self {
        UnsafeRef::from_raw(ptr)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> IntrusivePointer<T> for Box<T> {
    #[inline]
    fn into_raw(self) -> *const T {
        Box::into_raw(self)
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Self {
        Box::from_raw(ptr as *mut T)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> IntrusivePointer<T> for Rc<T> {
    #[inline]
    fn into_raw(self) -> *const T {
        Rc::into_raw(self)
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Rc<T> {
        Rc::from_raw(ptr)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> IntrusivePointer<T> for Arc<T> {
    #[inline]
    fn into_raw(self) -> *const T {
        Arc::into_raw(self)
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Arc<T> {
        Arc::from_raw(ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::IntrusivePointer;
    use std::boxed::Box;
    use std::fmt::Debug;
    use std::mem;
    use std::rc::Rc;
    use std::sync::Arc;

    #[test]
    fn test_box() {
        unsafe {
            let p = Box::new(1);
            let a: *const i32 = &*p;
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            let p2: Box<i32> = IntrusivePointer::from_raw(r);
            let a2: *const i32 = &*p2;
            assert_eq!(a, a2);
        }
    }

    #[test]
    fn test_rc() {
        unsafe {
            let p = Rc::new(1);
            let a: *const i32 = &*p;
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            let p2: Rc<i32> = IntrusivePointer::from_raw(r);
            let a2: *const i32 = &*p2;
            assert_eq!(a, a2);
        }
    }

    #[test]
    fn test_arc() {
        unsafe {
            let p = Arc::new(1);
            let a: *const i32 = &*p;
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            let p2: Arc<i32> = IntrusivePointer::from_raw(r);
            let a2: *const i32 = &*p2;
            assert_eq!(a, a2);
        }
    }

    #[test]
    fn test_box_unsized() {
        unsafe {
            let p = Box::new(1) as Box<dyn Debug>;
            let a: *const dyn Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Box<dyn Debug> = IntrusivePointer::from_raw(r);
            let a2: *const dyn Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }

    #[test]
    fn test_rc_unsized() {
        unsafe {
            let p = Rc::new(1) as Rc<dyn Debug>;
            let a: *const dyn Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Rc<dyn Debug> = IntrusivePointer::from_raw(r);
            let a2: *const dyn Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }

    #[test]
    fn test_arc_unsized() {
        unsafe {
            let p = Arc::new(1) as Arc<dyn Debug>;
            let a: *const dyn Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Arc<dyn Debug> = IntrusivePointer::from_raw(r);
            let a2: *const dyn Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }
}
