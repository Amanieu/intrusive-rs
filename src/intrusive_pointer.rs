// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#[cfg(all(feature = "nightly", feature = "alloc"))]
use alloc::arc::Arc;
#[cfg(feature = "alloc")]
use alloc::boxed::Box;
#[cfg(feature = "alloc")]
use alloc::rc::Rc;
#[cfg(all(not(feature = "nightly"), feature = "alloc"))]
use alloc::sync::Arc;
use core::ops::Deref;
#[cfg(feature = "alloc")]
use core::{mem, ptr};
use UnsafeRef;

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
        let ptr = self.as_ref() as *const T;
        mem::forget(self);
        ptr
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Rc<T> {
        // Create a temporary fake Rc object from the given pointer and
        // calculate the address of the inner T.
        let fake_rc: Self = mem::transmute(ptr);
        let fake_rc_target = fake_rc.as_ref() as *const _;
        mem::forget(fake_rc);

        // Calculate the offset of T in RcBox<T>
        let rc_offset = (fake_rc_target as *const u8) as isize - (ptr as *const u8) as isize;

        // Get the address of the RcBox<T> by subtracting the offset from the
        // pointer we were originally given.
        let rc_ptr = (ptr as *const u8).offset(-rc_offset);

        // If T is an unsized type, then *const T is a fat pointer. To handle
        // this case properly we need to preserve the second word of the fat
        // pointer but overwrite the first one with our adjusted pointer.
        let mut result = mem::transmute(ptr);
        ptr::write(&mut result as *mut _ as *mut *const u8, rc_ptr);
        result
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> IntrusivePointer<T> for Arc<T> {
    #[inline]
    fn into_raw(self) -> *const T {
        let ptr = self.as_ref() as *const T;
        mem::forget(self);
        ptr
    }
    #[inline]
    unsafe fn from_raw(ptr: *const T) -> Arc<T> {
        // Create a temporary fake Arc object from the given pointer and
        // calculate the address of the inner T.
        let fake_rc: Self = mem::transmute(ptr);
        let fake_rc_target = fake_rc.as_ref() as *const _;
        mem::forget(fake_rc);

        // Calculate the offset of T in ArcInner<T>
        let rc_offset = (fake_rc_target as *const u8) as isize - (ptr as *const u8) as isize;

        // Get the address of the ArcInner<T> by subtracting the offset from the
        // pointer we were originally given.
        let rc_ptr = (ptr as *const u8).offset(-rc_offset);

        // If T is an unsized type, then *const T is a fat pointer. To handle
        // this case properly we need to preserve the second word of the fat
        // pointer but overwrite the first one with our adjusted pointer.
        let mut result = mem::transmute(ptr);
        ptr::write(&mut result as *mut _ as *mut *const u8, rc_ptr);
        result
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
            let p = Box::new(1) as Box<Debug>;
            let a: *const Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Box<Debug> = IntrusivePointer::from_raw(r);
            let a2: *const Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }

    #[test]
    fn test_rc_unsized() {
        unsafe {
            let p = Rc::new(1) as Rc<Debug>;
            let a: *const Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Rc<Debug> = IntrusivePointer::from_raw(r);
            let a2: *const Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }

    #[test]
    fn test_arc_unsized() {
        unsafe {
            let p = Arc::new(1) as Arc<Debug>;
            let a: *const Debug = &*p;
            let b: (usize, usize) = mem::transmute(a);
            let r = IntrusivePointer::into_raw(p);
            assert_eq!(a, r);
            assert_eq!(b, mem::transmute(r));
            let p2: Arc<Debug> = IntrusivePointer::from_raw(r);
            let a2: *const Debug = &*p2;
            assert_eq!(a, a2);
            assert_eq!(b, mem::transmute(a2));
        }
    }
}
