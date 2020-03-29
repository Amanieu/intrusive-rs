// Copyright 2020 Amari Robinson
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
use core::marker::PhantomData;


pub unsafe trait PointerOps {
    type Value: ?Sized;
    type Pointer;

    /// Constructs an owned pointer from a raw pointer.
    /// 
    /// # Safety
    /// The raw pointer must have been previously returned by `into_raw`.
    unsafe fn from_raw(&self, value: *const Self::Value) -> Self::Pointer;

    /// Consumes the owned pointer and returns a raw pointer to the owned object.
    fn into_raw(&self, ptr: Self::Pointer) -> *const Self::Value;
}

/// The default implementation that is used when `PointerOps`
/// is not specified in the invocation of `intrusive_adapter!`.
pub struct DefaultPointerOps<Pointer>(PhantomData<Pointer>);

impl<Pointer> DefaultPointerOps<Pointer> {
    #[inline]
    pub const fn new() -> DefaultPointerOps<Pointer> {
        DefaultPointerOps(PhantomData)
    }
}

impl<Pointer> Clone for DefaultPointerOps<Pointer> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<Pointer> Copy for DefaultPointerOps<Pointer> {}

impl<Pointer> Default for DefaultPointerOps<Pointer> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

unsafe impl<'a, T: ?Sized> PointerOps for DefaultPointerOps<&'a T> {
    type Value = T;
    type Pointer = &'a T;

    #[inline]
    unsafe fn from_raw(&self, raw: *const T) -> &'a T {
        &*raw
    }

    #[inline]
    fn into_raw(&self, ptr: &'a T) -> *const T {
        ptr
    }
}

unsafe impl<T: ?Sized> PointerOps for DefaultPointerOps<UnsafeRef<T>> {
    type Value = T;
    type Pointer = UnsafeRef<T>;

    #[inline]
    unsafe fn from_raw(&self, raw: *const T) -> UnsafeRef<T> {
        UnsafeRef::from_raw(raw as *mut T)
    }

    #[inline]
    fn into_raw(&self, ptr: UnsafeRef<T>) -> *const T {
        UnsafeRef::into_raw(ptr) as *const T
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> PointerOps for DefaultPointerOps<Box<T>> {
    type Value = T;
    type Pointer = Box<T>;

    #[inline]
    unsafe fn from_raw(&self, raw: *const T) -> Box<T> {
        Box::from_raw(raw as *mut T)
    }

    #[inline]
    fn into_raw(&self, ptr: Box<T>) -> *const T {
        Box::into_raw(ptr) as *const T
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> PointerOps for DefaultPointerOps<Rc<T>> {
    type Value = T;
    type Pointer = Rc<T>;

    #[inline]
    unsafe fn from_raw(&self, raw: *const T) -> Rc<T> {
        Rc::from_raw(raw)
    }

    #[inline]
    fn into_raw(&self, ptr: Rc<T>) -> *const T {
        Rc::into_raw(ptr)
    }
}

#[cfg(feature = "alloc")]
unsafe impl<T: ?Sized> PointerOps for DefaultPointerOps<Arc<T>> {
    type Value = T;
    type Pointer = Arc<T>;

    #[inline]
    unsafe fn from_raw(&self, raw: *const T) -> Arc<T> {
        Arc::from_raw(raw)
    }

    #[inline]
    fn into_raw(&self, ptr: Arc<T>) -> *const T {
        Arc::into_raw(ptr)
    }
}

#[inline]
pub(crate) unsafe fn clone_pointer_from_raw<T: PointerOps>(
    pointer_ops: &T,
    ptr: *const T::Value,
) -> T::Pointer
where
    T::Pointer: Clone,
{
    use core::mem::ManuallyDrop;
    use core::ops::Deref;

    /// Guard which converts an pointer back into its raw version
    /// when it gets dropped. This makes sure we also perform a full
    /// `from_raw` and `into_raw` round trip - even in the case of panics.
    struct PointerGuard<'a, T: PointerOps> {
        pointer: ManuallyDrop<T::Pointer>,
        pointer_ops: &'a T,
    }

    impl<'a, T: PointerOps> Drop for PointerGuard<'a, T> {
        #[inline]
        fn drop(&mut self) {
            // Prevent shared pointers from being released by converting them
            // back into the raw pointers
            let _ = self
                .pointer_ops
                .into_raw(unsafe { ManuallyDrop::take(&mut self.pointer) });
        }
    }

    let holder = PointerGuard {
        pointer: ManuallyDrop::new(pointer_ops.from_raw(ptr)),
        pointer_ops,
    };
    holder.pointer.deref().clone()
}
