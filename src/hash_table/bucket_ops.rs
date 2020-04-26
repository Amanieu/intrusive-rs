// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::marker::PhantomData;
use core::ptr::NonNull;

use crate::adapter::Adapter;
use crate::linked_list::{LinkedList, LinkedListOps};
use crate::pointer_ops::PointerOps;
use crate::singly_linked_list::{SinglyLinkedList, SinglyLinkedListOps};

/// Trait for bucket operations.
///
/// # Time Complexities
///
/// |Operation|`SinglyLinkedList`|`LinkedList`|
/// |-|-|-|
/// |`is_empty`|`O(1)`|`O(1)`|
/// |`clear`|`O(n)`|`O(n)`|
/// |`fast_clear`|`O(1)`|`O(1)`|
/// |`is_null`|`O(1)`|`O(1)`|
/// |`get`|`O(1)`|`O(1)`|
/// |`cursor_from_ptr`|`O(1)`|`O(1)`|
/// |`find_prev`|`O(n)`|`O(n)`|
/// |`next`|`O(1)`|`O(1)`|
/// |`insert_after`|`O(1)`|`O(1)`|
/// |`remove_next`|`O(1)`|`O(1)`|
/// |`remove`|`O(n)`|`O(1)`|
/// |`replace_next_with`|`O(1)`|`O(1)`|
/// |`replace_with`|`O(n)`|`O(1)`|
pub unsafe trait BucketOps {
    /// Collection-specific pointer conversions which allow an object to
    /// be inserted in an intrusive collection.
    type PointerOps: PointerOps;

    /// The hash table bucket type.
    type Bucket;

    /// The cursor over elements within a bucket.
    type Cursor: Clone;

    /// Returns `true` if the bucket is empty.
    unsafe fn is_empty(&self, bucket: &Self::Bucket) -> bool;

    /// Removes all elements from the bucket.
    ///
    /// This will unlink all objects currently in the bucket, which requires iterating through
    /// all elements in the bucket. Each element is converted back into an owned pointer and then dropped.
    unsafe fn clear(&mut self, bucket: &mut Self::Bucket);

    /// Empties the bucket without unlinking or freeing the objects within it.
    ///
    /// Since this does not unlink any objects, any attempts to link these objects into another intrusive collection will fail,
    /// but will not cause any memory unsafety.
    /// To unlink those objects manually, you must call the `force_unlink` function on them.
    unsafe fn fast_clear(&mut self, bucket: &mut Self::Bucket);

    /// Returns `true` if the cursor is pointing to the null object.
    unsafe fn is_null(&self, bucket: &Self::Bucket, cursor: &Self::Cursor) -> bool;

    /// Returns a reference to the object that the cursor is currently pointing to.
    ///
    /// This returns `None` if the cursor is pointing to the null object.
    unsafe fn get(
        &self,
        bucket: &Self::Bucket,
        cursor: &Self::Cursor,
    ) -> Option<&<Self::PointerOps as PointerOps>::Value>;

    /// Returns a null cursor for this bucket.
    unsafe fn cursor(&self, bucket: &Self::Bucket) -> Self::Cursor;

    /// Creates a cursor from a pointer to an element.
    ///
    /// # Safety
    /// `ptr` must be a pointer to an object that is a member of this bucket.
    unsafe fn cursor_from_ptr(
        &self,
        bucket: &Self::Bucket,
        ptr: *const <Self::PointerOps as PointerOps>::Value,
    ) -> Self::Cursor;

    /// Searches the bucket for the first element where `is_match` returns `true`.
    ///
    /// Returns `None` if no match was found, or the bucket was empty.
    unsafe fn find_prev<F>(&self, bucket: &Self::Bucket, is_match: F) -> Option<Self::Cursor>
    where
        for<'b> F: FnMut(&'b <Self::PointerOps as PointerOps>::Value) -> bool;

    /// Returns a cursor that points to the next element of the bucket.
    ///
    /// If `self` points to the null object,
    /// then it will return a cursor that points to the first element of the bucket.
    ///
    /// If `self` points to the last element of the bucket,
    /// then it will return a cursor that points to the null object.
    unsafe fn next(&self, bucket: &Self::Bucket, prev: &Self::Cursor) -> Self::Cursor;

    /// Inserts a new element into the bucket after the current one.
    ///
    /// If the cursor currently points to the null object,
    /// then the new element is inserted at the front of the bucket.
    ///
    /// # Panics
    /// Panics if the new element is already linked to a different intrusive collection.
    unsafe fn insert_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    );

    /// Removes the next element from the bucket.
    ///
    /// Returns a pointer to the element that was removed.
    /// The cursor is not moved.
    ///
    /// If the cursor currently points to the last element of the bucket, then no element is removed  and `None` is returned.
    unsafe fn remove_next(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer>;

    /// Removes the current element from the bucket.
    ///
    /// Returns a pointer to the element that was removed.
    /// The cursor is advanced to the next element of the bucket.
    ///
    /// If the cursor currently points to the null object, then no element is removed  and `None` is returned.
    unsafe fn remove(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer>;

    /// Removes the next element from the bucket, and inserts another object in its place.
    ///
    /// Returns a pointer to the element that was removed.
    /// The cursor is not moved.
    ///
    /// If the cursor currently points to the last element of the bucket, then `Err(value)` is returned.
    ///
    /// # Panics
    /// Panics if the new element is already linked to a different intrusive collection.
    unsafe fn replace_next_with(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>;

    /// Removes the current element from the bucket, and inserts another object in its place.
    ///
    /// Returns a pointer to the element that was removed.
    /// The cursor points to the newly added element.
    ///
    /// If the cursor currently points to the null object, then `Err(value)` is returned.
    ///
    /// # Panics
    /// Panics if the new element is already linked to a different intrusive collection.
    unsafe fn replace_with(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>;
}

/// The default implementation of `BucketOps`.
pub struct DefaultBucketOps<T>(PhantomData<T>);

impl<T> Default for DefaultBucketOps<T> {
    #[inline]
    fn default() -> Self {
        DefaultBucketOps(PhantomData)
    }
}

unsafe impl<A: Adapter> BucketOps for DefaultBucketOps<SinglyLinkedList<A>>
where
    A::LinkOps: SinglyLinkedListOps,
{
    type Bucket = SinglyLinkedList<A>;
    type PointerOps = A::PointerOps;
    type Cursor = Option<NonNull<<Self::PointerOps as PointerOps>::Value>>;

    #[inline]
    unsafe fn is_empty(&self, bucket: &Self::Bucket) -> bool {
        bucket.is_empty()
    }

    #[inline]
    unsafe fn clear(&mut self, bucket: &mut Self::Bucket) {
        bucket.clear();
    }

    #[inline]
    unsafe fn fast_clear(&mut self, bucket: &mut Self::Bucket) {
        bucket.fast_clear();
    }

    #[inline]
    unsafe fn is_null(&self, _bucket: &Self::Bucket, cursor: &Self::Cursor) -> bool {
        cursor.is_none()
    }

    unsafe fn get(
        &self,
        bucket: &Self::Bucket,
        cursor: &Self::Cursor,
    ) -> Option<&<Self::PointerOps as PointerOps>::Value> {
        if let Some(x) = bucket.cursor_from_ptr(cursor.as_ref()?.as_ptr()).get() {
            Some(&*(x as *const _))
        } else {
            None
        }
    }

    #[inline]
    unsafe fn cursor(&self, _bucket: &Self::Bucket) -> Self::Cursor {
        None
    }

    #[inline]
    unsafe fn cursor_from_ptr(
        &self,
        _bucket: &Self::Bucket,
        ptr: *const <Self::PointerOps as PointerOps>::Value,
    ) -> Self::Cursor {
        NonNull::new(ptr as *mut _)
    }

    #[inline]
    unsafe fn find_prev<F>(&self, bucket: &Self::Bucket, mut is_match: F) -> Option<Self::Cursor>
    where
        for<'b> F: FnMut(&'b <Self::PointerOps as PointerOps>::Value) -> bool,
    {
        let mut cursor = bucket.cursor();

        while let Some(value) = cursor.peek_next().get() {
            if is_match(value) {
                if let Some(prev) = cursor.get() {
                    return Some(NonNull::new(prev as *const _ as *mut _));
                } else {
                    return Some(None);
                }
            }
            cursor.move_next();
        }

        None
    }

    #[inline]
    unsafe fn next(&self, bucket: &Self::Bucket, prev: &Self::Cursor) -> Self::Cursor {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor()
        };

        cursor.move_next();

        if let Some(next) = cursor.get() {
            NonNull::new(next as *const _ as *mut _)
        } else {
            None
        }
    }

    #[inline]
    unsafe fn insert_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.insert_after(value)
    }

    #[inline]
    unsafe fn remove_next(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer> {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.remove_next()
    }

    #[inline]
    unsafe fn remove(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer> {
        if let Some(x) = current {
            if let Some(prev) =
                self.find_prev(bucket, |value| value as *const _ == x.as_ptr() as *const _)
            {
                if let Some(ret) = self.remove_next(bucket, &prev) {
                    *current = self.next(bucket, &prev);

                    return Some(ret);
                }
            }
        }

        None
    }

    #[inline]
    unsafe fn replace_next_with(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>
    {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.replace_next_with(value)
    }

    #[inline]
    unsafe fn replace_with(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>
    {
        if let Some(x) = current {
            if let Some(prev) =
                self.find_prev(bucket, |value| value as *const _ == x.as_ptr() as *const _)
            {
                let ret = self.replace_next_with(bucket, &prev, value);

                if ret.is_ok() {
                    *current = self.next(bucket, &prev);
                }

                return ret;
            }
        }

        Err(value)
    }
}

unsafe impl<A: Adapter> BucketOps for DefaultBucketOps<LinkedList<A>>
where
    A::LinkOps: LinkedListOps,
{
    type Bucket = LinkedList<A>;
    type PointerOps = A::PointerOps;
    type Cursor = Option<NonNull<<Self::PointerOps as PointerOps>::Value>>;

    #[inline]
    unsafe fn is_empty(&self, bucket: &Self::Bucket) -> bool {
        bucket.is_empty()
    }

    #[inline]
    unsafe fn clear(&mut self, bucket: &mut Self::Bucket) {
        bucket.clear();
    }

    #[inline]
    unsafe fn fast_clear(&mut self, bucket: &mut Self::Bucket) {
        bucket.fast_clear();
    }

    #[inline]
    unsafe fn is_null(&self, _bucket: &Self::Bucket, cursor: &Self::Cursor) -> bool {
        cursor.is_none()
    }

    unsafe fn get(
        &self,
        bucket: &Self::Bucket,
        cursor: &Self::Cursor,
    ) -> Option<&<Self::PointerOps as PointerOps>::Value> {
        if let Some(x) = bucket.cursor_from_ptr(cursor.as_ref()?.as_ptr()).get() {
            Some(&*(x as *const _))
        } else {
            None
        }
    }

    #[inline]
    unsafe fn cursor(&self, _bucket: &Self::Bucket) -> Self::Cursor {
        None
    }

    #[inline]
    unsafe fn cursor_from_ptr(
        &self,
        _bucket: &Self::Bucket,
        ptr: *const <Self::PointerOps as PointerOps>::Value,
    ) -> Self::Cursor {
        NonNull::new(ptr as *mut _)
    }

    #[inline]
    unsafe fn find_prev<F>(&self, bucket: &Self::Bucket, mut is_match: F) -> Option<Self::Cursor>
    where
        for<'b> F: FnMut(&'b <Self::PointerOps as PointerOps>::Value) -> bool,
    {
        let mut cursor = bucket.cursor();

        while let Some(value) = cursor.peek_next().get() {
            if is_match(value) {
                if let Some(prev) = cursor.get() {
                    return Some(NonNull::new(prev as *const _ as *mut _));
                } else {
                    return Some(None);
                }
            }
            cursor.move_next();
        }

        None
    }

    #[inline]
    unsafe fn next(&self, bucket: &Self::Bucket, prev: &Self::Cursor) -> Self::Cursor {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor()
        };

        cursor.move_next();

        if let Some(next) = cursor.get() {
            NonNull::new(next as *const _ as *mut _)
        } else {
            None
        }
    }

    #[inline]
    unsafe fn insert_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.insert_after(value)
    }

    #[inline]
    unsafe fn remove_next(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer> {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.move_next();

        cursor.remove()
    }

    #[inline]
    unsafe fn remove(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer> {
        let mut cursor = bucket.cursor_mut_from_ptr((*current)?.as_ptr());

        let ret = cursor.remove();

        *current = cursor
            .get()
            .map(|x| NonNull::new_unchecked(x as *const _ as *mut _));

        ret
    }

    #[inline]
    unsafe fn replace_next_with(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>
    {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.move_next();

        cursor.replace_with(value)
    }

    #[inline]
    unsafe fn replace_with(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>
    {
        if let Some(x) = current {
            let mut cursor = bucket.cursor_mut_from_ptr(x.as_ptr());

            let ret = cursor.replace_with(value);

            *current = cursor
                .get()
                .map(|x| NonNull::new_unchecked(x as *const _ as *mut _));

            ret
        } else {
            Err(value)
        }
    }
}
