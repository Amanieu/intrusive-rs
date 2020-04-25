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
use crate::unchecked_option::UncheckedOptionExt;
use crate::xor_linked_list::{XorLinkedList, XorLinkedListOps};

pub unsafe trait BucketOps {
    type PointerOps: PointerOps;
    type Bucket;
    type Cursor: Clone;

    unsafe fn is_empty(&self, bucket: &Self::Bucket) -> bool;

    unsafe fn clear(&mut self, bucket: &mut Self::Bucket);

    unsafe fn fast_clear(&mut self, bucket: &mut Self::Bucket);

    unsafe fn is_null(&self, bucket: &Self::Bucket, cursor: &Self::Cursor) -> bool;

    unsafe fn get(
        &self,
        bucket: &Self::Bucket,
        cursor: &Self::Cursor,
    ) -> Option<&<Self::PointerOps as PointerOps>::Value>;

    unsafe fn cursor(&self, bucket: &Self::Bucket) -> Self::Cursor;

    unsafe fn cursor_from_ptr(
        &self,
        bucket: &Self::Bucket,
        ptr: *const <Self::PointerOps as PointerOps>::Value,
    ) -> Self::Cursor;

    unsafe fn find_prev<F>(&self, bucket: &Self::Bucket, is_match: F) -> Option<Self::Cursor>
    where
        for<'b> F: FnMut(&'b <Self::PointerOps as PointerOps>::Value) -> bool;

    unsafe fn next(&self, bucket: &Self::Bucket, prev: &Self::Cursor) -> Self::Cursor;

    unsafe fn insert_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    );

    unsafe fn remove_next(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer>;

    unsafe fn remove(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
    ) -> Option<<Self::PointerOps as PointerOps>::Pointer>;

    unsafe fn replace_next_with(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>;

    unsafe fn replace_with(
        &mut self,
        bucket: &mut Self::Bucket,
        current: &mut Self::Cursor,
        value: <Self::PointerOps as PointerOps>::Pointer,
    ) -> Result<<Self::PointerOps as PointerOps>::Pointer, <Self::PointerOps as PointerOps>::Pointer>;

    unsafe fn splice_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        other: Self::Bucket,
    ) -> Result<(), Self::Bucket>;
}

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

    #[inline]
    unsafe fn splice_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        other: Self::Bucket,
    ) -> Result<(), Self::Bucket> {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.splice_after(other);

        Ok(())
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

    #[inline]
    unsafe fn splice_after(
        &mut self,
        bucket: &mut Self::Bucket,
        prev: &Self::Cursor,
        other: Self::Bucket,
    ) -> Result<(), Self::Bucket> {
        let mut cursor = if let Some(prev) = prev {
            bucket.cursor_mut_from_ptr(prev.as_ptr())
        } else {
            bucket.cursor_mut()
        };

        cursor.splice_after(other);

        Ok(())
    }
}
