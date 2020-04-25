// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::borrow::Borrow;
use core::fmt;
#[cfg(feature = "nightly")]
use core::intrinsics::unlikely;
use core::iter::{ExactSizeIterator, Extend, FromIterator, FusedIterator, IntoIterator};
use core::ops::Index;

use crate::adapter::Adapter;
use crate::key_adapter::KeyAdapter;
use crate::link_ops::{self, DefaultLinkOps};
use crate::linked_list;
use crate::pointer_ops::{DefaultPointerOps, PointerOps};
use crate::singly_linked_list;
use crate::unchecked_option::UncheckedOptionExt;
use crate::unsafe_ref::UnsafeRef;
use crate::xor_linked_list;

use crate::hash_table::array::Array;
use crate::hash_table::bucket_ops::{BucketOps, DefaultBucketOps};
use crate::hash_table::hash_ops::{DefaultHashOps, HashOps};
use crate::hash_table::load_factor::LoadFactor;

#[cfg(not(feature = "nightly"))]
#[inline]
fn unlikely(b: bool) -> bool {
    b
}

// =============================================================================
// HashTableAdapter
// =============================================================================

pub trait HashTableAdapter {
    type PointerOps: PointerOps;

    type BucketOps: BucketOps<PointerOps = Self::PointerOps>;

    type KeyOps;

    type HashOps;

    fn pointer_ops(&self) -> &Self::PointerOps;

    fn bucket_ops(&self) -> &Self::BucketOps;

    fn bucket_ops_mut(&mut self) -> &mut Self::BucketOps;

    fn key_ops(&self) -> &Self::KeyOps;

    fn hash_ops(&self) -> &Self::HashOps;
}

// =============================================================================
// KeyOps
// =============================================================================

pub trait KeyOps<'a, T: ?Sized> {
    type Key;

    fn key(&self, value: &'a T) -> Self::Key;
}

// =============================================================================
// HashTable
// =============================================================================

pub struct HashTable<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    pub(super) adapter: A,
    pub(super) buckets: B,
    pub(super) len: usize,
    pub(super) load_factor_target: LoadFactor,
}

impl<A: HashTableAdapter + Default, B: Array<<A::BucketOps as BucketOps>::Bucket> + Default>
    HashTable<A, B>
{
    #[inline]
    pub fn new() -> HashTable<A, B> {
        HashTable {
            adapter: Default::default(),
            buckets: Default::default(),
            len: 0,
            load_factor_target: unsafe { LoadFactor::new_unchecked(24, 8) },
        }
    }
}

impl<A: HashTableAdapter + Default, B: Array<<A::BucketOps as BucketOps>::Bucket> + Default> Default
    for HashTable<A, B>
{
    #[inline]
    fn default() -> HashTable<A, B> {
        HashTable::new()
    }
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> HashTable<A, B> {
    #[inline]
    pub unsafe fn from_parts(adapter: A, buckets: B, len: usize) -> HashTable<A, B> {
        HashTable {
            adapter,
            buckets,
            len,
            load_factor_target: LoadFactor::new_unchecked(24, 8),
        }
    }
}

#[inline]
fn checked_index_from_hash(hash: u64, bucket_count: usize) -> Option<usize> {
    hash.checked_rem(bucket_count as u64).map(|x| x as usize)
}

#[inline]
fn index_from_hash(hash: u64, bucket_count: usize) -> usize {
    checked_index_from_hash(hash, bucket_count).expect("bucket count must be greater than 0")
}

impl<'a, A, B> fmt::Debug for HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    <A::PointerOps as PointerOps>::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<A, B> HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn capacity(&self) -> usize {
        self.buckets.capacity()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    #[inline]
    pub fn bucket_cursor(&self) -> BucketCursor<'_, A, B> {
        BucketCursor {
            table: self,
            index: None,
        }
    }

    #[inline]
    pub fn bucket_cursor_mut(&mut self) -> BucketCursorMut<'_, A, B> {
        BucketCursorMut {
            table: self,
            index: None,
        }
    }

    #[inline]
    pub fn bucket_cursor_from_hash(&self, hash: u64) -> BucketCursor<'_, A, B> {
        let bucket_count = self.buckets.borrow().len();

        BucketCursor {
            index: checked_index_from_hash(hash, bucket_count),
            table: self,
        }
    }

    #[inline]
    pub fn bucket_cursor_mut_from_hash(&mut self, hash: u64) -> BucketCursorMut<'_, A, B> {
        let bucket_count = self.buckets.borrow().len();

        BucketCursorMut {
            index: checked_index_from_hash(hash, bucket_count),
            table: self,
        }
    }

    pub fn iter(&self) -> Iter<'_, A, B> {
        Iter {
            table: self,
            bucket_cursor: None,
            len: self.len,
        }
    }

    pub fn drain(&mut self) -> Drain<'_, A, B> {
        Drain {
            len: self.len,
            table: self,
            bucket_cursor: None,
        }
    }

    pub fn clear(&mut self) {
        for bucket in self.buckets.borrow_mut() {
            unsafe {
                self.adapter.bucket_ops_mut().clear(bucket);
            }
        }

        self.len = 0;
    }

    pub fn fast_clear(&mut self) {
        for bucket in self.buckets.borrow_mut() {
            unsafe {
                self.adapter.bucket_ops_mut().fast_clear(bucket);
            }
        }

        self.len = 0;
    }
}

#[inline]
fn compute_hash<A: HashTableAdapter>(
    adapter: &A,
    value: <A::PointerOps as PointerOps>::Pointer,
) -> (<A::PointerOps as PointerOps>::Pointer, u64)
where
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
{
    /// Guard which converts an pointer back from its raw version
    /// when it gets dropped. This makes sure that the pointer is
    /// dropped during panics.
    struct PointerGuard<'a, T: PointerOps> {
        pointer: Option<&'a T::Value>,
        pointer_ops: *const T,
    }

    impl<'a, T: PointerOps> Drop for PointerGuard<'a, T> {
        #[inline]
        fn drop(&mut self) {
            if let Some(ptr) = self.pointer.take() {
                unsafe {
                    (*self.pointer_ops).from_raw(ptr);
                }
            }
        }
    }

    let raw = adapter.pointer_ops().into_raw(value);

    let mut holder = PointerGuard {
        pointer: Some(unsafe { &*raw }),
        pointer_ops: adapter.pointer_ops(),
    };

    let key = adapter.key_ops().key(unsafe { &*raw });
    let hash = adapter.hash_ops().hash(&key);

    holder.pointer = None;

    let value = unsafe { adapter.pointer_ops().from_raw(raw) };

    (value, hash)
}

impl<A, B> HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
{
    #[inline(always)]
    fn rehash_move(&mut self, mut new_buckets: B) -> B {
        let new_bucket_count = new_buckets.borrow().len();

        for bucket in self.buckets.borrow_mut().iter_mut() {
            let cursor = unsafe { self.adapter.bucket_ops().cursor(bucket) };

            while let Some(value) =
                unsafe { self.adapter.bucket_ops_mut().remove_next(bucket, &cursor) }
            {
                let (value, hash) = compute_hash(&self.adapter, value);

                let index =
                    unsafe { checked_index_from_hash(hash, new_bucket_count).unwrap_unchecked() };

                let new_bucket = &mut new_buckets.borrow_mut()[index];

                unsafe {
                    let cursor = self.adapter.bucket_ops().cursor(new_bucket);

                    self.adapter
                        .bucket_ops_mut()
                        .insert_after(new_bucket, &cursor, value);
                }
            }

            // the bucket is already empty. we're just telling the compiler that this is always the case.
            unsafe {
                self.adapter.bucket_ops_mut().fast_clear(bucket);
            }
        }

        core::mem::replace(&mut self.buckets, new_buckets)
    }

    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        // panic because if a `usize` overflows, the program is degenerate and therefore unsupported.
        let new_len = self.len.checked_add(additional).expect("capacity overflow");

        match self.buckets.reserve(new_len) {
            Some(new_buckets) => {
                self.rehash_move(new_buckets);
            }
            None => {
                assert_ne!(self.buckets.borrow().len(), 0, "bad bucket array");
            }
        }
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        if let Some(new_buckets) = self.buckets.shrink_to(self.len) {
            self.rehash_move(new_buckets);
        }
    }

    #[inline]
    pub fn insert<'b>(
        &mut self,
        value: <A::PointerOps as PointerOps>::Pointer,
    ) -> CursorMut<'_, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        self.reserve(1);

        let (value, hash) = compute_hash(&self.adapter, value);

        let mut cursor = self.bucket_cursor_mut_from_hash(hash).into_cursor_mut();

        cursor.insert_after(value);
        cursor.move_next();

        cursor
    }

    pub fn remove<'b, Q: ?Sized>(&mut self, k: &Q) -> Option<<A::PointerOps as PointerOps>::Pointer>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        if self.is_empty() {
            return None;
        }

        if let RawEntryMut::Occupied(mut entry) = self.raw_entry_mut().from_key(k) {
            entry.remove()
        } else {
            None
        }
    }
}

impl<A, B> HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline(always)]
    fn find_internal<F>(
        &self,
        hash: u64,
        is_match: F,
    ) -> (
        usize,
        <A::BucketOps as BucketOps>::Cursor,
        <A::BucketOps as BucketOps>::Cursor,
    )
    where
        for<'b> F: FnMut(&'b <A::PointerOps as PointerOps>::Value) -> bool,
    {
        let bucket_count = self.buckets.borrow().len();

        if unlikely(bucket_count == 0) {
            unreachable!("program is degenerate. a zero-sized bucket array is not valid.");
        }

        let index = index_from_hash(hash, bucket_count);

        let bucket = &self.buckets.borrow()[index];

        if !self.is_empty() {
            let raw_cursor = unsafe { self.adapter.bucket_ops().find_prev(bucket, is_match) };

            if let Some(raw_cursor) = raw_cursor {
                let next = unsafe { self.adapter.bucket_ops().next(bucket, &raw_cursor) };

                return (index, raw_cursor, next);
            }
        }

        let raw_cursor = unsafe { self.adapter.bucket_ops().cursor(bucket) };
        let next = raw_cursor.clone();

        return (index, raw_cursor, next);
    }
}

impl<A, B> HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
{
    pub fn get<'b, Q: ?Sized>(&self, k: &Q) -> Option<&<A::PointerOps as PointerOps>::Value>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        self.raw_entry().from_key(k).get()
    }

    #[inline]
    pub fn contains_key<'b, Q: ?Sized>(&self, k: &Q) -> bool
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        !self.raw_entry().from_key(k).is_null()
    }

    #[inline]
    pub fn raw_entry(&self) -> RawEntryBuilder<'_, A, B> {
        RawEntryBuilder { table: self }
    }

    #[inline]
    pub fn raw_entry_mut(&mut self) -> RawEntryBuilderMut<'_, A, B> {
        RawEntryBuilderMut { table: self }
    }
}

impl<A, B> HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&<A::PointerOps as PointerOps>::Value) -> bool,
    {
        let mut bucket_cursor = self.bucket_cursor_mut();
        bucket_cursor.move_next();

        while !bucket_cursor.is_null() {
            let mut cursor = bucket_cursor.cursor_mut();

            loop {
                if let Some(next) = cursor.peek_next().get() {
                    if !f(next) {
                        cursor.remove_next();
                    } else {
                        cursor.move_next();
                    }
                    continue;
                }
                break;
            }

            bucket_cursor.move_next();
        }
    }
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Drop for HashTable<A, B> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> IntoIterator
    for &'a HashTable<A, B>
{
    type Item = &'a <A::PointerOps as PointerOps>::Value;
    type IntoIter = Iter<'a, A, B>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> IntoIterator
    for HashTable<A, B>
{
    type Item = <A::PointerOps as PointerOps>::Pointer;
    type IntoIter = IntoIter<A, B>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            len: self.len(),
            table: self,
            bucket_cursor: None,
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    FromIterator<<A::PointerOps as PointerOps>::Pointer> for HashTable<A, B>
where
    HashTable<A, B>: Default,
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
    <A::KeyOps as KeyOps<'a, <A::PointerOps as PointerOps>::Value>>::Key: Eq,
    <A::PointerOps as PointerOps>::Value: 'a,
{
    #[inline]
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = <A::PointerOps as PointerOps>::Pointer>,
    {
        let mut m = HashTable::default();

        for value in iter {
            m.insert(value);
        }

        m
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    Extend<<A::PointerOps as PointerOps>::Pointer> for HashTable<A, B>
where
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
    <A::KeyOps as KeyOps<'a, <A::PointerOps as PointerOps>::Value>>::Key: Eq,
    <A::PointerOps as PointerOps>::Value: 'a,
{
    #[inline]
    fn extend<T>(&mut self, iter: T)
    where
        T: IntoIterator<Item = <A::PointerOps as PointerOps>::Pointer>,
    {
        for value in iter {
            self.insert(value);
        }
    }
}

impl<'a, 'b, A, B, Q> Index<&'b Q> for HashTable<A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    A::KeyOps: for<'c> KeyOps<'c, <A::PointerOps as PointerOps>::Value>,
    <A::KeyOps as KeyOps<'a, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
    A::HashOps: HashOps<Q>,
    Q: Eq,
    <A::PointerOps as PointerOps>::Value: 'a,
{
    type Output = <A::PointerOps as PointerOps>::Value;

    fn index(&self, index: &'b Q) -> &Self::Output {
        self.get(index).expect("no entry found for key")
    }
}

// =============================================================================
// BucketCursor
// =============================================================================

pub struct BucketCursor<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    pub(super) table: &'a HashTable<A, B>,
    pub(super) index: Option<usize>,
}
impl<'a, A, B> BucketCursor<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn is_null(&self) -> bool {
        self.index.is_none()
    }

    #[inline]
    pub fn get(&self) -> Option<&<A::BucketOps as BucketOps>::Bucket> {
        Some(&self.table.buckets.borrow()[self.index?])
    }

    #[inline]
    pub fn index(&self) -> Option<usize> {
        self.index
    }

    #[inline]
    pub fn move_next(&mut self) {
        if let Some(index) = self.index {
            if index < self.table.buckets.borrow().len().saturating_sub(1) {
                self.index = Some(index + 1);
            } else {
                self.index = None;
            }
        } else if self.table.buckets.borrow().len() > 0 {
            self.index = Some(0);
        }
    }

    #[inline]
    pub fn move_prev(&mut self) {
        if let Some(index) = self.index {
            if index > 0 {
                self.index = Some(index - 1);
            } else {
                self.index = None;
            }
        } else if self.table.buckets.borrow().len() > 0 {
            self.index = Some(self.table.buckets.borrow().len() - 1);
        }
    }

    #[inline]
    pub fn peek_next(&self) -> BucketCursor<'_, A, B> {
        let mut cursor = self.clone();
        cursor.move_next();
        cursor
    }

    #[inline]
    pub fn peek_prev(&self) -> BucketCursor<'_, A, B> {
        let mut cursor = self.clone();
        cursor.move_next();
        cursor
    }

    #[inline]
    pub fn cursor(&self) -> Cursor<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn cursor_from_ptr(
        &self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn into_cursor(self) -> Cursor<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn into_cursor_from_ptr(
        self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn front(&self) -> Cursor<'_, A, B> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Clone
    for BucketCursor<'a, A, B>
{
    #[inline]
    fn clone(&self) -> Self {
        BucketCursor {
            table: self.table,
            index: self.index.clone(),
        }
    }
}

// =============================================================================
// BucketCursorMut
// =============================================================================

pub struct BucketCursorMut<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    pub(super) table: &'a mut HashTable<A, B>,
    pub(super) index: Option<usize>,
}

impl<'a, A, B> BucketCursorMut<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn is_null(&self) -> bool {
        self.index.is_none()
    }

    #[inline]
    pub fn get(&self) -> Option<&<A::BucketOps as BucketOps>::Bucket> {
        Some(&self.table.buckets.borrow()[self.index?])
    }

    #[inline]
    pub fn get_mut(&mut self) -> Option<&mut <A::BucketOps as BucketOps>::Bucket> {
        Some(&mut self.table.buckets.borrow_mut()[self.index?])
    }

    #[inline]
    pub fn index(&self) -> Option<usize> {
        self.index
    }

    #[inline]
    pub fn as_bucket_cursor(&self) -> BucketCursor<'_, A, B> {
        BucketCursor {
            table: self.table,
            index: self.index,
        }
    }

    #[inline]
    pub fn move_next(&mut self) {
        if let Some(index) = self.index {
            if index < self.table.buckets.borrow().len().saturating_sub(1) {
                self.index = Some(index + 1);
            } else {
                self.index = None;
            }
        } else if self.table.buckets.borrow().len() > 0 {
            self.index = Some(0);
        }
    }

    #[inline]
    pub fn move_prev(&mut self) {
        if let Some(index) = self.index {
            if index > 0 {
                self.index = Some(index - 1);
            } else {
                self.index = None;
            }
        } else if self.table.buckets.borrow().len() > 0 {
            self.index = Some(self.table.buckets.borrow().len() - 1);
        }
    }

    #[inline]
    pub fn peek_next(&self) -> BucketCursor<'_, A, B> {
        let mut cursor = self.as_bucket_cursor();
        cursor.move_next();
        cursor
    }

    #[inline]
    pub fn peek_prev(&self) -> BucketCursor<'_, A, B> {
        let mut cursor = self.as_bucket_cursor();
        cursor.move_prev();
        cursor
    }

    #[inline]
    pub fn cursor(&self) -> Cursor<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            CursorMut {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            CursorMut {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn cursor_from_ptr(
        &self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn cursor_mut_from_ptr(
        &mut self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorMut<'_, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            CursorMut {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            CursorMut {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn into_cursor(self) -> Cursor<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn into_cursor_mut(self) -> CursorMut<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            CursorMut {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor(bucket)
                })),
                table: self.table,
            }
        } else {
            CursorMut {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn into_cursor_from_ptr(
        self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            Cursor {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            Cursor {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub unsafe fn into_cursor_mut_from_ptr(
        self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorMut<'a, A, B> {
        if let Some(index) = self.index {
            let bucket = &self.table.buckets.borrow()[index];

            CursorMut {
                position: Some((index, unsafe {
                    self.table.adapter.bucket_ops().cursor_from_ptr(bucket, ptr)
                })),
                table: self.table,
            }
        } else {
            CursorMut {
                position: None,
                table: self.table,
            }
        }
    }

    #[inline]
    pub fn front(&self) -> Cursor<'_, A, B> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<'_, A, B> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }
}

// =============================================================================
// Cursor
// =============================================================================

pub struct Cursor<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    pub(super) table: &'a HashTable<A, B>,
    pub(super) position: Option<(usize, <A::BucketOps as BucketOps>::Cursor)>,
}

impl<'a, A, B> Cursor<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn is_null(&self) -> bool {
        if let Some((index, current)) = &self.position {
            let bucket = &self.table.buckets.borrow()[*index];

            unsafe { self.table.adapter.bucket_ops().is_null(bucket, current) }
        } else {
            false
        }
    }

    #[inline]
    pub fn get(&self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        if let Some((index, current)) = &self.position {
            let bucket = &self.table.buckets.borrow()[*index];

            let value = unsafe { self.table.adapter.bucket_ops().get(bucket, current) }?;

            Some(unsafe { &*(value as *const _) })
        } else {
            None
        }
    }

    #[inline]
    pub fn clone_pointer(&self) -> Option<<A::PointerOps as PointerOps>::Pointer>
    where
        <A::PointerOps as PointerOps>::Pointer: Clone,
    {
        let raw_pointer = self.get()? as *const <A::PointerOps as PointerOps>::Value;
        Some(unsafe {
            crate::pointer_ops::clone_pointer_from_raw(
                self.table.adapter.pointer_ops(),
                raw_pointer,
            )
        })
    }

    #[inline]
    pub fn move_next(&mut self) {
        if let Some((index, current)) = &mut self.position {
            let bucket = &self.table.buckets.borrow()[*index];
            let next = unsafe { self.table.adapter.bucket_ops().next(bucket, current) };

            *current = next;
        }
    }

    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A, B> {
        let mut cursor = self.clone();
        cursor.move_next();
        cursor
    }

    #[inline]
    pub fn as_bucket_cursor(&self) -> BucketCursor<'_, A, B> {
        BucketCursor {
            table: self.table,
            index: self.position.as_ref().map(|(index, _)| *index),
        }
    }

    #[inline]
    pub fn into_bucket_cursor(self) -> BucketCursor<'a, A, B> {
        BucketCursor {
            table: self.table,
            index: self.position.map(|(index, _)| index),
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Clone
    for Cursor<'a, A, B>
{
    #[inline]
    fn clone(&self) -> Self {
        Cursor {
            table: self.table,
            position: self.position.clone(),
        }
    }
}

// =============================================================================
// CursorMut
// =============================================================================

pub struct CursorMut<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    pub(super) table: &'a mut HashTable<A, B>,
    pub(super) position: Option<(usize, <A::BucketOps as BucketOps>::Cursor)>,
}

impl<'a, A, B> CursorMut<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn is_null(&self) -> bool {
        if let Some((index, current)) = &self.position {
            let bucket = &self.table.buckets.borrow()[*index];

            unsafe { self.table.adapter.bucket_ops().is_null(bucket, current) }
        } else {
            false
        }
    }

    #[inline]
    pub fn get(&self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        if let Some((index, current)) = &self.position {
            let bucket = &self.table.buckets.borrow()[*index];

            let value = unsafe { self.table.adapter.bucket_ops().get(bucket, current) }?;

            Some(unsafe { &*(value as *const _) })
        } else {
            None
        }
    }

    #[inline]
    pub fn as_cursor(&self) -> Cursor<'_, A, B> {
        Cursor {
            table: self.table,
            position: self.position.clone(),
        }
    }

    #[inline]
    pub fn move_next(&mut self) {
        if let Some((index, current)) = &mut self.position {
            let bucket = &self.table.buckets.borrow()[*index];
            let next = unsafe { self.table.adapter.bucket_ops().next(bucket, current) };

            *current = next;
        }
    }

    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A, B> {
        let mut cursor = self.as_cursor();
        cursor.move_next();

        cursor
    }

    #[inline]
    pub fn as_bucket_cursor(&self) -> BucketCursor<'_, A, B> {
        BucketCursor {
            table: self.table,
            index: self.position.as_ref().map(|(index, _)| *index),
        }
    }

    #[inline]
    pub fn as_bucket_cursor_mut(&mut self) -> BucketCursorMut<'_, A, B> {
        BucketCursorMut {
            table: self.table,
            index: self.position.as_ref().map(|(index, _)| *index),
        }
    }

    #[inline]
    pub fn into_bucket_cursor(self) -> BucketCursor<'a, A, B> {
        BucketCursor {
            table: self.table,
            index: self.position.map(|(index, _)| index),
        }
    }

    #[inline]
    pub fn into_bucket_cursor_mut(self) -> BucketCursorMut<'a, A, B> {
        BucketCursorMut {
            table: self.table,
            index: self.position.map(|(index, _)| index),
        }
    }

    #[inline]
    pub fn remove_next(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        let (index, current) = self.position.clone()?;

        let bucket = &mut self.table.buckets.borrow_mut()[index];

        let ret = unsafe {
            self.table
                .adapter
                .bucket_ops_mut()
                .remove_next(bucket, &current)
        };

        if ret.is_some() {
            self.table.len -= 1;
        }

        ret
    }

    #[inline]
    pub fn remove(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        let (index, current) = self.position.as_mut()?;

        let bucket = &mut self.table.buckets.borrow_mut()[*index];

        let ret = unsafe { self.table.adapter.bucket_ops_mut().remove(bucket, current) };

        if ret.is_some() {
            self.table.len -= 1;
        }

        ret
    }

    #[inline]
    pub fn replace_next_with(
        &mut self,
        value: <A::PointerOps as PointerOps>::Pointer,
    ) -> Result<<A::PointerOps as PointerOps>::Pointer, <A::PointerOps as PointerOps>::Pointer>
    {
        if let Some((index, current)) = self.position.clone() {
            let bucket = &mut self.table.buckets.borrow_mut()[index];

            unsafe {
                self.table
                    .adapter
                    .bucket_ops_mut()
                    .replace_next_with(bucket, &current, value)
            }
        } else {
            Err(value)
        }
    }

    #[inline]
    pub fn replace_with(
        &mut self,
        value: <A::PointerOps as PointerOps>::Pointer,
    ) -> Result<<A::PointerOps as PointerOps>::Pointer, <A::PointerOps as PointerOps>::Pointer>
    {
        if let Some((index, current)) = self.position.as_mut() {
            let bucket = &mut self.table.buckets.borrow_mut()[*index];

            unsafe {
                self.table
                    .adapter
                    .bucket_ops_mut()
                    .replace_with(bucket, current, value)
            }
        } else {
            Err(value)
        }
    }

    #[inline]
    pub fn insert_after(&mut self, value: <A::PointerOps as PointerOps>::Pointer) {
        if let Some((index, current)) = self.position.clone() {
            let new_len = self.table.len.checked_add(1).expect("capacity overflow");

            let bucket = &mut self.table.buckets.borrow_mut()[index];

            unsafe {
                self.table
                    .adapter
                    .bucket_ops_mut()
                    .insert_after(bucket, &current, value);
            }

            self.table.len = new_len;
        }
    }
}

// =============================================================================
// RawEntryBuilder
// =============================================================================

pub struct RawEntryBuilder<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    table: &'a HashTable<A, B>,
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    RawEntryBuilder<'a, A, B>
where
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
{
    #[inline]
    pub fn from_key<'b, Q: ?Sized>(self, k: &Q) -> Cursor<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        let hash = self.table.adapter.hash_ops().hash(&k);

        self.from_key_hashed_nocheck(hash, k)
    }

    #[inline]
    pub fn from_key_hashed_nocheck<'b, Q: ?Sized>(self, hash: u64, k: &Q) -> Cursor<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        match self.prev_from_key_hashed_nocheck(hash, k) {
            Ok(mut cursor) => {
                cursor.move_next();
                cursor
            }
            Err(cursor) => cursor,
        }
    }

    #[inline]
    pub fn prev_from_key<'b, Q: ?Sized>(self, k: &Q) -> Result<Cursor<'a, A, B>, Cursor<'a, A, B>>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        let hash = self.table.adapter.hash_ops().hash(&k);

        self.prev_from_key_hashed_nocheck(hash, k)
    }

    #[inline]
    pub fn prev_from_key_hashed_nocheck<'b, Q: ?Sized>(
        self,
        hash: u64,
        k: &Q,
    ) -> Result<Cursor<'a, A, B>, Cursor<'a, A, B>>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        let adapter = &self.table.adapter;

        self.prev_from_hash(hash, |value| {
            adapter
                .key_ops()
                .key(unsafe { &*(value as *const _) })
                .borrow()
                == k
        })
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    RawEntryBuilder<'a, A, B>
{
    #[inline]
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> Cursor<'a, A, B>
    where
        for<'b> F: FnMut(&'b <A::PointerOps as PointerOps>::Value) -> bool,
    {
        if unlikely(self.table.buckets.borrow().len() == 0) {
            return Cursor {
                table: self.table,
                position: None,
            };
        }

        let (index, _, current) = self.table.find_internal(hash, is_match);

        Cursor {
            position: Some((index, current)),
            table: self.table,
        }
    }

    #[inline]
    pub fn prev_from_hash<F>(
        self,
        hash: u64,
        is_match: F,
    ) -> Result<Cursor<'a, A, B>, Cursor<'a, A, B>>
    where
        for<'b> F: FnMut(&'b <A::PointerOps as PointerOps>::Value) -> bool,
    {
        if unlikely(self.table.buckets.borrow().len() == 0) {
            return Ok(Cursor {
                table: self.table,
                position: None,
            });
        }

        let (index, prev, next) = self.table.find_internal(hash, is_match);

        let next = Cursor {
            position: Some((index, next)),
            table: self.table,
        };

        if !next.is_null() {
            Ok(Cursor {
                position: Some((index, prev)),
                table: self.table,
            })
        } else {
            Err(unsafe {
                BucketCursor {
                    index: Some(index),
                    table: self.table,
                }
                .into_cursor()
            })
        }
    }
}

// =============================================================================
// RawEntryBuilderMut
// =============================================================================

pub struct RawEntryBuilderMut<
    'a,
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
> {
    table: &'a mut HashTable<A, B>,
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    RawEntryBuilderMut<'a, A, B>
where
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
{
    #[inline]
    pub fn from_key<'b, Q: ?Sized>(self, k: &Q) -> RawEntryMut<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        let hash = self.table.adapter.hash_ops().hash(&k);

        self.from_key_hashed_nocheck(hash, k)
    }

    #[inline]
    pub fn from_key_hashed_nocheck<'b, Q: ?Sized>(self, hash: u64, k: &Q) -> RawEntryMut<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        match self.prev_from_key_hashed_nocheck(hash, k) {
            RawEntryMut::Occupied(mut cursor) => {
                cursor.move_next();
                RawEntryMut::Occupied(cursor)
            }
            RawEntryMut::Vacant(cursor) => RawEntryMut::Vacant(cursor),
        }
    }

    #[inline]
    pub fn prev_from_key<'b, Q: ?Sized>(self, k: &Q) -> RawEntryMut<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        A::HashOps: HashOps<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        let hash = self.table.adapter.hash_ops().hash(&k);

        self.prev_from_key_hashed_nocheck(hash, k)
    }

    #[inline]
    pub fn prev_from_key_hashed_nocheck<'b, Q: ?Sized>(
        self,
        hash: u64,
        k: &Q,
    ) -> RawEntryMut<'a, A, B>
    where
        <A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key: Borrow<Q>,
        Q: Eq,
        <A::PointerOps as PointerOps>::Value: 'b,
    {
        if unlikely(self.table.buckets.borrow().len() == 0) {
            return RawEntryMut::Vacant(InsertCursor {
                hash,
                index: None,
                table: self.table,
            });
        }

        let (index, prev, next) = self.table.find_internal(hash, |value| {
            self.table
                .adapter
                .key_ops()
                .key(unsafe { &*(value as *const _) })
                .borrow()
                == k
        });

        let next = CursorMut {
            position: Some((index, next)),
            table: self.table,
        };

        if !next.is_null() {
            RawEntryMut::Occupied(CursorMut {
                position: Some((index, prev)),
                table: self.table,
            })
        } else {
            RawEntryMut::Vacant(InsertCursor {
                hash,
                index: Some(index),
                table: self.table,
            })
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>>
    RawEntryBuilderMut<'a, A, B>
{
    #[inline]
    pub fn from_hash<F>(self, hash: u64, is_match: F) -> RawEntryMut<'a, A, B>
    where
        for<'b> F: FnMut(&'b <A::PointerOps as PointerOps>::Value) -> bool,
    {
        if unlikely(self.table.buckets.borrow().len() == 0) {
            return RawEntryMut::Vacant(InsertCursor {
                hash,
                index: None,
                table: self.table,
            });
        }

        let (index, _, current) = self.table.find_internal(hash, is_match);

        let cursor = CursorMut {
            position: Some((index, current)),
            table: self.table,
        };

        if !cursor.is_null() {
            RawEntryMut::Occupied(cursor)
        } else {
            let BucketCursorMut { index, table } = cursor.into_bucket_cursor_mut();

            RawEntryMut::Vacant(InsertCursor { table, index, hash })
        }
    }

    #[inline]
    pub fn prev_from_hash<F>(self, hash: u64, is_match: F) -> RawEntryMut<'a, A, B>
    where
        for<'b> F: FnMut(&'b <A::PointerOps as PointerOps>::Value) -> bool,
    {
        if unlikely(self.table.buckets.borrow().len() == 0) {
            return RawEntryMut::Vacant(InsertCursor {
                hash,
                index: None,
                table: self.table,
            });
        }

        let (index, prev, next) = self.table.find_internal(hash, is_match);

        let next = CursorMut {
            position: Some((index, next)),
            table: self.table,
        };

        if !next.is_null() {
            RawEntryMut::Occupied(CursorMut {
                position: Some((index, prev)),
                table: self.table,
            })
        } else {
            RawEntryMut::Vacant(InsertCursor {
                hash,
                index: Some(index),
                table: self.table,
            })
        }
    }
}

// =============================================================================
// RawEntryMut
// =============================================================================

pub enum RawEntryMut<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    Occupied(CursorMut<'a, A, B>),
    Vacant(InsertCursor<'a, A, B>),
}

use self::RawEntryMut::{Occupied, Vacant};

impl<'a, A, B> RawEntryMut<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
{
    #[inline]
    pub fn or_insert(self, default: <A::PointerOps as PointerOps>::Pointer) -> CursorMut<'a, A, B> {
        self.or_insert_with(|| default)
    }

    #[inline]
    pub fn or_insert_with<F>(self, default: F) -> CursorMut<'a, A, B>
    where
        F: FnOnce() -> <A::PointerOps as PointerOps>::Pointer,
    {
        match self {
            RawEntryMut::Occupied(entry) => entry,
            RawEntryMut::Vacant(entry) => entry.insert_with(default),
        }
    }
}

impl<'a, A, B> RawEntryMut<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn and_modify<F>(self, f: F) -> Self
    where
        F: for<'b> FnOnce(&'b <A::PointerOps as PointerOps>::Value),
    {
        match self {
            RawEntryMut::Occupied(entry) => {
                f(unsafe { entry.get().unwrap_unchecked() });
                RawEntryMut::Occupied(entry)
            }
            RawEntryMut::Vacant(entry) => RawEntryMut::Vacant(entry),
        }
    }
}

// =============================================================================
// InsertCursor
// =============================================================================

pub struct InsertCursor<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    table: &'a mut HashTable<A, B>,
    hash: u64,
    index: Option<usize>,
}

impl<'a, A, B> InsertCursor<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
    A::KeyOps: for<'b> KeyOps<'b, <A::PointerOps as PointerOps>::Value>,
    A::HashOps:
        for<'b> HashOps<<A::KeyOps as KeyOps<'b, <A::PointerOps as PointerOps>::Value>>::Key>,
{
    #[inline]
    pub fn insert(self, default: <A::PointerOps as PointerOps>::Pointer) -> CursorMut<'a, A, B> {
        self.insert_with(|| default)
    }

    #[inline]
    pub fn insert_with<F>(mut self, default: F) -> CursorMut<'a, A, B>
    where
        F: FnOnce() -> <A::PointerOps as PointerOps>::Pointer,
    {
        self.table.reserve(1);

        self.index = checked_index_from_hash(self.hash, self.table.buckets.borrow().len());

        let mut cursor = self.into_bucket_cursor_mut().into_cursor_mut();
        cursor.insert_after(default());
        cursor.move_next();
        cursor
    }
}

impl<'a, A, B> InsertCursor<'a, A, B>
where
    A: HashTableAdapter,
    B: Array<<A::BucketOps as BucketOps>::Bucket>,
{
    #[inline]
    pub fn as_bucket_cursor(&self) -> BucketCursor<'_, A, B> {
        BucketCursor {
            table: self.table,
            index: self.index,
        }
    }

    #[inline]
    pub fn as_bucket_cursor_mut(&mut self) -> BucketCursorMut<'_, A, B> {
        BucketCursorMut {
            table: self.table,
            index: self.index,
        }
    }

    #[inline]
    pub fn into_bucket_cursor(self) -> BucketCursor<'a, A, B> {
        BucketCursor {
            table: self.table,
            index: self.index,
        }
    }

    #[inline]
    pub fn into_bucket_cursor_mut(self) -> BucketCursorMut<'a, A, B> {
        BucketCursorMut {
            table: self.table,
            index: self.index,
        }
    }
}

// =============================================================================
// Iter
// =============================================================================

pub struct Iter<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    table: &'a HashTable<A, B>,
    bucket_cursor: Option<(usize, <A::BucketOps as BucketOps>::Cursor)>,
    len: usize,
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Clone
    for Iter<'a, A, B>
{
    #[inline]
    fn clone(&self) -> Self {
        Iter {
            table: self.table,
            bucket_cursor: self.bucket_cursor.clone(),
            len: self.len,
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> fmt::Debug
    for Iter<'a, A, B>
where
    <A::PointerOps as PointerOps>::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((index, current)) = self.bucket_cursor.clone() {
            let cursor = Cursor {
                table: self.table,
                position: Some((index, current)),
            };
            let val = unsafe { cursor.get().unwrap_unchecked() };

            val.fmt(f)
        } else {
            f.pad("null")
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Iterator
    for Iter<'a, A, B>
{
    type Item = &'a <A::PointerOps as PointerOps>::Value;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut bucket_cursor = if let Some((index, current)) = self.bucket_cursor.clone() {
            let mut cursor = Cursor {
                table: self.table,
                position: Some((index, current)),
            };

            cursor.move_next();

            if let Some(value) = cursor.get() {
                self.bucket_cursor = cursor.position.clone().map(|(_, current)| (index, current));
                self.len -= 1;

                return Some(value);
            } else {
                BucketCursor {
                    table: self.table,
                    index: Some(index),
                }
            }
        } else {
            self.table.bucket_cursor()
        };

        bucket_cursor.move_next();

        while !bucket_cursor.is_null() {
            let mut cursor = bucket_cursor.clone().into_cursor();
            cursor.move_next();

            if let Some(value) = cursor.get() {
                self.bucket_cursor = cursor.position.clone();
                self.len -= 1;

                return Some(value);
            }

            bucket_cursor.move_next();
        }

        self.bucket_cursor = None;

        debug_assert_eq!(self.len, 0);

        None
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> ExactSizeIterator
    for Iter<'a, A, B>
{
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> FusedIterator
    for Iter<'a, A, B>
{
}

// =============================================================================
// Drain
// =============================================================================

pub struct Drain<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    table: &'a mut HashTable<A, B>,
    bucket_cursor: Option<(usize, <A::BucketOps as BucketOps>::Cursor)>,
    len: usize,
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> fmt::Debug
    for Drain<'a, A, B>
where
    <A::PointerOps as PointerOps>::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((index, current)) = self.bucket_cursor.clone() {
            let cursor = Cursor {
                table: self.table,
                position: Some((index, current)),
            };
            let val = unsafe { cursor.get().unwrap_unchecked() };

            val.fmt(f)
        } else {
            f.pad("null")
        }
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Drop
    for Drain<'a, A, B>
{
    #[inline]
    fn drop(&mut self) {
        while let Some(_) = self.next() {}
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Iterator
    for Drain<'a, A, B>
{
    type Item = <A::PointerOps as PointerOps>::Pointer;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut bucket_cursor = if let Some((index, current)) = self.bucket_cursor.clone() {
            let mut cursor = CursorMut {
                table: self.table,
                position: Some((index, current)),
            };

            if !cursor.peek_next().is_null() {
                let ret = cursor.remove_next();
                self.len -= 1;

                return ret;
            } else {
                BucketCursorMut {
                    table: self.table,
                    index: Some(index),
                }
            }
        } else {
            self.table.bucket_cursor_mut()
        };

        bucket_cursor.move_next();

        while !bucket_cursor.is_null() {
            if let Some(ret) = bucket_cursor.cursor_mut().remove_next() {
                self.len -= 1;

                return Some(ret);
            }

            bucket_cursor.move_next();
        }

        self.bucket_cursor = None;

        debug_assert_eq!(self.len, 0);

        None
    }
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> ExactSizeIterator
    for Drain<'a, A, B>
{
}

impl<'a, A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> FusedIterator
    for Drain<'a, A, B>
{
}

// =============================================================================
// IntoIter
// =============================================================================

pub struct IntoIter<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> {
    table: HashTable<A, B>,
    bucket_cursor: Option<(usize, <A::BucketOps as BucketOps>::Cursor)>,
    len: usize,
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> fmt::Debug
    for IntoIter<A, B>
where
    <A::PointerOps as PointerOps>::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some((index, current)) = self.bucket_cursor.clone() {
            let cursor = Cursor {
                table: &self.table,
                position: Some((index, current)),
            };
            let val = unsafe { cursor.get().unwrap_unchecked() };

            val.fmt(f)
        } else {
            f.pad("null")
        }
    }
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> Iterator
    for IntoIter<A, B>
{
    type Item = <A::PointerOps as PointerOps>::Pointer;

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        if self.len == 0 {
            return None;
        }

        let mut bucket_cursor = if let Some((index, current)) = self.bucket_cursor.clone() {
            let mut cursor = CursorMut {
                table: &mut self.table,
                position: Some((index, current)),
            };

            if !cursor.peek_next().is_null() {
                let ret = cursor.remove_next();
                self.len -= 1;

                return ret;
            } else {
                BucketCursorMut {
                    table: &mut self.table,
                    index: Some(index),
                }
            }
        } else {
            self.table.bucket_cursor_mut()
        };

        bucket_cursor.move_next();

        while !bucket_cursor.is_null() {
            if let Some(ret) = bucket_cursor.cursor_mut().remove_next() {
                self.len -= 1;

                return Some(ret);
            }

            bucket_cursor.move_next();
        }

        self.bucket_cursor = None;

        debug_assert_eq!(self.len, 0);

        None
    }
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> ExactSizeIterator
    for IntoIter<A, B>
{
}

impl<A: HashTableAdapter, B: Array<<A::BucketOps as BucketOps>::Bucket>> FusedIterator
    for IntoIter<A, B>
{
}

#[cfg(test)]
mod tests {
    use core::cell::Cell;
    use std::collections::hash_map::RandomState;
    use std::rc::Rc;
    use std::vec::Vec;

    use super::*;
    use crate::hash_table::{array::DynamicArray, hash_ops::DefaultHashOps};
    use crate::pointer_ops::DefaultPointerOps;
    use crate::singly_linked_list::SinglyLinkedListOps;
    use crate::SinglyLinkedList;
    use crate::SinglyLinkedListLink;

    #[derive(Clone, Copy, Default)]
    pub struct IdentityHashOps;

    impl<T: Borrow<i32>> HashOps<T> for IdentityHashOps {
        #[inline(always)]
        fn hash(&self, value: &T) -> u64 {
            *value.borrow() as u64
        }
    }

    #[derive(Debug, Clone)]
    struct Obj {
        link: SinglyLinkedListLink,
        key: i32,
        value: Cell<i32>,
    }

    impl Obj {
        #[inline]
        pub const fn new(key: i32, value: i32) -> Obj {
            Obj {
                link: SinglyLinkedListLink::new(),
                key,
                value: Cell::new(value),
            }
        }

        #[inline]
        pub fn key(&self) -> &i32 {
            &self.key
        }

        #[inline]
        pub fn value(&self) -> i32 {
            self.value.get()
        }
    }

    impl PartialEq for Obj {
        #[inline]
        fn eq(&self, other: &Obj) -> bool {
            self.key == other.key && self.value == other.value
        }
    }

    impl Eq for Obj {}

    #[inline]
    fn make_obj(key: i32, value: i32) -> Rc<Obj> {
        Rc::new(Obj::new(key, value))
    }

    intrusive_adapter!(ObjAdapter = Rc<Obj> : Obj { link: SinglyLinkedListLink });

    #[derive(Default)]
    pub struct ObjKeyOps;

    impl<'a> KeyOps<'a, Obj> for ObjKeyOps {
        type Key = i32;

        #[inline]
        fn key(&self, value: &'a Obj) -> Self::Key {
            value.key
        }
    }

    #[derive(Default)]
    struct ObjHashTableAdapter {
        pointer_ops: DefaultPointerOps<Rc<Obj>>,
        hash_ops: DefaultHashOps<RandomState>,
        bucket_ops: DefaultBucketOps<SinglyLinkedList<ObjAdapter>>,
        key_ops: ObjKeyOps,
    }

    impl HashTableAdapter for ObjHashTableAdapter {
        type PointerOps = DefaultPointerOps<Rc<Obj>>;

        type BucketOps = DefaultBucketOps<SinglyLinkedList<ObjAdapter>>;

        type KeyOps = ObjKeyOps;

        type HashOps = DefaultHashOps<RandomState>;

        fn pointer_ops(&self) -> &Self::PointerOps {
            &self.pointer_ops
        }

        fn bucket_ops(&self) -> &Self::BucketOps {
            &self.bucket_ops
        }

        fn bucket_ops_mut(&mut self) -> &mut Self::BucketOps {
            &mut self.bucket_ops
        }

        fn key_ops(&self) -> &Self::KeyOps {
            &self.key_ops
        }

        fn hash_ops(&self) -> &Self::HashOps {
            &self.hash_ops
        }
    }

    #[test]
    fn test_empty_remove() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        assert_eq!(m.remove(&0), None);
    }

    #[test]
    fn test_empty_entry() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        match m.raw_entry_mut().from_key(&0) {
            Occupied(_) => panic!(),
            Vacant(_) => {}
        }
        assert!(!m
            .raw_entry_mut()
            .from_key(&0)
            .or_insert(make_obj(0, 0))
            .is_null());
        assert_eq!(m.len(), 1);
    }

    #[test]
    fn test_empty_iter() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        assert_eq!(m.drain().next(), None);
        assert_eq!(m.iter().next(), None);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
        //assert_eq!(m.into_iter().next(), None);
    }

    #[test]
    fn test_lots_of_insertions() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();

        // Try this a few times to make sure we never screw up the hashmap's
        // internal state.
        for _ in 0..10 {
            assert!(m.is_empty());

            for i in 1..1001 {
                assert!(!m.insert(make_obj(i, i)).is_null());

                for j in 1..=i {
                    let r = m.get(&j);
                    assert_eq!(r.map(|x| &x.key), Some(&j));
                }

                for j in i + 1..1001 {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in 1001..2001 {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..1001 {
                assert!(m.remove(&i).is_some());

                for j in 1..=i {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..1001 {
                    assert!(m.contains_key(&j));
                }
            }

            for i in 1..1001 {
                assert!(!m.contains_key(&i));
            }

            for i in 1..1001 {
                assert!(!m.insert(make_obj(i, i)).is_null());
            }

            // remove backwards
            for i in (1..1001).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..1001 {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }

    #[test]
    fn test_insert_overwrite() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        assert!(!m.insert(make_obj(1, 2)).is_null());
        assert_eq!(m.get(&1).unwrap().value(), 2);
        match m.raw_entry_mut().from_key(&1) {
            Occupied(mut entry) => assert!(entry.replace_with(make_obj(1, 3)).is_ok()),
            Vacant(_) => panic!(),
        }
        assert_eq!(m.get(&1).unwrap().value(), 3);
    }

    #[test]
    fn test_insert_conflicts() {
        let mut m: HashTable<ObjHashTableAdapter, _> =
            unsafe { HashTable::from_parts(Default::default(), DynamicArray::with_capacity(4), 0) };
        assert!(!m.insert(make_obj(1, 2)).is_null());
        assert!(!m.insert(make_obj(5, 3)).is_null());
        assert!(!m.insert(make_obj(9, 4)).is_null());
        match m.raw_entry_mut().from_key(&9) {
            Occupied(mut entry) => assert_eq!(entry.get().unwrap().value(), 4),
            Vacant(_) => panic!(),
        }
        match m.raw_entry_mut().from_key(&5) {
            Occupied(mut entry) => assert_eq!(entry.get().unwrap().value(), 3),
            Vacant(_) => panic!(),
        }
        match m.raw_entry_mut().from_key(&1) {
            Occupied(mut entry) => assert_eq!(entry.get().unwrap().value(), 2),
            Vacant(_) => panic!(),
        }
        assert_eq!(m.get(&9).unwrap().value(), 4);
        assert_eq!(m.get(&5).unwrap().value(), 3);
        assert_eq!(m.get(&1).unwrap().value(), 2);
    }

    #[test]
    fn test_conflict_remove() {
        let mut m: HashTable<ObjHashTableAdapter, _> =
            unsafe { HashTable::from_parts(Default::default(), DynamicArray::with_capacity(4), 0) };
        assert!(!m.insert(make_obj(1, 2)).is_null());
        assert_eq!(m.get(&1).unwrap().value(), 2);
        assert!(!m.insert(make_obj(5, 3)).is_null());
        assert_eq!(m.get(&1).unwrap().value(), 2);
        assert_eq!(m.get(&5).unwrap().value(), 3);
        assert!(!m.insert(make_obj(9, 4)).is_null());
        assert_eq!(m.get(&1).unwrap().value(), 2);
        assert_eq!(m.get(&5).unwrap().value(), 3);
        assert_eq!(m.get(&9).unwrap().value(), 4);
        assert!(m.remove(&1).is_some());
        assert_eq!(m.get(&9).unwrap().value(), 4);
        assert_eq!(m.get(&5).unwrap().value(), 3);
    }

    #[test]
    fn test_is_empty() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        assert!(!m.insert(make_obj(1, 2)).is_null());
        assert!(!m.is_empty());
        assert!(m.remove(&1).is_some());
        assert!(m.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        assert!(!m.insert(make_obj(1, 2)).is_null());
        assert!(m.remove(&1).is_some());
        assert!(m.remove(&1).is_none());
    }

    #[test]
    fn test_iterate() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        for i in 0..32 {
            assert!(!m.insert(make_obj(i, i * 2)).is_null());
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        for obj in &m {
            assert_eq!(obj.value(), obj.key() * 2);
            observed |= 1 << obj.key();
        }

        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_reserve_shrink_to_fit() {
        let mut m: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        m.insert(make_obj(0, 0));
        m.remove(&0);
        assert!(m.capacity() >= m.len());
        for i in 0..128 {
            m.insert(make_obj(i, i));
        }
        m.reserve(256);

        let usable_cap = m.capacity();
        for i in 128..(128 + 256) {
            m.insert(make_obj(i, i));
            assert_eq!(m.capacity(), usable_cap);
        }

        for i in 100..(128 + 256) {
            assert_eq!(m.remove(&i).map(|x| x.value()), Some(i));
        }
        m.shrink_to_fit();

        assert_eq!(m.len(), 100);
        assert!(!m.is_empty());
        assert!(m.capacity() >= m.len());

        for i in 0..100 {
            assert_eq!(m.remove(&i).map(|x| x.value()), Some(i));
        }
        m.shrink_to_fit();
        m.insert(make_obj(0, 0));

        assert_eq!(m.len(), 1);
        assert!(m.capacity() >= m.len());
        assert_eq!(m.remove(&0).map(|x| x.value()), Some(0));
    }

    #[test]
    fn test_from_iter() {
        let xs = [
            make_obj(1, 1),
            make_obj(2, 2),
            make_obj(3, 3),
            make_obj(4, 4),
            make_obj(5, 5),
            make_obj(6, 6),
        ];

        let map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = xs.iter().cloned().collect();

        for obj in &xs {
            assert_eq!(map.get(&obj.key()).map(|x| x.value()), Some(obj.value()));
        }

        assert_eq!(map.iter().len(), xs.len());
    }

    #[test]
    fn test_size_hint() {
        let xs = [
            make_obj(1, 1),
            make_obj(2, 2),
            make_obj(3, 3),
            make_obj(4, 4),
            make_obj(5, 5),
            make_obj(6, 6),
        ];

        let map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = xs.iter().cloned().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_iter_len() {
        let xs = [
            make_obj(1, 1),
            make_obj(2, 2),
            make_obj(3, 3),
            make_obj(4, 4),
            make_obj(5, 5),
            make_obj(6, 6),
        ];

        let map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = xs.iter().cloned().collect();

        let mut iter = map.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.len(), 3);
    }

    #[test]
    fn test_index() {
        let mut map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();

        map.insert(make_obj(1, 2));
        map.insert(make_obj(2, 1));
        map.insert(make_obj(3, 4));

        assert_eq!(map[&2].value(), 1);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();

        map.insert(make_obj(1, 2));
        map.insert(make_obj(2, 1));
        map.insert(make_obj(3, 4));

        &map[&4];
    }

    #[test]
    fn test_extend_ref() {
        let mut a: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        a.insert(make_obj(1, 1_000));
        let mut b: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        b.insert(make_obj(2, 2_000));
        b.insert(make_obj(3, 3_000));

        a.extend(b.iter().map(|obj| Rc::new(obj.clone())));

        assert_eq!(a.len(), 3);
        assert_eq!(a[&1].value(), 1_000);
        assert_eq!(a[&2].value(), 2_000);
        assert_eq!(a[&3].value(), 3_000);
    }

    #[test]
    fn test_capacity_not_less_than_len() {
        let mut a: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();
        let mut item = 0;

        for _ in 0..116 {
            a.insert(make_obj(item, 0));
            item += 1;
        }

        assert!(a.capacity() > a.len());

        let free = a.capacity() - a.len();
        for _ in 0..free {
            a.insert(make_obj(item, 0));
            item += 1;
        }

        assert_eq!(a.len(), a.capacity());

        // Insert at capacity should cause allocation.
        a.insert(make_obj(item, 0));
        assert!(a.capacity() > a.len());
    }

    #[test]
    fn test_retain() {
        let mut map: HashTable<ObjHashTableAdapter, DynamicArray<_>> =
            (0..100).map(|x| make_obj(x, x * 10)).collect();

        map.retain(|obj| obj.key() % 2 == 0);
        assert_eq!(map.len(), 50);
        assert_eq!(map[&2].value(), 20);
        assert_eq!(map[&4].value(), 40);
        assert_eq!(map[&6].value(), 60);
    }

    /*
    #[test]
    fn test_try_reserve() {
        let mut empty_bytes: HashMap<u8, u8>: HashTable<ObjHashTableAdapter, DynamicArray<_>> = HashTable::new();

        const MAX_USIZE: usize = usize::MAX;

        if let Err(CapacityOverflow) = empty_bytes.try_reserve(MAX_USIZE) {
        } else {
            panic!("usize::MAX should trigger an overflow!");
        }

        if let Err(AllocError { .. }) = empty_bytes.try_reserve(MAX_USIZE / 8) {
        } else {
            panic!("usize::MAX / 8 should trigger an OOM!")
        }
    }
    */

    #[test]
    fn test_raw_entry() {
        use super::RawEntryMut::{Occupied, Vacant};

        let xs = [
            make_obj(1i32, 10i32),
            make_obj(2, 20),
            make_obj(3, 30),
            make_obj(4, 40),
            make_obj(5, 50),
            make_obj(6, 60),
        ];

        let mut map: HashTable<ObjHashTableAdapter, DynamicArray<_>> = xs.iter().cloned().collect();

        let compute_hash = |map: &HashTable<ObjHashTableAdapter, DynamicArray<_>>, k: i32| -> u64 {
            use core::hash::{BuildHasher, Hash, Hasher};

            map.adapter.hash_ops().hash(&k)
        };

        // Existing key (insert)
        match map.raw_entry_mut().from_key(&1) {
            Vacant(_) => unreachable!(),
            Occupied(mut view) => {
                assert_eq!(view.get().unwrap().value(), 10);
                assert_eq!(view.replace_with(make_obj(1, 100)).unwrap().value(), 10);
            }
        }
        let hash1 = compute_hash(&map, 1);
        assert_eq!(
            *map.raw_entry().from_key(&1).get().unwrap(),
            Obj::new(1, 100)
        );
        assert_eq!(
            *map.raw_entry()
                .from_hash(hash1, |obj| *obj.key() == 1)
                .get()
                .unwrap(),
            Obj::new(1, 100)
        );
        assert_eq!(
            *map.raw_entry()
                .from_key_hashed_nocheck(hash1, &1)
                .get()
                .unwrap(),
            Obj::new(1, 100)
        );
        assert_eq!(map.len(), 6);

        // Existing key (update)
        match map.raw_entry_mut().from_key(&2) {
            Vacant(_) => unreachable!(),
            Occupied(mut view) => {
                let v = view.get().unwrap();
                let new_v = v.value() * 10;
                v.value.set(new_v);
            }
        }
        let hash2 = compute_hash(&map, 2);
        assert_eq!(
            *map.raw_entry().from_key(&2).get().unwrap(),
            Obj::new(2, 200)
        );
        assert_eq!(
            *map.raw_entry()
                .from_hash(hash2, |obj| *obj.key() == 2)
                .get()
                .unwrap(),
            Obj::new(2, 200)
        );
        assert_eq!(
            *map.raw_entry()
                .from_key_hashed_nocheck(hash2, &2)
                .get()
                .unwrap(),
            Obj::new(2, 200)
        );
        assert_eq!(map.len(), 6);

        // Existing key (take)
        let hash3 = compute_hash(&map, 3);
        match map.raw_entry_mut().from_key_hashed_nocheck(hash3, &3) {
            Vacant(_) => unreachable!(),
            Occupied(mut view) => {
                assert_eq!(*view.remove().unwrap(), Obj::new(3, 30));
            }
        }
        assert!(map.raw_entry().from_key(&3).is_null());
        assert!(map.raw_entry().from_hash(hash3, |k| k.key == 3).is_null());
        assert!(map.raw_entry().from_key_hashed_nocheck(hash3, &3).is_null());
        assert_eq!(map.len(), 5);

        // Nonexistent key (insert)
        match map.raw_entry_mut().from_key(&10) {
            Occupied(_) => unreachable!(),
            Vacant(view) => {
                assert_eq!(
                    view.insert(make_obj(10, 1000))
                        .get()
                        .map(|obj| (obj.key(), obj.value()))
                        .unwrap(),
                    (&10, 1000)
                );
            }
        }
        assert_eq!(
            *map.raw_entry().from_key(&10).get().unwrap(),
            Obj::new(10, 1000)
        );
        assert_eq!(map.len(), 6);

        // Ensure all lookup methods produce equivalent results.
        for k in 0..12 {
            let hash = compute_hash(&map, k);
            let v = map.get(&k).cloned();
            let kv = v.as_ref().map(|v| (&k, v));

            assert_eq!(
                map.raw_entry()
                    .from_key(&k)
                    .get()
                    .map(|obj| (obj.key(), obj)),
                kv
            );
            assert_eq!(
                map.raw_entry()
                    .from_hash(hash, |q| q.key == k)
                    .get()
                    .map(|obj| (obj.key(), obj)),
                kv
            );
            assert_eq!(
                map.raw_entry()
                    .from_key_hashed_nocheck(hash, &k)
                    .get()
                    .map(|obj| (obj.key(), obj)),
                kv
            );

            match map.raw_entry_mut().from_key(&k) {
                Occupied(mut o) => assert_eq!(o.get().map(|obj| (obj.key(), obj)), kv),
                Vacant(_) => assert_eq!(v, None),
            }
            match map.raw_entry_mut().from_key_hashed_nocheck(hash, &k) {
                Occupied(mut o) => assert_eq!(o.get().map(|obj| (obj.key(), obj)), kv),
                Vacant(_) => assert_eq!(v, None),
            }
            match map.raw_entry_mut().from_hash(hash, |q| q.key == k) {
                Occupied(mut o) => assert_eq!(o.get().map(|obj| (obj.key(), obj)), kv),
                Vacant(_) => assert_eq!(v, None),
            }
        }
    }
}
