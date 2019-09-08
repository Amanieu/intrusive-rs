// Copyright 2019 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive hash table that uses "separate chaining" for collision resolution.
use core::borrow::Borrow;
use core::cmp;
use core::hash::{BuildHasher, Hash, Hasher};
use core::ops::Deref;
use core::iter;
use core::fmt;

use crate::adapter::Adapter;
use crate::array::Array;
use crate::dynamic_array::DynamicArray;
use crate::hash_adapter::HashAdapter;
pub use crate::hash_table::ChainedLoadFactor;
use crate::key_adapter::KeyAdapter;
use crate::linked_list::Link as LinkedListLink;
use crate::linked_list::LinkedList;
//use crate::intrusive_pointer::IntrusivePointer;
use crate::hash_table::DEFAULT_CHAINED_LOAD_FACTOR;

/// An intrusive hash table.
///
/// When this collection is dropped, all elements linked into it will be
/// converted back to owned pointers and dropped.
#[derive(Clone)]
pub struct ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    adapter: A,
    buckets: B,
    hash_builder: S,
    max_load_factor: ChainedLoadFactor,
    cap: usize,
    size: usize,
}

impl<A, B, S> Drop for ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    fn drop(&mut self) {
        // Must be explicit b/c the array used to index the buckets may never be dropped.
        self.clear();
    }
}

impl<A, B, S> Default for ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink> + Default,
    B: Array<Item = LinkedList<A>> + Default,
    S: BuildHasher + Default,
{
    #[inline]
    fn default() -> ChainedHashTable<A, B, S> {
        ChainedHashTable::with_adapter_buckets_hasher_and_load_factor(A::default(), B::default(), S::default(), DEFAULT_CHAINED_LOAD_FACTOR)
    }
}

impl<A, B, S> fmt::Debug for ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
    A::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>> + Default,
    S: BuildHasher + Default,
{
    /// Creates an empty `ChainedHashTable`.
    ///
    /// The hash table is initially created with a capacity of 0.
    ///
    /// If `B` implements [`DynamicArray`], then it will not allocated until it is first inserted into.
    ///
    #[inline]
    pub fn new(adapter: A) -> ChainedHashTable<A, B, S> {
        ChainedHashTable::with_adapter_buckets_hasher_and_load_factor(
            adapter,
            Default::default(),
            Default::default(),
            DEFAULT_CHAINED_LOAD_FACTOR,
        )
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
    S: BuildHasher,
{
    /// Creates an empty `ChainedHashTable`.
    #[inline]
    pub fn with_adapter_buckets_hasher_and_load_factor(
        adapter: A,
        buckets: B,
        hasher: S,
        load_factor: ChainedLoadFactor,
    ) -> ChainedHashTable<A, B, S> {
        let cap = (buckets.len() / load_factor.bucket_count) * load_factor.size;

        ChainedHashTable {
            adapter,
            buckets,
            hash_builder: hasher,
            max_load_factor: load_factor,
            cap,
            size: 0,
        }
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Returns `true` if the `ChainedHashTable` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns `true` if the `ChainedHashTable` is full.
    #[inline]
    pub fn is_full(&self) -> bool {
        self.size == self.cap
    }

    /// Returns a null `Cursor` for this hash table.
    #[inline]
    pub fn cursor(&self) -> Cursor<'_, A, B, S> {
        Cursor {
            hash_table: self,
            inner: None,
        }
    }

    /// Returns a null `CursorMut` for this hash table.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A, B, S> {
        CursorMut {
            hash_table: self,
            inner: None,
        }
    }

    /// Returns the capacity of the hash table.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Returns the size (in items) of the hash table.
    #[inline]
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns the hasher.
    #[inline]
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Sets the maximum load factor.
    ///
    /// *Note*:
    /// `set_max_load_factor` is only a 'bare-bones' setter.
    /// There are no allocations triggered by this function.
    #[inline]
    pub fn set_max_load_factor(&mut self, max_load_factor: ChainedLoadFactor) {
        self.max_load_factor = max_load_factor;
    }

    /// Returns the maximum load factor (before growth is necessary).
    #[inline]
    pub fn max_load_factor(&self) -> ChainedLoadFactor {
        self.max_load_factor
    }

    /// Returns the current load factor.
    #[inline]
    pub fn load_factor(&self) -> ChainedLoadFactor {
        ChainedLoadFactor {
            size: self.size,
            bucket_count: self.buckets.len(),
        }
    }

    #[inline]
    fn clear(&mut self) {
        for bucket in self.buckets.as_mut_slice() {
            bucket.clear()
        }
        self.size = 0;
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Empties the `ChainedHashTable` without unlinking or freeing objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `ChainedHashTable` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `force_unlink` function on them.
    #[inline]
    pub fn fast_clear(&mut self) {
        for bucket in self.buckets.as_mut_slice() {
            bucket.fast_clear()
        }
        self.size = 0;
    }

    /// Returns a `Cursor` pointing to the first element of the hash table. If the
    /// hash table is empty then a null cursor is returned.
    #[inline]
    pub fn front(&self) -> Cursor<'_, A, B, S> {
        let mut ret = self.cursor();
        ret.move_next();
        ret
    }

    /// Returns a `CursorMut` pointing to the first element of the hash table. If the
    /// hash table is empty then a null cursor is returned.
    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<'_, A, B, S> {
        let mut ret = self.cursor_mut();
        ret.move_next();
        ret
    }

    /// Returns a `Cursor` pointing to the last element of the hash table. If the
    /// hash table is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<'_, A, B, S> {
        let mut ret = self.cursor();
        ret.move_prev();
        ret
    }

    /// Returns a `CursorMut` pointing to the last element of the hash table. If the
    /// hash table is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<'_, A, B, S> {
        let mut ret = self.cursor_mut();
        ret.move_prev();
        ret
    }

    /// Gets an iterator over the objects in the `ChainedHashTable`, in ascending key
    /// order.
    #[inline]
    pub fn iter(&self) -> Iter<'_, A, B, S> {
        Iter {
            cursor: self.front(),
        }
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: for<'a> KeyAdapter<'a, Link = LinkedListLink> + HashAdapter,
    B: Array<Item = LinkedList<A>>,
    S: BuildHasher,
{
    #[inline]
    fn find_internal<'a, Q: ?Sized + Eq + Hash>(&self, key: &Q, hash_code: u64) -> (usize, Option<*const A::Value>)
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
        //B::Item: 'a,
    {
        let bucket_idx = (hash_code % (self.buckets.len() as u64)) as usize;

        for val in self.buckets.as_slice()[bucket_idx].iter() {
            // did we cache the hash code?
            if let Some(other_hash_code) = self.adapter.get_cached_hash(val) {
                // if we did, we may not need to compare the keys
                if hash_code != other_hash_code {
                    continue;
                }
            }

            unsafe {
                if key == self.adapter.get_key(&*(val as *const _)).borrow() {
                    return (bucket_idx, Some(val as *const _));
                }
            }
        }

        (bucket_idx, None)
    }

    #[inline]
    fn find_key<'a, Q: ?Sized + Eq + Hash>(&self, key: &Q) -> (usize, Option<*const A::Value>)
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let hash_code = {
            let mut hasher = self.hash_builder.build_hasher();
            key.hash(&mut hasher);
            hasher.finish()
        };
        
        self.find_internal(key, hash_code)
    }

    /// Returns a `Cursor` pointing to an element with the given key. If no such element is found then a null cursor is returned.
    /// If multiple elements with an identical key are found then an first one found is returned.
    /// 
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn find<'a, Q: ?Sized + Eq + Hash>(&self, key: &Q) -> Cursor<'_, A, B, S>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        if self.is_empty() {
            return Cursor {
                hash_table: self,
                inner: None,
            };
        }

        let (bucket_idx, ptr) = self.find_key(key);
        Cursor {
            hash_table: self,
            inner: ptr.map(|ptr| (ptr, bucket_idx)),
        }
    }

    /// Returns a `CursorMut` pointing to an element with the given key. If no such element is found then a null cursor is returned.
    /// If multiple elements with an identical key are found then an first one found is returned.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn find_mut<'a, Q: ?Sized + Eq + Hash>(&mut self, key: &Q) -> CursorMut<'_, A, B, S>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        if self.is_empty() {
            return CursorMut {
                hash_table: self,
                inner: None,
            };
        }

        let (bucket_idx, ptr) = self.find_key(key);
        CursorMut {
            hash_table: self,
            inner: ptr.map(|ptr| (ptr, bucket_idx)),
        }
    }

    /// Returns `true` if the hash table contains the key.
    #[inline]
    pub fn contains_key<'a, Q: ?Sized + Eq + Hash>(&self, key: &Q) -> bool
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        self.find_key(key).1.is_some()
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink> + HashAdapter,
    A: for<'a> KeyAdapter<'a>,
    B: Array<Item = LinkedList<A>>,
    S: BuildHasher,
{
    /// Returns an `Entry` for the given key which contains a `CursorMut` to an
    /// element with the given key or an `InsertCursor` which points to a place
    /// in which to insert a new element with the given key.
    ///
    /// This is more efficient than calling `find` followed by `insert` since
    /// the hash table does not have to be searched a second time to find a place to
    /// insert the new element.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn entry_noalloc<'a>(
        &mut self,
        val: A::Pointer,
    ) -> Result<Entry<'_, A, B, S>, A::Pointer>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        let raw_val = &*val as *const _;
        let key = self.adapter.get_key(unsafe { &*raw_val });
        let hash_code = {
            let mut hasher = self.hash_builder.build_hasher();
            (&key).hash(&mut hasher);
            hasher.finish()
        };

        let (bucket_idx, raw_ptr) = self.find_internal(&key, hash_code);
        if let Some(raw_ptr) = raw_ptr {
            // CursorMut
            Ok(Entry::Occupied(CursorMut {
                hash_table: self,
                inner: Some((raw_ptr, bucket_idx)),
            }))
        } else {
            // InsertCursor
            Ok(Entry::Vacant(InsertCursor {
                hash_table: self,
                hash_code,
            }))
        }
    }

    /// Inserts a value into the table.
    #[inline]
    pub fn insert_noalloc<'a>(
        &mut self,
        val: A::Pointer,
    ) -> Result<CursorMut<'_, A, B, S>, A::Pointer>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        let raw = self as *mut _;

        let (ptr, bucket_idx) = {
            match self.insert_noalloc_helper(val) {
                Ok((ptr, bucket_idx)) => (ptr, bucket_idx),
                Err(ptr) => return Err(ptr),
            }
        };

        Ok(CursorMut {
            hash_table: unsafe { &mut *raw },
            inner: Some((ptr as *const _, bucket_idx)),
        })
    }

    #[inline]
    fn insert_noalloc_helper_hash_code<'a>(
        &mut self,
        val: A::Pointer,
        hash_code: u64,
    ) -> Result<(*const A::Value, usize), A::Pointer>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        if self.size == self.cap {
            return Err(val);
        }

        // have we exceeded the constrained load factor?
        // remember your fractions + inequalities.
        // self.size / self.buckets_len < self.max_load_factor.size / self.max_load_factor.bucket_count
        // |
        // |
        // V
        // self.size * self.max_load_factor.bucket_count < self.max_load_factor.size * self.buckets_len
        if !(self.size * self.max_load_factor.bucket_count
            < self.max_load_factor.size * self.buckets.len())
        {
            return Err(val);
        }

        self.adapter.set_cached_hash(val.deref(), Some(hash_code));
        let bucket_idx = (hash_code % (self.buckets.len() as u64)) as usize;

        let ptr = { val.deref() as *const _ };
        self.size += 1;
        self.buckets.as_mut_slice()[bucket_idx].push_back(val);

        Ok((ptr, bucket_idx))
    }

    #[inline]
    fn insert_noalloc_helper<'a>(
        &mut self,
        val: A::Pointer,
    ) -> Result<(*const A::Value, usize), A::Pointer>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        if self.size == self.cap {
            return Err(val);
        }

        // have we exceeded the constrained load factor?
        // remember your fractions + inequalities.
        // self.size / self.buckets_len < self.max_load_factor.size / self.max_load_factor.bucket_count
        // |
        // |
        // V
        // self.size * self.max_load_factor.bucket_count < self.max_load_factor.size * self.buckets_len
        if !(self.size * self.max_load_factor.bucket_count
            < self.max_load_factor.size * self.buckets.len())
        {
            return Err(val);
        }

        let raw = &*val as *const _;

        let hash_code = {
            let key = unsafe { self.adapter.get_key(&*raw) };
            let mut hasher = self.hash_builder.build_hasher();
            key.borrow().hash(&mut hasher);
            hasher.finish()
        };
        self.insert_noalloc_helper_hash_code(val, hash_code)
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    #[inline]
    pub fn append_noalloc<'a>(&mut self, other: &mut Self) -> Result<(), ()>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        if self.capacity() - self.len() < other.len() {
            return Err(());
        }

        let mut cursor = other.front_mut();
        while let Some(item) = cursor.remove() {
            self.insert_noalloc(item).map(|_| ()).map_err(|_| ()).expect("");
        }

        Ok(())
    }

    /// Removes a value from the hash table.
    #[inline]
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<A::Pointer>
    where
        for<'a> <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        Q: Eq + Hash,
    {
        if self.size == 0 {
            return None;
        }

        self.find_mut(key).remove()
    }
}

impl<A, B, S> ChainedHashTable<A, B, S>
where
    A: Adapter<Link = LinkedListLink> + HashAdapter + Clone,
    A: for<'a> KeyAdapter<'a>,
    B: DynamicArray<Item = LinkedList<A>>,
    S: BuildHasher,
{
    /// Inserts a value into the table.
    pub fn insert<'a>(&mut self, mut val: A::Pointer) -> CursorMut<'_, A, B, S>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        loop {
            match self.insert_noalloc_helper(val) {
                Ok((ptr, idx)) => {
                    return CursorMut {
                        hash_table: self,
                        inner: Some((ptr, idx)),
                    };
                }
                Err(ptr) => {
                    self.rehash(self.buckets.len() + (self.buckets.len() >> 1));
                    // try to insert again
                    val = ptr;
                }
            }
        }
    }

    /// Returns an `Entry` for the given key which contains a `CursorMut` to an
    /// element with the given key or an `InsertCursor` which points to a place
    /// in which to insert a new element with the given key.
    ///
    /// This is more efficient than calling `find` followed by `insert` since
    /// the hash table does not have to be searched a second time to find a place to
    /// insert the new element.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn entry<'a>(
        &mut self,
        mut val: A::Pointer,
    ) -> Entry<'_, A, B, S>
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        let raw = self as *mut Self;

        loop {
            let this = unsafe { &mut *raw };
            match this.entry_noalloc(val) {
                Ok(x) => {
                    return x;
                }
                Err(ptr) => {
                    self.rehash(self.buckets.len() + (self.buckets.len() >> 1));
                    // try to insert again
                    val = ptr;
                }
            }
        }
    }

    /// Moves all the elements of `other` into `Self`, leaving `other` empty.
    pub fn append<'a>(&mut self, other: &mut Self)
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        let new_len = self.len() + other.len();
        let new_buckets_len = new_len * self.max_load_factor.bucket_count / self.max_load_factor.size;
        self.rehash(new_buckets_len);
        let mut cursor = other.front_mut();
        while let Some(item) = cursor.remove() {
            self.insert(item);
        }
    }

    fn rehash<'a>(&mut self, new_buckets_len: usize)
    where
        <A as KeyAdapter<'a>>::Key: Eq + Hash,
        A::Value: 'a,
    {
        // resize the dynamic array
        let mut items = self.buckets.as_mut_slice().iter_mut().fold(
            LinkedList::new(self.adapter.clone()),
            |mut acc, bucket| {
                acc.back_mut().splice_after(bucket.take());
                acc
            },
        );
        
        let old_bucket_count = self.buckets.len();
        // increase by 1.5x, not 2x.
        // 1.5x is optimal for resizing dynamic arrays. look it up!
        let new_bucket_count = cmp::max(cmp::max(2, old_bucket_count + (old_bucket_count >> 1)), new_buckets_len);
        //self.buckets.resize_with(new_bucket_count, Default::default);
        let new_adapter = self.adapter.clone();
        self.buckets
            .resize_with(new_bucket_count, || LinkedList::new(new_adapter.clone()));
        // Re-hash everything.
        let mut cursor = items.front_mut();
        while let Some(item) = cursor.remove() {
            let raw_item_ref = unsafe { &*(&*item as *const _) };

            let hash_code = self
                .adapter
                .get_cached_hash(raw_item_ref)
                .unwrap_or_else(|| {
                    let mut hasher = self.hash_builder.build_hasher();
                    self.adapter
                        .get_key(raw_item_ref)
                        .borrow()
                        .hash(&mut hasher);
                    hasher.finish()
                });
            let bucket_idx = (hash_code % (new_bucket_count as u64)) as usize;

            self.buckets.as_mut_slice()[bucket_idx].push_back(item);
        }
        // what is the new capacity?
        let new_cap = cmp::max(1, new_bucket_count / self.max_load_factor.bucket_count)
            * self.max_load_factor.size;
        self.cap = new_cap;
    }
}

/// A cursor which provides read-only access to a `ChainedHashTable`.
pub struct Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    hash_table: &'a ChainedHashTable<A, B, S>,
    inner: Option<(*const A::Value, usize)>,
}
// bucket_index(&self) -> Option<usize>
// move_next, move_prev, move_next_bucket, move_prev_bucket

impl<'a, A, B, S> Clone for Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    #[inline]
    fn clone(&self) -> Self {
        Cursor {
            hash_table: self.hash_table,
            inner: self.inner.clone(),
        }
    }
}

unsafe impl<'a, A, B, S> Send for Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
}

unsafe impl<'a, A, B, S> Sync for Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
}

impl<'a, A, B, S> Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.inner.is_none()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&A::Value> {
        unsafe { self.inner.map(|(ptr, _)| &*ptr) }
    }

    /// Returns the index of the bucket that the cursor is currently pointing to.
    #[inline]
    pub fn bucket_index(&self) -> Option<usize> {
        self.inner.map(|(_, bucket_idx)| bucket_idx)
    }
}

impl<'a, A, B, S> Cursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Moves the cursor to the next element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        let start = if let Some((ptr, idx)) = self.inner {
            // find next item in bucket 'idx'
            {
                let mut cursor =
                    unsafe { self.hash_table.buckets.as_slice()[idx].cursor_from_ptr(ptr) };
                cursor.move_next();
                if !cursor.is_null() {
                    self.inner = cursor.get().map(|x| (x as *const _, idx));
                    return;
                }
            }
            // or start the search at idx, exclusive
            idx.saturating_add(1)
        } else {
            0
        };

        // find item in any bucket
        for i in start..(self.hash_table.buckets.len()) {
            let cursor = self.hash_table.buckets.as_slice()[i].front();
            if !cursor.is_null() {
                self.inner = cursor.get().map(|x| (x as *const _, i));
                return;
            }
        }
        
        self.inner = None;
    }

    /// Moves the cursor to the previous element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the last element of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let end = if let Some((ptr, idx)) = self.inner {
            // find prev item in bucket 'idx'
            {
                let mut cursor =
                    unsafe { self.hash_table.buckets.as_slice()[idx].cursor_from_ptr(ptr) };
                cursor.move_prev();
                if !cursor.is_null() {
                    self.inner = cursor.get().map(|x| (x as *const _, idx));
                    return;
                }
            }
            // or end the search at idx, exclusive
            idx
        } else {
            self.hash_table.buckets.len()
        };

        // find item in any bucket
        for i in (0..end).rev() {
            let cursor = self.hash_table.buckets.as_slice()[i].front();
            if !cursor.is_null() {
                self.inner = cursor.get().map(|x| (x as *const _, i));
                return;
            }
        }

        self.inner = None;
    }

    /// Moves the cursor to the first element of the next bucket of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the first bucket of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_next_bucket(&mut self) {
        // idx is exclusive
        let start = self.inner.map(|(_, idx)| idx.saturating_add(1)).unwrap_or(0);
        for i in start..(self.hash_table.buckets.len()) {
            let cursor = self.hash_table.buckets.as_slice()[i].front();
            if !cursor.is_null() {
                self.inner = cursor.get().map(|x| (x as *const _, i));
                return;
            }
        }
        
        self.inner = None;
    }

    /// Moves the cursor to the first element of the previous bucket of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the last bucket of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_prev_bucket(&mut self) {
        // idx is exclusive
        let end = self.inner.map(|(_, idx)| idx).unwrap_or(self.hash_table.buckets.len());
        for i in (0..end).rev() {
            let cursor = self.hash_table.buckets.as_slice()[i].front();
            if !cursor.is_null() {
                self.inner = cursor.get().map(|x| (x as *const _, i));
                return;
            }
        }
        
        self.inner = None;
    }
}

/// A cursor which provides mutable access to a `ChainedHashTable`.
pub struct CursorMut<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    hash_table: &'a mut ChainedHashTable<A, B, S>,
    inner: Option<(*const A::Value, usize)>,
}
// bucket_index(&self) -> Option<usize>
// move_next, move_prev, move_next_bucket, move_prev_bucket
// remove
// replace

impl<'a, A, B, S> CursorMut<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.inner.is_none()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&A::Value> {
        unsafe { self.inner.map(|(ptr, _)| &*ptr) }
    }

    /// Returns the index of the bucket that the cursor is currently pointing to.
    #[inline]
    pub fn bucket_index(&self) -> Option<usize> {
        self.inner.map(|(_, bucket_idx)| bucket_idx)
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the `Cursor`.
    #[inline]
    pub fn as_cursor(&self) -> Cursor<'_, A, B, S> {
        Cursor {
            hash_table: self.hash_table,
            inner: self.inner.clone(),
        }
    }

    /// Moves the cursor to the next element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        let mut next = self.as_cursor();
        next.move_next();
        self.inner = next.inner;
    }

    /// Moves the cursor to the previous element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the last element of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let mut prev = self.as_cursor();
        prev.move_prev();
        self.inner = prev.inner;
    }

    /// Moves the cursor to the first element of the next bucket of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the first bucket of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_next_bucket(&mut self) {
        let mut next = self.as_cursor();
        next.move_next_bucket();
        self.inner = next.inner;
    }

    /// Moves the cursor to the first element of the previous bucket of the `ChainedHashTable`.
    ///
    /// If the cursor is pointing to the null object then this will move it to
    /// the first element of the last bucket of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will move it to the null object.
    #[inline]
    pub fn move_prev_bucket(&mut self) {
        let mut prev = self.as_cursor();
        prev.move_prev_bucket();
        self.inner = prev.inner;
    }

    /// Returns a cursor pointing to the next element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `ChainedHashTable`. If it is pointing to the last
    /// element of the `ChainedHashTable` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A, B, S> {
        let mut next = self.as_cursor();
        next.move_next();
        next
    }

    /// Returns a cursor pointing to the previous element of the `ChainedHashTable`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// last element of the `ChainedHashTable`. If it is pointing to the first
    /// element of the `ChainedHashTable` then this will return a null cursor.
    #[inline]
    pub fn peek_prev(&self) -> Cursor<'_, A, B, S> {
        let mut prev = self.as_cursor();
        prev.move_prev();
        prev
    }

    /// Removes the current element from the `ChainedHashTable`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `ChainedHashTable`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<A::Pointer> {
        match self.inner {
            None => None,
            Some((ptr, idx)) => {
                let next_inner = {
                    let mut cursor = self.as_cursor();
                    cursor.move_next();
                    cursor.inner
                };
                let mut cursor =
                    unsafe { self.hash_table.buckets.as_mut_slice()[idx].cursor_mut_from_ptr(ptr) };
                self.hash_table.size -= 1;
                let ret = cursor.remove();
                self.inner = next_inner;
                ret
            }
        }
    }
}

impl<'a, A, B, S> CursorMut<'a, A, B, S>
where
    A: HashAdapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// Removes the current element from the `ChainedHashTable` and inserts another
    /// object in its place.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// modified to point to the newly added element.
    ///
    /// When using this function you must ensure that the elements in the
    /// collection are maintained in increasing order. Failure to do this may
    /// lead to `find` returning
    /// incorrect results.
    ///
    /// If the cursor is currently pointing to the null object then an error is
    /// returned containing the given `val` parameter.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn replace_with(&mut self, val: A::Pointer) -> Result<A::Pointer, A::Pointer> {
        match self.inner {
            Some((ptr, idx)) => unsafe {
                let hash = self.hash_table.adapter.get_cached_hash(&*ptr);
                self.hash_table.adapter.set_cached_hash(&*val, hash);
                let mut cursor = self.hash_table.buckets.as_mut_slice()[idx].cursor_mut_from_ptr(ptr);
                cursor.replace_with(val)
            },
            None => {
                Err(val)
            },
        }
    }
}

impl<'a, A, B, S> CursorMut<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + HashAdapter,
    A: for<'b> KeyAdapter<'b>,
    B: Array<Item = LinkedList<A>>,
    S: core::hash::BuildHasher,
{
    /// Inserts a new element into the `ChainedHashTable`.
    ///
    /// The new element will be inserted at the correct position in the hash table
    /// based on its key, regardless of the current cursor position.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_noalloc(&mut self, val: A::Pointer) -> Result<(), A::Pointer>
    where
        for<'b> <A as KeyAdapter<'b>>::Key: Eq + Hash,
    {
        match self.hash_table.insert_noalloc(val) {
            Ok(new_cursor) => {
                self.inner = new_cursor.inner;
                Ok(())
            }
            Err(ptr) => Err(ptr),
        }
    }
}

impl<'a, A, B, S> CursorMut<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + HashAdapter + Clone + Default,
    A: for<'b> KeyAdapter<'b>,
    B: DynamicArray<Item = LinkedList<A>>,
    S: core::hash::BuildHasher,
{
    /// Inserts a new element into the `ChainedHashTable`.
    ///
    /// The new element will be inserted at the correct position in the hash table
    /// based on its key, regardless of the current cursor position.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert(&mut self, val: A::Pointer)
    where
        for<'b> <A as KeyAdapter<'b>>::Key: Eq + Hash,
    {
        self.inner = self.hash_table.insert(val).inner;
    }
}

// insert_after, insert_before may be unsafe b/c we must ensure that the key hashes to the appropriate bucket.

/// A iterator over the items in a chained hash table.
pub struct Iter<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    cursor: Cursor<'a, A, B, S>,
}

impl<'a, A, B, S> Clone for Iter<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + 'a,
    B: Array<Item = LinkedList<A>>,
{
    #[inline]
    fn clone(&self) -> Self {
        Iter {
            cursor: self.cursor.clone(),
        }
    }
}

impl<'a, A, B, S> Iterator for Iter<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + 'a,
    B: Array<Item = LinkedList<A>>,
{
    type Item = &'a A::Value;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            if !self.cursor.is_null() {
                let ret = self.cursor.get().map(|x| &*(x as *const _));
                self.cursor.move_next();
                ret
            } else {
                None
            }
        }
    }
}

impl<'a, A, B, S> DoubleEndedIterator for Iter<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + 'a,
    B: Array<Item = LinkedList<A>>,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        unsafe {
            if !self.cursor.is_null() {
                let ret = self.cursor.get().map(|x| &*(x as *const _));
                self.cursor.move_prev();
                ret
            } else {
                None
            }
        }
    }
}

impl<'a, A, B, S> iter::FusedIterator for Iter<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink> + 'a,
    B: Array<Item = LinkedList<A>>,
{
}

/// An entry in a `ChainedHashTable`.
///
/// See the documentation for `ChainedHashTable::entry`.
pub enum Entry<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    /// An occupied entry.
    Occupied(CursorMut<'a, A, B, S>),
    /// A vacant entry.
    Vacant(InsertCursor<'a, A, B, S>),
}

impl<'a, A, B, S> Entry<'a, A, B, S>
where
    A: HashAdapter<Link = LinkedListLink>,
    A: for<'b> KeyAdapter<'b>,
    B: Array<Item = LinkedList<A>>,
    S: BuildHasher,
    <A as KeyAdapter<'a>>::Key: Eq + Hash,
{
    /// Inserts an element into the `ChainedHashTable` if the entry is vacant, returning
    /// a `CursorMut` to the resulting value. If the entry is occupied then a
    /// `CursorMut` pointing to the element is returned.
    ///
    /// # Panics
    ///
    /// Panics if the `Entry` is vacant and the new element is already linked to
    /// a different intrusive collection.
    #[inline]
    pub fn or_insert(self, val: A::Pointer) -> CursorMut<'a, A, B, S> {
        match self {
            Entry::Occupied(x) => x,
            Entry::Vacant(x) => x.insert(val),
        }
    }

    /// Calls the given function and inserts the result into the `ChainedHashTable` if the
    /// entry is vacant, returning a `CursorMut` to the resulting value. If the
    /// entry is occupied then a `CursorMut` pointing to the element is
    /// returned and the function is not executed.
    ///
    /// # Panics
    ///
    /// Panics if the `Entry` is vacant and the new element is already linked to
    /// a different intrusive collection.
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> A::Pointer>(self, f: F) -> CursorMut<'a, A, B, S> {
        match self {
            Entry::Occupied(x) => x,
            Entry::Vacant(x) => x.insert(f()),
        }
    }
}

/// A cursor pointing to a slot in which an element can be inserted into a
/// `ChainedHashTable`.
pub struct InsertCursor<'a, A, B, S>
where
    A: Adapter<Link = LinkedListLink>,
    B: Array<Item = LinkedList<A>>,
{
    hash_table: &'a mut ChainedHashTable<A, B, S>,
    hash_code: u64,
}

impl<'a, A, B, S> InsertCursor<'a, A, B, S>
where
    A: HashAdapter<Link = LinkedListLink> + 'a,
    A: for<'b> KeyAdapter<'b>,
    B: Array<Item = LinkedList<A>>,
    S: BuildHasher,
    <A as KeyAdapter<'a>>::Key: Eq + Hash,
{
    /// Inserts a new element into the `ChainedHashTable` at the location indicated by
    /// this `InsertCursor`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert(self, val: A::Pointer) -> CursorMut<'a, A, B, S> {
        match self.hash_table.insert_noalloc_helper_hash_code(val, self.hash_code) {
            Ok((ptr, idx)) => {
                CursorMut {
                    hash_table: self.hash_table,
                    inner: Some((ptr, idx)),
                }
            },
            Err(_) => {
                panic!("");
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use self::rand::{Rng, XorShiftRng};
    use super::*;
    use crate::linked_list::Link;
    use crate::{KeyAdapter, UnsafeRef};
    use rand;
    use std::boxed::Box;
    use std::collections::hash_map::RandomState;
    use std::fmt;
    use std::vec::Vec;

    #[derive(Clone)]
    struct Obj {
        link: LinkedListLink,
        hash: core::cell::Cell<Option<u64>>,
        value: i32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adapter!(ObjAdapter = UnsafeRef<Obj>: Obj { link: Link });
    impl<'a> KeyAdapter<'a> for ObjAdapter {
        type Key = &'a i32;
        fn get_key(&self, value: &'a Self::Value) -> &'a i32 {
            &value.value
        }
    }
    impl HashAdapter for ObjAdapter {
        #[inline]
        fn get_cached_hash(&self, val: &Self::Value) -> Option<u64> {
            val.hash.get()
        }

        #[inline]
        fn set_cached_hash(&self, val: &Self::Value, hash: Option<u64>) {
            val.hash.set(hash);
        }
    }
    fn make_obj(value: i32) -> UnsafeRef<Obj> {
        UnsafeRef::from_box(Box::new(Obj {
            link: Link::new(),
            hash: core::cell::Cell::new(None),
            value: value,
        }))
    }

    #[test]
    fn test_insert_remove() {
        let v = (0..100).map(make_obj).collect::<Vec<_>>();
        assert!(v.iter().all(|x| !x.link.is_linked()));
        let mut t: ChainedHashTable<_, Vec<_>, RandomState> =
            ChainedHashTable::new(ObjAdapter::new());
        t.set_max_load_factor(ChainedLoadFactor::new(7, 8));
        assert!(t.is_empty());
        let rng = XorShiftRng::new_unseeded();

        {
            let mut expected = Vec::new();
            for x in v.iter() {
                t.insert(x.clone());
                expected.push(x.value);
                let mut values = t.iter().map(|x| x.value).collect::<Vec<_>>();
                values.sort();
                assert_eq!(values, expected);
            }

            while let Some(_) = t.front_mut().remove() {}
            assert!(t.is_empty());
        }

        {
            let mut expected = Vec::new();
            for x in v.iter() {
                t.insert(x.clone());
                expected.push(x.value);
                let mut values = t.iter().map(|x| x.value).collect::<Vec<_>>();
                values.sort();
                assert_eq!(values, expected);
            }

            while let Some(_) = t.front_mut().remove() {}
            assert!(t.is_empty());
        }
    }

    #[test]
    fn test_find() {
        let v = (0..10).map(|x| make_obj(x * 10)).collect::<Vec<_>>();
        let mut t: ChainedHashTable<_, Vec<_>, RandomState> =
            ChainedHashTable::new(ObjAdapter::new());
        assert!(t.is_empty());
        for x in v.iter() {
            t.insert(x.clone());
        }

        for i in -9..100 {
            {
                let c = t.find(&i);
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i % 10 == 0 { Some(i) } else { None }
                );
            }
            {
                let c = t.find_mut(&i);
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i % 10 == 0 { Some(i) } else { None }
                );
            }
        }
    }

    #[test]
    fn test_fast_clear() {
        let mut t: ChainedHashTable<_, Vec<_>, RandomState> =
            ChainedHashTable::new(ObjAdapter::new());
        t.set_max_load_factor(ChainedLoadFactor::new(7, 8));
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        t.insert(a.clone());
        t.insert(b.clone());
        t.insert(c.clone());

        t.fast_clear();
        assert!(t.is_empty());
        assert!(a.link.is_linked());
        assert!(b.link.is_linked());
        assert!(c.link.is_linked());
        unsafe {
            a.link.force_unlink();
            b.link.force_unlink();
            c.link.force_unlink();
        }
        assert!(t.is_empty());
        assert!(!a.link.is_linked());
        assert!(!b.link.is_linked());
        assert!(!c.link.is_linked());
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a, T> {
            link: Link,
            hash: core::cell::Cell<Option<u64>>,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link: Link} where T: 'a);
        impl<'a, 'b, T: 'a + 'b> KeyAdapter<'a> for ObjAdapter<'b, T> {
            type Key = &'a T;

            fn get_key(&self, value: &'a Obj<'b, T>) -> Self::Key {
                value.value
            }
        }
        impl<'a, T: 'a> HashAdapter for ObjAdapter<'a, T> {
            #[inline]
            fn get_cached_hash(&self, val: &Self::Value) -> Option<u64> {
                val.hash.get()
            }

            #[inline]
            fn set_cached_hash(&self, val: &Self::Value, hash: Option<u64>) {
                val.hash.set(hash);
            }
        }

        let v = 5;
        let a: Obj<'_, i32> = Obj {
            link: Link::default(),
            hash: core::cell::Cell::new(None),
            value: &v,
        };
        let b = a.clone();
        let adapter: ObjAdapter<'_, i32> = ObjAdapter::new();
        let mut l: ChainedHashTable<_, Vec<_>, RandomState> =
            ChainedHashTable::new(adapter);
        l.insert(&a);
        l.insert(&b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
        assert_eq!(*l.find(&5).get().unwrap().value, 5);
    }
}
