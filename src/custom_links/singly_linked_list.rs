// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use core::fmt;
use core::cell::Cell;

use super::Adapter;

use crate::IntrusivePointer;

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a `SinglyLinkedList`.
pub trait Link<NodeRef> {
    /// Returns the reference to the "next" object.
    fn next(&self) -> NodeRef;

    /// Sets the reference to the "next" object.
    fn set_next(&self, next: NodeRef);

    /// Checks whether the `Link` is linked into a `SinglyLinkedList`.
    fn is_linked(&self) -> bool;

    /// Forcibly unlinks an object from a `SinglyLinkedList`.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call this function while still linked into a
    /// `SinglyLinkedList`. The only situation where this function is useful is
    /// after calling `fast_clear` on a `SinglyLinkedList`, since this clears
    /// the collection without marking the nodes as unlinked.
    unsafe fn force_unlink(&self);
}

// =============================================================================
// NodeRef
// =============================================================================

/// A reference to an object that can be inserted into a `SinglyLinkedList`.
pub trait NodeRef: Copy + Eq {
    /// Constructs a "null" `NodeRef`.
    fn null() -> Self;

    /// Constructs an "UNLINKED_MARKER" `NodeRef`.
    fn unlinked_marker() -> Self;

    /// Returns `true` if `self == Self::null()`.
    fn is_null(self) -> bool;

    /// Returns the reference to the "next" object.
    #[inline]
    unsafe fn next<A>(self, adapter: &A) -> Self
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        (&*adapter.node_into_link(self)).next()
    }

    /// Sets the reference to the "next" object.
    #[inline]
    unsafe fn set_next<A>(self, adapter: &A, next: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        (&*adapter.node_into_link(self)).set_next(next);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn unlink<A>(self, adapter: &A)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        self.set_next(adapter, Self::unlinked_marker());
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn link_between<A>(self, adapter: &A, prev: Self, next: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if !prev.is_null() {
            prev.set_next(adapter, self);
        }
        self.set_next(adapter, next);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn link_after<A>(self, adapter: &A, prev: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        self.link_between(adapter, prev, prev.next(adapter));
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn replace_with<A>(self, adapter: &A, prev: Self, new: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if !prev.is_null() {
            prev.set_next(adapter, self.next(adapter));
        }
        new.set_next(adapter, self.next(adapter));
        self.unlink(adapter);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn remove<A>(self, adapter: &A, prev: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if !prev.is_null() {
            prev.set_next(adapter, self.next(adapter));
        }
        self.unlink(adapter);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn splice<A>(adapter: &A, start: Self, end: Self, prev: Self, next: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        end.set_next(adapter, next);
        if !prev.is_null() {
            prev.set_next(adapter, start);
        }
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `SinglyLinkedList`.
pub struct Cursor<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    current: A::NodeRef,
    list: &'a SinglyLinkedList<A>,
}

impl<'a, A: Adapter> Clone for Cursor<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            list: self.list,
        }
    }
}

impl<'a, A: Adapter> Cursor<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.current.is_null()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&'a A::Value> {
        if self.is_null() {
            None
        } else {
            let adapter = &self.list.adapter;
            Some(unsafe { &*adapter.get_value(adapter.node_into_link(self.current)) })
        }
    }

    /// Clones and returns the pointer that points to the element that the
    /// cursor is referencing.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn clone_pointer(&self) -> Option<A::Pointer>
    where
        A::Pointer: IntrusivePointer<A::Value> + Clone,
    {
        let raw_pointer = self.get()? as *const A::Value;
        Some(unsafe { crate::intrusive_pointer::clone_pointer_from_raw(raw_pointer) })
    }

    /// Moves the cursor to the next element of the `SinglyLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `SinglyLinkedList`. If it is pointing to the
    /// last element of the `SinglyLinkedList` then this will move it to the
    /// null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = self.list.head;
        } else {
            self.current = unsafe { self.current.next(&self.list.adapter) };
        }
    }

    /// Returns a cursor pointing to the next element of the `SinglyLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `SinglyLinkedList`. If it is pointing to the last
    /// element of the `SinglyLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
        let mut next = self.clone();
        next.move_next();
        next
    }
}

/// A cursor which provides mutable access to a `SinglyLinkedList`.
pub struct CursorMut<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    current: A::NodeRef,
    list: &'a mut SinglyLinkedList<A>,
}

impl<'a, A: Adapter> CursorMut<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.current.is_null()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&A::Value> {
        if self.is_null() {
            None
        } else {
            let adapter = &self.list.adapter;
            Some(unsafe { &*adapter.get_value(adapter.node_into_link(self.current)) })
        }
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the `Cursor`.
    #[inline]
    pub fn as_cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: self.current,
            list: self.list,
        }
    }

    /// Moves the cursor to the next element of the `SinglyLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `SinglyLinkedList`. If it is pointing to the
    /// last element of the `SinglyLinkedList` then this will move it to the
    /// null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = self.list.head;
        } else {
            self.current = unsafe { self.current.next(&self.list.adapter) };
        }
    }

    /// Returns a cursor pointing to the next element of the `SinglyLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `SinglyLinkedList`. If it is pointing to the last
    /// element of the `SinglyLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
        let mut next = self.as_cursor();
        next.move_next();
        next
    }

    /// Removes the next element from the `SinglyLinkedList`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// not moved.
    ///
    /// If the cursor is currently pointing to the last element of the
    /// `SinglyLinkedList` then no element is removed and `None` is returned.
    #[inline]
    pub fn remove_next(&mut self) -> Option<A::Pointer> {
        unsafe {
            let next = if self.is_null() {
                self.list.head
            } else {
                self.current.next(&self.list.adapter)
            };
            if next.is_null() {
                return None;
            }
            if self.is_null() {
                self.list.head = next.next(&self.list.adapter);
            }
            next.remove(&self.list.adapter, self.current);
            Some(unsafe { self.list.adapter.node_into_pointer(next) })
        }
    }

    /// Removes the next element from the `SinglyLinkedList` and inserts
    /// another object in its place.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// not moved.
    ///
    /// If the cursor is currently pointing to the last element of the
    /// `SinglyLinkedList` then no element is added or removed and an error is
    /// returned containing the given `val` parameter.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn replace_next_with(&mut self, val: A::Pointer) -> Result<A::Pointer, A::Pointer> {
        unsafe {
            let next = if self.is_null() {
                self.list.head
            } else {
                self.current.next(&self.list.adapter)
            };
            if next.is_null() {
                return Err(val);
            }
            let new = self.list.node_from_value(val);
            if self.is_null() {
                self.list.head = new;
            }
            next.replace_with(&self.list.adapter, self.current, new);
            Ok(self.list.adapter.node_into_pointer(next))
        }
    }

    /// Inserts a new element into the `SinglyLinkedList` after the current one.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the front of the `SinglyLinkedList`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_after(&mut self, val: A::Pointer) {
        unsafe {
            let new = self.list.node_from_value(val);
            if self.is_null() {
                new.link_between(&self.list.adapter, A::NodeRef::null(), self.list.head);
                self.list.head = new;
            } else {
                new.link_after(&self.list.adapter, self.current);
            }
        }
    }

    /// Inserts the elements from the given `SinglyLinkedList` after the current
    /// one.
    ///
    /// If the cursor is pointing at the null object then the new elements are
    /// inserted at the start of the `SinglyLinkedList`.
    ///
    /// Note that if the cursor is not pointing to the last element of the
    /// `SinglyLinkedList` then the given list must be scanned to find its last
    /// element. This has linear time complexity.
    #[inline]
    pub fn splice_after(&mut self, mut list: SinglyLinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                let next = if self.is_null() {
                    self.list.head
                } else {
                    self.current.next(&self.list.adapter)
                };
                if next.is_null() {
                    if self.is_null() {
                        self.list.head = list.head;
                    } else {
                        self.current.set_next(&self.list.adapter, list.head);
                    }
                } else {
                    let mut tail = list.head;
                    while !tail.next(&self.list.adapter).is_null() {
                        tail = tail.next(&self.list.adapter);
                    }
                    A::NodeRef::splice(&self.list.adapter, list.head, tail, self.current, next);
                    if self.is_null() {
                        self.list.head = list.head;
                    }
                }
                list.head = A::NodeRef::null();
            }
        }
    }

    /// Splits the list into two after the current element. This will return a
    /// new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the null object then the entire contents
    /// of the `SinglyLinkedList` are moved.
    #[inline]
    pub fn split_after(&mut self) -> SinglyLinkedList<A>
    where
        A: Clone,
    {
        if self.is_null() {
            let list = SinglyLinkedList {
                head: self.list.head,
                adapter: self.list.adapter.clone(),
            };
            self.list.head = A::NodeRef::null();
            list
        } else {
            unsafe {
                let list = SinglyLinkedList {
                    head: self.current.next(&self.list.adapter),
                    adapter: self.list.adapter.clone(),
                };
                self.current
                    .set_next(&self.list.adapter, A::NodeRef::null());
                list
            }
        }
    }
}

// =============================================================================
// SinglyLinkedList
// =============================================================================

/// An intrusive singly-linked list.
///
/// When this collection is dropped, all elements linked into it will be
/// converted back to owned pointers and dropped.
pub struct SinglyLinkedList<A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    head: A::NodeRef,
    adapter: A,
}

impl<A: Adapter> SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn node_from_value(&self, val: A::Pointer) -> A::NodeRef {
        unsafe {
            let node = self.adapter.node_from_pointer(val);

            if (*self.adapter.node_into_link(node)).is_linked() {
                // convert the node back into a pointer
                self.adapter.node_into_pointer(node);

                panic!("attempted to insert an object that is already linked");
            }

            node
        }
    }

    /// Creates an empty `SinglyLinkedList`.
    #[inline]
    pub fn new(adapter: A) -> SinglyLinkedList<A> {
        SinglyLinkedList {
            head: A::NodeRef::null(),
            adapter,
        }
    }

    /// Returns `true` if the `SinglyLinkedList` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Returns a null `Cursor` for this list.
    pub fn cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: NodeRef::null(),
            list: self,
        }
    }

    /// Returns a null `CursorMut` for this list.
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut {
            current: NodeRef::null(),
            list: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    pub unsafe fn cursor_from_ptr(&self, ptr: *const A::Value) -> Cursor<'_, A> {
        Cursor {
            current: self.adapter.node_from_link(self.adapter.get_link(ptr)),
            list: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    pub unsafe fn cursor_mut_from_ptr(&mut self, ptr: *const A::Value) -> CursorMut<'_, A> {
        CursorMut {
            current: self.adapter.node_from_link(self.adapter.get_link(ptr)),
            list: self,
        }
    }

    /// Returns a `Cursor` pointing to the first element of the list. If the
    /// list is empty then a null cursor is returned.
    pub fn front(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorMut` pointing to the first element of the list. If the
    /// the list is empty then a null cursor is returned.
    pub fn front_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }

    /// Gets an iterator over the objects in the `SinglyLinkedList`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, A> {
        Iter {
            current: self.head,
            list: self,
        }
    }

    /// Removes all elements from the `SinglyLinkedList`.
    ///
    /// This will unlink all object currently in the list, which requires
    /// iterating through all elements in the `SinglyLinkedList`. Each element is
    /// converted back to an owned pointer and then dropped.
    #[inline]
    pub fn clear(&mut self) {
        let mut current = self.head;
        self.head = A::NodeRef::null();
        while !current.is_null() {
            unsafe {
                let next = current.next(&self.adapter);
                current.unlink(&self.adapter);
                self.adapter.node_into_pointer(current);
                current = next;
            }
        }
    }

    /// Empties the `SinglyLinkedList` without unlinking or freeing objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `SinglyLinkedList` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `force_unlink` function on them.
    pub fn fast_clear(&mut self) {
        self.head = A::NodeRef::null();
    }

    /// Takes all the elements out of the `SinglyLinkedList`, leaving it empty.
    /// The taken elements are returned as a new `SinglyLinkedList`.
    pub fn take(&mut self) -> SinglyLinkedList<A>
    where
        A: Clone,
    {
        let list = SinglyLinkedList {
            head: self.head,
            adapter: self.adapter.clone(),
        };
        self.head = A::NodeRef::null();
        list
    }

    /// Inserts a new element at the start of the `SinglyLinkedList`.
    #[inline]
    pub fn push_front(&mut self, val: A::Pointer) {
        self.cursor_mut().insert_after(val);
    }

    /// Removes the first element of the `SinglyLinkedList`.
    ///
    /// This returns `None` if the `SinglyLinkedList` is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<A::Pointer> {
        self.cursor_mut().remove_next()
    }
}

// Allow read-only access to values from multiple threads
unsafe impl<A: Adapter + Sync> Sync for SinglyLinkedList<A>
where
    A::Value: Sync,
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
}

// Allow sending to another thread if the ownership (represented by the A::Pointer owned
// pointer type) can be transferred to another thread.
unsafe impl<A: Adapter + Send> Send for SinglyLinkedList<A>
where
    A::Pointer: Send,
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
}

// Drop all owned pointers if the collection is dropped
impl<A: Adapter> Drop for SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Adapter> IntoIterator for SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = A::Pointer;
    type IntoIter = IntoIter<A>;

    #[inline]
    fn into_iter(self) -> IntoIter<A> {
        IntoIter { list: self }
    }
}

impl<'a, A: Adapter + 'a> IntoIterator for &'a SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = &'a A::Value;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adapter + Default> Default for SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    fn default() -> SinglyLinkedList<A> {
        SinglyLinkedList::new(A::default())
    }
}

impl<A: Adapter> fmt::Debug for SinglyLinkedList<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
    A::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// =============================================================================
// Iter
// =============================================================================

/// An iterator over references to the items of a `SinglyLinkedList`.
pub struct Iter<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    current: A::NodeRef,
    list: &'a SinglyLinkedList<A>,
}
impl<'a, A: Adapter + 'a> Iterator for Iter<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = &'a A::Value;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Value> {
        if self.current.is_null() {
            None
        } else {
            let current = self.current;
            self.current = unsafe { current.next(&self.list.adapter) };
            Some(unsafe {
                &*self
                    .list
                    .adapter
                    .get_value(self.list.adapter.node_into_link(current))
            })
        }
    }
}
impl<'a, A: Adapter + 'a> Clone for Iter<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            current: self.current,
            list: self.list,
        }
    }
}

// =============================================================================
// IntoIter
// =============================================================================

/// An iterator which consumes a `SinglyLinkedList`.
pub struct IntoIter<A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    list: SinglyLinkedList<A>,
}
impl<A: Adapter> Iterator for IntoIter<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = A::Pointer;

    #[inline]
    fn next(&mut self) -> Option<A::Pointer> {
        self.list.pop_front()
    }
}

// =============================================================================
// RawLink, RawLinkRef
// =============================================================================

/// Intrusive link that uses raw pointers to allow an object to be inserted into a
/// `SinglyLinkedList`.
pub struct RawLink {
    next: Cell<RawLinkRef>,
}

impl RawLink {
    /// Creates a new `Link`.
    #[inline]
    pub const fn new() -> RawLink {
        RawLink {
            next: Cell::new(UNLINKED_MARKER),
        }
    }
}

// An object containing a link can be sent to another thread if it is unlinked.
unsafe impl Send for RawLink {}

// Provide an implementation of Clone which simply initializes the new link as
// unlinked. This allows structs containing a link to derive Clone.
impl Clone for RawLink {
    #[inline]
    fn clone(&self) -> RawLink {
        RawLink::new()
    }
}

// Same as above
impl Default for RawLink {
    #[inline]
    fn default() -> RawLink {
        RawLink::new()
    }
}

// Provide an implementation of Debug so that structs containing a link can
// still derive Debug.
impl fmt::Debug for RawLink {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // There isn't anything sensible to print here except whether the link
        // is currently in a list.
        if self.is_linked() {
            write!(f, "linked")
        } else {
            write!(f, "unlinked")
        }
    }
}

impl Link<RawLinkRef> for RawLink {
    #[inline]
    fn next(&self) -> RawLinkRef {
        self.next.get()
    }

    #[inline]
    fn set_next(&self, next: RawLinkRef) {
        self.next.set(next);
    }

    #[inline]
    fn is_linked(&self) -> bool {
        self.next.get() != UNLINKED_MARKER
    }

    #[inline]
    unsafe fn force_unlink(&self) {
        self.next.set(UNLINKED_MARKER);
    }
}

/// A concrete `NodeRef` that uses raw pointers.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RawLinkRef(*const RawLink);

impl NodeRef for RawLinkRef {
    #[inline]
    fn null() -> Self {
        RawLinkRef(core::ptr::null())
    }

    #[inline]
    fn unlinked_marker() -> Self {
        UNLINKED_MARKER
    }

    #[inline]
    fn is_null(self) -> bool {
        self.0.is_null()
    }
}

// Use a special value to indicate an unlinked node
const UNLINKED_MARKER: RawLinkRef = RawLinkRef(1 as *const _);


// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::{Link, NodeRef, SinglyLinkedList, RawLink, RawLinkRef};
    use crate::IntrusivePointer;
    use crate::UnsafeRef;
    use core::cell::Cell;
    use std::boxed::Box;
    use std::fmt;
    use std::vec::Vec;

    struct Obj {
        link1: RawLink,
        link2: RawLink,
        value: u32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adapter!(ObjAdapter1 = UnsafeRef<Obj>: Obj { link1: RawLink });
    intrusive_adapter!(ObjAdapter2 = UnsafeRef<Obj>: Obj { link2: RawLink });
    fn make_obj(value: u32) -> UnsafeRef<Obj> {
        UnsafeRef::from_box(Box::new(Obj {
            link1: RawLink::new(),
            link2: RawLink::default(),
            value: value,
        }))
    }
    unsafe impl crate::custom_links::Adapter for ObjAdapter1 {
        type Link = RawLink;
        type NodeRef = RawLinkRef;
        type Value = <Self as crate::Adapter>::Value;
        type Pointer = <Self as crate::Adapter>::Pointer;

        /// Gets a reference to an object from a reference to a link in that object.
        #[inline]
        unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value {
            <Self as crate::Adapter>::get_value(self, link)
        }

        /// Gets a reference to the link for the given object.
        #[inline]
        unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link {
            <Self as crate::Adapter>::get_link(self, value)
        }

        /// Converts an object pointer into a node reference.
        #[inline]
        unsafe fn node_from_pointer(&self, pointer: Self::Pointer) -> Self::NodeRef {
            self.node_from_link(self.get_link(Self::Pointer::into_raw(pointer)))
        }

        /// Converts a node reference into an object pointer.
        #[inline]
        unsafe fn node_into_pointer(&self, node: Self::NodeRef) -> Self::Pointer {
            Self::Pointer::from_raw(self.get_value(self.node_into_link(node)))
        }

        /// Converts a node reference into a link reference.
        #[inline]
        unsafe fn node_from_link(&self, link: *const Self::Link) -> Self::NodeRef {
            RawLinkRef(link)
        }

        /// Converts a link reference to a node reference.
        #[inline]
        unsafe fn node_into_link(&self, node: Self::NodeRef) -> *const Self::Link {
            node.0
        }
    }
    unsafe impl crate::custom_links::Adapter for ObjAdapter2 {
        type Link = RawLink;
        type NodeRef = RawLinkRef;
        type Value = <Self as crate::Adapter>::Value;
        type Pointer = <Self as crate::Adapter>::Pointer;

        /// Gets a reference to an object from a reference to a link in that object.
        #[inline]
        unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value {
            <Self as crate::Adapter>::get_value(self, link)
        }

        /// Gets a reference to the link for the given object.
        #[inline]
        unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link {
            <Self as crate::Adapter>::get_link(self, value)
        }

        ///
        #[inline]
        unsafe fn node_from_pointer(&self, pointer: Self::Pointer) -> Self::NodeRef {
            self.node_from_link(self.get_link(Self::Pointer::into_raw(pointer)))
        }

        ///
        #[inline]
        unsafe fn node_into_pointer(&self, node: Self::NodeRef) -> Self::Pointer {
            Self::Pointer::from_raw(self.get_value(self.node_into_link(node)))
        }

        ///
        #[inline]
        unsafe fn node_from_link(&self, link: *const Self::Link) -> Self::NodeRef {
            RawLinkRef(link)
        }

        ///
        #[inline]
        unsafe fn node_into_link(&self, node: Self::NodeRef) -> *const Self::Link {
            node.0
        }
    }

    #[test]
    fn test_link() {
        let a = make_obj(1);
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());

        let mut b = SinglyLinkedList::<ObjAdapter1>::default();
        assert!(b.is_empty());

        b.push_front(a.clone());
        assert!(!b.is_empty());
        assert!(a.link1.is_linked());
        assert!(!a.link2.is_linked());
        assert_eq!(format!("{:?}", a.link1), "linked");
        assert_eq!(format!("{:?}", a.link2), "unlinked");

        assert_eq!(
            b.pop_front().unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(b.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());
    }

    #[test]
    fn test_cursor() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);

        let mut l = SinglyLinkedList::new(ObjAdapter1::new());
        let mut cur = l.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
        assert!(cur.remove_next().is_none());
        assert_eq!(
            cur.replace_next_with(a.clone()).unwrap_err().as_ref() as *const _,
            a.as_ref() as *const _
        );

        cur.insert_after(c.clone());
        cur.insert_after(a.clone());
        cur.move_next();
        cur.insert_after(b.clone());
        cur.move_next();
        cur.move_next();
        assert!(cur.peek_next().is_null());
        cur.move_next();
        assert!(cur.is_null());

        cur.move_next();
        assert!(!cur.is_null());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);

        {
            let mut cur2 = cur.as_cursor();
            assert_eq!(cur2.get().unwrap() as *const _, a.as_ref() as *const _);
            assert_eq!(cur2.peek_next().get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            cur2.move_next();
            assert!(cur2.is_null());
            assert!(cur2.clone().get().is_none());
        }
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);

        assert_eq!(
            cur.remove_next().unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        cur.insert_after(b.clone());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        cur.move_next();
        assert_eq!(cur.get().unwrap() as *const _, b.as_ref() as *const _);
        assert_eq!(
            cur.remove_next().unwrap().as_ref() as *const _,
            c.as_ref() as *const _
        );
        assert!(!c.link1.is_linked());
        assert!(a.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, b.as_ref() as *const _);
        cur.move_next();
        assert!(cur.is_null());
        assert_eq!(
            cur.replace_next_with(c.clone()).unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(!a.link1.is_linked());
        assert!(c.link1.is_linked());
        assert!(cur.is_null());
        cur.move_next();
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(
            cur.replace_next_with(a.clone()).unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert!(a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
    }

    #[test]
    fn test_split_splice() {
        let mut l1 = SinglyLinkedList::new(ObjAdapter1::new());
        let mut l2 = SinglyLinkedList::new(ObjAdapter1::new());
        let mut l3 = SinglyLinkedList::new(ObjAdapter1::new());

        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
        l1.cursor_mut().insert_after(d.clone());
        l1.cursor_mut().insert_after(c.clone());
        l1.cursor_mut().insert_after(b.clone());
        l1.cursor_mut().insert_after(a.clone());
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.front_mut();
            cur.move_next();
            l2 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [3, 4]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l2.front_mut();
            l3 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [3]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [4]);
        {
            let mut cur = l1.front_mut();
            cur.splice_after(l2.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [4]);
        {
            let mut cur = l1.cursor_mut();
            cur.splice_after(l3.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 1, 3, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.cursor_mut();
            l2 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 1, 3, 2]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l2.front_mut();
            cur.move_next();
            l3 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 1]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [3, 2]);
        {
            let mut cur = l2.front_mut();
            cur.splice_after(l3.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l3.cursor_mut();
            cur.splice_after(l2.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);
        {
            let mut cur = l3.front_mut();
            cur.move_next();
            l2 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [2, 1]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3]);
        {
            let mut cur = l2.front_mut();
            cur.move_next();
            cur.splice_after(l3.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [2, 1, 4, 3]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
    }

    #[test]
    fn test_iter() {
        let mut l = SinglyLinkedList::new(ObjAdapter1::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
        l.cursor_mut().insert_after(d.clone());
        l.cursor_mut().insert_after(c.clone());
        l.cursor_mut().insert_after(b.clone());
        l.cursor_mut().insert_after(a.clone());

        assert_eq!(l.front().get().unwrap().value, 1);
        unsafe {
            assert_eq!(l.cursor_from_ptr(b.as_ref()).get().unwrap().value, 2);
            assert_eq!(l.cursor_mut_from_ptr(c.as_ref()).get().unwrap().value, 3);
        }

        let mut v = Vec::new();
        for x in &l {
            v.push(x.value);
        }
        assert_eq!(v, [1, 2, 3, 4]);
        assert_eq!(
            l.iter().clone().map(|x| x.value).collect::<Vec<_>>(),
            [1, 2, 3, 4]
        );
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);

        assert_eq!(format!("{:?}", l), "[1, 2, 3, 4]");

        let mut v = Vec::new();
        for x in l.take() {
            v.push(x.value);
        }
        assert_eq!(v, [1, 2, 3, 4]);
        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert!(!d.link1.is_linked());

        l.cursor_mut().insert_after(d.clone());
        l.cursor_mut().insert_after(c.clone());
        l.cursor_mut().insert_after(b.clone());
        l.cursor_mut().insert_after(a.clone());
        l.clear();
        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert!(!d.link1.is_linked());
    }

    #[test]
    fn test_multi_list() {
        let mut l1 = SinglyLinkedList::new(ObjAdapter1::new());
        let mut l2 = SinglyLinkedList::new(ObjAdapter2::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
        l1.cursor_mut().insert_after(d.clone());
        l1.cursor_mut().insert_after(c.clone());
        l1.cursor_mut().insert_after(b.clone());
        l1.cursor_mut().insert_after(a.clone());
        l2.cursor_mut().insert_after(a.clone());
        l2.cursor_mut().insert_after(b.clone());
        l2.cursor_mut().insert_after(c.clone());
        l2.cursor_mut().insert_after(d.clone());
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);
    }

    #[test]
    fn test_fast_clear() {
        let mut l = SinglyLinkedList::new(ObjAdapter1::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_after(a.clone());
        l.cursor_mut().insert_after(b.clone());
        l.cursor_mut().insert_after(c.clone());

        l.fast_clear();
        assert!(l.is_empty());
        assert!(a.link1.is_linked());
        assert!(b.link1.is_linked());
        assert!(c.link1.is_linked());
        unsafe {
            a.link1.force_unlink();
            b.link1.force_unlink();
            c.link1.force_unlink();
        }
        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a, T> {
            link: RawLink,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link: RawLink} where T: 'a);
        unsafe impl<'a, T: 'a> crate::custom_links::Adapter for ObjAdapter<'a, T> {
            type Link = RawLink;
            type NodeRef = RawLinkRef;
            type Value = <Self as crate::Adapter>::Value;
            type Pointer = <Self as crate::Adapter>::Pointer;

            /// Gets a reference to an object from a reference to a link in that object.
            #[inline]
            unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value {
                <Self as crate::Adapter>::get_value(self, link)
            }

            /// Gets a reference to the link for the given object.
            #[inline]
            unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link {
                <Self as crate::Adapter>::get_link(self, value)
            }

            ///
            #[inline]
            unsafe fn node_from_pointer(&self, pointer: Self::Pointer) -> Self::NodeRef {
                self.node_from_link(self.get_link(Self::Pointer::into_raw(pointer)))
            }

            ///
            #[inline]
            unsafe fn node_into_pointer(&self, node: Self::NodeRef) -> Self::Pointer {
                Self::Pointer::from_raw(self.get_value(self.node_into_link(node)))
            }

            ///
            #[inline]
            unsafe fn node_from_link(&self, link: *const Self::Link) -> Self::NodeRef {
                RawLinkRef(link)
            }

            ///
            #[inline]
            unsafe fn node_into_link(&self, node: Self::NodeRef) -> *const Self::Link {
                node.0
            }
        }

        let v = 5;
        let a = Obj {
            link: RawLink::new(),
            value: &v,
        };
        let b = a.clone();
        let mut l = SinglyLinkedList::new(ObjAdapter::new());
        l.cursor_mut().insert_after(&a);
        l.cursor_mut().insert_after(&b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.front().get().unwrap().value, 5);
    }

    macro_rules! test_clone_pointer {
        ($ptr: ident, $ptr_import: path) => {
            use $ptr_import;

            #[derive(Clone)]
            struct Obj {
                link: RawLink,
                value: usize,
            }
            intrusive_adapter!(ObjAdapter = $ptr<Obj>: Obj { link: RawLink });
            unsafe impl crate::custom_links::Adapter for ObjAdapter {
                type Link = RawLink;
                type NodeRef = RawLinkRef;
                type Value = <Self as crate::Adapter>::Value;
                type Pointer = <Self as crate::Adapter>::Pointer;

                /// Gets a reference to an object from a reference to a link in that object.
                #[inline]
                unsafe fn get_value(&self, link: *const Self::Link) -> *const Self::Value {
                    <Self as crate::Adapter>::get_value(self, link)
                }

                /// Gets a reference to the link for the given object.
                #[inline]
                unsafe fn get_link(&self, value: *const Self::Value) -> *const Self::Link {
                    <Self as crate::Adapter>::get_link(self, value)
                }

                ///
                #[inline]
                unsafe fn node_from_pointer(&self, pointer: Self::Pointer) -> Self::NodeRef {
                    self.node_from_link(self.get_link(Self::Pointer::into_raw(pointer)))
                }

                ///
                #[inline]
                unsafe fn node_into_pointer(&self, node: Self::NodeRef) -> Self::Pointer {
                    Self::Pointer::from_raw(self.get_value(self.node_into_link(node)))
                }

                ///
                #[inline]
                unsafe fn node_from_link(&self, link: *const Self::Link) -> Self::NodeRef {
                    RawLinkRef(link)
                }

                ///
                #[inline]
                unsafe fn node_into_link(&self, node: Self::NodeRef) -> *const Self::Link {
                    node.0
                }
            }


            let a = $ptr::new(Obj {
                link: RawLink::new(),
                value: 5,
            });
            let mut l = SinglyLinkedList::new(ObjAdapter::new());
            l.cursor_mut().insert_after(a.clone());
            assert_eq!(2, $ptr::strong_count(&a));

            let pointer = l.front().clone_pointer().unwrap();
            assert_eq!(pointer.value, 5);
            assert_eq!(3, $ptr::strong_count(&a));

            l.clear();
            assert!(l.front().clone_pointer().is_none());
        }
    }

    #[test]
    fn test_clone_pointer_rc() {
        test_clone_pointer!(Rc, std::rc::Rc);
    }

    #[test]
    fn test_clone_pointer_arc() {
        test_clone_pointer!(Arc, std::sync::Arc);
    }
}
