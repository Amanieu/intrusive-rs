// Copyright 2016 Amanieu d'Antras
// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive xor doubly-linked list which uses less memory than a regular doubly linked list.
//!
//! In exchange for less memory use, it is impossible to create a cursor from a pointer to
//! an element.

use core::cell::Cell;
use core::fmt;
use core::ptr::NonNull;
use core::sync::atomic::{AtomicUsize, Ordering};

use crate::link_ops::{self, DefaultLinkOps};
use crate::pointer_ops::PointerOps;
use crate::singly_linked_list::SinglyLinkedListOps;
use crate::Adapter;

// =============================================================================
// XorLinkedListOps
// =============================================================================

/// Link operations for `XorLinkedList`.
pub unsafe trait XorLinkedListOps: link_ops::LinkOps {
    /// Returns the "next" link pointer of `ptr`.
    ///
    /// # Safety
    /// `prev` must have been previously passed to the [`set`] method, or
    /// `prev` must be equal to the `new` argument previously passed to [`replace_next_or_prev`].
    ///
    /// An implementation of `next` must not panic.
    ///
    /// [`replace_next_or_prev`]: #tymethod.replace_next_or_prev
    /// [`set`]: #tymethod.set
    unsafe fn next(&self, ptr: Self::LinkPtr, prev: Option<Self::LinkPtr>)
        -> Option<Self::LinkPtr>;

    /// Returns the "prev" link pointer of `ptr`.
    ///
    /// # Safety
    /// `next` must have been previously passed to the [`set`] method, or
    /// `next` must be equal to the `new` argument previously passed to [`replace_next_or_prev`].
    ///
    /// An implementation of `prev` must not panic.
    ///
    /// [`replace_next_or_prev`]: #tymethod.replace_next_or_prev
    /// [`set`]: #tymethod.set
    unsafe fn prev(&self, ptr: Self::LinkPtr, next: Option<Self::LinkPtr>)
        -> Option<Self::LinkPtr>;

    /// Assigns the "prev" and "next" link pointers of `ptr`.
    ///
    /// # Safety
    /// An implementation of `set` must not panic.
    unsafe fn set(
        &mut self,
        ptr: Self::LinkPtr,
        prev: Option<Self::LinkPtr>,
        next: Option<Self::LinkPtr>,
    );

    /// Replaces the "next" or "prev" link pointer of `ptr`.
    ///
    /// # Safety
    /// `old` must be equal to either the `next` or `prev` argument previously passed to the [`set`] method, or
    /// `old` must be equal to the `new` argument previously passed to `replace_next_or_prev`.
    ///
    /// An implementation of `replace_next_or_prev` must not panic.
    ///
    /// [`set`]: #tymethod.set
    unsafe fn replace_next_or_prev(
        &mut self,
        ptr: Self::LinkPtr,
        old: Option<Self::LinkPtr>,
        new: Option<Self::LinkPtr>,
    );
}

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a
/// `XorLinkedList`.
#[repr(align(2))]
pub struct Link {
    packed: Cell<usize>,
}

// Use a special value to indicate an unlinked node
const UNLINKED_MARKER: usize = 1_usize;

impl Link {
    /// Creates a new `Link`.
    #[inline]
    pub const fn new() -> Link {
        Link {
            packed: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Checks whether the `Link` is linked into a `XorLinkedList`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        self.packed.get() != UNLINKED_MARKER
    }

    /// Forcibly unlinks an object from a `XorLinkedList`.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call this function while still linked into a
    /// `XorLinkedList`. The only situation where this function is useful is
    /// after calling `fast_clear` on a `XorLinkedList`, since this clears
    /// the collection without marking the nodes as unlinked.
    #[inline]
    pub unsafe fn force_unlink(&self) {
        self.packed.set(UNLINKED_MARKER);
    }
}

impl DefaultLinkOps for Link {
    type Ops = LinkOps;

    const NEW: Self::Ops = LinkOps;
}

// An object containing a link can be sent to another thread if it is unlinked.
unsafe impl Send for Link {}

// Provide an implementation of Clone which simply initializes the new link as
// unlinked. This allows structs containing a link to derive Clone.
impl Clone for Link {
    #[inline]
    fn clone(&self) -> Link {
        Link::new()
    }
}

// Same as above
impl Default for Link {
    #[inline]
    fn default() -> Link {
        Link::new()
    }
}

// Provide an implementation of Debug so that structs containing a link can
// still derive Debug.
impl fmt::Debug for Link {
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

// =============================================================================
// LinkOps
// =============================================================================

/// Default `LinkOps` implementation for `XorLinkedList`.
#[derive(Clone, Copy, Default)]
pub struct LinkOps;

unsafe impl link_ops::LinkOps for LinkOps {
    type LinkPtr = NonNull<Link>;

    #[inline]
    unsafe fn acquire_link(&mut self, ptr: Self::LinkPtr) -> bool {
        if ptr.as_ref().is_linked() {
            false
        } else {
            ptr.as_ref().packed.set(0);
            true
        }
    }

    #[inline]
    unsafe fn release_link(&mut self, ptr: Self::LinkPtr) {
        ptr.as_ref().packed.set(UNLINKED_MARKER);
    }
}

unsafe impl XorLinkedListOps for LinkOps {
    #[inline]
    unsafe fn next(
        &self,
        ptr: Self::LinkPtr,
        prev: Option<Self::LinkPtr>,
    ) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed.get() ^ prev.map(|x| x.as_ptr() as usize).unwrap_or(0);
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn prev(
        &self,
        ptr: Self::LinkPtr,
        next: Option<Self::LinkPtr>,
    ) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed.get() ^ next.map(|x| x.as_ptr() as usize).unwrap_or(0);
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn set(
        &mut self,
        ptr: Self::LinkPtr,
        prev: Option<Self::LinkPtr>,
        next: Option<Self::LinkPtr>,
    ) {
        let new_packed = prev.map(|x| x.as_ptr() as usize).unwrap_or(0)
            ^ next.map(|x| x.as_ptr() as usize).unwrap_or(0);
        ptr.as_ref().packed.set(new_packed);
    }

    #[inline]
    unsafe fn replace_next_or_prev(
        &mut self,
        ptr: Self::LinkPtr,
        old: Option<Self::LinkPtr>,
        new: Option<Self::LinkPtr>,
    ) {
        let new_packed = ptr.as_ref().packed.get()
            ^ old.map(|x| x.as_ptr() as usize).unwrap_or(0)
            ^ new.map(|x| x.as_ptr() as usize).unwrap_or(0);

        ptr.as_ref().packed.set(new_packed);
    }
}

unsafe impl SinglyLinkedListOps for LinkOps {
    #[inline]
    unsafe fn next(&self, ptr: Self::LinkPtr) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed.get();
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn set_next(&mut self, ptr: Self::LinkPtr, next: Option<Self::LinkPtr>) {
        ptr.as_ref()
            .packed
            .set(next.map(|x| x.as_ptr() as usize).unwrap_or(0));
    }
}

// =============================================================================
// AtomicLink
// =============================================================================

/// Intrusive link that allows an object to be inserted into a
/// `XorLinkedList`. This link allows the structure to be shared between threads.
#[repr(align(2))]
pub struct AtomicLink {
    packed: AtomicUsize,
}

impl AtomicLink {
    /// Creates a new `Link`.
    #[inline]
    pub const fn new() -> AtomicLink {
        AtomicLink {
            packed: AtomicUsize::new(UNLINKED_MARKER),
        }
    }

    /// Checks whether the `Link` is linked into a `XorLinkedList`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        self.packed.load(core::sync::atomic::Ordering::Relaxed) != UNLINKED_MARKER
    }

    /// Forcibly unlinks an object from a `XorLinkedList`.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call this function while still linked into a
    /// `XorLinkedList`. The only situation where this function is useful is
    /// after calling `fast_clear` on a `XorLinkedList`, since this clears
    /// the collection without marking the nodes as unlinked.
    #[inline]
    pub unsafe fn force_unlink(&self) {
        self.packed.store(UNLINKED_MARKER, Ordering::Release);
    }

    #[inline]
    fn packed(&self) -> usize {
        self.packed.load(Ordering::Relaxed)
    }

    #[inline]
    fn set_packed(&self, packed: usize) {
        self.packed.store(packed, Ordering::Relaxed);
    }
}

impl DefaultLinkOps for AtomicLink {
    type Ops = AtomicLinkOps;

    const NEW: Self::Ops = AtomicLinkOps;
}

// An object containing a link can be sent to another thread since `acquire_link` is atomic.
unsafe impl Send for AtomicLink {}

// An object containing a link can be shared between threads since `acquire_link` is atomic.
unsafe impl Sync for AtomicLink {}

impl Clone for AtomicLink {
    #[inline]
    fn clone(&self) -> AtomicLink {
        AtomicLink::new()
    }
}

impl Default for AtomicLink {
    #[inline]
    fn default() -> AtomicLink {
        AtomicLink::new()
    }
}

// Provide an implementation of Debug so that structs containing a link can
// still derive Debug.
impl fmt::Debug for AtomicLink {
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

// =============================================================================
// AtomicLinkOps
// =============================================================================

/// Default `AtomicLinkOps` implementation for `LinkedList`.
#[derive(Clone, Copy, Default)]
pub struct AtomicLinkOps;

const LINKED_DEFAULT_VALUE: usize = 0;

unsafe impl link_ops::LinkOps for AtomicLinkOps {
    type LinkPtr = NonNull<AtomicLink>;

    #[inline]
    unsafe fn acquire_link(&mut self, ptr: Self::LinkPtr) -> bool {
        ptr.as_ref()
            .packed
            .compare_exchange(
                UNLINKED_MARKER,
                LINKED_DEFAULT_VALUE,
                Ordering::Acquire,
                Ordering::Relaxed,
            )
            .is_ok()
    }

    #[inline]
    unsafe fn release_link(&mut self, ptr: Self::LinkPtr) {
        ptr.as_ref()
            .packed
            .store(UNLINKED_MARKER, Ordering::Release)
    }
}

unsafe impl XorLinkedListOps for AtomicLinkOps {
    #[inline]
    unsafe fn next(
        &self,
        ptr: Self::LinkPtr,
        prev: Option<Self::LinkPtr>,
    ) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed() ^ prev.map(|x| x.as_ptr() as usize).unwrap_or(0);
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn prev(
        &self,
        ptr: Self::LinkPtr,
        next: Option<Self::LinkPtr>,
    ) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed() ^ next.map(|x| x.as_ptr() as usize).unwrap_or(0);
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn set(
        &mut self,
        ptr: Self::LinkPtr,
        prev: Option<Self::LinkPtr>,
        next: Option<Self::LinkPtr>,
    ) {
        let new_packed = prev.map(|x| x.as_ptr() as usize).unwrap_or(0)
            ^ next.map(|x| x.as_ptr() as usize).unwrap_or(0);
        ptr.as_ref().set_packed(new_packed);
    }

    #[inline]
    unsafe fn replace_next_or_prev(
        &mut self,
        ptr: Self::LinkPtr,
        old: Option<Self::LinkPtr>,
        new: Option<Self::LinkPtr>,
    ) {
        let new_packed = ptr.as_ref().packed()
            ^ old.map(|x| x.as_ptr() as usize).unwrap_or(0)
            ^ new.map(|x| x.as_ptr() as usize).unwrap_or(0);

        ptr.as_ref().set_packed(new_packed);
    }
}

unsafe impl SinglyLinkedListOps for AtomicLinkOps {
    #[inline]
    unsafe fn next(&self, ptr: Self::LinkPtr) -> Option<Self::LinkPtr> {
        let raw = ptr.as_ref().packed();
        NonNull::new(raw as *mut _)
    }

    #[inline]
    unsafe fn set_next(&mut self, ptr: Self::LinkPtr, next: Option<Self::LinkPtr>) {
        ptr.as_ref()
            .set_packed(next.map(|x| x.as_ptr() as usize).unwrap_or(0));
    }
}

#[inline]
unsafe fn link_between<T: XorLinkedListOps>(
    link_ops: &mut T,
    ptr: T::LinkPtr,
    prev: Option<T::LinkPtr>,
    next: Option<T::LinkPtr>,
) {
    if let Some(prev) = prev {
        let prev_of_prev = link_ops.prev(prev, next);
        link_ops.set(prev, prev_of_prev, Some(ptr));
    }
    if let Some(next) = next {
        let next_of_next = link_ops.next(next, prev);
        link_ops.set(next, Some(ptr), next_of_next);
    }
    link_ops.set(ptr, prev, next);
}

/// Splices the non-empty range from `start` to `end` between `prev` and `next`.
///
/// This only rewires the XOR links. Callers must update list endpoints and
/// cursor state separately.
#[inline]
unsafe fn splice_between<T: XorLinkedListOps>(
    link_ops: &mut T,
    start: T::LinkPtr,
    end: T::LinkPtr,
    prev: Option<T::LinkPtr>,
    next: Option<T::LinkPtr>,
) {
    if let Some(prev) = prev {
        link_ops.replace_next_or_prev(prev, next, Some(start));
    }
    if let Some(next) = next {
        link_ops.replace_next_or_prev(next, prev, Some(end));
    }
    link_ops.replace_next_or_prev(start, None, prev);
    link_ops.replace_next_or_prev(end, None, next);
}

// =============================================================================
// Cursor, CursorMut, CursorOwning
// =============================================================================

/// A cursor which provides read-only access to a `XorLinkedList`.
pub struct Cursor<'a, A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    current: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    prev: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    next: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    list: &'a XorLinkedList<A>,
}

impl<'a, A: Adapter> Clone for Cursor<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            prev: self.prev,
            next: self.next,
            list: self.list,
        }
    }
}

impl<'a, A: Adapter> Cursor<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.current.is_none()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        Some(unsafe { &*self.list.adapter.get_value(self.current?) })
    }

    /// Returns a raw pointer to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get_ptr(&self) -> Option<NonNull<<A::PointerOps as PointerOps>::Value>> {
        unsafe {
            let ptr = self.list.adapter.get_value(self.current?);
            Some(NonNull::new_unchecked(ptr.cast_mut()))
        }
    }

    /// Clones and returns the pointer that points to the element that the
    /// cursor is referencing.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn clone_pointer(&self) -> Option<<A::PointerOps as PointerOps>::Pointer>
    where
        <A::PointerOps as PointerOps>::Pointer: Clone,
    {
        let raw_pointer = unsafe { self.list.adapter.get_value(self.current?) };
        Some(unsafe {
            crate::pointer_ops::clone_pointer_from_raw(self.list.adapter.pointer_ops(), raw_pointer)
        })
    }

    /// Moves the cursor to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `XorLinkedList`. If it is pointing to the
    /// last element of the `XorLinkedList` then this will move it to the
    /// null object.
    #[inline]
    pub fn move_next(&mut self) {
        let prev = self.current;
        self.current = self.next;
        unsafe {
            if let Some(current) = self.current {
                self.prev = prev;
                self.next = self.list.adapter.link_ops().next(current, prev);
            } else {
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Moves the cursor to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let next = self.current;
        self.current = self.prev;
        unsafe {
            if let Some(current) = self.current {
                self.prev = self.list.adapter.link_ops().prev(current, next);
                self.next = next;
            } else {
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Returns a cursor pointing to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `XorLinkedList`. If it is pointing to the last
    /// element of the `XorLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
        let mut next = self.clone();
        next.move_next();
        next
    }

    /// Returns a cursor pointing to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_prev(&self) -> Cursor<'_, A> {
        let mut prev = self.clone();
        prev.move_prev();
        prev
    }
}

/// A cursor which provides mutable access to a `XorLinkedList`.
pub struct CursorMut<'a, A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    current: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    prev: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    next: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    list: &'a mut XorLinkedList<A>,
}

impl<'a, A: Adapter> CursorMut<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.current.is_none()
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&<A::PointerOps as PointerOps>::Value> {
        Some(unsafe { &*self.list.adapter.get_value(self.current?) })
    }

    /// Returns a raw pointer to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns `None` if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get_ptr(&self) -> Option<NonNull<<A::PointerOps as PointerOps>::Value>> {
        unsafe {
            let ptr = self.list.adapter.get_value(self.current?);
            Some(NonNull::new_unchecked(ptr.cast_mut()))
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
            prev: self.prev,
            next: self.next,
            list: self.list,
        }
    }

    /// Moves the cursor to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `XorLinkedList`. If it is pointing to the
    /// last element of the `XorLinkedList` then this will move it to the
    /// null object.
    #[inline]
    pub fn move_next(&mut self) {
        let prev = self.current;
        self.current = self.next;
        unsafe {
            if let Some(current) = self.current {
                self.prev = prev;
                self.next = self.list.adapter.link_ops().next(current, prev);
            } else {
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Moves the cursor to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let next = self.current;
        self.current = self.prev;
        unsafe {
            if let Some(current) = self.current {
                self.prev = self.list.adapter.link_ops().prev(current, next);
                self.next = next;
            } else {
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Returns a cursor pointing to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `XorLinkedList`. If it is pointing to the last
    /// element of the `XorLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
        let mut next = self.as_cursor();
        next.move_next();
        next
    }

    /// Returns a cursor pointing to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will return a null cursor.
    #[inline]
    pub fn peek_prev(&self) -> Cursor<'_, A> {
        let mut prev = self.as_cursor();
        prev.move_prev();
        prev
    }

    /// Removes the current element from the `XorLinkedList`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `XorLinkedList`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        use link_ops::LinkOps;

        unsafe {
            let current = self.current?;
            let result = current;

            self.list.adapter.link_ops_mut().release_link(current);
            if let Some(prev) = self.prev {
                self.list.adapter.link_ops_mut().replace_next_or_prev(
                    prev,
                    Some(current),
                    self.next,
                );
            }
            if let Some(next) = self.next {
                self.list.adapter.link_ops_mut().replace_next_or_prev(
                    next,
                    Some(current),
                    self.prev,
                );
            }
            if self.list.head == Some(current) {
                self.list.head = self.next;
            }
            if self.list.tail == Some(current) {
                self.list.tail = self.prev;
            }
            self.current = self.next;
            if let Some(current) = self.current {
                self.next = self.list.adapter.link_ops().next(current, self.prev);
            } else {
                self.prev = self.list.tail;
                self.next = self.list.head;
            }

            Some(
                self.list
                    .adapter
                    .pointer_ops()
                    .from_raw(self.list.adapter.get_value(result)),
            )
        }
    }

    /// Removes the current element from the `XorLinkedList` and inserts another
    /// object in its place.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// modified to point to the newly added element.
    ///
    /// If the cursor is currently pointing to the null object then an error is
    /// returned containing the given `val` parameter.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn replace_with(
        &mut self,
        val: <A::PointerOps as PointerOps>::Pointer,
    ) -> Result<<A::PointerOps as PointerOps>::Pointer, <A::PointerOps as PointerOps>::Pointer>
    {
        use link_ops::LinkOps;

        unsafe {
            if let Some(current) = self.current {
                let new = self.list.node_from_value(val);
                let result = current;

                if self.list.head == Some(current) {
                    self.list.head = Some(new);
                }
                if self.list.tail == Some(current) {
                    self.list.tail = Some(new);
                }

                if let Some(prev) = self.prev {
                    self.list.adapter.link_ops_mut().replace_next_or_prev(
                        prev,
                        Some(current),
                        Some(new),
                    );
                }
                if let Some(next) = self.next {
                    self.list.adapter.link_ops_mut().replace_next_or_prev(
                        next,
                        Some(current),
                        Some(new),
                    );
                }

                self.list
                    .adapter
                    .link_ops_mut()
                    .set(new, self.prev, self.next);
                self.list.adapter.link_ops_mut().release_link(result);
                self.current = Some(new);

                Ok(self
                    .list
                    .adapter
                    .pointer_ops()
                    .from_raw(self.list.adapter.get_value(result)))
            } else {
                Err(val)
            }
        }
    }

    /// Inserts a new element into the `XorLinkedList` after the current one.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the front of the `XorLinkedList`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_after(&mut self, val: <A::PointerOps as PointerOps>::Pointer) {
        unsafe {
            let new = self.list.node_from_value(val);
            if let Some(current) = self.current {
                link_between(
                    self.list.adapter.link_ops_mut(),
                    new,
                    Some(current),
                    self.next,
                );
                if self.next.is_none() {
                    // Current pointer was tail
                    self.list.tail = Some(new);
                }
                self.next = Some(new);
            } else {
                link_between(self.list.adapter.link_ops_mut(), new, None, self.list.head);
                self.list.head = Some(new);
                if self.list.tail.is_none() {
                    self.list.tail = Some(new);
                }
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Inserts a new element into the `XorLinkedList` before the current one.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the end of the `XorLinkedList`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_before(&mut self, val: <A::PointerOps as PointerOps>::Pointer) {
        unsafe {
            let new = self.list.node_from_value(val);
            if let Some(current) = self.current {
                link_between(
                    self.list.adapter.link_ops_mut(),
                    new,
                    self.prev,
                    Some(current),
                );
                if self.prev.is_none() {
                    // Current pointer was tail
                    self.list.head = Some(new);
                }
                self.prev = Some(new);
            } else {
                link_between(self.list.adapter.link_ops_mut(), new, self.list.tail, None);
                self.list.tail = Some(new);
                if self.list.head.is_none() {
                    self.list.head = Some(new);
                }
                self.prev = self.list.tail;
                self.next = self.list.head;
            }
        }
    }

    /// Inserts the elements from the given `XorLinkedList` after the current one.
    ///
    /// If the cursor is pointing at the null object then the new elements are
    /// inserted at the start of the `XorLinkedList`.
    #[inline]
    pub fn splice_after(&mut self, mut list: XorLinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                let head = list.head.unwrap_unchecked();
                let tail = list.tail.unwrap_unchecked();

                let link_ops = self.list.adapter.link_ops_mut();

                splice_between(link_ops, head, tail, self.current, self.next);
                if self.current.is_some() {
                    self.next = list.head;
                } else {
                    self.list.head = list.head;
                }
                if self.list.tail == self.current {
                    self.list.tail = list.tail;
                }
                if self.current.is_none() {
                    self.prev = self.list.tail;
                    self.next = self.list.head;
                }
                list.head = None;
                list.tail = None;
            }
        }
    }

    /// Moves all element from the given `XorLinkedList` before the current one.
    ///
    /// If the cursor is pointing at the null object then the new elements are
    /// inserted at the end of the `XorLinkedList`.
    #[inline]
    pub fn splice_before(&mut self, mut list: XorLinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                let head = list.head.unwrap_unchecked();
                let tail = list.tail.unwrap_unchecked();

                let link_ops = self.list.adapter.link_ops_mut();

                splice_between(link_ops, head, tail, self.prev, self.current);
                if self.current.is_some() {
                    self.prev = list.tail;
                } else {
                    self.list.tail = list.tail;
                }
                if self.list.head == self.current {
                    self.list.head = list.head;
                }
                if self.current.is_none() {
                    self.prev = self.list.tail;
                    self.next = self.list.head;
                }
                list.head = None;
                list.tail = None;
            }
        }
    }

    /// Splits the list into two after the current element. This will return a
    /// new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the null object then the entire contents
    /// of the `XorLinkedList` are moved.
    #[inline]
    pub fn split_after(&mut self) -> XorLinkedList<A>
    where
        A: Clone,
    {
        if let Some(current) = self.current {
            unsafe {
                let mut list = XorLinkedList {
                    head: self.next,
                    tail: self.list.tail,
                    adapter: self.list.adapter.clone(),
                };
                if let Some(head) = list.head {
                    self.list.adapter.link_ops_mut().replace_next_or_prev(
                        head,
                        Some(current),
                        None,
                    );
                    self.next = None;
                } else {
                    list.tail = None;
                }
                self.list
                    .adapter
                    .link_ops_mut()
                    .set(current, self.prev, None);
                self.list.tail = self.current;
                list
            }
        } else {
            let list = XorLinkedList {
                head: self.list.head,
                tail: self.list.tail,
                adapter: self.list.adapter.clone(),
            };
            self.list.head = None;
            self.list.tail = None;
            list
        }
    }

    /// Splits the list into two before the current element. This will return a
    /// new list consisting of everything before the cursor, with the original
    /// list retaining everything after.
    ///
    /// If the cursor is pointing at the null object then the entire contents
    /// of the `XorLinkedList` are moved.
    #[inline]
    pub fn split_before(&mut self) -> XorLinkedList<A>
    where
        A: Clone,
    {
        if let Some(current) = self.current {
            unsafe {
                let mut list = XorLinkedList {
                    head: self.list.head,
                    tail: self.prev,
                    adapter: self.list.adapter.clone(),
                };
                if let Some(tail) = list.tail {
                    self.list.adapter.link_ops_mut().replace_next_or_prev(
                        tail,
                        Some(current),
                        None,
                    );
                    self.prev = None;
                } else {
                    list.head = None;
                }
                self.list
                    .adapter
                    .link_ops_mut()
                    .set(current, None, self.next);
                self.list.head = self.current;
                list
            }
        } else {
            let list = XorLinkedList {
                head: self.list.head,
                tail: self.list.tail,
                adapter: self.list.adapter.clone(),
            };
            self.list.head = None;
            self.list.tail = None;
            list
        }
    }

    /// Consumes `CursorMut` and returns a reference to the object that
    /// the cursor is currently pointing to. Unlike [get](Self::get),
    /// the returned reference's lifetime is tied to `XorLinkedList`'s lifetime.
    ///
    /// This returns None if the cursor is currently pointing to the null object.
    #[inline]
    pub fn into_ref(self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        Some(unsafe { &*self.list.adapter.get_value(self.current?) })
    }
}

/// A cursor with ownership over the `XorLinkedList` it points into.
pub struct CursorOwning<A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    current: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    prev: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    next: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    list: XorLinkedList<A>,
}

impl<A: Adapter> CursorOwning<A>
where
    A::LinkOps: XorLinkedListOps,
{
    /// Consumes self and returns the inner `XorLinkedList`.
    #[inline]
    pub fn into_inner(self) -> XorLinkedList<A> {
        self.list
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorOwning`, which means it cannot outlive the `CursorOwning` and that the
    /// `CursorOwning` is frozen for the lifetime of the `Cursor`.
    ///
    /// Mutations of the returned cursor are _not_ reflected in the original.
    #[inline]
    pub fn as_cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: self.current,
            prev: self.prev,
            next: self.next,
            list: &self.list,
        }
    }

    /// Perform action with mutable reference to the cursor.
    ///
    /// All mutations of the cursor are reflected in the original.
    #[inline]
    pub fn with_cursor_mut<T>(&mut self, f: impl FnOnce(&mut CursorMut<'_, A>) -> T) -> T {
        struct WritebackOnDrop<'a, 'b, A: Adapter>
        where
            A::LinkOps: XorLinkedListOps,
        {
            current: &'a mut Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
            prev: &'a mut Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
            next: &'a mut Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
            cursor: CursorMut<'b, A>,
        }

        impl<'a, 'b, A: Adapter> Drop for WritebackOnDrop<'a, 'b, A>
        where
            A::LinkOps: XorLinkedListOps,
        {
            fn drop(&mut self) {
                *self.current = self.cursor.current;
                *self.prev = self.cursor.prev;
                *self.next = self.cursor.next;
            }
        }

        let current = self.current;
        let prev = self.prev;
        let next = self.next;
        let mut guard = WritebackOnDrop {
            current: &mut self.current,
            prev: &mut self.prev,
            next: &mut self.next,
            cursor: CursorMut {
                current,
                prev,
                next,
                list: &mut self.list,
            },
        };

        f(&mut guard.cursor)
    }
}
unsafe impl<A: Adapter> Send for CursorOwning<A>
where
    XorLinkedList<A>: Send,
    A::LinkOps: XorLinkedListOps,
{
}

// =============================================================================
// XorLinkedList
// =============================================================================

/// Intrusive xor doubly-linked list which uses less memory than a regular doubly linked list
///
/// In exchange for less memory use, it is impossible to create a cursor from a pointer to
/// an element.
///
/// When this collection is dropped, all elements linked into it will be
/// converted back to owned pointers and dropped.
pub struct XorLinkedList<A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    head: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    tail: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    adapter: A,
}

impl<A: Adapter> XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn node_from_value(
        &mut self,
        val: <A::PointerOps as PointerOps>::Pointer,
    ) -> <A::LinkOps as link_ops::LinkOps>::LinkPtr {
        use link_ops::LinkOps;

        unsafe {
            let raw = self.adapter.pointer_ops().into_raw(val);
            let link = self.adapter.get_link(raw);

            if !self.adapter.link_ops_mut().acquire_link(link) {
                // convert the node back into a pointer
                self.adapter.pointer_ops().from_raw(raw);

                panic!("attempted to insert an object that is already linked");
            }

            link
        }
    }

    /// Creates an empty `XorLinkedList`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adapter: A) -> XorLinkedList<A> {
        XorLinkedList {
            head: None,
            tail: None,
            adapter,
        }
    }

    /// Creates an empty `XorLinkedList`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adapter: A) -> XorLinkedList<A> {
        XorLinkedList {
            head: None,
            tail: None,
            adapter,
        }
    }

    /// Returns `true` if the `XorLinkedList` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns a null `Cursor` for this list.
    #[inline]
    pub fn cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: None,
            prev: self.tail,
            next: self.head,
            list: self,
        }
    }

    /// Returns a null `CursorMut` for this list.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut {
            current: None,
            prev: self.tail,
            next: self.head,
            list: self,
        }
    }

    /// Returns a null `CursorOwning` for this list.
    #[inline]
    pub fn cursor_owning(self) -> CursorOwning<A> {
        CursorOwning {
            current: None,
            prev: self.tail,
            next: self.head,
            list: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element and a pointer to the previous element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `prev` must be a pointer to an object that is the previous object in this list (null for the head)
    #[inline]
    pub unsafe fn cursor_from_ptr_and_prev(
        &self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        prev: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'_, A> {
        let current = self.adapter.get_link(ptr);
        let prev = if !prev.is_null() {
            Some(self.adapter.get_link(prev))
        } else {
            None
        };
        let next = self.adapter.link_ops().next(current, prev);

        Cursor {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element and a pointer to the previous element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `prev` must be a pointer to an object that is the previous object in this list (null for the head)
    #[inline]
    pub unsafe fn cursor_mut_from_ptr_and_prev(
        &mut self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        prev: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorMut<'_, A> {
        let current = self.adapter.get_link(ptr);
        let prev = if !prev.is_null() {
            Some(self.adapter.get_link(prev))
        } else {
            None
        };
        let next = self.adapter.link_ops().next(current, prev);

        CursorMut {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Creates a `CursorOwning` from a pointer to an element and a pointer to the previous element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `prev` must be a pointer to an object that is the previous object in this list (null for the head)
    #[inline]
    pub unsafe fn cursor_owning_from_ptr_and_prev(
        self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        prev: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorOwning<A> {
        let current = self.adapter.get_link(ptr);
        let prev = if !prev.is_null() {
            Some(self.adapter.get_link(prev))
        } else {
            None
        };
        let next = self.adapter.link_ops().next(current, prev);

        CursorOwning {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element and a pointer to the next element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `next` must be a pointer to an object that is the next object in this list (null for the tail)
    #[inline]
    pub unsafe fn cursor_from_ptr_and_next(
        &self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        next: *const <A::PointerOps as PointerOps>::Value,
    ) -> Cursor<'_, A> {
        let current = self.adapter.get_link(ptr);
        let next = if !next.is_null() {
            Some(self.adapter.get_link(next))
        } else {
            None
        };
        let prev = self.adapter.link_ops().prev(current, next);

        Cursor {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element and a pointer to the next element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `next` must be a pointer to an object that is the next object in this list (null for the tail)
    #[inline]
    pub unsafe fn cursor_mut_from_ptr_and_next(
        &mut self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        next: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorMut<'_, A> {
        let current = self.adapter.get_link(ptr);
        let next = if !next.is_null() {
            Some(self.adapter.get_link(next))
        } else {
            None
        };
        let prev = self.adapter.link_ops().prev(current, next);

        CursorMut {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Creates a `CursorOwning` from a pointer to an element and a pointer to the next element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    /// `next` must be a pointer to an object that is the next object in this list (null for the tail)
    #[inline]
    pub unsafe fn cursor_owning_from_ptr_and_next(
        self,
        ptr: *const <A::PointerOps as PointerOps>::Value,
        next: *const <A::PointerOps as PointerOps>::Value,
    ) -> CursorOwning<A> {
        let current = self.adapter.get_link(ptr);
        let next = if !next.is_null() {
            Some(self.adapter.get_link(next))
        } else {
            None
        };
        let prev = self.adapter.link_ops().prev(current, next);

        CursorOwning {
            current: Some(current),
            prev,
            next,
            list: self,
        }
    }

    /// Returns a `Cursor` pointing to the first element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn front(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorMut` pointing to the first element of the list. If the
    /// the list is empty then a null cursor is returned.
    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorOwning` pointing to the first element of the list. If the
    /// the list is empty then a null cursor is returned.
    #[inline]
    pub fn front_owning(self) -> CursorOwning<A> {
        let mut cursor = self.cursor_owning();
        cursor.with_cursor_mut(|c| c.move_next());
        cursor
    }

    /// Returns a `Cursor` pointing to the last element of the list. If the list
    /// is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_prev();
        cursor
    }

    /// Returns a `CursorMut` pointing to the last element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_prev();
        cursor
    }

    /// Returns a `CursorOwning` pointing to the last element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn back_owning(self) -> CursorOwning<A> {
        let mut cursor = self.cursor_owning();
        cursor.with_cursor_mut(|c| c.move_prev());
        cursor
    }

    /// Gets an iterator over the objects in the `XorLinkedList`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, A> {
        Iter {
            prev_head: None,
            head: self.head,
            tail: self.tail,
            next_tail: None,
            list: self,
        }
    }

    /// Removes all elements from the `XorLinkedList`.
    ///
    /// This will unlink all object currently in the list, which requires
    /// iterating through all elements in the `XorLinkedList`. Each element is
    /// converted back to an owned pointer and then dropped.
    #[inline]
    pub fn clear(&mut self) {
        use link_ops::LinkOps;

        let mut current = self.head;
        let mut prev = None;
        self.head = None;
        self.tail = None;
        while let Some(x) = current {
            unsafe {
                let next = self.adapter.link_ops().next(x, prev);
                self.adapter.link_ops_mut().release_link(x);
                self.adapter
                    .pointer_ops()
                    .from_raw(self.adapter.get_value(x));
                prev = current;
                current = next;
            }
        }
    }

    /// Empties the `XorLinkedList` without unlinking or freeing objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `XorLinkedList` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `force_unlink` function on them.
    #[inline]
    pub fn fast_clear(&mut self) {
        self.head = None;
        self.tail = None;
    }

    /// Takes all the elements out of the `XorLinkedList`, leaving it empty.
    /// The taken elements are returned as a new `XorLinkedList`.
    #[inline]
    pub fn take(&mut self) -> XorLinkedList<A>
    where
        A: Clone,
    {
        let list = XorLinkedList {
            head: self.head,
            tail: self.tail,
            adapter: self.adapter.clone(),
        };
        self.head = None;
        self.tail = None;
        list
    }

    /// Inserts a new element at the start of the `XorLinkedList`.
    #[inline]
    pub fn push_front(&mut self, val: <A::PointerOps as PointerOps>::Pointer) {
        self.cursor_mut().insert_after(val);
    }

    /// Inserts a new element at the end of the `XorLinkedList`.
    #[inline]
    pub fn push_back(&mut self, val: <A::PointerOps as PointerOps>::Pointer) {
        self.cursor_mut().insert_before(val);
    }

    /// Removes the first element of the `XorLinkedList`.
    ///
    /// This returns `None` if the `XorLinkedList` is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        self.front_mut().remove()
    }

    /// Removes the last element of the `XorLinkedList`.
    ///
    /// This returns `None` if the `XorLinkedList` is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        self.back_mut().remove()
    }

    /// Reverses the list in-place.
    ///
    /// Due to the structure of `XorLinkedList`, this operation is O(1).
    #[inline]
    pub fn reverse(&mut self) {
        core::mem::swap(&mut self.head, &mut self.tail);
    }
}

// Allow read-only access to values from multiple threads
unsafe impl<A: Adapter + Sync> Sync for XorLinkedList<A>
where
    <A::PointerOps as PointerOps>::Value: Sync,
    <A::PointerOps as PointerOps>::Pointer: Sync,
    A::LinkOps: XorLinkedListOps,
{
}

// Allow sending to another thread if the ownership (represented by the <A::PointerOps as PointerOps>::Pointer owned
// pointer type) can be transferred to another thread.
unsafe impl<A: Adapter + Send> Send for XorLinkedList<A>
where
    <A::PointerOps as PointerOps>::Pointer: Send,
    A::LinkOps: XorLinkedListOps,
{
}

// Drop all owned pointers if the collection is dropped
impl<A: Adapter> Drop for XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Adapter> IntoIterator for XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
{
    type Item = <A::PointerOps as PointerOps>::Pointer;
    type IntoIter = IntoIter<A>;

    #[inline]
    fn into_iter(self) -> IntoIter<A> {
        IntoIter { list: self }
    }
}

impl<'a, A: Adapter + 'a> IntoIterator for &'a XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
{
    type Item = &'a <A::PointerOps as PointerOps>::Value;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adapter + Default> Default for XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
{
    fn default() -> XorLinkedList<A> {
        XorLinkedList::new(A::default())
    }
}

impl<A: Adapter> fmt::Debug for XorLinkedList<A>
where
    A::LinkOps: XorLinkedListOps,
    <A::PointerOps as PointerOps>::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// =============================================================================
// Iter
// =============================================================================

/// An iterator over references to the items of a `XorLinkedList`.
pub struct Iter<'a, A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    prev_head: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    head: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    tail: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    next_tail: Option<<A::LinkOps as link_ops::LinkOps>::LinkPtr>,
    list: &'a XorLinkedList<A>,
}
impl<'a, A: Adapter + 'a> Iterator for Iter<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    type Item = &'a <A::PointerOps as PointerOps>::Value;

    #[inline]
    fn next(&mut self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        let head = self.head?;

        if Some(head) == self.tail {
            self.prev_head = None;
            self.head = None;
            self.next_tail = None;
            self.tail = None;
        } else {
            let next = unsafe { self.list.adapter.link_ops().next(head, self.prev_head) };
            self.prev_head = self.head;
            self.head = next;
        }
        Some(unsafe { &*self.list.adapter.get_value(head) })
    }
}
impl<'a, A: Adapter + 'a> DoubleEndedIterator for Iter<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a <A::PointerOps as PointerOps>::Value> {
        let tail = self.tail?;

        if Some(tail) == self.head {
            self.prev_head = None;
            self.head = None;
            self.next_tail = None;
            self.tail = None;
        } else {
            let new_tail = unsafe { self.list.adapter.link_ops().prev(tail, self.next_tail) };
            self.next_tail = self.tail;
            self.tail = new_tail;
        }
        Some(unsafe { &*self.list.adapter.get_value(tail) })
    }
}
impl<'a, A: Adapter + 'a> Clone for Iter<'a, A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            prev_head: self.prev_head,
            head: self.head,
            tail: self.tail,
            next_tail: self.next_tail,
            list: self.list,
        }
    }
}

// =============================================================================
// IntoIter
// =============================================================================

/// An iterator which consumes a `XorLinkedList`.
pub struct IntoIter<A: Adapter>
where
    A::LinkOps: XorLinkedListOps,
{
    list: XorLinkedList<A>,
}
impl<A: Adapter> Iterator for IntoIter<A>
where
    A::LinkOps: XorLinkedListOps,
{
    type Item = <A::PointerOps as PointerOps>::Pointer;

    #[inline]
    fn next(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        self.list.pop_front()
    }
}
impl<A: Adapter> DoubleEndedIterator for IntoIter<A>
where
    A::LinkOps: XorLinkedListOps,
{
    #[inline]
    fn next_back(&mut self) -> Option<<A::PointerOps as PointerOps>::Pointer> {
        self.list.pop_back()
    }
}
// Allow sending to another thread if the ownership of the container can be
// transferred to another thread.
unsafe impl<A: Adapter> Send for IntoIter<A>
where
    XorLinkedList<A>: Send,
    A::LinkOps: XorLinkedListOps,
{
}
// Allow read-only access to values from multiple threads since IntoIter is
// essentially a wrapper around the container so similar rules apply.
unsafe impl<A: Adapter> Sync for IntoIter<A>
where
    XorLinkedList<A>: Sync,
    A::LinkOps: XorLinkedListOps,
{
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use crate::UnsafeRef;

    use super::{CursorOwning, Link, XorLinkedList};
    use core::cell::Cell;
    use core::ptr;
    use core::ptr::NonNull;
    use std::boxed::Box;
    use std::fmt;
    use std::format;
    use std::rc::Rc;
    use std::vec::Vec;

    struct Obj {
        link1: Link,
        link2: Link,
        value: u32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adapter!(RcObjAdapter1 = Rc<Obj>: Obj { link1 => Link });
    intrusive_adapter!(RcObjAdapter2 = Rc<Obj>: Obj { link2 => Link });
    intrusive_adapter!(UnsafeRefObjAdapter1 = UnsafeRef<Obj>: Obj { link1 => Link });

    fn make_rc_obj(value: u32) -> Rc<Obj> {
        Rc::new(make_obj(value))
    }

    fn make_obj(value: u32) -> Obj {
        Obj {
            link1: Link::new(),
            link2: Link::default(),
            value,
        }
    }

    #[test]
    fn test_link() {
        let a = make_rc_obj(1);
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());

        let mut b = XorLinkedList::<RcObjAdapter1>::default();
        assert!(b.is_empty());

        b.cursor_mut().insert_after(a.clone());
        assert!(!b.is_empty());
        assert!(a.link1.is_linked());
        assert!(!a.link2.is_linked());
        assert_eq!(format!("{:?}", a.link1), "linked");
        assert_eq!(format!("{:?}", a.link2), "unlinked");

        assert_eq!(
            b.front_mut().remove().unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(b.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());
    }

    #[test]
    fn test_cursor() {
        let a = make_rc_obj(1);
        let b = make_rc_obj(2);
        let c = make_rc_obj(3);

        let mut l = XorLinkedList::new(RcObjAdapter1::new());
        let mut cur = l.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
        assert!(cur.get_ptr().is_none());
        assert!(cur.remove().is_none());
        assert_eq!(
            cur.replace_with(a.clone()).unwrap_err().as_ref() as *const _,
            a.as_ref() as *const _
        );

        cur.insert_before(a.clone());
        cur.insert_before(c.clone());
        cur.move_prev();
        cur.insert_before(b.clone());
        assert!(cur.peek_next().is_null());
        cur.move_next();
        assert!(cur.is_null());

        cur.move_next();
        assert!(cur.peek_prev().is_null());
        assert!(!cur.is_null());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(a.as_ref()));

        {
            let mut cur2 = cur.as_cursor();
            assert_eq!(cur2.get().unwrap() as *const _, a.as_ref() as *const _);
            assert_eq!(cur2.get_ptr().unwrap(), NonNull::from(a.as_ref()));
            assert_eq!(cur2.peek_next().get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.peek_prev().get().unwrap().value, 2);
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            assert_eq!(cur2.get_ptr().unwrap(), NonNull::from(c.as_ref()));
            cur2.move_prev();
            assert_eq!(cur2.get().unwrap() as *const _, b.as_ref() as *const _);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            cur2.move_next();
            assert!(cur2.is_null());
            assert!(cur2.clone().get().is_none());
            assert!(cur2.get_ptr().is_none());
        }
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(a.as_ref()));

        cur.move_next();
        assert_eq!(
            cur.remove().unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(c.as_ref()));
        cur.insert_after(b.clone());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        cur.move_prev();
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(a.as_ref()));
        assert_eq!(
            cur.remove().unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(!a.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(c.as_ref()));
        assert_eq!(
            cur.replace_with(a.clone()).unwrap().as_ref() as *const _,
            c.as_ref() as *const _
        );
        assert!(a.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(a.as_ref()));
        cur.move_next();
        assert_eq!(
            cur.replace_with(c.clone()).unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert!(a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(cur.get_ptr().unwrap(), NonNull::from(c.as_ref()));
    }

    #[test]
    fn test_cursor_owning() {
        struct Container {
            cur: CursorOwning<RcObjAdapter1>,
        }

        let mut l = XorLinkedList::new(RcObjAdapter1::new());
        l.push_back(make_rc_obj(1));
        l.push_back(make_rc_obj(2));
        l.push_back(make_rc_obj(3));
        l.push_back(make_rc_obj(4));
        let mut con = Container {
            cur: l.cursor_owning(),
        };
        assert!(con.cur.as_cursor().is_null());

        con.cur = con.cur.into_inner().front_owning();
        assert_eq!(con.cur.as_cursor().get().unwrap().value, 1);

        con.cur.with_cursor_mut(|c| c.move_next());
        assert_eq!(con.cur.as_cursor().get().unwrap().value, 2);

        con.cur = con.cur.into_inner().back_owning();
        assert_eq!(con.cur.as_cursor().get().unwrap().value, 4);
    }

    #[test]
    fn test_push_pop() {
        let a = make_rc_obj(1);
        let b = make_rc_obj(2);
        let c = make_rc_obj(3);

        let mut l = XorLinkedList::new(RcObjAdapter1::new());
        l.push_front(a);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1]);
        l.push_front(b);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [2, 1]);
        l.push_back(c);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [2, 1, 3]);
        assert_eq!(l.pop_front().unwrap().value, 2);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3]);
        assert_eq!(l.pop_back().unwrap().value, 3);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1]);
        assert_eq!(l.pop_front().unwrap().value, 1);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert!(l.pop_front().is_none());
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert!(l.pop_back().is_none());
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), []);
    }

    #[test]
    fn test_split_splice() {
        let mut l1 = XorLinkedList::new(RcObjAdapter1::new());
        let mut l2 = XorLinkedList::new(RcObjAdapter1::new());
        let mut l3 = XorLinkedList::new(RcObjAdapter1::new());

        let a = make_rc_obj(1);
        let b = make_rc_obj(2);
        let c = make_rc_obj(3);
        let d = make_rc_obj(4);
        l1.cursor_mut().insert_before(a);
        l1.cursor_mut().insert_before(b);
        l1.cursor_mut().insert_before(c);
        l1.cursor_mut().insert_before(d);
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
            let mut cur = l2.back_mut();
            l3 = cur.split_before();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [3]);
        {
            let mut cur = l1.front_mut();
            cur.splice_after(l2.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), [3]);
        {
            let mut cur = l1.front_mut();
            cur.move_next();
            cur.splice_before(l3.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l2.cursor_mut();
            cur.splice_after(l1.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.cursor_mut();
            cur.splice_before(l2.take());
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.cursor_mut();
            l2 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l2.cursor_mut();
            l1 = cur.split_before();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.front_mut();
            l2 = cur.split_before();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        {
            let mut cur = l1.back_mut();
            l2 = cur.split_after();
        }
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 3, 4, 2]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), []);
        assert_eq!(l3.iter().map(|x| x.value).collect::<Vec<_>>(), []);
    }

    #[test]
    fn splice_boundary_cases() {
        let values =
            |list: &XorLinkedList<RcObjAdapter1>| list.iter().map(|x| x.value).collect::<Vec<_>>();

        let mut list = XorLinkedList::new(RcObjAdapter1::new());
        for value in [1, 2, 3] {
            list.push_back(make_rc_obj(value));
        }
        let mut inserted = XorLinkedList::new(RcObjAdapter1::new());
        inserted.push_back(make_rc_obj(4));
        inserted.push_back(make_rc_obj(5));
        list.back_mut().splice_before(inserted);
        assert_eq!(values(&list), [1, 2, 4, 5, 3]);
        assert_eq!(list.back().get().unwrap().value, 3);
        assert_eq!(
            list.iter().rev().map(|x| x.value).collect::<Vec<_>>(),
            [3, 5, 4, 2, 1]
        );

        let mut inserted = XorLinkedList::new(RcObjAdapter1::new());
        inserted.push_back(make_rc_obj(6));
        list.front_mut().splice_before(inserted);
        assert_eq!(values(&list), [6, 1, 2, 4, 5, 3]);
        assert_eq!(list.front().get().unwrap().value, 6);

        let mut inserted = XorLinkedList::new(RcObjAdapter1::new());
        inserted.push_back(make_rc_obj(7));
        list.cursor_mut().splice_before(inserted);
        assert_eq!(values(&list), [6, 1, 2, 4, 5, 3, 7]);
        assert_eq!(list.back().get().unwrap().value, 7);

        let mut inserted = XorLinkedList::new(RcObjAdapter1::new());
        inserted.push_back(make_rc_obj(8));
        list.cursor_mut().splice_after(inserted);
        assert_eq!(values(&list), [8, 6, 1, 2, 4, 5, 3, 7]);
        assert_eq!(list.front().get().unwrap().value, 8);
    }

    #[test]
    fn test_iter() {
        let mut l = XorLinkedList::new(RcObjAdapter1::new());
        let a = make_rc_obj(1);
        let b = make_rc_obj(2);
        let c = make_rc_obj(3);
        let d = make_rc_obj(4);
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());
        l.cursor_mut().insert_before(d.clone());

        assert_eq!(l.front().get().unwrap().value, 1);
        assert_eq!(l.back().get().unwrap().value, 4);
        unsafe {
            let mut cursor = l.cursor_from_ptr_and_prev(b.as_ref(), a.as_ref());
            assert_eq!(cursor.get().unwrap().value, 2);
            cursor.move_next();
            assert_eq!(cursor.get().unwrap().value, 3);

            assert_eq!(
                l.cursor_mut_from_ptr_and_next(c.as_ref(), d.as_ref())
                    .get()
                    .unwrap()
                    .value,
                3
            );

            assert_eq!(
                l.cursor_mut_from_ptr_and_prev(a.as_ref(), ptr::null())
                    .get()
                    .unwrap()
                    .value,
                1
            );
            assert_eq!(
                l.cursor_mut_from_ptr_and_next(d.as_ref(), ptr::null())
                    .get()
                    .unwrap()
                    .value,
                4
            );

            let mut cursor = l.cursor_from_ptr_and_next(d.as_ref(), ptr::null());
            assert_eq!(cursor.get().unwrap().value, 4);
            cursor.move_prev();
            assert_eq!(cursor.get().unwrap().value, 3);
            cursor.move_next();
            assert_eq!(cursor.get().unwrap().value, 4);
            cursor.move_next();
            assert!(cursor.is_null());
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
        assert_eq!(
            l.iter().rev().map(|x| x.value).collect::<Vec<_>>(),
            [4, 3, 2, 1]
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

        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());
        l.cursor_mut().insert_before(d.clone());
        l.clear();
        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert!(!d.link1.is_linked());

        v.clear();
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());
        l.cursor_mut().insert_before(d.clone());
        for x in l.into_iter().rev() {
            v.push(x.value);
        }
        assert_eq!(v, [4, 3, 2, 1]);
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert!(!d.link1.is_linked());
    }

    #[test]
    fn test_multi_list() {
        let mut l1 = XorLinkedList::new(RcObjAdapter1::new());
        let mut l2 = XorLinkedList::new(RcObjAdapter2::new());
        let a = make_rc_obj(1);
        let b = make_rc_obj(2);
        let c = make_rc_obj(3);
        let d = make_rc_obj(4);
        l1.cursor_mut().insert_before(a.clone());
        l1.cursor_mut().insert_before(b.clone());
        l1.cursor_mut().insert_before(c.clone());
        l1.cursor_mut().insert_before(d.clone());
        l2.cursor_mut().insert_after(a);
        l2.cursor_mut().insert_after(b);
        l2.cursor_mut().insert_after(c);
        l2.cursor_mut().insert_after(d);
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);
    }

    #[test]
    fn test_fast_clear_force_unlink() {
        let mut l = XorLinkedList::new(UnsafeRefObjAdapter1::new());
        let a = UnsafeRef::from_box(Box::new(make_obj(1)));
        let b = UnsafeRef::from_box(Box::new(make_obj(2)));
        let c = UnsafeRef::from_box(Box::new(make_obj(3)));
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());

        l.fast_clear();
        assert!(l.is_empty());

        unsafe {
            assert!(a.link1.is_linked());
            assert!(b.link1.is_linked());
            assert!(c.link1.is_linked());

            a.link1.force_unlink();
            b.link1.force_unlink();
            c.link1.force_unlink();

            assert!(l.is_empty());

            assert!(!a.link1.is_linked());
            assert!(!b.link1.is_linked());
            assert!(!c.link1.is_linked());
        }

        unsafe {
            UnsafeRef::into_box(a);
            UnsafeRef::into_box(b);
            UnsafeRef::into_box(c);
        }
    }

    #[test]
    fn test_reverse() {
        let mut l = XorLinkedList::new(RcObjAdapter1::new());

        l.push_back(make_rc_obj(1));
        l.push_back(make_rc_obj(2));
        l.push_back(make_rc_obj(3));
        l.push_back(make_rc_obj(4));
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);

        l.reverse();
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);

        l.push_back(make_rc_obj(5));
        l.push_back(make_rc_obj(6));
        assert_eq!(
            l.iter().map(|x| x.value).collect::<Vec<_>>(),
            [4, 3, 2, 1, 5, 6]
        );

        l.reverse();
        assert_eq!(
            l.iter().map(|x| x.value).collect::<Vec<_>>(),
            [6, 5, 1, 2, 3, 4]
        );
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a, T> {
            link: Link,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link => Link} where T: 'a);

        let v = 5;
        let a = Obj {
            link: Link::new(),
            value: &v,
        };
        let b = a.clone();
        let mut l = XorLinkedList::new(ObjAdapter::new());
        l.cursor_mut().insert_before(&a);
        l.cursor_mut().insert_before(&b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
    }

    #[test]
    fn test_drop() {
        #[derive(Clone)]
        struct Obj<'a> {
            link: Link,
            value: &'a Cell<u32>,
        }
        impl<'a> Drop for Obj<'a> {
            fn drop(&mut self) {
                let val = self.value.get();
                self.value.set(val + 1);
            }
        }
        intrusive_adapter!(ObjAdapter<'a> = Box<Obj<'a>>: Obj<'a> {link => Link});

        let v = Cell::new(0);
        let obj = Obj {
            link: Link::new(),
            value: &v,
        };
        let mut l = XorLinkedList::new(ObjAdapter::new());
        l.cursor_mut().insert_before(Box::new(obj.clone()));
        l.cursor_mut().insert_before(Box::new(obj.clone()));
        assert_eq!(l.front().get().unwrap().value.get(), 0);
        assert_eq!(l.back().get().unwrap().value.get(), 0);
        assert_eq!(v.get(), 0);

        l.pop_front();
        assert_eq!(v.get(), 1);

        l.front_mut().insert_after(Box::new(obj.clone()));
        assert_eq!(v.get(), 1);

        drop(l);
        assert_eq!(v.get(), 3);
    }

    macro_rules! test_clone_pointer {
        ($ptr: ident, $ptr_import: path) => {
            use $ptr_import;

            #[derive(Clone)]
            struct Obj {
                link: Link,
                value: usize,
            }
            intrusive_adapter!(ObjAdapter = $ptr<Obj>: Obj { link => Link });

            let a = $ptr::new(Obj {
                link: Link::new(),
                value: 5,
            });
            let mut l = XorLinkedList::new(ObjAdapter::new());
            l.cursor_mut().insert_before(a.clone());
            assert_eq!(2, $ptr::strong_count(&a));

            let pointer = l.front().clone_pointer().unwrap();
            assert_eq!(pointer.value, 5);
            assert_eq!(3, $ptr::strong_count(&a));

            l.front_mut().remove();
            assert!(l.front().clone_pointer().is_none());
        };
    }

    #[test]
    fn test_clone_pointer_rc() {
        test_clone_pointer!(Rc, std::rc::Rc);
    }

    #[test]
    fn test_clone_pointer_arc() {
        test_clone_pointer!(Arc, std::sync::Arc);
    }

    #[test]
    fn cursor_owning_panic_leaves_dangling_current() {
        use std::panic::{catch_unwind, AssertUnwindSafe};

        struct Obj {
            link: Link,
            _value: u32,
        }
        intrusive_adapter!(ObjAdapter = Box<Obj>: Obj { link => Link });

        let mut list = XorLinkedList::new(ObjAdapter::new());
        list.push_back(Box::new(Obj {
            link: Link::new(),
            _value: 1,
        }));

        let mut cursor = list.front_owning();
        let panic = catch_unwind(AssertUnwindSafe(|| {
            cursor.with_cursor_mut(|cursor| {
                drop(cursor.remove().unwrap());
                panic!("leave CursorOwning state stale");
            });
        }));

        assert!(panic.is_err());
        // Regression test: without panic-safe cursor state writeback,
        // `CursorOwning.current` still points at the removed and dropped node
        // here, and `as_cursor().get()` dereferences freed storage under Miri.
        assert!(cursor.as_cursor().is_null());
    }

    #[cfg(miri)]
    #[test]
    fn splice_before_head_corrupts_head_link() {
        struct Obj {
            link: Link,
            value: u32,
        }
        intrusive_adapter!(ObjAdapter = Box<Obj>: Obj { link => Link });

        let mut list = XorLinkedList::new(ObjAdapter::new());
        list.push_back(Box::new(Obj {
            link: Link::new(),
            value: 1,
        }));
        list.push_back(Box::new(Obj {
            link: Link::new(),
            value: 2,
        }));

        let mut inserted = XorLinkedList::new(ObjAdapter::new());
        inserted.push_back(Box::new(Obj {
            link: Link::new(),
            value: 3,
        }));
        inserted.push_back(Box::new(Obj {
            link: Link::new(),
            value: 4,
        }));

        {
            let mut cursor = list.front_mut();
            // UB: splicing before the current head should move `list.head` to
            // the spliced list's head. The implementation leaves `head`
            // pointing at the old node even though that node now has a
            // previous neighbor, so traversal reconstructs and dereferences a
            // bogus XOR pointer.
            cursor.splice_before(inserted);
        }

        let _ = list.iter().map(|x| x.value).collect::<Vec<_>>();
    }

    #[cfg(miri)]
    #[test]
    fn splice_before_null_corrupts_tail_link() {
        struct Obj {
            link: Link,
            value: u32,
        }
        intrusive_adapter!(ObjAdapter = Box<Obj>: Obj { link => Link });

        let mut list = XorLinkedList::new(ObjAdapter::new());
        list.push_back(Box::new(Obj {
            link: Link::new(),
            value: 1,
        }));
        list.push_back(Box::new(Obj {
            link: Link::new(),
            value: 2,
        }));

        let mut inserted = XorLinkedList::new(ObjAdapter::new());
        inserted.push_back(Box::new(Obj {
            link: Link::new(),
            value: 3,
        }));
        inserted.push_back(Box::new(Obj {
            link: Link::new(),
            value: 4,
        }));

        {
            let mut cursor = list.cursor_mut();
            // UB: splicing before the null cursor means appending to the
            // non-empty list. The implementation overwrites `head` instead of
            // updating `tail`, making the new head encode a non-null previous
            // pointer. Iteration then materializes and dereferences an invalid
            // pointer.
            cursor.splice_before(inserted);
        }

        let _ = list.iter().map(|x| x.value).collect::<Vec<_>>();
    }

    #[cfg(miri)]
    #[test]
    fn atomic_link_is_linked_races_with_list_mutation() {
        use std::sync::atomic::{AtomicBool, Ordering};
        use std::sync::Arc;
        use std::thread;

        struct Obj {
            link: super::AtomicLink,
            value: usize,
        }
        intrusive_adapter!(ObjAdapter = Arc<Obj>: Obj { link => super::AtomicLink });

        let obj = Arc::new(Obj {
            link: super::AtomicLink::new(),
            value: 1,
        });
        let mut list = XorLinkedList::new(ObjAdapter::new());
        list.push_back(obj.clone());

        let mutation_done = AtomicBool::new(false);
        thread::scope(|scope| {
            let obj = &obj;
            let reader_done = &mutation_done;
            scope.spawn(move || {
                while !reader_done.load(Ordering::Relaxed) {
                    thread::yield_now();
                }
                // UB: `AtomicLink::is_linked` performs an atomic load, but
                // `AtomicLinkOps` updates the packed link word through a
                // transmuted `Cell` during safe list mutation.
                let _ = obj.link.is_linked();
            });

            let list = &mut list;
            let writer_done = &mutation_done;
            scope.spawn(move || {
                let value = list.pop_front().unwrap();
                assert_eq!(value.value, 1);
                list.push_back(value);
                writer_done.store(true, Ordering::Relaxed);
            });
        });
    }
}
