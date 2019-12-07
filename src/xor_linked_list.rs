// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive xor doubly-linked list which uses less memory than a regular doubly linked list
//!
//! In exchange for less memory use, it is impossible to create a cursor from a pointer to
//! an element.

use crate::Adapter;
use crate::IntrusivePointer;
use core::cell::Cell;
use core::fmt;
use core::mem;
use core::ptr;

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a `XorLinkedList`.
pub struct Link {
    inner: Cell<XorPtr>,
}

impl Link {
    /// Creates a new `Link`.
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: Cell::new(XorPtr::unlinked()),
        }
    }

    /// Checks whether the `Link` is linked into a `XorLinkedList`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        self.inner.get().is_linked()
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
        self.inner.set(XorPtr::unlinked());
    }

    fn with_prev(&self, prev: *const Link) -> BidirPtr {
        self.inner.get().with_prev(prev)
    }

    fn with_next(&self, next: *const Link) -> BidirPtr {
        self.inner.get().with_next(next)
    }

    fn replace_ptr(&self, old: *const Link, new: *const Link) {
        let mut ptrs = self.with_prev(old);
        ptrs.prev = new;
        self.inner.set(ptrs.to_xor())
    }

    #[inline]
    unsafe fn link_between(&self, prev: *const Link, next: *const Link) {
        if let Some(prev) = prev.as_ref() {
            let mut prev_ptrs = prev.with_next(next);
            prev_ptrs.next = self;
            prev.inner.set(prev_ptrs.to_xor());
        }
        if let Some(next) = next.as_ref() {
            let mut next_ptrs = next.with_prev(prev);
            next_ptrs.prev = self;
            next.inner.set(next_ptrs.to_xor());
        }

        self.inner.set(XorPtr::new(prev, next));
    }

    fn set(&self, bidir: BidirPtr) {
        self.inner.set(bidir.to_xor())
    }

    fn next(&self, prev: *const Link) -> *const Link {
        self.with_prev(prev).next
    }

    fn prev(&self, next: *const Link) -> *const Link {
        self.with_next(next).prev
    }
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.pad(if self.is_linked() {
            "linked"
        } else {
            "unlinked"
        })
    }
}

// =============================================================================
// XorPtr
// =============================================================================

#[derive(Copy, Clone, PartialEq, Eq)]
struct XorPtr(usize);

impl XorPtr {
    #[inline]
    fn unlinked() -> XorPtr {
        XorPtr(1)
    }

    #[inline]
    fn is_linked(self) -> bool {
        self.0 != 1
    }

    #[inline]
    fn new(prev: *const Link, next: *const Link) -> XorPtr {
        XorPtr(prev as usize ^ next as usize)
    }

    #[inline]
    fn with_prev(self, prev: *const Link) -> BidirPtr {
        BidirPtr {
            prev,
            next: (self.0 ^ prev as usize) as *const Link,
        }
    }

    #[inline]
    fn with_next(self, next: *const Link) -> BidirPtr {
        BidirPtr {
            prev: (self.0 ^ next as usize) as *const Link,
            next,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct BidirPtr {
    prev: *const Link,
    next: *const Link,
}

impl BidirPtr {
    #[inline]
    fn to_xor(self) -> XorPtr {
        XorPtr::new(self.prev, self.next)
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `XorLinkedList`.
pub struct Cursor<'a, A: Adapter<Link = Link>> {
    current: *const Link,
    link: BidirPtr,
    list: &'a XorLinkedList<A>,
}

impl<'a, A: Adapter<Link = Link> + 'a> Clone for Cursor<'a, A> {
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            link: self.link,
            list: self.list,
        }
    }
}

impl<'a, A: Adapter<Link = Link>> Cursor<'a, A> {
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
    pub fn get(&self) -> Option<&'a A::Value> {
        if self.is_null() {
            None
        } else {
            Some(unsafe { &*self.list.adapter.get_value(self.current) })
        }
    }

    /// Moves the cursor to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `XorLinkedList`. If it is pointing to the last
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        let prev = self.current;
        self.current = self.link.next;
        self.link = unsafe {
            if let Some(current) = self.current.as_ref() {
                current.with_prev(prev)
            } else {
                BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                }
            }
        };
    }

    /// Moves the cursor to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let next = self.current;
        self.current = self.link.prev;
        self.link = unsafe {
            if let Some(current) = self.current.as_ref() {
                current.with_next(next)
            } else {
                BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                }
            }
        };
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
pub struct CursorMut<'a, A: Adapter<Link = Link>> {
    current: *const Link,
    link: BidirPtr,
    list: &'a mut XorLinkedList<A>,
}

impl<'a, A: Adapter<Link = Link>> CursorMut<'a, A> {
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
            Some(unsafe { &*self.list.adapter.get_value(self.current) })
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
            link: self.link,
            list: self.list,
        }
    }

    /// Moves the cursor to the next element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `XorLinkedList`. If it is pointing to the last
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        let prev = self.current;
        self.current = self.link.next;
        self.link = unsafe {
            if let Some(current) = self.current.as_ref() {
                current.with_prev(prev)
            } else {
                BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                }
            }
        };
    }

    /// Moves the cursor to the previous element of the `XorLinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `XorLinkedList`. If it is pointing to the first
    /// element of the `XorLinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        let next = self.current;
        self.current = self.link.prev;
        self.link = unsafe {
            if let Some(current) = self.current.as_ref() {
                current.with_next(next)
            } else {
                BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                }
            }
        };
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
    pub fn insert_after(&mut self, val: A::Pointer) {
        unsafe {
            let node = &*self.list.node_from_value(val);
            if self.is_null() {
                node.link_between(ptr::null(), self.list.head);
                self.list.head = node;
                if self.list.tail.is_null() {
                    self.list.tail = node;
                }
                self.link = BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                };
            } else {
                node.link_between(self.current, self.link.next);
                if self.link.next.is_null() {
                    // Current pointer was tail
                    self.list.tail = node;
                }
                self.link.next = node;
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
    pub fn insert_before(&mut self, val: A::Pointer) {
        unsafe {
            let node = &*self.list.node_from_value(val);
            if self.is_null() {
                node.link_between(self.list.tail, ptr::null());
                self.list.tail = node;
                if self.list.head.is_null() {
                    self.list.head = node;
                }
                self.link = BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                };
            } else {
                node.link_between(self.link.prev, self.current);
                if self.link.prev.is_null() {
                    // Current pointer was head
                    self.list.head = node;
                }
                self.link.prev = node;
            }
        }
    }

    /// Removes the current element from the `XorLinkedList`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `XorLinkedList`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<A::Pointer> {
        if self.is_null() {
            return None;
        }

        let BidirPtr { prev, next } = self.link;
        let current = self.current;
        unsafe {
            (*current).force_unlink();
            if let Some(prev) = prev.as_ref() {
                prev.replace_ptr(current, next);
            }

            if let Some(next) = next.as_ref() {
                next.replace_ptr(current, prev);
            }
        }
        if self.list.head == current {
            self.list.head = next;
        }
        if self.list.tail == current {
            self.list.tail = prev;
        }
        self.current = next;
        self.link = unsafe {
            if let Some(current) = self.current.as_ref() {
                current.with_prev(prev)
            } else {
                BidirPtr {
                    prev: self.list.tail,
                    next: self.list.head,
                }
            }
        };
        Some(unsafe { A::Pointer::from_raw(self.list.adapter.get_value(current)) })
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
    pub fn replace_with(&mut self, val: A::Pointer) -> Result<A::Pointer, A::Pointer> {
        unsafe {
            let current = match self.current.as_ref() {
                Some(current) => current,
                None => return Err(val),
            };

            let new = &*self.list.node_from_value(val);
            if self.list.head == current {
                self.list.head = new;
            }
            if self.list.tail == current {
                self.list.tail = new;
            }

            if let Some(prev) = self.link.prev.as_ref() {
                prev.replace_ptr(current, new);
            }
            if let Some(next) = self.link.next.as_ref() {
                next.replace_ptr(current, new);
            }
            current.force_unlink();
            new.set(self.link);

            let result = mem::replace(&mut self.current, new);
            Ok(A::Pointer::from_raw(self.list.adapter.get_value(result)))
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
                // Safe because list is non-empty
                let head = &*list.head;
                let tail = &*list.tail;
                list.fast_clear();

                if let Some(current) = self.current.as_ref() {
                    if let Some(next) = self.link.next.as_ref() {
                        next.replace_ptr(current, tail);
                        tail.replace_ptr(ptr::null(), next);
                    }
                    head.replace_ptr(ptr::null(), current);
                    self.link.next = head;
                    current.set(self.link)
                } else {
                    if let Some(our_head) = self.list.head.as_ref() {
                        tail.replace_ptr(ptr::null(), our_head);
                        our_head.replace_ptr(ptr::null(), tail);
                    }
                    self.list.head = head;
                    self.link.next = head;
                }
                if self.list.tail == self.current {
                    self.list.tail = tail;
                }
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
                // Safe because list is non-empty
                let head = &*list.head;
                let tail = &*list.tail;
                list.fast_clear();

                if let Some(current) = self.current.as_ref() {
                    if let Some(prev) = self.link.prev.as_ref() {
                        prev.replace_ptr(current, head);
                        head.replace_ptr(ptr::null(), prev);
                    }
                    tail.replace_ptr(ptr::null(), current);
                    self.link.prev = tail;
                    current.set(self.link)
                } else {
                    if let Some(our_tail) = self.list.tail.as_ref() {
                        head.replace_ptr(ptr::null(), our_tail);
                        our_tail.replace_ptr(ptr::null(), head);
                    }
                    self.list.head = head;
                    self.link.next = head;
                }
                if self.list.tail == self.current {
                    self.list.tail = tail;
                }
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
        unsafe {
            let current = match self.current.as_ref() {
                Some(current) => current,
                None => {
                    let adapter = self.list.adapter.clone();
                    return mem::replace(&mut self.list, XorLinkedList::new(adapter));
                }
            };
            let head = self.link.next;
            let tail = if let Some(head) = head.as_ref() {
                head.replace_ptr(self.current, ptr::null());
                self.link.next = ptr::null();
                current.set(self.link);
                self.list.tail
            } else {
                // Empty list after current
                ptr::null()
            };
            let list = XorLinkedList {
                head,
                tail,
                adapter: self.list.adapter.clone(),
            };
            self.list.tail = current;
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
        unsafe {
            let current = match self.current.as_ref() {
                Some(current) => current,
                None => {
                    let adapter = self.list.adapter.clone();
                    return mem::replace(&mut self.list, XorLinkedList::new(adapter));
                }
            };
            let tail = self.link.prev;
            let head = if let Some(tail) = tail.as_ref() {
                tail.replace_ptr(self.current, ptr::null());
                self.link.prev = ptr::null();
                current.set(self.link);
                self.list.head
            } else {
                // Empty list before current
                ptr::null()
            };
            let list = XorLinkedList {
                head,
                tail,
                adapter: self.list.adapter.clone(),
            };
            self.list.head = current;
            list
        }
    }
}

// =============================================================================
// XorLinkedList
// =============================================================================

/// Intrusive xor doubly-linked list which uses less memory than a regular doubly linked list
///
/// When this collection is dropped, all elements linked into it will be
/// converted back to owned pointers and dropped.
pub struct XorLinkedList<A: Adapter<Link = Link>> {
    head: *const Link,
    tail: *const Link,
    adapter: A,
}

impl<A: Adapter<Link = Link>> XorLinkedList<A> {
    /// Creates an empty `XorLinkedList`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adapter: A) -> XorLinkedList<A> {
        XorLinkedList {
            head: ptr::null(),
            tail: ptr::null(),
            adapter,
        }
    }

    /// Creates an empty `XorLinkedList`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adapter: A) -> XorLinkedList<A> {
        XorLinkedList {
            head: ptr::null(),
            tail: ptr::null(),
            adapter,
        }
    }

    /// Returns `true` if the `XorLinkedList` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Returns a null `Cursor` for this list.
    #[inline]
    pub fn cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: ptr::null(),
            link: BidirPtr {
                next: self.head,
                prev: self.tail,
            },
            list: self,
        }
    }

    /// Returns a null `CursorMut` for this list.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut {
            current: ptr::null(),
            link: BidirPtr {
                next: self.head,
                prev: self.tail,
            },
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
        ptr: *const A::Value,
        prev: *const A::Value,
    ) -> Cursor<'_, A> {
        debug_assert!(!ptr.is_null());

        let current = &*self.adapter.get_link(ptr);
        debug_assert!(current.is_linked());

        let prev = if prev.is_null() {
            ptr::null()
        } else {
            self.adapter.get_link(prev)
        };
        debug_assert!(prev.is_null() || (*prev).is_linked());

        let next = current.next(prev);
        debug_assert!(next.is_null() || (*next).is_linked());

        Cursor {
            current,
            link: BidirPtr { prev, next },
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
        ptr: *const A::Value,
        prev: *const A::Value,
    ) -> CursorMut<'_, A> {
        debug_assert!(!ptr.is_null());

        let current = &*self.adapter.get_link(ptr);
        debug_assert!(current.is_linked());

        let prev = if prev.is_null() {
            ptr::null()
        } else {
            self.adapter.get_link(prev)
        };
        debug_assert!(prev.is_null() || (*prev).is_linked());

        let next = current.next(prev);
        debug_assert!(next.is_null() || (*next).is_linked());

        CursorMut {
            current,
            link: BidirPtr { prev, next },
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
        ptr: *const A::Value,
        next: *const A::Value,
    ) -> Cursor<'_, A> {
        debug_assert!(!ptr.is_null());

        let current = &*self.adapter.get_link(ptr);
        debug_assert!(current.is_linked());

        let next = if next.is_null() {
            ptr::null()
        } else {
            self.adapter.get_link(next)
        };
        debug_assert!(next.is_null() || (*next).is_linked());

        let prev = current.prev(next);
        debug_assert!(prev.is_null() || (*prev).is_linked());

        Cursor {
            current,
            link: BidirPtr { prev, next },
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
        ptr: *const A::Value,
        next: *const A::Value,
    ) -> CursorMut<'_, A> {
        debug_assert!(!ptr.is_null());

        let current = &*self.adapter.get_link(ptr);
        debug_assert!(current.is_linked());

        let next = if next.is_null() {
            ptr::null()
        } else {
            self.adapter.get_link(next)
        };
        debug_assert!(next.is_null() || (*next).is_linked());

        let prev = current.next(next);
        debug_assert!(prev.is_null() || (*prev).is_linked());

        CursorMut {
            current,
            link: BidirPtr { prev, next },
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

    /// Returns a `Cursor` pointing to the last element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_prev();
        cursor
    }
    /// Returns a `CursorMut` pointing to the last element of the list. If the
    /// the list is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_prev();
        cursor
    }

    /// Gets an iterator over the objects in the `XorLinkedList`.
    #[inline]
    pub fn iter(&self) -> Iter<'_, A> {
        Iter {
            prev_head: ptr::null(),
            head: self.head,
            prev_tail: ptr::null(),
            tail: self.tail,
            adapter: &self.adapter,
        }
    }

    /// Removes all elements from the `XorLinkedList`.
    ///
    /// This will unlink all object currently in the list, which requires
    /// iterating through all elements in the `XorLinkedList`. Each element is
    /// converted back to an owned pointer and then dropped.
    #[inline]
    pub fn clear(&mut self) {
        let mut prev = ptr::null();
        let mut current = self.head;
        self.fast_clear();
        while !current.is_null() {
            unsafe {
                let next = (*current).next(prev);
                (*current).force_unlink();
                let _ = A::Pointer::from_raw(self.adapter.get_value(current));
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
        self.head = ptr::null();
        self.tail = ptr::null();
    }

    /// Takes all the elements out of the `XorLinkedList`, leaving it empty. The
    /// taken elements are returned as a new `XorLinkedList`.
    #[inline]
    pub fn take(&mut self) -> XorLinkedList<A>
    where
        A: Clone,
    {
        mem::replace(self, XorLinkedList::new(self.adapter.clone()))
    }

    #[inline]
    fn node_from_value(&self, val: A::Pointer) -> *const Link {
        unsafe {
            assert!(
                !(*self.adapter.get_link(&*val)).is_linked(),
                "attempted to insert an object that is already linked"
            );
            self.adapter.get_link(val.into_raw())
        }
    }

    /// Inserts a new element at the start of the `XorLinkedList`.
    #[inline]
    pub fn push_front(&mut self, val: A::Pointer) {
        self.cursor_mut().insert_after(val);
    }

    /// Inserts a new element at the end of the `XorLinkedList`.
    #[inline]
    pub fn push_back(&mut self, val: A::Pointer) {
        self.cursor_mut().insert_before(val);
    }

    /// Removes the first element of the `XorLinkedList`.
    ///
    /// This returns `None` if the `XorLinkedList` is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<A::Pointer> {
        self.front_mut().remove()
    }

    /// Removes the last element of the `XorLinkedList`.
    ///
    /// This returns `None` if the `XorLinkedList` is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<A::Pointer> {
        self.back_mut().remove()
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: Adapter<Link = Link> + Sync> Sync for XorLinkedList<A> where A::Value: Sync {}

// Allow sending to another thread if the ownership (represented by the A::Pointer owned
// pointer type) can be transferred to another thread.
unsafe impl<A: Adapter<Link = Link> + Send> Send for XorLinkedList<A> where A::Pointer: Send {}

// Drop all owned pointers if the collection is dropped
impl<A: Adapter<Link = Link>> Drop for XorLinkedList<A> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Adapter<Link = Link>> IntoIterator for XorLinkedList<A> {
    type Item = A::Pointer;
    type IntoIter = IntoIter<A>;

    #[inline]
    fn into_iter(self) -> IntoIter<A> {
        IntoIter { list: self }
    }
}

impl<'a, A: Adapter<Link = Link> + 'a> IntoIterator for &'a XorLinkedList<A> {
    type Item = &'a A::Value;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adapter<Link = Link> + Default> Default for XorLinkedList<A> {
    fn default() -> XorLinkedList<A> {
        XorLinkedList::new(A::default())
    }
}

impl<A: Adapter<Link = Link>> fmt::Debug for XorLinkedList<A>
where
    A::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// =============================================================================
// Iter
// =============================================================================

/// An iterator over references to the items of a `XorLinkedList`.
pub struct Iter<'a, A: Adapter<Link = Link>> {
    prev_head: *const Link,
    head: *const Link,
    prev_tail: *const Link,
    tail: *const Link,
    adapter: &'a A,
}
impl<'a, A: Adapter<Link = Link> + 'a> Iterator for Iter<'a, A> {
    type Item = &'a A::Value;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Value> {
        unsafe {
            let current_head = self.head.as_ref()?;
            if self.tail == current_head {
                self.head = ptr::null();
                self.tail = ptr::null();
            } else {
                self.head = current_head.next(self.prev_head);
                self.prev_head = current_head;
            }

            Some(&*self.adapter.get_value(current_head))
        }
    }
}
impl<'a, A: Adapter<Link = Link> + 'a> DoubleEndedIterator for Iter<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a A::Value> {
        unsafe {
            let current_tail = self.tail.as_ref()?;
            if self.head == current_tail {
                self.head = ptr::null();
                self.tail = ptr::null();
            } else {
                self.tail = current_tail.next(self.prev_tail);
                self.prev_tail = current_tail;
            }

            Some(&*self.adapter.get_value(current_tail))
        }
    }
}
impl<'a, A: Adapter<Link = Link> + 'a> Clone for Iter<'a, A> {
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            prev_head: self.prev_head,
            head: self.head,
            prev_tail: self.prev_tail,
            tail: self.tail,
            adapter: self.adapter,
        }
    }
}

// =============================================================================
// IntoIter
// =============================================================================

/// An iterator which consumes a `XorLinkedList`.
pub struct IntoIter<A: Adapter<Link = Link>> {
    list: XorLinkedList<A>,
}
impl<A: Adapter<Link = Link>> Iterator for IntoIter<A> {
    type Item = A::Pointer;

    #[inline]
    fn next(&mut self) -> Option<A::Pointer> {
        self.list.pop_front()
    }
}
impl<A: Adapter<Link = Link>> DoubleEndedIterator for IntoIter<A> {
    #[inline]
    fn next_back(&mut self) -> Option<A::Pointer> {
        self.list.pop_back()
    }
}

#[cfg(test)]
mod tests {
    use super::{Link, XorLinkedList};
    use crate::UnsafeRef;
    use std::boxed::Box;
    use std::cell::Cell;
    use std::fmt;
    use std::ptr;
    use std::vec::Vec;

    #[derive(Clone)]
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
    intrusive_adapter!(ObjAdapter1 = UnsafeRef<Obj>: Obj { link1: Link });
    intrusive_adapter!(ObjAdapter2 = UnsafeRef<Obj>: Obj { link2: Link });

    fn make_obj(value: u32) -> UnsafeRef<Obj> {
        UnsafeRef::from_box(Box::new(Obj {
            link1: Link::new(),
            link2: Link::default(),
            value: value,
        }))
    }

    #[test]
    fn test_link() {
        let a = make_obj(1);
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());

        let mut b = XorLinkedList::<ObjAdapter1>::default();
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
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);

        let mut l = XorLinkedList::new(ObjAdapter1::new());
        let mut cur = l.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
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

        {
            let mut cur2 = cur.as_cursor();
            assert_eq!(cur2.get().unwrap() as *const _, a.as_ref() as *const _);
            assert_eq!(cur2.peek_next().get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.peek_prev().get().unwrap().value, 2);
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            cur2.move_prev();
            assert_eq!(cur2.get().unwrap() as *const _, b.as_ref() as *const _);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            cur2.move_next();
            assert!(cur2.is_null());
            assert!(cur2.clone().get().is_none());
        }
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);

        cur.move_next();
        assert_eq!(
            cur.remove().unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        cur.insert_after(b.clone());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        cur.move_prev();
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(
            cur.remove().unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(!a.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(
            cur.replace_with(a.clone()).unwrap().as_ref() as *const _,
            c.as_ref() as *const _
        );
        assert!(a.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        cur.move_next();
        assert_eq!(
            cur.replace_with(c.clone()).unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert!(a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
    }

    #[test]
    fn test_push_pop() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);

        let mut l = XorLinkedList::new(ObjAdapter1::new());
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
        let mut l1 = XorLinkedList::new(ObjAdapter1::new());
        let mut l2 = XorLinkedList::new(ObjAdapter1::new());
        let mut l3 = XorLinkedList::new(ObjAdapter1::new());

        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
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
    fn test_iter() {
        let mut l = XorLinkedList::new(ObjAdapter1::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
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
        let mut l1 = XorLinkedList::new(ObjAdapter1::new());
        let mut l2 = XorLinkedList::new(ObjAdapter2::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
        l1.cursor_mut().insert_before(a.clone());
        l1.cursor_mut().insert_before(b.clone());
        l1.cursor_mut().insert_before(c.clone());
        l1.cursor_mut().insert_before(d.clone());
        l2.cursor_mut().insert_after(a.clone());
        l2.cursor_mut().insert_after(b.clone());
        l2.cursor_mut().insert_after(c.clone());
        l2.cursor_mut().insert_after(d.clone());
        assert_eq!(l1.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);
        assert_eq!(l2.iter().map(|x| x.value).collect::<Vec<_>>(), [4, 3, 2, 1]);
    }

    #[test]
    fn test_force_unlink() {
        let mut l = XorLinkedList::new(ObjAdapter1::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());

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
            link: Link,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link: Link} where T: 'a);

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
        intrusive_adapter!(ObjAdapter<'a> = Box<Obj<'a>>: Obj<'a> {link: Link});

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
}
