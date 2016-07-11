// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive singly-linked list.

use Adaptor;
use intrusive_ref::IntrusiveRef;
use core::ptr;
use core::fmt;
use core::mem;
use core::cell::Cell;

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a
/// `SinglyLinkedList`.
pub struct Link {
    next: Cell<NodePtr>,
}

impl Link {
    /// Creates a new `Link`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> Link {
        Link { next: Cell::new(UNLINKED_MARKER) }
    }

    /// Creates a new `Link`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> Link {
        Link { next: Cell::new(UNLINKED_MARKER) }
    }

    /// Checks whether the `Link` is linked into a `SinglyLinkedList`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        unsafe {
            // The link might be concurrently modified by another thread,
            // so make sure we read the value only once. Normally we would just
            // make the links atomic but this significantly hurts optimization.
            ptr::read_volatile(&self.next).get() != UNLINKED_MARKER
        }
    }

    /// Unlinks the object from the `SinglyLinkedList` without invalidating the
    /// rest of the list.
    ///
    /// # Safety
    ///
    /// The `SinglyLinkedList` is left in an invalid state after this function
    /// is called. To continue using the `SinglyLinkedList`, it must be manually
    /// reset by calling the `fast_clear` function on it. Any other operations
    /// on the affected list will result in undefined behavior.
    #[inline]
    pub unsafe fn unsafe_unlink(&self) {
        self.next.set(UNLINKED_MARKER);
    }
}

// An object containing a link can be sent to another thread if it is unlinked.
unsafe impl Send for Link {}

// The cells are only accessed indirectly through `SinglyLinkedList` and are not
// accessible directly, so a `&Link` is always safe to access from multiple
// threads. The check in is_linked uses a volatile read and is therefore
// thread-safe.
unsafe impl Sync for Link {}

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
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
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
// NodePtr
// =============================================================================

#[derive(Copy, Clone, PartialEq, Eq)]
struct NodePtr(*const Link);

// Use a special value to indicate an unlinked node
const UNLINKED_MARKER: NodePtr = NodePtr(1 as *const _);

impl NodePtr {
    #[inline]
    fn null() -> NodePtr {
        NodePtr(ptr::null())
    }

    #[inline]
    fn is_null(self) -> bool {
        self.0.is_null()
    }

    #[inline]
    unsafe fn is_linked(self) -> bool {
        self.next() != UNLINKED_MARKER
    }

    #[inline]
    unsafe fn next(self) -> NodePtr {
        (*self.0).next.get()
    }

    #[inline]
    unsafe fn set_next(self, next: NodePtr) {
        (*self.0).next.set(next);
    }

    #[inline]
    unsafe fn unlink(self) {
        self.set_next(UNLINKED_MARKER);
    }

    #[inline]
    unsafe fn link_between(self, prev: NodePtr, next: NodePtr) {
        if !prev.is_null() {
            prev.set_next(self);
        }
        self.set_next(next);
    }

    #[inline]
    unsafe fn link_after(self, prev: NodePtr) {
        self.link_between(prev, prev.next());
    }

    #[inline]
    unsafe fn replace_with(self, prev: NodePtr, new: NodePtr) {
        if !prev.is_null() {
            prev.set_next(new);
        }
        new.set_next(self.next());
        self.unlink();
    }

    #[inline]
    unsafe fn remove(self, prev: NodePtr) {
        if !prev.is_null() {
            prev.set_next(self.next());
        }
        self.unlink();
    }

    #[inline]
    unsafe fn splice(start: NodePtr, end: NodePtr, prev: NodePtr, next: NodePtr) {
        end.set_next(next);
        if !prev.is_null() {
            prev.set_next(start);
        }
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `SinglyLinkedList`.
pub struct Cursor<'a, A: Adaptor<Link> + 'a> {
    current: NodePtr,
    list: &'a SinglyLinkedList<A>,
}

impl<'a, A: Adaptor<Link> + 'a> Clone for Cursor<'a, A> {
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            list: self.list,
        }
    }
}

impl<'a, A: Adaptor<Link>> Cursor<'a, A> {
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
    pub fn get(&self) -> Option<&'a A::Container> {
        if self.is_null() {
            None
        } else {
            Some(unsafe { &*self.list.adaptor.get_container(self.current.0) })
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
            self.current = unsafe { self.current.next() };
        }
    }
}

/// A cursor which provides mutable access to a `SinglyLinkedList`.
pub struct CursorMut<'a, A: Adaptor<Link> + 'a> {
    current: NodePtr,
    list: &'a mut SinglyLinkedList<A>,
}

impl<'a, A: Adaptor<Link>> CursorMut<'a, A> {
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
    pub fn get(&self) -> Option<&'a A::Container> {
        if self.is_null() {
            None
        } else {
            Some(unsafe { &*self.list.adaptor.get_container(self.current.0) })
        }
    }

    /// Returns a read-only cursor pointing to the current element.
    ///
    /// The lifetime of the returned `Cursor` is bound to that of the
    /// `CursorMut`, which means it cannot outlive the `CursorMut` and that the
    /// `CursorMut` is frozen for the lifetime of the `Cursor`.
    #[inline]
    pub fn as_cursor(&self) -> Cursor<A> {
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
            self.current = unsafe { self.current.next() };
        }
    }

    /// Removes the next element from the `SinglyLinkedList`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// not moved.
    ///
    /// If the cursor is currently pointing to the last element of the
    /// `SinglyLinkedList` then no element is removed and `None` is returned.
    #[inline]
    pub fn remove_next(&mut self) -> Option<IntrusiveRef<A::Container>> {
        unsafe {
            let next = if self.is_null() {
                self.list.head
            } else {
                self.current.next()
            };
            if next.is_null() {
                return None;
            }
            if self.is_null() {
                self.list.head = next.next();
            }
            next.remove(self.current);
            Some(IntrusiveRef::from_raw(self.list.adaptor.get_container(next.0)))
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
    pub fn replace_next_with(&mut self,
                             val: IntrusiveRef<A::Container>)
                             -> Result<IntrusiveRef<A::Container>, IntrusiveRef<A::Container>> {
        unsafe {
            let next = if self.is_null() {
                self.list.head
            } else {
                self.current.next()
            };
            if next.is_null() {
                return Err(val);
            }
            let new = NodePtr(self.list.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.is_null() {
                self.list.head = new;
            }
            next.replace_with(self.current, new);
            Ok(IntrusiveRef::from_raw(self.list.adaptor.get_container(next.0)))
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
    pub fn insert_after(&mut self, val: IntrusiveRef<A::Container>) {
        unsafe {
            let new = NodePtr(self.list.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.is_null() {
                new.link_between(NodePtr::null(), self.list.head);
                self.list.head = new;
            } else {
                new.link_after(self.current);
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
    pub fn splice_after(&mut self, list: SinglyLinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                let next = if self.is_null() {
                    self.list.head
                } else {
                    self.current.next()
                };
                if next.is_null() {
                    if self.is_null() {
                        self.list.head = list.head;
                    } else {
                        self.current.set_next(list.head);
                    }
                } else {
                    let mut tail = list.head;
                    while !tail.next().is_null() {
                        tail = tail.next();
                    }
                    NodePtr::splice(list.head, tail, self.current, next);
                    if self.is_null() {
                        self.list.head = list.head;
                    }
                }
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
        where A: Clone
    {
        if self.is_null() {
            let list = SinglyLinkedList {
                head: self.list.head,
                adaptor: self.list.adaptor.clone(),
            };
            self.list.head = NodePtr::null();
            list
        } else {
            unsafe {
                let list = SinglyLinkedList {
                    head: self.current.next(),
                    adaptor: self.list.adaptor.clone(),
                };
                self.current.set_next(NodePtr::null());
                list
            }
        }
    }
}

// =============================================================================
// SinglyLinkedList
// =============================================================================

/// An intrusive doubly-linked list.
pub struct SinglyLinkedList<A: Adaptor<Link>> {
    head: NodePtr,
    adaptor: A,
}

impl<A: Adaptor<Link>> SinglyLinkedList<A> {
    /// Creates an empty `SinglyLinkedList`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adaptor: A) -> SinglyLinkedList<A> {
        SinglyLinkedList {
            head: NodePtr(ptr::null()),
            adaptor: adaptor,
        }
    }

    /// Creates an empty `SinglyLinkedList`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adaptor: A) -> SinglyLinkedList<A> {
        SinglyLinkedList {
            head: NodePtr::null(),
            adaptor: adaptor,
        }
    }

    /// Returns `true if the `SinglyLinkedList` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Returns a null `Cursor` for this list.
    #[inline]
    pub fn cursor(&self) -> Cursor<A> {
        Cursor {
            current: NodePtr::null(),
            list: self,
        }
    }

    /// Returns a null `CursorMut` for this list.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<A> {
        CursorMut {
            current: NodePtr::null(),
            list: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    #[inline]
    pub unsafe fn cursor_from_ptr(&self, ptr: *const A::Container) -> Cursor<A> {
        Cursor {
            current: NodePtr(self.adaptor.get_link(ptr)),
            list: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this list.
    #[inline]
    pub unsafe fn cursor_mut_from_ptr(&mut self, ptr: *const A::Container) -> CursorMut<A> {
        CursorMut {
            current: NodePtr(self.adaptor.get_link(ptr)),
            list: self,
        }
    }

    /// Returns a `Cursor` pointing to the first element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn front(&self) -> Cursor<A> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorMut` pointing to the first element of the list. If the
    /// the list is empty then a null cursor is returned.
    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<A> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }

    /// Gets an iterator over the objects in the `SinglyLinkedList`.
    #[inline]
    pub fn iter(&self) -> Iter<A> {
        Iter {
            raw: RawIter { current: self.head },
            list: self,
        }
    }

    /// Calls the given function for each element in the `SinglyLinkedList`
    /// before removing it from the list.
    ///
    /// This will unlink all objects currently in the list.
    ///
    /// If the given function panics then all elements in the `SinglyLinkedList`
    /// will still be unlinked, but the function will not be called for any
    /// elements after the one that panicked.
    #[inline]
    pub fn drain<F>(&mut self, mut f: F)
        where F: FnMut(IntrusiveRef<A::Container>)
    {
        // If the given function panics, we still need to go through the rest of
        // the list and unlink all remaining links.
        struct PanicGuard(NodePtr);
        impl Drop for PanicGuard {
            #[inline]
            fn drop(&mut self) {
                let mut current = self.0;
                while !current.is_null() {
                    unsafe {
                        let next = current.next();
                        current.unlink();
                        current = next;
                    }
                }
            }
        };

        let mut current = self.head;
        self.head = NodePtr::null();
        while !current.is_null() {
            unsafe {
                let next = current.next();
                current.unlink();
                let guard = PanicGuard(next);
                f(IntrusiveRef::from_raw(self.adaptor.get_container(current.0)));
                mem::forget(guard);
                current = next;
            }
        }
    }

    /// Removes all elements from the `SinglyLinkedList`.
    ///
    /// This will unlink all object currently in the list, which requires
    /// iterating through all elements in the `SinglyLinkedList`.
    #[inline]
    pub fn clear(&mut self) {
        self.drain(|_| {});
    }

    /// Empties the `SinglyLinkedList` without unlinking objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `SinglyLinkedList` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `unsafe_unlink` function on them.
    ///
    /// This is the only function that can be safely called after an object has
    /// been moved or dropped while still being linked into this
    /// `SinglyLinkedList`.
    #[inline]
    pub fn fast_clear(&mut self) {
        self.head = NodePtr::null();
    }

    /// Takes all the elements out of the `SinglyLinkedList`, leaving it empty.
    /// The taken elements are returned as a new `SinglyLinkedList`.
    #[inline]
    pub fn take(&mut self) -> SinglyLinkedList<A>
        where A: Clone
    {
        let list = SinglyLinkedList {
            head: self.head,
            adaptor: self.adaptor.clone(),
        };
        self.head = NodePtr::null();
        list
    }

    /// Inserts a new element at the start of the `SinglyLinkedList`.
    #[inline]
    pub fn push_front(&mut self, val: IntrusiveRef<A::Container>) {
        self.cursor_mut().insert_after(val);
    }

    /// Removes the first element of the `SinglyLinkedList`.
    ///
    /// This returns `None` if the `SinglyLinkedList` is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<IntrusiveRef<A::Container>> {
        self.cursor_mut().remove_next()
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: Adaptor<Link> + Sync> Sync for SinglyLinkedList<A> where A::Container: Sync {}

// We require Sync on objects here because they may belong to multiple collections
unsafe impl<A: Adaptor<Link> + Send> Send for SinglyLinkedList<A> where A::Container: Send + Sync {}

impl<'a, A: Adaptor<Link> + 'a> IntoIterator for &'a SinglyLinkedList<A> {
    type Item = &'a A::Container;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adaptor<Link> + Default> Default for SinglyLinkedList<A> {
    fn default() -> SinglyLinkedList<A> {
        SinglyLinkedList::new(A::default())
    }
}

impl<A: Adaptor<Link>> fmt::Debug for SinglyLinkedList<A>
    where A::Container: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

// =============================================================================
// RawIter, Iter
// =============================================================================

#[derive(Copy, Clone)]
struct RawIter {
    current: NodePtr,
}
impl Iterator for RawIter {
    type Item = NodePtr;

    #[inline]
    fn next(&mut self) -> Option<NodePtr> {
        if self.current.is_null() {
            None
        } else {
            let current = self.current;
            self.current = unsafe { current.next() };
            Some(current)
        }
    }
}

/// An iterator over references to the items of a `SinglyLinkedList`.
pub struct Iter<'a, A: Adaptor<Link> + 'a> {
    raw: RawIter,
    list: &'a SinglyLinkedList<A>,
}
impl<'a, A: Adaptor<Link> + 'a> Iterator for Iter<'a, A> {
    type Item = &'a A::Container;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Container> {
        self.raw.next().map(|x| unsafe { &*self.list.adaptor.get_container(x.0) })
    }
}
impl<'a, A: Adaptor<Link> + 'a> Clone for Iter<'a, A> {
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            raw: self.raw,
            list: self.list,
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use std::vec::Vec;
    use std::boxed::Box;
    use IntrusiveRef;
    use super::{SinglyLinkedList, Link};
    use std::fmt;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    #[derive(Clone)]
    struct Obj {
        link1: Link,
        link2: Link,
        value: u32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adaptor!(ObjAdaptor1 = Obj { link1: Link });
    intrusive_adaptor!(ObjAdaptor2 = Obj { link2: Link });
    fn make_obj(value: u32) -> IntrusiveRef<Obj> {
        IntrusiveRef::from_box(Box::new(Obj {
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

        let mut b = SinglyLinkedList::<ObjAdaptor1>::default();
        assert!(b.is_empty());

        b.push_front(a.clone());
        assert!(!b.is_empty());
        assert!(a.link1.is_linked());
        assert!(!a.link2.is_linked());
        assert_eq!(format!("{:?}", a.link1), "linked");
        assert_eq!(format!("{:?}", a.link2), "unlinked");

        assert_eq!(b.pop_front().unwrap().as_ref() as *const _,
                   a.as_ref() as *const _);
        assert!(b.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!a.link2.is_linked());
    }

    #[test]
    fn test_cursor() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);

        let mut l = SinglyLinkedList::new(ObjAdaptor1);
        let mut cur = l.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
        assert!(cur.remove_next().is_none());
        assert_eq!(cur.replace_next_with(a.clone()).unwrap_err().as_ref() as *const _,
                   a.as_ref() as *const _);

        cur.insert_after(c.clone());
        cur.insert_after(a.clone());
        cur.move_next();
        cur.insert_after(b.clone());
        cur.move_next();
        cur.move_next();
        cur.move_next();
        assert!(cur.is_null());

        cur.move_next();
        assert!(!cur.is_null());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);

        {
            let mut cur2 = cur.as_cursor();
            assert_eq!(cur2.get().unwrap() as *const _, a.as_ref() as *const _);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap() as *const _, c.as_ref() as *const _);
            cur2.move_next();
            assert!(cur2.is_null());
            assert!(cur2.clone().get().is_none());
        }
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);

        assert_eq!(cur.remove_next().unwrap().as_ref() as *const _,
                   b.as_ref() as *const _);
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        cur.insert_after(b.clone());
        assert_eq!(cur.get().unwrap() as *const _, a.as_ref() as *const _);
        cur.move_next();
        assert_eq!(cur.get().unwrap() as *const _, b.as_ref() as *const _);
        assert_eq!(cur.remove_next().unwrap().as_ref() as *const _,
                   c.as_ref() as *const _);
        assert!(!c.link1.is_linked());
        assert!(a.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, b.as_ref() as *const _);
        cur.move_next();
        assert!(cur.is_null());
        assert_eq!(cur.replace_next_with(c.clone()).unwrap().as_ref() as *const _,
                   a.as_ref() as *const _);
        assert!(!a.link1.is_linked());
        assert!(c.link1.is_linked());
        assert!(cur.is_null());
        cur.move_next();
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(cur.replace_next_with(a.clone()).unwrap().as_ref() as *const _,
                   b.as_ref() as *const _);
        assert!(a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get().unwrap() as *const _, c.as_ref() as *const _);
    }

    #[test]
    fn test_split_splice() {
        let mut l1 = SinglyLinkedList::new(ObjAdaptor1);
        let mut l2 = SinglyLinkedList::new(ObjAdaptor1);
        let mut l3 = SinglyLinkedList::new(ObjAdaptor1);

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
        let mut l = SinglyLinkedList::new(ObjAdaptor1);
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
        assert_eq!(l.iter().clone().map(|x| x.value).collect::<Vec<_>>(),
                   [1, 2, 3, 4]);
        assert_eq!(l.iter().map(|x| x.value).collect::<Vec<_>>(), [1, 2, 3, 4]);

        assert_eq!(format!("{:?}", l), "[1, 2, 3, 4]");

        let mut v = Vec::new();
        l.drain(|x| {
            v.push(x.value);
        });
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
        let mut l1 = SinglyLinkedList::new(ObjAdaptor1);
        let mut l2 = SinglyLinkedList::new(ObjAdaptor2);
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
    fn test_unsafe_unlink() {
        let mut l = SinglyLinkedList::new(ObjAdaptor1);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_after(a.clone());
        l.cursor_mut().insert_after(b.clone());
        l.cursor_mut().insert_after(c.clone());

        unsafe {
            l.fast_clear();
            a.link1.unsafe_unlink();
            b.link1.unsafe_unlink();
            c.link1.unsafe_unlink();
        }
        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
    }

    #[test]
    fn test_panic() {
        let mut l = SinglyLinkedList::new(ObjAdaptor1);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_after(a.clone());
        l.cursor_mut().insert_after(b.clone());
        l.cursor_mut().insert_after(c.clone());

        catch_unwind(AssertUnwindSafe(|| l.drain(|_| panic!("test")))).unwrap_err();

        assert!(l.is_empty());
        assert!(!a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(!c.link1.is_linked());
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a> {
            link: Link,
            value: &'a u32,
        }
        struct ObjAdaptor<'a>(::std::marker::PhantomData<*mut Obj<'a>>);
        unsafe impl<'a> ::Adaptor<Link> for ObjAdaptor<'a> {
            type Container = Obj<'a>;
            unsafe fn get_container(&self, link: *const Link) -> *const Self::Container {
                container_of!(link, Obj<'a>, link)
            }
            unsafe fn get_link(&self, container: *const Self::Container) -> *const Link {
                &(*container).link
            }
        }

        let v = 5;
        let mut l = SinglyLinkedList::new(ObjAdaptor(::std::marker::PhantomData));
        let o = Obj {
            link: Link::new(),
            value: &v,
        };
        let a = IntrusiveRef::from_box(Box::new(o.clone()));
        let b = IntrusiveRef::from_box(Box::new(o.clone()));
        l.cursor_mut().insert_after(a);
        l.cursor_mut().insert_after(b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.front().get().unwrap().value, 5);
    }
}
