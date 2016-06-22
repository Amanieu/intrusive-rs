// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive doubly-linked list.

use Adaptor;
use intrusive_ref::IntrusiveRef;
use core::ptr;
use core::fmt;
use core::mem;
use core::cell::Cell;

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a `LinkedList`.
pub struct Link {
    next: Cell<NodePtr>,
    prev: Cell<NodePtr>,
}

impl Link {
    /// Creates a new `Link`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> Link {
        Link {
            next: Cell::new(UNLINKED_MARKER),
            prev: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Creates a new `Link`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> Link {
        Link {
            next: Cell::new(UNLINKED_MARKER),
            prev: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Checks whether the `Link` is linked into a `LinkedList`.
    ///
    /// Note that this function is only thread-safe if the "nightly" feature
    /// is enabled.
    #[inline]
    #[cfg(feature = "nightly")]
    pub fn is_linked(&self) -> bool {
        use core::ptr;
        unsafe {
            // The link might be concurrently modified by another thread,
            // so make sure we read the value only once. Normally we would just
            // make the links atomic but this significantly hurts optimization.
            ptr::read_volatile(&self.next).get() != UNLINKED_MARKER
        }
    }

    /// Checks whether the `Link` is linked into a `LinkedList`.
    ///
    /// Note that this function is only thread-safe if the "nightly" feature
    /// is enabled.
    #[inline]
    #[cfg(not(feature = "nightly"))]
    pub fn is_linked(&self) -> bool {
        // If we don't have read_volatile then there's not much we can do, so
        // just hope the compiler does the right thing.
        self.next.get() != UNLINKED_MARKER
    }


    /// Unlinks the object from the `LinkedList` without invalidating the rest
    /// of the list.
    ///
    /// # Safety
    ///
    /// The `LinkedList` is left in an invalid state after this function is
    /// called. To continue using the `LinkedList`, it must be manually reset by
    /// calling the `fast_clear` function on it. Any other operations on the
    /// affected list will result in undefined behavior.
    #[inline]
    pub unsafe fn unsafe_unlink(&self) {
        self.next.set(UNLINKED_MARKER);
    }
}

// An object containing a link can be sent to another thread if it is unlinked.
unsafe impl Send for Link {}

// The cells are only accessed indirectly through `LinkedList` and are not
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
    unsafe fn prev(self) -> NodePtr {
        (*self.0).prev.get()
    }

    #[inline]
    unsafe fn set_next(self, next: NodePtr) {
        (*self.0).next.set(next);
    }

    #[inline]
    unsafe fn set_prev(self, prev: NodePtr) {
        (*self.0).prev.set(prev);
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
        if !next.is_null() {
            next.set_prev(self);
        }
        self.set_next(next);
        self.set_prev(prev);
    }

    #[inline]
    unsafe fn link_after(self, prev: NodePtr) {
        self.link_between(prev, prev.next());
    }

    #[inline]
    unsafe fn link_before(self, next: NodePtr) {
        self.link_between(next.prev(), next);
    }

    #[inline]
    unsafe fn replace_with(self, new: NodePtr) {
        if !self.prev().is_null() {
            self.prev().set_next(new);
        }
        if !self.next().is_null() {
            self.next().set_prev(new);
        }
        new.set_next(self.next());
        new.set_prev(self.prev());
        self.unlink();
    }

    #[inline]
    unsafe fn remove(self) {
        if !self.next().is_null() {
            self.next().set_prev(self.prev());
        }
        if !self.prev().is_null() {
            self.prev().set_next(self.next());
        }
        self.unlink();
    }

    #[inline]
    unsafe fn splice(start: NodePtr, end: NodePtr, prev: NodePtr, next: NodePtr) {
        start.set_prev(prev);
        end.set_next(next);
        if !prev.is_null() {
            prev.set_next(start);
        }
        if !next.is_null() {
            next.set_prev(end);
        }
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `LinkedList`.
pub struct Cursor<'a, A: Adaptor<Link> + 'a> {
    current: NodePtr,
    list: &'a LinkedList<A>,
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

    /// Returns a raw pointer to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get_raw(&self) -> Option<*const A::Container> {
        if self.is_null() {
            None
        } else {
            Some(unsafe { self.list.adaptor.get_container(self.current.0) })
        }
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&'a A::Container> {
        self.get_raw().map(|x| unsafe { &*x })
    }

    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = self.list.head;
        } else {
            self.current = unsafe { self.current.next() };
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        if self.is_null() {
            self.current = self.list.tail;
        } else {
            self.current = unsafe { self.current.prev() };
        }
    }
}

/// A cursor which provides mutable access to a `LinkedList`.
pub struct CursorMut<'a, A: Adaptor<Link> + 'a> {
    current: NodePtr,
    list: &'a mut LinkedList<A>,
}

impl<'a, A: Adaptor<Link>> CursorMut<'a, A> {
    /// Checks if the cursor is currently pointing to the null object.
    #[inline]
    pub fn is_null(&self) -> bool {
        self.current.is_null()
    }

    /// Returns a raw pointer to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get_raw(&self) -> Option<*const A::Container> {
        if self.is_null() {
            None
        } else {
            Some(unsafe { self.list.adaptor.get_container(self.current.0) })
        }
    }

    /// Returns a reference to the object that the cursor is currently
    /// pointing to.
    ///
    /// This returns None if the cursor is currently pointing to the null
    /// object.
    #[inline]
    pub fn get(&self) -> Option<&'a A::Container> {
        self.get_raw().map(|x| unsafe { &*x })
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

    /// Moves the cursor to the next element of the `LinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `LinkedList`. If it is pointing to the last
    /// element of the `LinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = self.list.head;
        } else {
            self.current = unsafe { self.current.next() };
        }
    }

    /// Moves the cursor to the previous element of the `LinkedList`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `LinkedList`. If it is pointing to the first
    /// element of the `LinkedList` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        if self.is_null() {
            self.current = self.list.tail;
        } else {
            self.current = unsafe { self.current.prev() };
        }
    }

    /// Removes the current element from the `LinkedList`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `LinkedList`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<IntrusiveRef<A::Container>> {
        unsafe {
            if self.is_null() {
                return None;
            }
            if self.list.head == self.current {
                self.list.head = self.current.next();
            }
            if self.list.tail == self.current {
                self.list.tail = self.current.prev();
            }
            let next = self.current.next();
            let result = self.current.0;
            self.current.remove();
            self.current = next;
            Some(IntrusiveRef::from_raw(self.list.adaptor.get_container(result)))
        }
    }

    /// Removes the current element from the `LinkedList` and inserts another
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
    pub fn replace_with(&mut self,
                        val: IntrusiveRef<A::Container>)
                        -> Result<IntrusiveRef<A::Container>, IntrusiveRef<A::Container>> {
        if self.is_null() {
            return Err(val);
        }
        unsafe {
            let new = NodePtr(self.list.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.list.head == self.current {
                self.list.head = new;
            }
            if self.list.tail == self.current {
                self.list.tail = new;
            }
            let result = self.current.0;
            self.current.replace_with(new);
            self.current = new;
            Ok(IntrusiveRef::from_raw(self.list.adaptor.get_container(result)))
        }
    }

    /// Inserts a new element into the `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the front of the `LinkedList`.
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
            if self.list.tail == self.current {
                self.list.tail = new;
            }
        }
    }

    /// Inserts a new element into the `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the end of the `LinkedList`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_before(&mut self, val: IntrusiveRef<A::Container>) {
        unsafe {
            let new = NodePtr(self.list.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.is_null() {
                new.link_between(self.list.tail, NodePtr::null());
                self.list.tail = new;
            } else {
                new.link_before(self.current);
            }
            if self.list.head == self.current {
                self.list.head = new;
            }
        }
    }

    /// Inserts the elements from the given `LinkedList` after the current one.
    ///
    /// If the cursor is pointing at the null object then the new elements are
    /// inserted at the start of the `LinkedList`.
    #[inline]
    pub fn splice_after(&mut self, list: LinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                if self.is_null() {
                    NodePtr::splice(list.head, list.tail, NodePtr::null(), self.list.head);
                    self.list.head = list.head;
                } else {
                    NodePtr::splice(list.head, list.tail, self.current, self.current.next());
                }
                if self.list.tail == self.current {
                    self.list.tail = list.tail;
                }
            }
        }
    }

    /// Moves all element from the given `LinkedList` before the current one.
    ///
    /// If the cursor is pointing at the null object then the new elements are
    /// inserted at the end of the `LinkedList`.
    #[inline]
    pub fn splice_before(&mut self, list: LinkedList<A>) {
        if !list.is_empty() {
            unsafe {
                if self.is_null() {
                    NodePtr::splice(list.head, list.tail, self.list.tail, NodePtr::null());
                    self.list.tail = list.tail;
                } else {
                    NodePtr::splice(list.head, list.tail, self.current.prev(), self.current);
                }
                if self.list.head == self.current {
                    self.list.head = list.head;
                }
            }
        }
    }

    /// Splits the list into two after the current element. This will return a
    /// new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the null object then the entire contents
    /// of the `LinkedList` are moved.
    #[inline]
    pub fn split_after(&mut self) -> LinkedList<A>
        where A: Clone
    {
        if self.is_null() {
            let list = LinkedList {
                head: self.list.head,
                tail: self.list.tail,
                adaptor: self.list.adaptor.clone(),
            };
            self.list.head = NodePtr::null();
            self.list.tail = NodePtr::null();
            list
        } else {
            unsafe {
                let list = LinkedList {
                    head: self.current.next(),
                    tail: self.list.tail,
                    adaptor: self.list.adaptor.clone(),
                };
                if !list.head.is_null() {
                    list.head.set_prev(NodePtr::null());
                }
                self.current.set_next(NodePtr::null());
                self.list.tail = self.current;
                list
            }
        }
    }

    /// Splits the list into two before the current element. This will return a
    /// new list consisting of everything before the cursor, with the original
    /// list retaining everything after.
    ///
    /// If the cursor is pointing at the null object then the entire contents
    /// of the `LinkedList` are moved.
    #[inline]
    pub fn split_before(&mut self) -> LinkedList<A>
        where A: Clone
    {
        if self.is_null() {
            let list = LinkedList {
                head: self.list.head,
                tail: self.list.tail,
                adaptor: self.list.adaptor.clone(),
            };
            self.list.head = NodePtr::null();
            self.list.tail = NodePtr::null();
            list
        } else {
            unsafe {
                let list = LinkedList {
                    head: self.list.head,
                    tail: self.current.prev(),
                    adaptor: self.list.adaptor.clone(),
                };
                if !list.tail.is_null() {
                    list.tail.set_next(NodePtr::null());
                }
                self.current.set_prev(NodePtr::null());
                self.list.head = self.current;
                list
            }
        }
    }
}

// =============================================================================
// LinkedList
// =============================================================================

/// An intrusive doubly-linked list.
pub struct LinkedList<A: Adaptor<Link>> {
    head: NodePtr,
    tail: NodePtr,
    adaptor: A,
}

impl<A: Adaptor<Link>> LinkedList<A> {
    /// Creates an empty `LinkedList`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adaptor: A) -> LinkedList<A> {
        LinkedList {
            head: NodePtr(ptr::null()),
            tail: NodePtr(ptr::null()),
            adaptor: adaptor,
        }
    }

    /// Creates an empty `LinkedList`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adaptor: A) -> LinkedList<A> {
        LinkedList {
            head: NodePtr::null(),
            tail: NodePtr::null(),
            adaptor: adaptor,
        }
    }

    /// Returns `true if the `LinkedList` is empty.
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

    /// Returns a `Cursor` pointing to the last element of the list. If the list
    /// is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<A> {
        let mut cursor = self.cursor();
        cursor.move_prev();
        cursor
    }

    /// Returns a `CursorMut` pointing to the last element of the list. If the
    /// list is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<A> {
        let mut cursor = self.cursor_mut();
        cursor.move_prev();
        cursor
    }

    /// Gets an iterator over the objects in the `LinkedList`.
    #[inline]
    pub fn iter(&self) -> Iter<A> {
        Iter {
            raw: RawIter {
                head: self.head,
                tail: self.tail,
            },
            list: self,
        }
    }

    /// Calls the given function for each element in the `LinkedList` and
    /// removes it from the list.
    ///
    /// This will unlink all objects currently in the list.
    ///
    /// If the given function panics then all elements in the `LinkedList` will
    /// still be unlinked, but the function will not be called for any elements
    /// after the one that panicked.
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
        self.tail = NodePtr::null();
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

    /// Removes all elements from the `LinkedList`.
    ///
    /// This will unlink all object currently in the list, which requires
    /// iterating through all elements in the `LinkedList`.
    #[inline]
    pub fn clear(&mut self) {
        self.drain(|_| {});
    }

    /// Empties the `LinkedList` without unlinking objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `LinkedList` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `unsafe_unlink` function on them.
    ///
    /// This is the only function that can be safely called after an object has
    /// been moved or dropped while still being linked into this `LinkedList`.
    #[inline]
    pub fn fast_clear(&mut self) {
        self.head = NodePtr::null();
        self.tail = NodePtr::null();
    }

    /// Takes all the elements out of the `LinkedList`, leaving it empty. The
    /// taken elements are returned as a new `LinkedList`.
    #[inline]
    pub fn take(&mut self) -> LinkedList<A>
        where A: Clone
    {
        let list = LinkedList {
            head: self.head,
            tail: self.tail,
            adaptor: self.adaptor.clone(),
        };
        self.head = NodePtr::null();
        self.tail = NodePtr::null();
        list
    }

    /// Inserts a new element at the start of the `LinkedList`.
    #[inline]
    pub fn push_front(&mut self, val: IntrusiveRef<A::Container>) {
        self.cursor_mut().insert_after(val);
    }

    /// Inserts a new element at the end of the `LinkedList`.
    #[inline]
    pub fn push_back(&mut self, val: IntrusiveRef<A::Container>) {
        self.cursor_mut().insert_before(val);
    }

    /// Removes the first element of the `LinkedList`.
    ///
    /// This returns `None` if the `LinkedList` is empty.
    #[inline]
    pub fn pop_front(&mut self) -> Option<IntrusiveRef<A::Container>> {
        self.front_mut().remove()
    }

    /// Removes the last element of the `LinkedList`.
    ///
    /// This returns `None` if the `LinkedList` is empty.
    #[inline]
    pub fn pop_back(&mut self) -> Option<IntrusiveRef<A::Container>> {
        self.back_mut().remove()
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: Adaptor<Link> + Sync> Sync for LinkedList<A> where A::Container: Sync {}

// We require Sync on objects here because they may belong to multiple collections
unsafe impl<A: Adaptor<Link> + Send> Send for LinkedList<A> where A::Container: Send + Sync {}

impl<'a, A: Adaptor<Link> + 'a> IntoIterator for &'a LinkedList<A> {
    type Item = &'a A::Container;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adaptor<Link> + Default> Default for LinkedList<A> {
    fn default() -> LinkedList<A> {
        LinkedList::new(A::default())
    }
}

impl<A: Adaptor<Link>> fmt::Debug for LinkedList<A>
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
    head: NodePtr,
    tail: NodePtr,
}
impl Iterator for RawIter {
    type Item = NodePtr;

    #[inline]
    fn next(&mut self) -> Option<NodePtr> {
        if self.head.is_null() {
            None
        } else {
            let head = self.head;
            if head == self.tail {
                self.head = NodePtr::null();
            } else {
                self.head = unsafe { head.next() };
            }
            Some(head)
        }
    }
}
impl DoubleEndedIterator for RawIter {
    #[inline]
    fn next_back(&mut self) -> Option<NodePtr> {
        if self.tail.is_null() {
            None
        } else {
            let tail = self.tail;
            if self.head == tail {
                self.tail = NodePtr::null();
            } else {
                self.tail = unsafe { tail.prev() };
            }
            Some(tail)
        }
    }
}

/// An iterator over references to the items of a `LinkedList`.
pub struct Iter<'a, A: Adaptor<Link> + 'a> {
    raw: RawIter,
    list: &'a LinkedList<A>,
}
impl<'a, A: Adaptor<Link> + 'a> Iterator for Iter<'a, A> {
    type Item = &'a A::Container;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Container> {
        self.raw.next().map(|x| unsafe { &*self.list.adaptor.get_container(x.0) })
    }
}
impl<'a, A: Adaptor<Link> + 'a> DoubleEndedIterator for Iter<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a A::Container> {
        self.raw.next_back().map(|x| unsafe { &*self.list.adaptor.get_container(x.0) })
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
    use super::{LinkedList, Link};
    use std::fmt;

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

        let mut b = LinkedList::<ObjAdaptor1>::default();
        assert!(b.is_empty());

        b.cursor_mut().insert_after(a.clone());
        assert!(!b.is_empty());
        assert!(a.link1.is_linked());
        assert!(!a.link2.is_linked());
        assert_eq!(format!("{:?}", a.link1), "linked");
        assert_eq!(format!("{:?}", a.link2), "unlinked");

        assert_eq!(b.front_mut().remove().unwrap().as_ref() as *const _,
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

        let mut l = LinkedList::new(ObjAdaptor1);
        let mut cur = l.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get_raw().is_none());
        assert!(cur.get().is_none());
        assert!(cur.remove().is_none());
        assert_eq!(cur.replace_with(a.clone()).unwrap_err().as_ref() as *const _,
                   a.as_ref() as *const _);

        cur.insert_before(a.clone());
        cur.insert_before(c.clone());
        cur.move_prev();
        cur.insert_before(b.clone());
        cur.move_next();
        assert!(cur.is_null());

        cur.move_next();
        assert!(!cur.is_null());
        assert_eq!(cur.get_raw().unwrap() as *const _, a.as_ref() as *const _);

        {
            let mut cur2 = cur.as_cursor();
            assert_eq!(cur2.get_raw().unwrap(), a.as_ref() as *const _);
            cur2.move_next();
            assert_eq!(cur2.get().unwrap().value, 2);
            cur2.move_next();
            assert_eq!(cur2.get_raw().unwrap(), c.as_ref() as *const _);
            cur2.move_prev();
            assert_eq!(cur2.get_raw().unwrap(), b.as_ref() as *const _);
            cur2.move_next();
            assert_eq!(cur2.get_raw().unwrap(), c.as_ref() as *const _);
            cur2.move_next();
            assert!(cur2.is_null());
            assert_eq!(cur2.clone().get_raw(), cur2.get_raw());
        }
        assert_eq!(cur.get_raw().unwrap() as *const _, a.as_ref() as *const _);

        cur.move_next();
        assert_eq!(cur.remove().unwrap().as_ref() as *const _,
                   b.as_ref() as *const _);
        assert_eq!(cur.get_raw().unwrap() as *const _, c.as_ref() as *const _);
        cur.insert_after(b.clone());
        assert_eq!(cur.get_raw().unwrap() as *const _, c.as_ref() as *const _);
        cur.move_prev();
        assert_eq!(cur.get_raw().unwrap() as *const _, a.as_ref() as *const _);
        assert_eq!(cur.remove().unwrap().as_ref() as *const _,
                   a.as_ref() as *const _);
        assert!(!a.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get_raw().unwrap() as *const _, c.as_ref() as *const _);
        assert_eq!(cur.replace_with(a.clone()).unwrap().as_ref() as *const _,
                   c.as_ref() as *const _);
        assert!(a.link1.is_linked());
        assert!(!c.link1.is_linked());
        assert_eq!(cur.get_raw().unwrap() as *const _, a.as_ref() as *const _);
        cur.move_next();
        assert_eq!(cur.replace_with(c.clone()).unwrap().as_ref() as *const _,
                   b.as_ref() as *const _);
        assert!(a.link1.is_linked());
        assert!(!b.link1.is_linked());
        assert!(c.link1.is_linked());
        assert_eq!(cur.get_raw().unwrap() as *const _, c.as_ref() as *const _);
    }

    #[test]
    fn test_push_pop() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);

        let mut l = LinkedList::new(ObjAdaptor1);
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
        let mut l1 = LinkedList::new(ObjAdaptor1);
        let mut l2 = LinkedList::new(ObjAdaptor1);
        let mut l3 = LinkedList::new(ObjAdaptor1);

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
    }

    #[test]
    fn test_iter() {
        let mut l = LinkedList::new(ObjAdaptor1);
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
        assert_eq!(l.iter().rev().map(|x| x.value).collect::<Vec<_>>(),
                   [4, 3, 2, 1]);
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
    }

    #[test]
    fn test_multi_list() {
        let mut l1 = LinkedList::new(ObjAdaptor1);
        let mut l2 = LinkedList::new(ObjAdaptor2);
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
    fn test_unsafe_unlink() {
        let mut l = LinkedList::new(ObjAdaptor1);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());

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
    #[cfg(feature = "nightly")]
    fn test_panic() {
        use std::panic::{catch_unwind, AssertUnwindSafe};
        let mut l = LinkedList::new(ObjAdaptor1);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        l.cursor_mut().insert_before(a.clone());
        l.cursor_mut().insert_before(b.clone());
        l.cursor_mut().insert_before(c.clone());

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
        let mut l = LinkedList::new(ObjAdaptor(::std::marker::PhantomData));
        let o = Obj {
            link: Link::new(),
            value: &v,
        };
        let a = IntrusiveRef::from_box(Box::new(o.clone()));
        let b = IntrusiveRef::from_box(Box::new(o.clone()));
        l.cursor_mut().insert_before(a);
        l.cursor_mut().insert_before(b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
    }
}
