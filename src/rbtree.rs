// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive red-black tree.

use core::borrow::Borrow;
use core::cell::Cell;
use core::cmp::Ordering;
use core::fmt;
use core::mem;
use core::ptr;
use Bound::{self, Excluded, Included, Unbounded};
use IntrusivePointer;
use {Adapter, KeyAdapter};

// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a `RBTree`.
pub struct Link {
    left: Cell<NodePtr>,
    right: Cell<NodePtr>,
    parent_color: Cell<usize>,
}

impl Link {
    /// Creates a new `Link`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new() -> Link {
        Link {
            left: Cell::new(NodePtr(ptr::null())),
            right: Cell::new(NodePtr(ptr::null())),
            parent_color: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Creates a new `Link`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new() -> Link {
        Link {
            left: Cell::new(NodePtr::null()),
            right: Cell::new(NodePtr::null()),
            parent_color: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Checks whether the `Link` is linked into a `RBTree`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        self.parent_color.get() != UNLINKED_MARKER
    }

    /// Forcibly unlinks an object from a `RBTree`.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call this function while still linked into a
    /// `RBTree`. The only situation where this function is useful is
    /// after calling `fast_clear` on a `RBTree`, since this clears
    /// the collection without marking the nodes as unlinked.
    #[inline]
    pub unsafe fn force_unlink(&self) {
        self.parent_color.set(UNLINKED_MARKER);
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
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // There isn't anything sensible to print here except whether the link
        // is currently in a tree.
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
enum Color {
    Red,
    Black,
}

#[derive(Copy, Clone, PartialEq, Eq)]
struct NodePtr(*const Link);

// Use a special value to indicate an unlinked node. This value represents a
// red root node, which is impossible in a valid red-black tree.
const UNLINKED_MARKER: usize = 0;

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
    unsafe fn unlink(self) {
        (*self.0).parent_color.set(UNLINKED_MARKER);
    }

    #[inline]
    unsafe fn parent(self) -> NodePtr {
        NodePtr(((*self.0).parent_color.get() & !1) as *const _)
    }

    #[inline]
    unsafe fn color(self) -> Color {
        if (*self.0).parent_color.get() & 1 == 1 {
            Color::Black
        } else {
            Color::Red
        }
    }

    #[inline]
    unsafe fn set_parent_color(self, parent: NodePtr, color: Color) {
        assert!(mem::align_of::<Link>() >= 2);
        let bit = match color {
            Color::Red => 0,
            Color::Black => 1,
        };
        (*self.0).parent_color.set((parent.0 as usize & !1) | bit);
    }

    #[inline]
    unsafe fn set_parent(self, parent: NodePtr) {
        self.set_parent_color(parent, self.color());
    }

    #[inline]
    unsafe fn set_color(self, color: Color) {
        self.set_parent_color(self.parent(), color);
    }

    #[inline]
    unsafe fn left(self) -> NodePtr {
        (*self.0).left.get()
    }

    #[inline]
    unsafe fn right(self) -> NodePtr {
        (*self.0).right.get()
    }

    #[inline]
    unsafe fn set_left(self, left: NodePtr) {
        (*self.0).left.set(left);
    }

    #[inline]
    unsafe fn set_right(self, right: NodePtr) {
        (*self.0).right.set(right);
    }

    #[inline]
    unsafe fn is_left_child(self) -> bool {
        self.parent().left() == self
    }

    #[inline]
    unsafe fn first_child(self) -> NodePtr {
        if self.is_null() {
            NodePtr::null()
        } else {
            let mut x = self;
            while !x.left().is_null() {
                x = x.left();
            }
            x
        }
    }

    #[inline]
    unsafe fn last_child(self) -> NodePtr {
        if self.is_null() {
            NodePtr::null()
        } else {
            let mut x = self;
            while !x.right().is_null() {
                x = x.right();
            }
            x
        }
    }

    unsafe fn next(self) -> NodePtr {
        if !self.right().is_null() {
            self.right().first_child()
        } else {
            let mut x = self;
            loop {
                if x.parent().is_null() {
                    return NodePtr::null();
                }
                if x.is_left_child() {
                    return x.parent();
                }
                x = x.parent();
            }
        }
    }

    unsafe fn prev(self) -> NodePtr {
        if !self.left().is_null() {
            self.left().last_child()
        } else {
            let mut x = self;
            loop {
                if x.parent().is_null() {
                    return NodePtr::null();
                }
                if !x.is_left_child() {
                    return x.parent();
                }
                x = x.parent();
            }
        }
    }

    unsafe fn replace_with(self, new: NodePtr, root: &mut NodePtr) {
        if self.parent().is_null() {
            *root = new;
        } else if self.is_left_child() {
            self.parent().set_left(new);
        } else {
            self.parent().set_right(new);
        }
        if !self.left().is_null() {
            self.left().set_parent(new);
        }
        if !self.right().is_null() {
            self.right().set_parent(new);
        }
        new.set_left(self.left());
        new.set_right(self.right());
        new.set_parent_color(self.parent(), self.color());
        self.unlink();
    }

    #[inline]
    unsafe fn insert_left(self, new: NodePtr, root: &mut NodePtr) {
        new.set_parent_color(self, Color::Red);
        new.set_left(NodePtr::null());
        new.set_right(NodePtr::null());
        self.set_left(new);
        new.post_insert(root);
    }

    #[inline]
    unsafe fn insert_right(self, new: NodePtr, root: &mut NodePtr) {
        new.set_parent_color(self, Color::Red);
        new.set_left(NodePtr::null());
        new.set_right(NodePtr::null());
        self.set_right(new);
        new.post_insert(root);
    }

    unsafe fn rotate_left(self, root: &mut NodePtr) {
        let y = self.right();
        self.set_right(y.left());
        if !self.right().is_null() {
            self.right().set_parent(self);
        }
        y.set_parent(self.parent());
        if self.parent().is_null() {
            *root = y;
        } else if self.is_left_child() {
            self.parent().set_left(y);
        } else {
            self.parent().set_right(y);
        }
        y.set_left(self);
        self.set_parent(y);
    }

    unsafe fn rotate_right(self, root: &mut NodePtr) {
        let y = self.left();
        self.set_left(y.right());
        if !self.left().is_null() {
            self.left().set_parent(self);
        }
        y.set_parent(self.parent());
        if self.parent().is_null() {
            *root = y;
        } else if self.is_left_child() {
            self.parent().set_left(y);
        } else {
            self.parent().set_right(y);
        }
        y.set_right(self);
        self.set_parent(y);
    }

    // This code is based on the red-black tree implementation in libc++
    unsafe fn post_insert(self, root: &mut NodePtr) {
        let mut x = self;
        while !x.parent().is_null() && x.parent().color() == Color::Red {
            if x.parent().is_left_child() {
                let y = x.parent().parent().right();
                if !y.is_null() && y.color() == Color::Red {
                    x = x.parent();
                    x.set_color(Color::Black);
                    x = x.parent();
                    if x.parent().is_null() {
                        x.set_color(Color::Black);
                    } else {
                        x.set_color(Color::Red);
                    }
                    y.set_color(Color::Black);
                } else {
                    if !x.is_left_child() {
                        x = x.parent();
                        x.rotate_left(root);
                    }
                    x = x.parent();
                    x.set_color(Color::Black);
                    x = x.parent();
                    x.set_color(Color::Red);
                    x.rotate_right(root);
                    break;
                }
            } else {
                let y = x.parent().parent().left();
                if !y.is_null() && y.color() == Color::Red {
                    x = x.parent();
                    x.set_color(Color::Black);
                    x = x.parent();
                    if x.parent().is_null() {
                        x.set_color(Color::Black);
                    } else {
                        x.set_color(Color::Red);
                    }
                    y.set_color(Color::Black);
                } else {
                    if x.is_left_child() {
                        x = x.parent();
                        x.rotate_right(root);
                    }
                    x = x.parent();
                    x.set_color(Color::Black);
                    x = x.parent();
                    x.set_color(Color::Red);
                    x.rotate_left(root);
                    break;
                }
            }
        }
    }

    // This code is based on the red-black tree implementation in libc++
    unsafe fn remove(self, root: &mut NodePtr) {
        let y = if self.left().is_null() || self.right().is_null() {
            self
        } else {
            self.next()
        };
        let mut x = if !y.left().is_null() {
            y.left()
        } else {
            y.right()
        };
        let mut w = NodePtr::null();
        if !x.is_null() {
            x.set_parent(y.parent());
        }
        if y.parent().is_null() {
            *root = x;
        } else if y.is_left_child() {
            y.parent().set_left(x);
            w = y.parent().right();
        } else {
            y.parent().set_right(x);
            w = y.parent().left();
        }
        let removed_black = y.color() == Color::Black;
        if y != self {
            y.set_parent(self.parent());
            if self.parent().is_null() {
                *root = y;
            } else if self.is_left_child() {
                y.parent().set_left(y);
            } else {
                y.parent().set_right(y);
            }
            y.set_left(self.left());
            y.left().set_parent(y);
            y.set_right(self.right());
            if !y.right().is_null() {
                y.right().set_parent(y);
            }
            y.set_color(self.color());
        }
        if removed_black && !root.is_null() {
            if !x.is_null() {
                x.set_color(Color::Black);
            } else {
                loop {
                    if !w.is_left_child() {
                        if w.color() == Color::Red {
                            w.set_color(Color::Black);
                            w.parent().set_color(Color::Red);
                            w.parent().rotate_left(root);
                            w = w.left().right();
                        }
                        if (w.left().is_null() || w.left().color() == Color::Black)
                            && (w.right().is_null() || w.right().color() == Color::Black)
                        {
                            w.set_color(Color::Red);
                            x = w.parent();
                            if x.parent().is_null() || x.color() == Color::Red {
                                x.set_color(Color::Black);
                                break;
                            }
                            w = if x.is_left_child() {
                                x.parent().right()
                            } else {
                                x.parent().left()
                            };
                        } else {
                            if w.right().is_null() || w.right().color() == Color::Black {
                                w.left().set_color(Color::Black);
                                w.set_color(Color::Red);
                                w.rotate_right(root);
                                w = w.parent();
                            }
                            w.set_color(w.parent().color());
                            w.parent().set_color(Color::Black);
                            w.right().set_color(Color::Black);
                            w.parent().rotate_left(root);
                            break;
                        }
                    } else {
                        if w.color() == Color::Red {
                            w.set_color(Color::Black);
                            w.parent().set_color(Color::Red);
                            w.parent().rotate_right(root);
                            w = w.right().left();
                        }
                        if (w.left().is_null() || w.left().color() == Color::Black)
                            && (w.right().is_null() || w.right().color() == Color::Black)
                        {
                            w.set_color(Color::Red);
                            x = w.parent();
                            if x.parent().is_null() || x.color() == Color::Red {
                                x.set_color(Color::Black);
                                break;
                            }
                            w = if x.is_left_child() {
                                x.parent().right()
                            } else {
                                x.parent().left()
                            };
                        } else {
                            if w.left().is_null() || w.left().color() == Color::Black {
                                w.right().set_color(Color::Black);
                                w.set_color(Color::Red);
                                w.rotate_left(root);
                                w = w.parent();
                            }
                            w.set_color(w.parent().color());
                            w.parent().set_color(Color::Black);
                            w.left().set_color(Color::Black);
                            w.parent().rotate_right(root);
                            break;
                        }
                    }
                }
            }
        }
        self.unlink();
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `RBTree`.
pub struct Cursor<'a, A: Adapter<Link = Link> + 'a> {
    current: NodePtr,
    tree: &'a RBTree<A>,
}

impl<'a, A: Adapter<Link = Link> + 'a> Clone for Cursor<'a, A> {
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            tree: self.tree,
        }
    }
}

impl<'a, A: Adapter<Link = Link> + 'a> Cursor<'a, A> {
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
            Some(unsafe { &*self.tree.adapter.get_value(self.current.0) })
        }
    }

    /// Moves the cursor to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = unsafe { self.tree.root.first_child() };
        } else {
            self.current = unsafe { self.current.next() };
        }
    }

    /// Moves the cursor to the previous element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `RBTree`. If it is pointing to the first
    /// element of the `RBTree` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        if self.is_null() {
            self.current = unsafe { self.tree.root.last_child() };
        } else {
            self.current = unsafe { self.current.prev() };
        }
    }

    /// Returns a cursor pointing to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<A> {
        let mut next = self.clone();
        next.move_next();
        next
    }

    /// Returns a cursor pointing to the previous element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// last element of the `RBTree`. If it is pointing to the first
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_prev(&self) -> Cursor<A> {
        let mut prev = self.clone();
        prev.move_prev();
        prev
    }
}

/// A cursor which provides mutable access to a `RBTree`.
pub struct CursorMut<'a, A: Adapter<Link = Link> + 'a> {
    current: NodePtr,
    tree: &'a mut RBTree<A>,
}

impl<'a, A: Adapter<Link = Link> + 'a> CursorMut<'a, A> {
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
            Some(unsafe { &*self.tree.adapter.get_value(self.current.0) })
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
            tree: self.tree,
        }
    }

    /// Moves the cursor to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = unsafe { self.tree.root.first_child() };
        } else {
            self.current = unsafe { self.current.next() };
        }
    }

    /// Moves the cursor to the previous element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the last element of the `RBTree`. If it is pointing to the first
    /// element of the `RBTree` then this will move it to the null object.
    #[inline]
    pub fn move_prev(&mut self) {
        if self.is_null() {
            self.current = unsafe { self.tree.root.last_child() };
        } else {
            self.current = unsafe { self.current.prev() };
        }
    }

    /// Returns a cursor pointing to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<A> {
        let mut next = self.as_cursor();
        next.move_next();
        next
    }

    /// Returns a cursor pointing to the previous element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// last element of the `RBTree`. If it is pointing to the first
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_prev(&self) -> Cursor<A> {
        let mut prev = self.as_cursor();
        prev.move_prev();
        prev
    }

    /// Removes the current element from the `RBTree`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `RBTree`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<A::Pointer> {
        unsafe {
            if self.is_null() {
                return None;
            }
            let next = self.current.next();
            let result = self.current.0;
            self.current.remove(&mut self.tree.root);
            self.current = next;
            Some(A::Pointer::from_raw(self.tree.adapter.get_value(result)))
        }
    }

    /// Removes the current element from the `RBTree` and inserts another
    /// object in its place.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// modified to point to the newly added element.
    ///
    /// When using this function you must ensure that the elements in the
    /// collection are maintained in increasing order. Failure to do this may
    /// lead to `find`, `upper_bound`, `lower_bound` and `range` returning
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
        if self.is_null() {
            return Err(val);
        }
        unsafe {
            let new = self.tree.node_from_value(val);
            let result = self.current.0;
            self.current.replace_with(new, &mut self.tree.root);
            self.current = new;
            Ok(A::Pointer::from_raw(self.tree.adapter.get_value(result)))
        }
    }

    /// Inserts a new element into the `RBTree` after the current one.
    ///
    /// When using this function you must ensure that the elements in the
    /// collection are maintained in increasing order. Failure to do this may
    /// lead to `find`, `upper_bound`, `lower_bound` and `range` returning
    /// incorrect results.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the start of the `RBTree`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_after(&mut self, val: A::Pointer) {
        unsafe {
            let new = self.tree.node_from_value(val);
            if self.tree.is_empty() {
                self.tree.insert_root(new);
            } else if self.is_null() {
                self.tree
                    .root
                    .first_child()
                    .insert_left(new, &mut self.tree.root);
            } else if self.current.right().is_null() {
                self.current.insert_right(new, &mut self.tree.root);
            } else {
                self.current.next().insert_left(new, &mut self.tree.root);
            }
        }
    }

    /// Inserts a new element into the `RBTree` before the current one.
    ///
    /// When using this function you must ensure that the elements in the
    /// collection are maintained in increasing order. Failure to do this may
    /// lead to `find`, `upper_bound`, `lower_bound` and `range` returning
    /// incorrect results.
    ///
    /// If the cursor is pointing at the null object then the new element is
    /// inserted at the end of the `RBTree`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert_before(&mut self, val: A::Pointer) {
        unsafe {
            let new = self.tree.node_from_value(val);
            if self.tree.is_empty() {
                self.tree.insert_root(new);
            } else if self.is_null() {
                self.tree
                    .root
                    .last_child()
                    .insert_right(new, &mut self.tree.root);
            } else if self.current.left().is_null() {
                self.current.insert_left(new, &mut self.tree.root);
            } else {
                self.current.prev().insert_right(new, &mut self.tree.root);
            }
        }
    }
}

impl<'a, A: for<'b> KeyAdapter<'b, Link = Link>> CursorMut<'a, A> {
    /// Inserts a new element into the `RBTree`.
    ///
    /// The new element will be inserted at the correct position in the tree
    /// based on its key, regardless of the current cursor position.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert<'c>(&'c mut self, val: A::Pointer)
    where
        <A as KeyAdapter<'c>>::Key: Ord,
    {
        // We explicitly drop the returned CursorMut here, otherwise we would
        // end up with multiple CursorMut in the same collection.
        self.tree.insert(val);
    }
}

// =============================================================================
// RBTree
// =============================================================================

/// An intrusive red-black tree.
///
/// When this collection is dropped, all elements linked into it will be
/// converted back to owned pointers and dropped.
///
/// Note that you are responsible for ensuring that the elements in a `RBTree`
/// remain in ascending key order. This property can be violated, either because
/// the key of an element was modified, or because the
/// `insert_before`/`insert_after` methods of `CursorMut` were incorrectly used.
/// If this situation occurs, memory safety will not be violated but the `find`,
/// `upper_bound`, `lower_bound` and `range` may return incorrect results.
pub struct RBTree<A: Adapter<Link = Link>> {
    root: NodePtr,
    adapter: A,
}

impl<A: Adapter<Link = Link>> RBTree<A> {
    #[inline]
    fn node_from_value(&self, val: A::Pointer) -> NodePtr {
        unsafe {
            assert!(
                !(*self.adapter.get_link(&*val)).is_linked(),
                "attempted to insert an object that is already linked"
            );
            NodePtr(self.adapter.get_link(val.into_raw()))
        }
    }

    /// Creates an empty `RBTree`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adapter: A) -> RBTree<A> {
        RBTree {
            root: NodePtr(ptr::null()),
            adapter,
        }
    }

    /// Creates an empty `RBTree`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adapter: A) -> RBTree<A> {
        RBTree {
            root: NodePtr::null(),
            adapter,
        }
    }

    /// Returns `true` if the `RBTree` is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.root.is_null()
    }

    /// Returns a null `Cursor` for this tree.
    #[inline]
    pub fn cursor(&self) -> Cursor<A> {
        Cursor {
            current: NodePtr::null(),
            tree: self,
        }
    }

    /// Returns a null `CursorMut` for this tree.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<A> {
        CursorMut {
            current: NodePtr::null(),
            tree: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this tree.
    #[inline]
    pub unsafe fn cursor_from_ptr(&self, ptr: *const A::Value) -> Cursor<A> {
        Cursor {
            current: NodePtr(self.adapter.get_link(ptr)),
            tree: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this tree.
    #[inline]
    pub unsafe fn cursor_mut_from_ptr(&mut self, ptr: *const A::Value) -> CursorMut<A> {
        CursorMut {
            current: NodePtr(self.adapter.get_link(ptr)),
            tree: self,
        }
    }

    /// Returns a `Cursor` pointing to the first element of the tree. If the
    /// tree is empty then a null cursor is returned.
    #[inline]
    pub fn front(&self) -> Cursor<A> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorMut` pointing to the first element of the tree. If the
    /// the tree is empty then a null cursor is returned.
    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<A> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }

    /// Returns a `Cursor` pointing to the last element of the tree. If the tree
    /// is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<A> {
        let mut cursor = self.cursor();
        cursor.move_prev();
        cursor
    }

    /// Returns a `CursorMut` pointing to the last element of the tree. If the
    /// tree is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<A> {
        let mut cursor = self.cursor_mut();
        cursor.move_prev();
        cursor
    }

    #[inline]
    unsafe fn insert_root(&mut self, node: NodePtr) {
        node.set_parent_color(NodePtr::null(), Color::Black);
        node.set_left(NodePtr::null());
        node.set_right(NodePtr::null());
        self.root = node;
    }

    /// Gets an iterator over the objects in the `RBTree`, in ascending key
    /// order.
    #[inline]
    pub fn iter(&self) -> Iter<A> {
        if self.root.is_null() {
            Iter {
                head: NodePtr::null(),
                tail: NodePtr::null(),
                tree: self,
            }
        } else {
            Iter {
                head: unsafe { self.root.first_child() },
                tail: unsafe { self.root.last_child() },
                tree: self,
            }
        }
    }

    #[inline]
    fn clear_recurse(&mut self, current: NodePtr) {
        // If adapter.get_value or Pointer::from_raw panic here, it will leak
        // the nodes and keep them linked. However this is harmless since there
        // is nothing you can do with just a Link.
        if !current.is_null() {
            unsafe {
                self.clear_recurse(current.left());
                self.clear_recurse(current.right());
                current.unlink();
                A::Pointer::from_raw(self.adapter.get_value(current.0));
            }
        }
    }

    /// Removes all elements from the `RBTree`.
    ///
    /// This will unlink all object currently in the tree, which requires
    /// iterating through all elements in the `RBTree`. Each element is
    /// converted back to an owned pointer and then dropped.
    #[inline]
    pub fn clear(&mut self) {
        let root = self.root;
        self.root = NodePtr::null();
        self.clear_recurse(root);
    }

    /// Empties the `RBTree` without unlinking or freeing objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `RBTree` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `force_unlink` function on them.
    #[inline]
    pub fn fast_clear(&mut self) {
        self.root = NodePtr::null();
    }

    /// Takes all the elements out of the `RBTree`, leaving it empty. The
    /// taken elements are returned as a new `RBTree`.
    #[inline]
    pub fn take(&mut self) -> RBTree<A>
    where
        A: Clone,
    {
        let tree = RBTree {
            root: self.root,
            adapter: self.adapter.clone(),
        };
        self.root = NodePtr::null();
        tree
    }
}

impl<A: for<'a> KeyAdapter<'a, Link = Link>> RBTree<A> {
    #[inline]
    fn find_internal<'a, Q: ?Sized + Ord>(&self, key: &Q) -> NodePtr
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(tree.0) };
            match key.cmp(self.adapter.get_key(current).borrow()) {
                Ordering::Less => tree = unsafe { tree.left() },
                Ordering::Equal => return tree,
                Ordering::Greater => tree = unsafe { tree.right() },
            }
        }
        NodePtr::null()
    }

    /// Returns a `Cursor` pointing to an element with the given key. If no such
    /// element is found then a null cursor is returned.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn find<'a, Q: ?Sized + Ord>(&'a self, key: &Q) -> Cursor<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        Cursor {
            current: self.find_internal(key),
            tree: self,
        }
    }

    /// Returns a `CursorMut` pointing to an element with the given key. If no
    /// such element is found then a null cursor is returned.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn find_mut<'a, Q: ?Sized + Ord>(&'a mut self, key: &Q) -> CursorMut<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        CursorMut {
            current: self.find_internal(key),
            tree: self,
        }
    }

    #[inline]
    fn lower_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> NodePtr
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        let mut result = NodePtr::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(tree.0) };
            let cond = match bound {
                Unbounded => true,
                Included(key) => key <= self.adapter.get_key(current).borrow(),
                Excluded(key) => key < self.adapter.get_key(current).borrow(),
            };
            if cond {
                result = tree;
                tree = unsafe { tree.left() };
            } else {
                tree = unsafe { tree.right() };
            }
        }
        result
    }

    /// Returns a `Cursor` pointing to the lowest element whose key is above
    /// the given bound. If no such element is found then a null cursor is
    /// returned.
    #[inline]
    pub fn lower_bound<'a, Q: ?Sized + Ord>(&'a self, bound: Bound<&Q>) -> Cursor<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        Cursor {
            current: self.lower_bound_internal(bound),
            tree: self,
        }
    }

    /// Returns a `CursorMut` pointing to the first element whose key is
    /// above the given bound. If no such element is found then a null
    /// cursor is returned.
    #[inline]
    pub fn lower_bound_mut<'a, Q: ?Sized + Ord>(&'a mut self, bound: Bound<&Q>) -> CursorMut<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        CursorMut {
            current: self.lower_bound_internal(bound),
            tree: self,
        }
    }

    #[inline]
    fn upper_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> NodePtr
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        let mut result = NodePtr::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(tree.0) };
            let cond = match bound {
                Unbounded => false,
                Included(key) => key < self.adapter.get_key(current).borrow(),
                Excluded(key) => key <= self.adapter.get_key(current).borrow(),
            };
            if cond {
                tree = unsafe { tree.left() };
            } else {
                result = tree;
                tree = unsafe { tree.right() };
            }
        }
        result
    }

    /// Returns a `Cursor` pointing to the last element whose key is below
    /// the given bound. If no such element is found then a null cursor is
    /// returned.
    #[inline]
    pub fn upper_bound<'a, Q: ?Sized + Ord>(&'a self, bound: Bound<&Q>) -> Cursor<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        Cursor {
            current: self.upper_bound_internal(bound),
            tree: self,
        }
    }

    /// Returns a `CursorMut` pointing to the last element whose key is
    /// below the given bound. If no such element is found then a null
    /// cursor is returned.
    #[inline]
    pub fn upper_bound_mut<'a, Q: ?Sized + Ord>(&'a mut self, bound: Bound<&Q>) -> CursorMut<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        CursorMut {
            current: self.upper_bound_internal(bound),
            tree: self,
        }
    }

    /// Inserts a new element into the `RBTree`.
    ///
    /// The new element will be inserted at the correct position in the tree
    /// based on its key.
    ///
    /// Returns a mutable cursor pointing to the newly added element.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    #[inline]
    pub fn insert<'a>(&'a mut self, val: A::Pointer) -> CursorMut<A>
    where
        <A as KeyAdapter<'a>>::Key: Ord,
    {
        unsafe {
            let raw = &*val as *const _;
            let new = self.node_from_value(val);
            if self.is_empty() {
                self.insert_root(new);
            } else {
                let key = self.adapter.get_key(&*raw);
                let mut tree = self.root;
                loop {
                    let current = &*self.adapter.get_value(tree.0);
                    if key < self.adapter.get_key(current) {
                        if tree.left().is_null() {
                            tree.insert_left(new, &mut self.root);
                            break;
                        } else {
                            tree = tree.left();
                        }
                    } else {
                        if tree.right().is_null() {
                            tree.insert_right(new, &mut self.root);
                            break;
                        } else {
                            tree = tree.right();
                        }
                    }
                }
            }
            CursorMut {
                current: new,
                tree: self,
            }
        }
    }

    /// Returns an `Entry` for the given key which contains a `CursorMut` to an
    /// element with the given key or an `InsertCursor` which points to a place
    /// in which to insert a new element with the given key.
    ///
    /// This is more efficient than calling `find` followed by `insert` since
    /// the tree does not have to be searched a second time to find a place to
    /// insert the new element.
    ///
    /// If multiple elements with an identical key are found then an arbitrary
    /// one is returned.
    #[inline]
    pub fn entry<'a, Q: ?Sized + Ord>(&'a mut self, key: &Q) -> Entry<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
    {
        unsafe {
            if self.is_empty() {
                Entry::Vacant(InsertCursor {
                    parent: NodePtr::null(),
                    insert_left: false,
                    tree: self,
                })
            } else {
                let mut tree = self.root;
                loop {
                    let current = &*self.adapter.get_value(tree.0);
                    match key.cmp(self.adapter.get_key(current).borrow()) {
                        Ordering::Less => if tree.left().is_null() {
                            return Entry::Vacant(InsertCursor {
                                parent: tree,
                                insert_left: true,
                                tree: self,
                            });
                        } else {
                            tree = tree.left();
                        },
                        Ordering::Equal => {
                            return Entry::Occupied(CursorMut {
                                current: tree,
                                tree: self,
                            });
                        }
                        Ordering::Greater => if tree.right().is_null() {
                            return Entry::Vacant(InsertCursor {
                                parent: tree,
                                insert_left: false,
                                tree: self,
                            });
                        } else {
                            tree = tree.right();
                        },
                    }
                }
            }
        }
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// tree, starting at min, and ending at max. If min is `Unbounded`, then it
    /// will be treated as "negative infinity", and if max is `Unbounded`, then
    /// it will be treated as "positive infinity". Thus
    /// `range(Unbounded, Unbounded)` will yield the whole collection.
    #[inline]
    pub fn range<'a, Min: ?Sized + Ord, Max: ?Sized + Ord>(
        &'a self,
        min: Bound<&Min>,
        max: Bound<&Max>,
    ) -> Iter<'a, A>
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Min> + Borrow<Max>,
        <A as KeyAdapter<'a>>::Key: Ord,
    {
        let lower = self.lower_bound_internal(min);
        let upper = self.upper_bound_internal(max);
        if !lower.is_null() && !upper.is_null() {
            let lower_key = unsafe { self.adapter.get_key(&*self.adapter.get_value(lower.0)) };
            let upper_key = unsafe { self.adapter.get_key(&*self.adapter.get_value(upper.0)) };
            if upper_key >= lower_key {
                return Iter {
                    head: lower,
                    tail: upper,
                    tree: self,
                };
            }
        }
        Iter {
            head: NodePtr::null(),
            tail: NodePtr::null(),
            tree: self,
        }
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: Adapter<Link = Link> + Sync> Sync for RBTree<A> where A::Value: Sync {}

// Allow sending to another thread if the ownership (represented by the A::Pointer owned
// pointer type) can be transferred to another thread.
unsafe impl<A: Adapter<Link = Link> + Send> Send for RBTree<A> where A::Pointer: Send {}

// Drop all owned pointers if the collection is dropped
impl<A: Adapter<Link = Link>> Drop for RBTree<A> {
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Adapter<Link = Link>> IntoIterator for RBTree<A> {
    type Item = A::Pointer;
    type IntoIter = IntoIter<A>;

    #[inline]
    fn into_iter(self) -> IntoIter<A> {
        if self.root.is_null() {
            IntoIter {
                head: NodePtr::null(),
                tail: NodePtr::null(),
                tree: self,
            }
        } else {
            IntoIter {
                head: unsafe { self.root.first_child() },
                tail: unsafe { self.root.last_child() },
                tree: self,
            }
        }
    }
}

impl<'a, A: Adapter<Link = Link> + 'a> IntoIterator for &'a RBTree<A> {
    type Item = &'a A::Value;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: Adapter<Link = Link> + Default> Default for RBTree<A> {
    fn default() -> RBTree<A> {
        RBTree::new(A::default())
    }
}

impl<A: Adapter<Link = Link>> fmt::Debug for RBTree<A>
where
    A::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// =============================================================================
// InsertCursor, Entry
// =============================================================================

/// A cursor pointing to a slot in which an element can be inserted into a
/// `RBTree`.
pub struct InsertCursor<'a, A: Adapter<Link = Link> + 'a> {
    parent: NodePtr,
    insert_left: bool,
    tree: &'a mut RBTree<A>,
}

impl<'a, A: Adapter<Link = Link> + 'a> InsertCursor<'a, A> {
    /// Inserts a new element into the `RBTree` at the location indicated by
    /// this `InsertCursor`.
    ///
    /// # Panics
    ///
    /// Panics if the new element is already linked to a different intrusive
    /// collection.
    pub fn insert(self, val: A::Pointer) -> CursorMut<'a, A> {
        unsafe {
            let new = self.tree.node_from_value(val);
            if self.parent.is_null() {
                self.tree.insert_root(new);
            } else if self.insert_left {
                self.parent.insert_left(new, &mut self.tree.root);
            } else {
                self.parent.insert_right(new, &mut self.tree.root);
            }
            CursorMut {
                current: new,
                tree: self.tree,
            }
        }
    }
}

/// An entry in a `RBTree`.
///
/// See the documentation for `RBTree::entry`.
pub enum Entry<'a, A: Adapter<Link = Link> + 'a> {
    /// An occupied entry.
    Occupied(CursorMut<'a, A>),

    /// A vacant entry.
    Vacant(InsertCursor<'a, A>),
}

impl<'a, A: Adapter<Link = Link> + 'a> Entry<'a, A> {
    /// Inserts an element into the `RBTree` if the entry is vacant, returning
    /// a `CursorMut` to the resulting value. If the entry is occupied then a
    /// `CursorMut` pointing to the element is returned.
    ///
    /// # Panics
    ///
    /// Panics if the `Entry` is vacant and the new element is already linked to
    /// a different intrusive collection.
    pub fn or_insert(self, val: A::Pointer) -> CursorMut<'a, A> {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(val),
        }
    }

    /// Calls the given function and inserts the result into the `RBTree` if the
    /// entry is vacant, returning a `CursorMut` to the resulting value. If the
    /// entry is occupied then a `CursorMut` pointing to the element is
    /// returned and the function is not executed.
    ///
    /// # Panics
    ///
    /// Panics if the `Entry` is vacant and the new element is already linked to
    /// a different intrusive collection.
    pub fn or_insert_with<F>(self, default: F) -> CursorMut<'a, A>
    where
        F: FnOnce() -> A::Pointer,
    {
        match self {
            Entry::Occupied(entry) => entry,
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }
}

// =============================================================================
// Iter
// =============================================================================

/// An iterator over references to the items of a `RBTree`.
pub struct Iter<'a, A: Adapter<Link = Link> + 'a> {
    head: NodePtr,
    tail: NodePtr,
    tree: &'a RBTree<A>,
}
impl<'a, A: Adapter<Link = Link> + 'a> Iterator for Iter<'a, A> {
    type Item = &'a A::Value;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Value> {
        if self.head.is_null() {
            None
        } else {
            let head = self.head;
            if head == self.tail {
                self.head = NodePtr::null();
                self.tail = NodePtr::null();
            } else {
                self.head = unsafe { head.next() };
            }
            Some(unsafe { &*self.tree.adapter.get_value(head.0) })
        }
    }
}
impl<'a, A: Adapter<Link = Link> + 'a> DoubleEndedIterator for Iter<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a A::Value> {
        if self.tail.is_null() {
            None
        } else {
            let tail = self.tail;
            if self.head == tail {
                self.tail = NodePtr::null();
                self.head = NodePtr::null();
            } else {
                self.tail = unsafe { tail.prev() };
            }
            Some(unsafe { &*self.tree.adapter.get_value(tail.0) })
        }
    }
}
impl<'a, A: Adapter<Link = Link> + 'a> Clone for Iter<'a, A> {
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            head: self.head,
            tail: self.tail,
            tree: self.tree,
        }
    }
}

// =============================================================================
// IntoIter
// =============================================================================

/// An iterator which consumes a `RBTree`.
pub struct IntoIter<A: Adapter<Link = Link>> {
    head: NodePtr,
    tail: NodePtr,
    tree: RBTree<A>,
}
impl<A: Adapter<Link = Link>> Iterator for IntoIter<A> {
    type Item = A::Pointer;

    #[inline]
    fn next(&mut self) -> Option<A::Pointer> {
        if self.head.is_null() {
            None
        } else {
            unsafe {
                // Remove the node from the tree. Since head is always the
                // left-most node, we can infer the following:
                // - head.left is null.
                // - head is a left child of its parent (or the root node).
                let head = self.head;
                let parent = head.parent();
                let right = head.right();
                if parent.is_null() {
                    self.tree.root = right;
                    if right.is_null() {
                        self.tail = NodePtr::null();
                    }
                } else {
                    parent.set_left(right);
                }
                if right.is_null() {
                    self.head = parent;
                } else {
                    right.set_parent(parent);
                    self.head = right.first_child();
                }
                head.unlink();
                Some(A::Pointer::from_raw(self.tree.adapter.get_value(head.0)))
            }
        }
    }
}
impl<A: Adapter<Link = Link>> DoubleEndedIterator for IntoIter<A> {
    #[inline]
    fn next_back(&mut self) -> Option<A::Pointer> {
        if self.tail.is_null() {
            None
        } else {
            unsafe {
                // Remove the node from the tree. Since tail is always the
                // right-most node, we can infer the following:
                // - tail.right is null.
                // - tail is a right child of its parent (or the root node).
                let tail = self.tail;
                let parent = tail.parent();
                let left = tail.left();
                if parent.is_null() {
                    self.tree.root = left;
                    if left.is_null() {
                        self.head = NodePtr::null();
                    }
                } else {
                    parent.set_right(left);
                }
                if left.is_null() {
                    self.tail = parent;
                } else {
                    left.set_parent(parent);
                    self.tail = left.last_child();
                }
                tail.unlink();
                Some(A::Pointer::from_raw(self.tree.adapter.get_value(tail.0)))
            }
        }
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::{Entry, Link, RBTree};
    use std::boxed::Box;
    use std::fmt;
    use std::marker::PhantomData;
    use std::vec::Vec;
    use Bound::*;
    use {KeyAdapter, UnsafeRef};
    extern crate rand;
    use self::rand::{Rng, XorShiftRng};

    #[derive(Clone)]
    struct Obj {
        link: Link,
        value: i32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adapter!(ObjAdapter = UnsafeRef<Obj>: Obj { link: Link });
    impl<'a> KeyAdapter<'a> for ObjAdapter {
        type Key = i32;
        fn get_key(&self, value: &'a Self::Value) -> i32 {
            value.value
        }
    }
    fn make_obj(value: i32) -> UnsafeRef<Obj> {
        UnsafeRef::from_box(Box::new(Obj {
            link: Link::new(),
            value: value,
        }))
    }

    #[test]
    fn test_link() {
        let a = make_obj(1);
        assert!(!a.link.is_linked());
        assert_eq!(format!("{:?}", a.link), "unlinked");

        let mut b = RBTree::<ObjAdapter>::default();
        assert!(b.is_empty());

        assert_eq!(b.insert(a.clone()).get().unwrap().value, 1);
        assert!(!b.is_empty());
        assert!(a.link.is_linked());
        assert_eq!(format!("{:?}", a.link), "linked");

        let c = a.as_ref().clone();
        assert!(!c.link.is_linked());

        unsafe {
            assert_eq!(b.cursor_from_ptr(a.as_ref()).get().unwrap().value, 1);
            assert_eq!(b.cursor_mut_from_ptr(a.as_ref()).get().unwrap().value, 1);
        }

        assert_eq!(
            b.front_mut().remove().unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(b.is_empty());
        assert!(!a.link.is_linked());
    }

    #[test]
    fn test_cursor() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let mut t = RBTree::new(ObjAdapter::new());
        let mut cur = t.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
        assert!(cur.remove().is_none());

        cur.insert_before(a.clone());
        cur.insert_before(c.clone());
        cur.move_prev();
        cur.insert(b.clone());
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

        let a2 = make_obj(1);
        let b2 = make_obj(2);
        let c2 = make_obj(3);
        assert_eq!(
            cur.replace_with(a2.clone()).unwrap().as_ref() as *const _,
            a.as_ref() as *const _
        );
        assert!(!a.link.is_linked());
        cur.move_next();
        assert_eq!(
            cur.replace_with(b2.clone()).unwrap().as_ref() as *const _,
            b.as_ref() as *const _
        );
        assert!(!b.link.is_linked());
        cur.move_next();
        assert_eq!(
            cur.replace_with(c2.clone()).unwrap().as_ref() as *const _,
            c.as_ref() as *const _
        );
        assert!(!c.link.is_linked());
        cur.move_next();
        assert_eq!(
            cur.replace_with(c.clone()).unwrap_err().as_ref() as *const _,
            c.as_ref() as *const _
        );
    }

    #[test]
    fn test_insert_remove() {
        let v = (0..100).map(make_obj).collect::<Vec<_>>();
        assert!(v.iter().all(|x| !x.link.is_linked()));
        let mut t = RBTree::new(ObjAdapter::new());
        assert!(t.is_empty());
        let mut rng = XorShiftRng::new_unseeded();

        {
            let mut expected = Vec::new();
            for x in v.iter() {
                t.insert(x.clone());
                expected.push(x.value);
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }

            while let Some(x) = t.front_mut().remove() {
                assert_eq!(x.value, expected.remove(0));
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }
            assert!(expected.is_empty());
            assert!(t.is_empty());
        }

        {
            let mut expected = Vec::new();
            for x in v.iter().rev() {
                t.insert(x.clone());
                expected.insert(0, x.value);
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }

            while let Some(x) = t.back_mut().remove() {
                assert_eq!(x.value, expected.pop().unwrap());
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }
            assert!(expected.is_empty());
            assert!(t.is_empty());
        }

        {
            let mut indices = (0..v.len()).collect::<Vec<_>>();
            rng.shuffle(&mut indices);
            let mut expected = Vec::new();
            for i in indices {
                t.insert(v[i].clone());
                expected.push(v[i].value);
                expected[..].sort();
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }

            while !expected.is_empty() {
                {
                    let index = rng.gen_range(0, expected.len());
                    let mut c = t.cursor_mut();
                    for _ in 0..(index + 1) {
                        c.move_next();
                    }
                    assert_eq!(c.remove().unwrap().value, expected.remove(index));
                }
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }
            assert!(t.is_empty());
        }

        {
            let mut indices = (0..v.len()).collect::<Vec<_>>();
            rng.shuffle(&mut indices);
            let mut expected = Vec::new();
            for i in indices {
                {
                    let mut c = t.front_mut();
                    loop {
                        if let Some(x) = c.get() {
                            if x.value > v[i].value {
                                break;
                            }
                        } else {
                            break;
                        }
                        c.move_next();
                    }
                    c.insert_before(v[i].clone());
                }
                expected.push(v[i].value);
                expected[..].sort();
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }

            t.clear();
            assert!(t.is_empty());
        }

        {
            let mut indices = (0..v.len()).collect::<Vec<_>>();
            rng.shuffle(&mut indices);
            let mut expected = Vec::new();
            for i in indices {
                {
                    let mut c = t.back_mut();
                    loop {
                        if let Some(x) = c.get() {
                            if x.value < v[i].value {
                                break;
                            }
                        } else {
                            break;
                        }
                        c.move_prev();
                    }
                    c.insert_after(v[i].clone());
                }
                expected.push(v[i].value);
                expected[..].sort();
                assert_eq!(t.iter().map(|x| x.value).collect::<Vec<_>>(), expected);
            }
        }
    }

    #[test]
    fn test_iter() {
        let v = (0..10).map(|x| make_obj(x * 10)).collect::<Vec<_>>();
        let mut t = RBTree::new(ObjAdapter::new());
        for x in v.iter() {
            t.insert(x.clone());
        }

        assert_eq!(
            format!("{:?}", t),
            "{0, 10, 20, 30, 40, 50, 60, 70, 80, 90}"
        );

        assert_eq!(
            t.iter().clone().map(|x| x.value).collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            (&t).into_iter().rev().map(|x| x.value).collect::<Vec<_>>(),
            vec![90, 80, 70, 60, 50, 40, 30, 20, 10, 0]
        );
        assert_eq!(
            t.range(Unbounded, Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
        );

        assert_eq!(
            t.range(Included(&0), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            t.range(Excluded(&0), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![10, 20, 30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            t.range(Included(&25), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            t.range(Excluded(&25), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            t.range(Included(&70), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![70, 80, 90]
        );
        assert_eq!(
            t.range(Excluded(&70), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![80, 90]
        );
        assert_eq!(
            t.range(Included(&100), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&100), Unbounded)
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );

        assert_eq!(
            t.range(Unbounded, Included(&90))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]
        );
        assert_eq!(
            t.range(Unbounded, Excluded(&90))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70, 80]
        );
        assert_eq!(
            t.range(Unbounded, Included(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20]
        );
        assert_eq!(
            t.range(Unbounded, Excluded(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20]
        );
        assert_eq!(
            t.range(Unbounded, Included(&70))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60, 70]
        );
        assert_eq!(
            t.range(Unbounded, Excluded(&70))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![0, 10, 20, 30, 40, 50, 60]
        );
        assert_eq!(
            t.range(Unbounded, Included(&-1))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Unbounded, Excluded(&-1))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );

        assert_eq!(
            t.range(Included(&25), Included(&80))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70, 80]
        );
        assert_eq!(
            t.range(Included(&25), Excluded(&80))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70]
        );
        assert_eq!(
            t.range(Excluded(&25), Included(&80))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70, 80]
        );
        assert_eq!(
            t.range(Excluded(&25), Excluded(&80))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![30, 40, 50, 60, 70]
        );

        assert_eq!(
            t.range(Included(&25), Included(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Included(&25), Excluded(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&25), Included(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&25), Excluded(&25))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );

        assert_eq!(
            t.range(Included(&50), Included(&50))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![50]
        );
        assert_eq!(
            t.range(Included(&50), Excluded(&50))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&50), Included(&50))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&50), Excluded(&50))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );

        assert_eq!(
            t.range(Included(&100), Included(&-2))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Included(&100), Excluded(&-2))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&100), Included(&-2))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );
        assert_eq!(
            t.range(Excluded(&100), Excluded(&-2))
                .map(|x| x.value)
                .collect::<Vec<_>>(),
            vec![]
        );

        let mut v2 = Vec::new();
        for x in t.take() {
            v2.push(x.value);
        }
        assert_eq!(v2, vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert!(t.is_empty());
        for _ in t.take() {
            unreachable!();
        }

        for x in v.iter() {
            t.insert(x.clone());
        }
        v2.clear();
        for x in t.into_iter().rev() {
            v2.push(x.value);
        }
        assert_eq!(v2, vec![90, 80, 70, 60, 50, 40, 30, 20, 10, 0]);
    }

    #[test]
    fn test_find() {
        let v = (0..10).map(|x| make_obj(x * 10)).collect::<Vec<_>>();
        let mut t = RBTree::new(ObjAdapter::new());
        for x in v.iter() {
            t.insert(x.clone());
        }

        for i in -9..100 {
            fn mod10(x: i32) -> i32 {
                if x < 0 {
                    10 + x % 10
                } else {
                    x % 10
                }
            }
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
            {
                let c = t.upper_bound(Unbounded);
                assert_eq!(c.get().map(|x| x.value), Some(90));
            }
            {
                let c = t.upper_bound_mut(Unbounded);
                assert_eq!(c.get().map(|x| x.value), Some(90));
            }
            {
                let c = t.upper_bound(Included(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i >= 0 { Some(i - mod10(i)) } else { None }
                );
            }
            {
                let c = t.upper_bound_mut(Included(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i >= 0 { Some(i - mod10(i)) } else { None }
                );
            }
            {
                let c = t.upper_bound(Excluded(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i > 0 {
                        Some(i - 1 - mod10(i - 1))
                    } else {
                        None
                    }
                );
            }
            {
                let c = t.upper_bound_mut(Excluded(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i > 0 {
                        Some(i - 1 - mod10(i - 1))
                    } else {
                        None
                    }
                );
            }
            {
                let c = t.lower_bound(Unbounded);
                assert_eq!(c.get().map(|x| x.value), Some(0));
            }
            {
                let c = t.lower_bound_mut(Unbounded);
                assert_eq!(c.get().map(|x| x.value), Some(0));
            }
            {
                let c = t.lower_bound(Included(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i <= 90 {
                        Some((i + 9) - mod10(i + 9))
                    } else {
                        None
                    }
                );
            }
            {
                let c = t.lower_bound_mut(Included(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i <= 90 {
                        Some((i + 9) - mod10(i + 9))
                    } else {
                        None
                    }
                );
            }
            {
                let c = t.lower_bound(Excluded(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i < 90 {
                        Some((i + 10) - mod10(i + 10))
                    } else {
                        None
                    }
                );
            }
            {
                let c = t.lower_bound_mut(Excluded(&i));
                assert_eq!(
                    c.get().map(|x| x.value),
                    if i < 90 {
                        Some((i + 10) - mod10(i + 10))
                    } else {
                        None
                    }
                );
            }
        }
    }

    #[test]
    fn test_fast_clear() {
        let mut t = RBTree::new(ObjAdapter::new());
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
    fn test_entry() {
        let mut t = RBTree::new(ObjAdapter::new());
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let d = make_obj(4);
        let e = make_obj(5);
        let f = make_obj(6);
        t.entry(&3).or_insert(c.clone());
        t.entry(&2).or_insert(b.clone());
        t.entry(&1).or_insert(a.clone());

        match t.entry(&2) {
            Entry::Vacant(_) => unreachable!(),
            Entry::Occupied(c) => assert_eq!(c.get().unwrap().value, 2),
        }
        assert_eq!(t.entry(&2).or_insert(b.clone()).get().unwrap().value, 2);
        assert_eq!(
            t.entry(&2)
                .or_insert_with(|| b.clone())
                .get()
                .unwrap()
                .value,
            2
        );

        match t.entry(&5) {
            Entry::Vacant(c) => assert_eq!(c.insert(e.clone()).get().unwrap().value, 5),
            Entry::Occupied(_) => unreachable!(),
        }
        assert!(e.link.is_linked());
        assert_eq!(t.entry(&4).or_insert(d.clone()).get().unwrap().value, 4);
        assert!(d.link.is_linked());
        assert_eq!(
            t.entry(&6)
                .or_insert_with(|| f.clone())
                .get()
                .unwrap()
                .value,
            6
        );
        assert!(f.link.is_linked());
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a, T: 'a> {
            link: Link,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link: Link} where T: 'a);
        impl<'a, 'b, T: 'a + 'b> KeyAdapter<'a> for ObjAdapter<'b, T> {
            type Key = &'a T;
            fn get_key(&self, value: &'a Obj<'b, T>) -> &'a T {
                value.value
            }
        }

        let v = 5;
        let a = Obj {
            link: Link::default(),
            value: &v,
        };
        let b = a.clone();
        let mut l = RBTree::new(ObjAdapter(PhantomData));
        l.insert(&a);
        l.insert(&b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
    }
}
