// Copyright 2020 Amari Robinson
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use crate::Bound::{self, Excluded, Included, Unbounded};
use crate::IntrusivePointer;
use core::borrow::Borrow;
use core::cell::Cell;
use core::cmp::Ordering;
use core::fmt;
use core::mem;
use core::ptr;

use crate::custom_links::{Adapter, KeyAdapter};


// =============================================================================
// Link
// =============================================================================

/// Intrusive link that allows an object to be inserted into a `RBTree`.
pub trait Link<NodeRef> {
    /// Returns the reference to the "left" object.
    fn left(&self) -> NodeRef;

    /// Returns the reference to the "right" object.
    fn right(&self) -> NodeRef;

    /// Returns the reference to the "parent" object.
    fn parent(&self) -> NodeRef;

    fn color(&self) -> Color;

    /// Sets the reference to the "left" object.
    fn set_left(&self, left: NodeRef);

    /// Sets the reference to the "right" object.
    fn set_right(&self, right: NodeRef);

    /// Sets the reference to the "parent" object.
    fn set_parent(&self, parent: NodeRef);

    fn set_color(&self, color: Color);

    /// Checks whether the `Link` is linked into a `RBTree`.
    fn is_linked(&self) -> bool;

    /// Forcibly unlinks an object from a `RBTree`.
    ///
    /// # Safety
    ///
    /// It is undefined behavior to call this function while still linked into a
    /// `RBTree`. The only situation where this function is useful is
    /// after calling `fast_clear` on a `RBTree`, since this clears
    /// the collection without marking the nodes as unlinked.
    unsafe fn force_unlink(&self);
}


// =============================================================================
// NodeRef
// =============================================================================

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Color {
    Red,
    Black,
}

/// A reference to an object that can be inserted into a `RBTRee`.
pub trait NodeRef: Copy + Eq {
    /// Constructs a "null" `NodeRef`.
    fn null() -> Self;


    /// Returns `true` if `self == Self::null()`.
    fn is_null(self) -> bool;

    /// Returns the reference to the "left" object.
    #[inline]
    unsafe fn left<A>(self, adapter: &A) -> Self
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).left()
    }

    /// Returns the reference to the "right" object.
    #[inline]
    unsafe fn right<A>(self, adapter: &A) -> Self
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).right()
    }

    /// Returns the reference to the "parent" object.
    #[inline]
    unsafe fn parent<A>(self, adapter: &A) -> Self
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).parent()
    }

    #[inline]
    unsafe fn color<A>(self, adapter: &A) -> Color
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).color()
    }

    /// Sets the reference to the "left" object.
    #[inline]
    unsafe fn set_left<A>(self, adapter: &A, left: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).set_left(left);
    }

    /// Sets the reference to the "right" object.
    #[inline]
    unsafe fn set_right<A>(self, adapter: &A, right: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).set_right(right);
    }

    /// Sets the reference to the "parent" object.
    #[inline]
    unsafe fn set_parent<A>(self, adapter: &A, parent: Self)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).set_parent(parent);
    }

    #[inline]
    unsafe fn set_color<A>(self, adapter: &A, color: Color)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (&*adapter.node_into_link(self)).set_color(color);
    }

    #[inline]
    unsafe fn set_parent_color<A>(self, adapter: &A, parent: Self, color: Color)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        self.set_parent(adapter, parent);
        self.set_color(adapter, color);
    }

    /// Sets the "unlinked marker".
    unsafe fn unlink<A>(self, adapter: &A)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>;

    #[doc(hidden)]
    #[inline]
    unsafe fn is_left_child<A>(self, adapter: &A) -> bool
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        self.parent(adapter).left(adapter) == self
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn first_child<A>(self, adapter: &A) -> A::NodeRef
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if self.is_null() {
            A::NodeRef::null()
        } else {
            let mut x = self;
            while !x.left(adapter).is_null() {
                x = x.left(adapter);
            }
            x
        }
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn last_child<A>(self, adapter: &A) -> A::NodeRef
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if self.is_null() {
            A::NodeRef::null()
        } else {
            let mut x = self;
            while !x.right(adapter).is_null() {
                x = x.right(adapter);
            }
            x
        }
    }

    #[doc(hidden)]
    unsafe fn next<A>(self, adapter: &A) -> A::NodeRef
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if !self.right(adapter).is_null() {
            self.right(adapter).first_child(adapter)
        } else {
            let mut x = self;
            loop {
                if x.parent(adapter).is_null() {
                    return A::NodeRef::null();
                }
                if x.is_left_child(adapter) {
                    return x.parent(adapter);
                }
                x = x.parent(adapter);
            }
        }
    }

    #[doc(hidden)]
    unsafe fn prev<A>(self, adapter: &A) -> A::NodeRef
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if !self.left(adapter).is_null() {
            self.left(adapter).last_child(adapter)
        } else {
            let mut x = self;
            loop {
                if x.parent(adapter).is_null() {
                    return A::NodeRef::null();
                }
                if !x.is_left_child(adapter) {
                    return x.parent(adapter);
                }
                x = x.parent(adapter);
            }
        }
    }

    #[doc(hidden)]
    unsafe fn replace_with<A>(self, adapter: &A, new: A::NodeRef, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        if self.parent(adapter).is_null() {
            *root = new;
        } else if self.is_left_child(adapter) {
            self.parent(adapter).set_left(adapter, new);
        } else {
            self.parent(adapter).set_right(adapter, new);
        }
        if !self.left(adapter).is_null() {
            self.left(adapter).set_parent(adapter, new);
        }
        if !self.right(adapter).is_null() {
            self.right(adapter).set_parent(adapter, new);
        }
        new.set_left(adapter, self.left(adapter));
        new.set_right(adapter, self.right(adapter));
        new.set_parent_color(adapter, self.parent(adapter), self.color(adapter));
        self.unlink(adapter);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn insert_left<A>(self, adapter: &A, new: A::NodeRef, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        new.set_parent_color(adapter, self, Color::Red);
        new.set_left(adapter, A::NodeRef::null());
        new.set_right(adapter, A::NodeRef::null());
        self.set_left(adapter, new);
        new.post_insert(adapter, root);
    }

    #[doc(hidden)]
    #[inline]
    unsafe fn insert_right<A>(self, adapter: &A, new: A::NodeRef, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        new.set_parent_color(adapter, self, Color::Red);
        new.set_left(adapter, A::NodeRef::null());
        new.set_right(adapter, A::NodeRef::null());
        self.set_right(adapter, new);
        new.post_insert(adapter, root);
    }

    #[doc(hidden)]
    unsafe fn rotate_left<A>(self, adapter: &A, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        let y = self.right(adapter);
        self.set_right(adapter, y.left(adapter));
        if !self.right(adapter).is_null() {
            self.right(adapter).set_parent(adapter, self);
        }
        y.set_parent(adapter, self.parent(adapter));
        if self.parent(adapter).is_null() {
            *root = y;
        } else if self.is_left_child(adapter) {
            self.parent(adapter).set_left(adapter, y);
        } else {
            self.parent(adapter).set_right(adapter, y);
        }
        y.set_left(adapter, self);
        self.set_parent(adapter, y);
    }

    #[doc(hidden)]
    unsafe fn rotate_right<A>(self, adapter: &A, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        let y = self.left(adapter);
        self.set_left(adapter, y.right(adapter));
        if !self.left(adapter).is_null() {
            self.left(adapter).set_parent(adapter, self);
        }
        y.set_parent(adapter, self.parent(adapter));
        if self.parent(adapter).is_null() {
            *root = y;
        } else if self.is_left_child(adapter) {
            self.parent(adapter).set_left(adapter, y);
        } else {
            self.parent(adapter).set_right(adapter, y);
        }
        y.set_right(adapter, self);
        self.set_parent(adapter, y);
    }

    // This code is based on the red-black tree implementation in libc++
    #[doc(hidden)]
    unsafe fn post_insert<A>(self, adapter: &A, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        let mut x = self;
        while !x.parent(adapter).is_null() && x.parent(adapter).color(adapter) == Color::Red {
            if x.parent(adapter).is_left_child(adapter) {
                let y = x.parent(adapter).parent(adapter).right(adapter);
                if !y.is_null() && y.color(adapter) == Color::Red {
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Black);
                    x = x.parent(adapter);
                    if x.parent(adapter).is_null() {
                        x.set_color(adapter, Color::Black);
                    } else {
                        x.set_color(adapter, Color::Red);
                    }
                    y.set_color(adapter, Color::Black);
                } else {
                    if !x.is_left_child(adapter) {
                        x = x.parent(adapter);
                        x.rotate_left(adapter, root);
                    }
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Black);
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Red);
                    x.rotate_right(adapter, root);
                    break;
                }
            } else {
                let y = x.parent(adapter).parent(adapter).left(adapter);
                if !y.is_null() && y.color(adapter) == Color::Red {
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Black);
                    x = x.parent(adapter);
                    if x.parent(adapter).is_null() {
                        x.set_color(adapter, Color::Black);
                    } else {
                        x.set_color(adapter, Color::Red);
                    }
                    y.set_color(adapter, Color::Black);
                } else {
                    if x.is_left_child(adapter) {
                        x = x.parent(adapter);
                        x.rotate_right(adapter, root);
                    }
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Black);
                    x = x.parent(adapter);
                    x.set_color(adapter, Color::Red);
                    x.rotate_left(adapter, root);
                    break;
                }
            }
        }
    }

    // This code is based on the red-black tree implementation in libc++
    #[doc(hidden)]
    unsafe fn remove<A>(self, adapter: &A, root: &mut A::NodeRef)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>,
    {
        let y = if self.left(adapter).is_null() || self.right(adapter).is_null() {
            self
        } else {
            self.next(adapter)
        };
        let mut x = if !y.left(adapter).is_null() {
            y.left(adapter)
        } else {
            y.right(adapter)
        };
        let mut w = A::NodeRef::null();
        if !x.is_null() {
            x.set_parent(adapter, y.parent(adapter));
        }
        if y.parent(adapter).is_null() {
            *root = x;
        } else if y.is_left_child(adapter) {
            y.parent(adapter).set_left(adapter, x);
            w = y.parent(adapter).right(adapter);
        } else {
            y.parent(adapter).set_right(adapter, x);
            w = y.parent(adapter).left(adapter);
        }
        let removed_black = y.color(adapter) == Color::Black;
        if y != self {
            y.set_parent(adapter, self.parent(adapter));
            if self.parent(adapter).is_null() {
                *root = y;
            } else if self.is_left_child(adapter) {
                y.parent(adapter).set_left(adapter, y);
            } else {
                y.parent(adapter).set_right(adapter, y);
            }
            y.set_left(adapter, self.left(adapter));
            y.left(adapter).set_parent(adapter, y);
            y.set_right(adapter, self.right(adapter));
            if !y.right(adapter).is_null() {
                y.right(adapter).set_parent(adapter, y);
            }
            y.set_color(adapter, self.color(adapter));
        }
        if removed_black && !root.is_null() {
            if !x.is_null() {
                x.set_color(adapter, Color::Black);
            } else {
                loop {
                    if !w.is_left_child(adapter) {
                        if w.color(adapter) == Color::Red {
                            w.set_color(adapter, Color::Black);
                            w.parent(adapter).set_color(adapter, Color::Red);
                            w.parent(adapter).rotate_left(adapter, root);
                            w = w.left(adapter).right(adapter);
                        }
                        if (w.left(adapter).is_null() || w.left(adapter).color(adapter) == Color::Black)
                            && (w.right(adapter).is_null() || w.right(adapter).color(adapter) == Color::Black)
                        {
                            w.set_color(adapter, Color::Red);
                            x = w.parent(adapter);
                            if x.parent(adapter).is_null() || x.color(adapter) == Color::Red {
                                x.set_color(adapter, Color::Black);
                                break;
                            }
                            w = if x.is_left_child(adapter) {
                                x.parent(adapter).right(adapter)
                            } else {
                                x.parent(adapter).left(adapter)
                            };
                        } else {
                            if w.right(adapter).is_null() || w.right(adapter).color(adapter) == Color::Black {
                                w.left(adapter).set_color(adapter, Color::Black);
                                w.set_color(adapter, Color::Red);
                                w.rotate_right(adapter, root);
                                w = w.parent(adapter);
                            }
                            w.set_color(adapter, w.parent(adapter).color(adapter));
                            w.parent(adapter).set_color(adapter, Color::Black);
                            w.right(adapter).set_color(adapter, Color::Black);
                            w.parent(adapter).rotate_left(adapter, root);
                            break;
                        }
                    } else {
                        if w.color(adapter) == Color::Red {
                            w.set_color(adapter, Color::Black);
                            w.parent(adapter).set_color(adapter, Color::Red);
                            w.parent(adapter).rotate_right(adapter, root);
                            w = w.right(adapter).left(adapter);
                        }
                        if (w.left(adapter).is_null() || w.left(adapter).color(adapter) == Color::Black)
                            && (w.right(adapter).is_null() || w.right(adapter).color(adapter) == Color::Black)
                        {
                            w.set_color(adapter, Color::Red);
                            x = w.parent(adapter);
                            if x.parent(adapter).is_null() || x.color(adapter) == Color::Red {
                                x.set_color(adapter, Color::Black);
                                break;
                            }
                            w = if x.is_left_child(adapter) {
                                x.parent(adapter).right(adapter)
                            } else {
                                x.parent(adapter).left(adapter)
                            };
                        } else {
                            if w.left(adapter).is_null() || w.left(adapter).color(adapter) == Color::Black {
                                w.right(adapter).set_color(adapter, Color::Black);
                                w.set_color(adapter, Color::Red);
                                w.rotate_left(adapter, root);
                                w = w.parent(adapter);
                            }
                            w.set_color(adapter, w.parent(adapter).color(adapter));
                            w.parent(adapter).set_color(adapter, Color::Black);
                            w.left(adapter).set_color(adapter, Color::Black);
                            w.parent(adapter).rotate_right(adapter, root);
                            break;
                        }
                    }
                }
            }
        }
        self.unlink(adapter);
    }
}

// =============================================================================
// Cursor, CursorMut
// =============================================================================

/// A cursor which provides read-only access to a `RBTree`.
pub struct Cursor<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    current: A::NodeRef,
    tree: &'a RBTree<A>,
}

impl<'a, A: Adapter + 'a> Clone for Cursor<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            tree: self.tree,
        }
    }
}

impl<'a, A: Adapter + 'a> Cursor<'a, A>
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
            let adapter = &self.tree.adapter;
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

    /// Moves the cursor to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will move it to
    /// the first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will move it to the null object.
    #[inline]
    pub fn move_next(&mut self) {
        if self.is_null() {
            self.current = unsafe { self.tree.root.first_child(&self.tree.adapter) };
        } else {
            self.current = unsafe { self.current.next(&self.tree.adapter) };
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
            self.current = unsafe { self.tree.root.last_child(&self.tree.adapter) };
        } else {
            self.current = unsafe { self.current.prev(&self.tree.adapter) };
        }
    }

    /// Returns a cursor pointing to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
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
    pub fn peek_prev(&self) -> Cursor<'_, A> {
        let mut prev = self.clone();
        prev.move_prev();
        prev
    }
}

/// A cursor which provides mutable access to a `RBTree`.
pub struct CursorMut<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    current: A::NodeRef,
    tree: &'a mut RBTree<A>,
}

impl<'a, A: Adapter + 'a> CursorMut<'a, A>
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
            let adapter = &self.tree.adapter;
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
            self.current = unsafe { self.tree.root.first_child(&self.tree.adapter) };
        } else {
            self.current = unsafe { self.current.next(&self.tree.adapter) };
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
            self.current = unsafe { self.tree.root.last_child(&self.tree.adapter) };
        } else {
            self.current = unsafe { self.current.prev(&self.tree.adapter) };
        }
    }

    /// Returns a cursor pointing to the next element of the `RBTree`.
    ///
    /// If the cursor is pointer to the null object then this will return the
    /// first element of the `RBTree`. If it is pointing to the last
    /// element of the `RBTree` then this will return a null cursor.
    #[inline]
    pub fn peek_next(&self) -> Cursor<'_, A> {
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
    pub fn peek_prev(&self) -> Cursor<'_, A> {
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
            let next = self.current.next(&self.tree.adapter);
            let result = self.current;
            self.current.remove(&self.tree.adapter, &mut self.tree.root);
            self.current = next;
            Some(unsafe { self.tree.adapter.node_into_pointer(result) })
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
            let result = self.current;
            self.current.replace_with(&self.tree.adapter, new, &mut self.tree.root);
            self.current = new;
            Ok(unsafe { self.tree.adapter.node_into_pointer(result) })
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
                    .first_child(&self.tree.adapter)
                    .insert_left(&self.tree.adapter, new, &mut self.tree.root);
            } else if self.current.right(&self.tree.adapter).is_null() {
                self.current.insert_right(&self.tree.adapter, new, &mut self.tree.root);
            } else {
                self.current.next(&self.tree.adapter).insert_left(&self.tree.adapter, new, &mut self.tree.root);
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
                    .last_child(&self.tree.adapter)
                    .insert_right(&self.tree.adapter, new, &mut self.tree.root);
            } else if self.current.left(&self.tree.adapter).is_null() {
                self.current.insert_left(&self.tree.adapter, new, &mut self.tree.root);
            } else {
                self.current.prev(&self.tree.adapter).insert_right(&self.tree.adapter, new, &mut self.tree.root);
            }
        }
    }
}

impl<'a, A: for<'b> KeyAdapter<'b>> CursorMut<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
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
pub struct RBTree<A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    root: A::NodeRef,
    adapter: A,
}

impl<A: Adapter> RBTree<A>
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

    /// Creates an empty `RBTree`.
    #[inline]
    pub fn new(adapter: A) -> RBTree<A> {
        RBTree {
            root: A::NodeRef::null(),
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
    pub fn cursor(&self) -> Cursor<'_, A> {
        Cursor {
            current: A::NodeRef::null(),
            tree: self,
        }
    }

    /// Returns a null `CursorMut` for this tree.
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, A> {
        CursorMut {
            current: A::NodeRef::null(),
            tree: self,
        }
    }

    /// Creates a `Cursor` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this tree.
    #[inline]
    pub unsafe fn cursor_from_ptr(&self, ptr: *const A::Value) -> Cursor<'_, A> {
        Cursor {
            current: self.adapter.node_from_link(self.adapter.get_link(ptr)),
            tree: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this tree.
    #[inline]
    pub unsafe fn cursor_mut_from_ptr(&mut self, ptr: *const A::Value) -> CursorMut<'_, A> {
        CursorMut {
            current: self.adapter.node_from_link(self.adapter.get_link(ptr)),
            tree: self,
        }
    }

    /// Returns a `Cursor` pointing to the first element of the tree. If the
    /// tree is empty then a null cursor is returned.
    #[inline]
    pub fn front(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_next();
        cursor
    }

    /// Returns a `CursorMut` pointing to the first element of the tree. If the
    /// the tree is empty then a null cursor is returned.
    #[inline]
    pub fn front_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_next();
        cursor
    }

    /// Returns a `Cursor` pointing to the last element of the tree. If the tree
    /// is empty then a null cursor is returned.
    #[inline]
    pub fn back(&self) -> Cursor<'_, A> {
        let mut cursor = self.cursor();
        cursor.move_prev();
        cursor
    }

    /// Returns a `CursorMut` pointing to the last element of the tree. If the
    /// tree is empty then a null cursor is returned.
    #[inline]
    pub fn back_mut(&mut self) -> CursorMut<'_, A> {
        let mut cursor = self.cursor_mut();
        cursor.move_prev();
        cursor
    }

    #[inline]
    unsafe fn insert_root(&mut self, node: A::NodeRef) {
        node.set_parent_color(&self.adapter, A::NodeRef::null(), Color::Black);
        node.set_left(&self.adapter, A::NodeRef::null());
        node.set_right(&self.adapter, A::NodeRef::null());
        self.root = node;
    }

    /// Gets an iterator over the objects in the `RBTree`, in ascending key
    /// order.
    #[inline]
    pub fn iter(&self) -> Iter<'_, A> {
        if self.root.is_null() {
            Iter {
                head: A::NodeRef::null(),
                tail: A::NodeRef::null(),
                tree: self,
            }
        } else {
            Iter {
                head: unsafe { self.root.first_child(&self.adapter) },
                tail: unsafe { self.root.last_child(&self.adapter) },
                tree: self,
            }
        }
    }

    #[inline]
    fn clear_recurse(&mut self, current: A::NodeRef) {
        // If adapter.get_value or Pointer::from_raw panic here, it will leak
        // the nodes and keep them linked. However this is harmless since there
        // is nothing you can do with just a Link.
        if !current.is_null() {
            unsafe {
                self.clear_recurse(current.left(&self.adapter));
                self.clear_recurse(current.right(&self.adapter));
                current.unlink(&self.adapter);
                self.adapter.node_into_pointer(current);
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
        self.root = A::NodeRef::null();
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
        self.root = A::NodeRef::null();
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
        self.root = A::NodeRef::null();
        tree
    }
}

impl<A: for<'a> KeyAdapter<'a>> RBTree<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn find_internal<'a, Q: ?Sized + Ord>(&self, key: &Q) -> A::NodeRef
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(self.adapter.node_into_link(tree)) };
            match key.cmp(self.adapter.get_key(current).borrow()) {
                Ordering::Less => tree = unsafe { tree.left(&self.adapter) },
                Ordering::Equal => return tree,
                Ordering::Greater => tree = unsafe { tree.right(&self.adapter) },
            }
        }
        A::NodeRef::null()
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
    fn lower_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> A::NodeRef
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        let mut result = A::NodeRef::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(self.adapter.node_into_link(tree)) };
            let cond = match bound {
                Unbounded => true,
                Included(key) => key <= self.adapter.get_key(current).borrow(),
                Excluded(key) => key < self.adapter.get_key(current).borrow(),
            };
            if cond {
                result = tree;
                tree = unsafe { tree.left(&self.adapter) };
            } else {
                tree = unsafe { tree.right(&self.adapter) };
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
    fn upper_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> A::NodeRef
    where
        <A as KeyAdapter<'a>>::Key: Borrow<Q>,
        A::Value: 'a,
    {
        let mut tree = self.root;
        let mut result = A::NodeRef::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adapter.get_value(self.adapter.node_into_link(tree)) };
            let cond = match bound {
                Unbounded => false,
                Included(key) => key < self.adapter.get_key(current).borrow(),
                Excluded(key) => key <= self.adapter.get_key(current).borrow(),
            };
            if cond {
                tree = unsafe { tree.left(&self.adapter) };
            } else {
                result = tree;
                tree = unsafe { tree.right(&self.adapter) };
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
    pub fn insert<'a>(&'a mut self, val: A::Pointer) -> CursorMut<'_, A>
    where
        <A as KeyAdapter<'a>>::Key: Ord,
    {
        unsafe {
            let new = self.node_from_value(val);
            let raw = self.adapter.get_value(self.adapter.node_into_link(new));
            if self.is_empty() {
                self.insert_root(new);
            } else {
                let key = self.adapter.get_key(&*raw);
                let mut tree = self.root;
                loop {
                    let current = &*self.adapter.get_value(self.adapter.node_into_link(tree));
                    if key < self.adapter.get_key(current) {
                        if tree.left(&self.adapter).is_null() {
                            tree.insert_left(&self.adapter, new, &mut self.root);
                            break;
                        } else {
                            tree = tree.left(&self.adapter);
                        }
                    } else {
                        if tree.right(&self.adapter).is_null() {
                            tree.insert_right(&self.adapter, new, &mut self.root);
                            break;
                        } else {
                            tree = tree.right(&self.adapter);
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
                    parent: A::NodeRef::null(),
                    insert_left: false,
                    tree: self,
                })
            } else {
                let mut tree = self.root;
                loop {
                    let current = &*self.adapter.get_value(self.adapter.node_into_link(tree));
                    match key.cmp(self.adapter.get_key(current).borrow()) {
                        Ordering::Less => {
                            if tree.left(&self.adapter).is_null() {
                                return Entry::Vacant(InsertCursor {
                                    parent: tree,
                                    insert_left: true,
                                    tree: self,
                                });
                            } else {
                                tree = tree.left(&self.adapter);
                            }
                        }
                        Ordering::Equal => {
                            return Entry::Occupied(CursorMut {
                                current: tree,
                                tree: self,
                            });
                        }
                        Ordering::Greater => {
                            if tree.right(&self.adapter).is_null() {
                                return Entry::Vacant(InsertCursor {
                                    parent: tree,
                                    insert_left: false,
                                    tree: self,
                                });
                            } else {
                                tree = tree.right(&self.adapter);
                            }
                        }
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
            let lower_key = unsafe { self.adapter.get_key(&*self.adapter.get_value(self.adapter.node_into_link(lower))) };
            let upper_key = unsafe { self.adapter.get_key(&*self.adapter.get_value(self.adapter.node_into_link(upper))) };
            if upper_key >= lower_key {
                return Iter {
                    head: lower,
                    tail: upper,
                    tree: self,
                };
            }
        }
        Iter {
            head: A::NodeRef::null(),
            tail: A::NodeRef::null(),
            tree: self,
        }
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: Adapter + Sync> Sync for RBTree<A> where A::Value: Sync, A::NodeRef: NodeRef,
A::Link: Link<A::NodeRef>, {}

// Allow sending to another thread if the ownership (represented by the A::Pointer owned
// pointer type) can be transferred to another thread.
unsafe impl<A: Adapter + Send> Send for RBTree<A> where A::Pointer: Send, A::NodeRef: NodeRef,
A::Link: Link<A::NodeRef>, {}

// Drop all owned pointers if the collection is dropped
impl<A: Adapter> Drop for RBTree<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn drop(&mut self) {
        self.clear();
    }
}

impl<A: Adapter> IntoIterator for RBTree<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = A::Pointer;
    type IntoIter = IntoIter<A>;

    #[inline]
    fn into_iter(self) -> IntoIter<A> {
        if self.root.is_null() {
            IntoIter {
                head: A::NodeRef::null(),
                tail: A::NodeRef::null(),
                tree: self,
            }
        } else {
            IntoIter {
                head: unsafe { self.root.first_child(&self.adapter) },
                tail: unsafe { self.root.last_child(&self.adapter) },
                tree: self,
            }
        }
    }
}

impl<'a, A: Adapter + 'a> IntoIterator for &'a RBTree<A>
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

impl<A: Adapter + Default> Default for RBTree<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    fn default() -> RBTree<A> {
        RBTree::new(A::default())
    }
}

impl<A: Adapter> fmt::Debug for RBTree<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
    A::Value: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

// =============================================================================
// InsertCursor, Entry
// =============================================================================

/// A cursor pointing to a slot in which an element can be inserted into a
/// `RBTree`.
pub struct InsertCursor<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    parent: A::NodeRef,
    insert_left: bool,
    tree: &'a mut RBTree<A>,
}

impl<'a, A: Adapter + 'a> InsertCursor<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
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
                self.parent.insert_left(&self.tree.adapter, new, &mut self.tree.root);
            } else {
                self.parent.insert_right(&self.tree.adapter, new, &mut self.tree.root);
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
pub enum Entry<'a, A: Adapter + 'a>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    /// An occupied entry.
    Occupied(CursorMut<'a, A>),

    /// A vacant entry.
    Vacant(InsertCursor<'a, A>),
}

impl<'a, A: Adapter + 'a> Entry<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
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
pub struct Iter<'a, A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    head: A::NodeRef,
    tail: A::NodeRef,
    tree: &'a RBTree<A>,
}
impl<'a, A: Adapter + 'a> Iterator for Iter<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    type Item = &'a A::Value;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Value> {
        if self.head.is_null() {
            None
        } else {
            let head = self.head;
            if head == self.tail {
                self.head = A::NodeRef::null();
                self.tail = A::NodeRef::null();
            } else {
                self.head = unsafe { head.next(&self.tree.adapter) };
            }
            Some(unsafe {
                &*self
                    .tree
                    .adapter
                    .get_value(self.tree.adapter.node_into_link(head))
            })
        }
    }
}
impl<'a, A: Adapter + 'a> DoubleEndedIterator for Iter<'a, A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    #[inline]
    fn next_back(&mut self) -> Option<&'a A::Value> {
        if self.tail.is_null() {
            None
        } else {
            let tail = self.tail;
            if self.head == tail {
                self.tail = A::NodeRef::null();
                self.head = A::NodeRef::null();
            } else {
                self.tail = unsafe { tail.prev(&self.tree.adapter) };
            }
            Some(unsafe {
                &*self
                    .tree
                    .adapter
                    .get_value(self.tree.adapter.node_into_link(tail))
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
pub struct IntoIter<A: Adapter>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
    head: A::NodeRef,
    tail: A::NodeRef,
    tree: RBTree<A>,
}
impl<A: Adapter> Iterator for IntoIter<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
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
                let parent = head.parent(&self.tree.adapter);
                let right = head.right(&self.tree.adapter);
                if parent.is_null() {
                    self.tree.root = right;
                    if right.is_null() {
                        self.tail = A::NodeRef::null();
                    }
                } else {
                    parent.set_left(&self.tree.adapter, right);
                }
                if right.is_null() {
                    self.head = parent;
                } else {
                    right.set_parent(&self.tree.adapter, parent);
                    self.head = right.first_child(&self.tree.adapter);
                }
                head.unlink(&self.tree.adapter);
                
                Some(self.tree.adapter.node_into_pointer(head))
            }
        }
    }
}
impl<A: Adapter> DoubleEndedIterator for IntoIter<A>
where
    A::NodeRef: NodeRef,
    A::Link: Link<A::NodeRef>,
{
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
                let parent = tail.parent(&self.tree.adapter);
                let left = tail.left(&self.tree.adapter);
                if parent.is_null() {
                    self.tree.root = left;
                    if left.is_null() {
                        self.head = A::NodeRef::null();
                    }
                } else {
                    parent.set_right(&self.tree.adapter, left);
                }
                if left.is_null() {
                    self.tail = parent;
                } else {
                    left.set_parent(&self.tree.adapter, parent);
                    self.tail = left.last_child(&self.tree.adapter);
                }
                tail.unlink(&self.tree.adapter);
                Some(self.tree.adapter.node_into_pointer(tail))
            }
        }
    }
}

// =============================================================================
// RawLink, RawLinkRef
// =============================================================================

pub struct RawLink {
    left: Cell<RawLinkRef>,
    right: Cell<RawLinkRef>,
    parent_color: Cell<usize>,
}

impl RawLink {
    /// Creates a new `RawLink`.
    #[inline]
    pub fn new() -> RawLink {
        RawLink {
            left: Cell::new(RawLinkRef::null()),
            right: Cell::new(RawLinkRef::null()),
            parent_color: Cell::new(UNLINKED_MARKER),
        }
    }

    /// Checks whether the `RawLink` is linked into a `RBTree`.
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

impl RawLink {
    #[inline]
    fn set_parent_color(&self, parent: RawLinkRef, color: Color) {
        assert!(mem::align_of::<Self>() >= 2);
        let bit = match color {
            Color::Red => 0,
            Color::Black => 1,
        };
        self.parent_color.set((parent.0 as usize & !1) | bit);
    }
}

impl Link<RawLinkRef> for RawLink {
    /// Returns the reference to the "left" object.
    #[inline]
    fn left(&self) -> RawLinkRef {
        self.left.get()
    }

    /// Returns the reference to the "right" object.
    #[inline]
    fn right(&self) -> RawLinkRef {
        self.right.get()
    }

    /// Returns the reference to the "parent" object.
    #[inline]
    fn parent(&self) -> RawLinkRef {
        RawLinkRef((self.parent_color.get() & !1) as *const _)
    }

    #[inline]
    fn color(&self) -> Color {
        if self.parent_color.get() & 1 == 1 {
            Color::Black
        } else {
            Color::Red
        }
    }

    /// Sets the reference to the "left" object.
    #[inline]
    fn set_left(&self, left: RawLinkRef) {
        self.left.set(left);
    }

    /// Sets the reference to the "right" object.
    #[inline]
    fn set_right(&self, right: RawLinkRef) {
        self.right.set(right);
    }

    /// Sets the reference to the "parent" object.
    #[inline]
    fn set_parent(&self, parent: RawLinkRef) {
        self.set_parent_color(parent, self.color());
    }

    #[inline]
    fn set_color(&self, color: Color) {
        self.set_parent_color(self.parent(), color);
    }

    /// Checks whether the `Link` is linked into a `RBTree`.
    #[inline]
    fn is_linked(&self) -> bool {
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
    unsafe fn force_unlink(&self) {
        self.parent_color.set(UNLINKED_MARKER);
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
        // is currently in a tree.
        if self.is_linked() {
            write!(f, "linked")
        } else {
            write!(f, "unlinked")
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct RawLinkRef(*const RawLink);

// Use a special value to indicate an unlinked node. This value represents a
// red root node, which is impossible in a valid red-black tree.
const UNLINKED_MARKER: usize = 0;

impl NodeRef for RawLinkRef {
    /// Constructs a "null" `NodeRef`.
    #[inline]
    fn null() -> Self {
        RawLinkRef(ptr::null())
    }


    /// Returns `true` if `self == Self::null()`.
    #[inline]
    fn is_null(self) -> bool {
        self.0.is_null()
    }

    #[inline]
    unsafe fn set_parent_color<A>(self, adapter: &A, parent: Self, color: Color)
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (*self.0).set_parent_color(parent, color)
    }

    #[inline]
    unsafe fn unlink<A>(self, adapter: &A) 
    where
        A: Adapter<NodeRef = Self>,
        A::Link: Link<Self>
    {
        (*self.0).parent_color.set(UNLINKED_MARKER)
    }
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use self::rand::{Rng, XorShiftRng};
    use super::{Entry, Link, RBTree, RawLink, RawLinkRef};
    use crate::Bound::*;
    use crate::{KeyAdapter, UnsafeRef, IntrusivePointer};
    use rand;
    use std::boxed::Box;
    use std::fmt;
    use std::vec::Vec;

    #[derive(Clone)]
    struct Obj {
        link: RawLink,
        value: i32,
    }
    impl fmt::Debug for Obj {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.value)
        }
    }
    intrusive_adapter!(ObjAdapter = UnsafeRef<Obj>: Obj { link: RawLink });
    impl<'a> KeyAdapter<'a> for ObjAdapter {
        type Key = i32;
        fn get_key(&self, value: &'a Self::Value) -> i32 {
            value.value
        }
    }
    fn make_obj(value: i32) -> UnsafeRef<Obj> {
        UnsafeRef::from_box(Box::new(Obj {
            link: RawLink::new(),
            value: value,
        }))
    }
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
    impl<'a> crate::custom_links::KeyAdapter<'a> for ObjAdapter {
        type Key = <Self as crate::KeyAdapter<'a>>::Key;

        #[inline]
        fn get_key(&self, value: &'a Self::Value) -> Self::Key {
            <Self as crate::KeyAdapter<'a>>::get_key(self, value)
        }
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
        struct Obj<'a, T> {
            link: RawLink,
            value: &'a T,
        }
        intrusive_adapter!(ObjAdapter<'a, T> = &'a Obj<'a, T>: Obj<'a, T> {link: RawLink} where T: 'a);
        impl<'a, 'b, T: 'a + 'b> KeyAdapter<'a> for ObjAdapter<'b, T> {
            type Key = &'a T;
            fn get_key(&self, value: &'a Obj<'b, T>) -> &'a T {
                value.value
            }
        }
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
        impl<'a, 'b, T: 'a + 'b> crate::custom_links::KeyAdapter<'a> for ObjAdapter<'b, T> {
            type Key = &'a T;
    
            #[inline]
            fn get_key(&self, value: &'a Obj<'b, T>) -> &'a T {
                value.value
            }
        }

        let v = 5;
        let a = Obj {
            link: RawLink::default(),
            value: &v,
        };
        let b = a.clone();
        let mut l = RBTree::new(ObjAdapter::new());
        l.insert(&a);
        l.insert(&b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
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
            impl<'a> KeyAdapter<'a> for ObjAdapter {
                type Key = usize;
                fn get_key(&self, value: &'a Obj) -> usize {
                    value.value
                }
            }
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
            impl<'a> crate::custom_links::KeyAdapter<'a> for ObjAdapter {
                type Key = <Self as crate::KeyAdapter<'a>>::Key;
        
                #[inline]
                fn get_key(&self, value: &'a Self::Value) -> Self::Key {
                    <Self as crate::KeyAdapter<'a>>::get_key(self, value)
                }
            }

            let a = $ptr::new(Obj {
                link: RawLink::new(),
                value: 5,
            });
            let mut l = RBTree::new(ObjAdapter::new());
            l.insert(a.clone());
            assert_eq!(2, $ptr::strong_count(&a));

            let pointer = l.front().clone_pointer().unwrap();
            assert_eq!(pointer.value, 5);
            assert_eq!(3, $ptr::strong_count(&a));

            l.front_mut().remove();
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
