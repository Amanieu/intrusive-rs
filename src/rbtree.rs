// Copyright 2016 Amanieu d'Antras
//
// Licensed under the Apache License, Version 2.0, <LICENSE-APACHE or
// http://apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT or
// http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

//! Intrusive red-black tree.

use Adaptor;
use intrusive_ref::IntrusiveRef;
use Bound::{self, Included, Excluded, Unbounded};
use core::ptr;
use core::fmt;
use core::mem;
use core::cell::Cell;
use core::borrow::Borrow;
use core::cmp::Ordering;

// =============================================================================
// TreeAdaptor
// =============================================================================

/// Trait which provides a way of extracting a key from an intrusive object.
/// This key is used to maintain all elements in the tree in increasing order.
/// The key can be returned either as a reference or as a value.
///
/// Note that you are responsible for ensuring that the elements in a `RBTree`
/// remain in ascending key order. This property can be violated, either because
/// the key of an element was modified, or because the
/// `insert_before`/`insert_after` methods of `CursorMut` were incorrectly used.
/// If this situation occurs, memory safety will not be violated but the `find`,
/// `upper_bound`, `lower_bound` and `range` may return incorrect results.
///
/// # Examples
///
/// ```
/// #[macro_use]
/// extern crate intrusive_collections;
/// use intrusive_collections::{rbtree, TreeAdaptor};
///
/// struct S {
///     link: rbtree::Link,
///     key: u32,
///     value: u64,
/// }
///
/// intrusive_adaptor!(MyAdaptor = S { link : rbtree::Link });
/// impl<'a> TreeAdaptor<'a> for MyAdaptor {
///     type Key = u32;
///     fn get_key(&self, s: &'a S) -> u32 { s.key }
/// }
///
/// // Alternative implementation returning the key by reference
/// intrusive_adaptor!(MyAdaptor2 = S { link : rbtree::Link });
/// impl<'a> TreeAdaptor<'a> for MyAdaptor2 {
///     type Key = &'a u32;
///     fn get_key(&self, s: &'a S) -> &'a u32 { &s.key }
/// }
/// # fn main() {}
/// ```
pub trait TreeAdaptor<'a>: Adaptor<Link> {
    /// Type of the key returned by `get_key`.
    type Key: Ord;

    /// Gets the key for the given object.
    fn get_key(&self, container: &'a Self::Container) -> Self::Key;
}

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

    /// Checks whether the `Link` is linked into a `LinkedList`.
    #[inline]
    pub fn is_linked(&self) -> bool {
        unsafe {
            // The link might be concurrently modified by another thread,
            // so make sure we read the value only once. Normally we would just
            // make the links atomic but this significantly hurts optimization.
            ptr::read_volatile(&self.parent_color).get() != UNLINKED_MARKER
        }
    }

    /// Unlinks the object from the `RBTree` without invalidating the rest
    /// of the tree.
    ///
    /// # Safety
    ///
    /// The `RBTree` is left in an invalid state after this function is called.
    /// To continue using the `RBTree`, it must be manually reset by calling the
    /// `fast_clear` function on it. Any other operations on the affected tree
    /// will result in undefined behavior.
    #[inline]
    pub unsafe fn unsafe_unlink(&self) {
        self.parent_color.set(UNLINKED_MARKER);
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
    unsafe fn is_linked(self) -> bool {
        (*self.0).parent_color.get() != UNLINKED_MARKER
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
        assert_eq!(parent.0 as usize & 1, 0);
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
                        if (w.left().is_null() || w.left().color() == Color::Black) &&
                           (w.right().is_null() || w.right().color() == Color::Black) {
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
                        if (w.left().is_null() || w.left().color() == Color::Black) &&
                           (w.right().is_null() || w.right().color() == Color::Black) {
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
pub struct Cursor<'a, A: for<'b> TreeAdaptor<'b> + 'a> {
    current: NodePtr,
    tree: &'a RBTree<A>,
}

impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> Clone for Cursor<'a, A> {
    #[inline]
    fn clone(&self) -> Cursor<'a, A> {
        Cursor {
            current: self.current,
            tree: self.tree,
        }
    }
}

impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> Cursor<'a, A> {
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
            Some(unsafe { &*self.tree.adaptor.get_container(self.current.0) })
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
}

/// A cursor which provides mutable access to a `RBTree`.
pub struct CursorMut<'a, A: for<'b> TreeAdaptor<'b> + 'a> {
    current: NodePtr,
    tree: &'a mut RBTree<A>,
}

impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> CursorMut<'a, A> {
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
            Some(unsafe { &*self.tree.adaptor.get_container(self.current.0) })
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

    /// Removes the current element from the `RBTree`.
    ///
    /// A pointer to the element that was removed is returned, and the cursor is
    /// moved to point to the next element in the `RBTree`.
    ///
    /// If the cursor is currently pointing to the null object then no element
    /// is removed and `None` is returned.
    #[inline]
    pub fn remove(&mut self) -> Option<IntrusiveRef<A::Container>> {
        unsafe {
            if self.is_null() {
                return None;
            }
            let next = self.current.next();
            let result = self.current.0;
            self.current.remove(&mut self.tree.root);
            self.current = next;
            Some(IntrusiveRef::from_raw(self.tree.adaptor.get_container(result)))
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
    pub fn replace_with(&mut self,
                        val: IntrusiveRef<A::Container>)
                        -> Result<IntrusiveRef<A::Container>, IntrusiveRef<A::Container>> {
        if self.is_null() {
            return Err(val);
        }
        unsafe {
            let new = NodePtr(self.tree.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            let result = self.current.0;
            self.current.replace_with(new, &mut self.tree.root);
            self.current = new;
            Ok(IntrusiveRef::from_raw(self.tree.adaptor.get_container(result)))
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
    pub fn insert_after(&mut self, val: IntrusiveRef<A::Container>) {
        unsafe {
            let new = NodePtr(self.tree.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.tree.is_empty() {
                self.tree.insert_root(new);
            } else if self.is_null() {
                self.tree.root.first_child().insert_left(new, &mut self.tree.root);
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
    pub fn insert_before(&mut self, val: IntrusiveRef<A::Container>) {
        unsafe {
            let new = NodePtr(self.tree.adaptor.get_link(val.into_raw()));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.tree.is_empty() {
                self.tree.insert_root(new);
            } else if self.is_null() {
                self.tree.root.last_child().insert_right(new, &mut self.tree.root);
            } else if self.current.left().is_null() {
                self.current.insert_left(new, &mut self.tree.root);
            } else {
                self.current.prev().insert_right(new, &mut self.tree.root);
            }
        }
    }
}

// =============================================================================
// RBTree
// =============================================================================

/// An intrusive red-black tree.
pub struct RBTree<A: for<'a> TreeAdaptor<'a>> {
    root: NodePtr,
    adaptor: A,
}

impl<A: for<'a> TreeAdaptor<'a>> RBTree<A> {
    /// Creates an empty `RBTree`.
    #[cfg(feature = "nightly")]
    #[inline]
    pub const fn new(adaptor: A) -> RBTree<A> {
        RBTree {
            root: NodePtr(ptr::null()),
            adaptor: adaptor,
        }
    }

    /// Creates an empty `RBTree`.
    #[cfg(not(feature = "nightly"))]
    #[inline]
    pub fn new(adaptor: A) -> RBTree<A> {
        RBTree {
            root: NodePtr::null(),
            adaptor: adaptor,
        }
    }

    /// Returns `true if the `RBTree` is empty.
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
    pub unsafe fn cursor_from_ptr(&self, ptr: *const A::Container) -> Cursor<A> {
        Cursor {
            current: NodePtr(self.adaptor.get_link(ptr)),
            tree: self,
        }
    }

    /// Creates a `CursorMut` from a pointer to an element.
    ///
    /// # Safety
    ///
    /// `ptr` must be a pointer to an object that is part of this tree.
    #[inline]
    pub unsafe fn cursor_mut_from_ptr(&mut self, ptr: *const A::Container) -> CursorMut<A> {
        CursorMut {
            current: NodePtr(self.adaptor.get_link(ptr)),
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
    fn find_internal<'a, Q: ?Sized + Ord>(&self, key: &Q) -> NodePtr
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>,
              A::Container: 'a
    {
        let mut tree = self.root;
        while !tree.is_null() {
            let current = unsafe { &*self.adaptor.get_container(tree.0) };
            match key.cmp(self.adaptor.get_key(current).borrow()) {
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
    {
        CursorMut {
            current: self.find_internal(key),
            tree: self,
        }
    }

    #[inline]
    fn lower_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> NodePtr
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>,
              A::Container: 'a
    {
        let mut tree = self.root;
        let mut result = NodePtr::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adaptor.get_container(tree.0) };
            let cond = match bound {
                Unbounded => true,
                Included(key) => key <= self.adaptor.get_key(current).borrow(),
                Excluded(key) => key < self.adaptor.get_key(current).borrow(),
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
    {
        CursorMut {
            current: self.lower_bound_internal(bound),
            tree: self,
        }
    }

    #[inline]
    fn upper_bound_internal<'a, Q: ?Sized + Ord>(&self, bound: Bound<&Q>) -> NodePtr
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>,
              A::Container: 'a
    {
        let mut tree = self.root;
        let mut result = NodePtr::null();
        while !tree.is_null() {
            let current = unsafe { &*self.adaptor.get_container(tree.0) };
            let cond = match bound {
                Unbounded => false,
                Included(key) => key < self.adaptor.get_key(current).borrow(),
                Excluded(key) => key <= self.adaptor.get_key(current).borrow(),
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
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
        where <A as TreeAdaptor<'a>>::Key: Borrow<Q>
    {
        CursorMut {
            current: self.upper_bound_internal(bound),
            tree: self,
        }
    }

    #[inline]
    unsafe fn insert_root(&mut self, node: NodePtr) {
        node.set_parent_color(NodePtr::null(), Color::Black);
        node.set_left(NodePtr::null());
        node.set_right(NodePtr::null());
        self.root = node;
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
    pub fn insert(&mut self, val: IntrusiveRef<A::Container>) -> CursorMut<A> {
        unsafe {
            let raw = val.into_raw();
            let new = NodePtr(self.adaptor.get_link(raw));
            assert!(!new.is_linked(),
                    "attempted to insert an object that is already linked");
            if self.is_empty() {
                self.insert_root(new);
            } else {
                let key = self.adaptor.get_key(&*raw);
                let mut tree = self.root;
                loop {
                    let current = &*self.adaptor.get_container(tree.0);
                    if key < self.adaptor.get_key(current) {
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

    /// Constructs a double-ended iterator over a sub-range of elements in the
    /// tree, starting at min, and ending at max. If min is `Unbounded`, then it
    /// will be treated as "negative infinity", and if max is `Unbounded`, then
    /// it will be treated as "positive infinity". Thus
    /// `range(Unbounded, Unbounded)` will yield the whole collection.
    #[inline]
    pub fn range<'a, Min: ?Sized + Ord, Max: ?Sized + Ord>(&'a self,
                                                           min: Bound<&Min>,
                                                           max: Bound<&Max>)
                                                           -> Iter<'a, A>
        where <A as TreeAdaptor<'a>>::Key: Borrow<Min> + Borrow<Max>
    {
        let lower = self.lower_bound_internal(min);
        let upper = self.upper_bound_internal(max);
        if !lower.is_null() && !upper.is_null() {
            let lower_key = unsafe { self.adaptor.get_key(&*self.adaptor.get_container(lower.0)) };
            let upper_key = unsafe { self.adaptor.get_key(&*self.adaptor.get_container(upper.0)) };
            if upper_key >= lower_key {
                return Iter {
                    raw: RawIter {
                        head: lower,
                        tail: upper,
                    },
                    tree: self,
                };
            }
        }
        Iter {
            raw: RawIter {
                head: NodePtr::null(),
                tail: NodePtr::null(),
            },
            tree: self,
        }
    }

    /// Gets an iterator over the objects in the `RBTree`, in ascending key
    /// order.
    #[inline]
    pub fn iter(&self) -> Iter<A> {
        if self.root.is_null() {
            Iter {
                raw: RawIter {
                    head: NodePtr::null(),
                    tail: NodePtr::null(),
                },
                tree: self,
            }
        } else {
            Iter {
                raw: RawIter {
                    head: unsafe { self.root.first_child() },
                    tail: unsafe { self.root.last_child() },
                },
                tree: self,
            }
        }
    }

    #[inline]
    fn drain_recurse<F>(&self, f: &mut F, current: NodePtr)
        where F: FnMut(IntrusiveRef<A::Container>)
    {
        // If the recursion down the left side of the tree panics, we should
        // still go through the right side of the tree and unlink all the nodes,
        // but without calling the user-supplied function to avoid any further
        // panics.
        struct PanicGuard(NodePtr);
        impl Drop for PanicGuard {
            #[inline]
            fn drop(&mut self) {
                fn recurse(current: NodePtr) {
                    if !current.is_null() {
                        unsafe {
                            current.unlink();
                            recurse(current.left());
                            recurse(current.right());
                        }
                    }
                }
                recurse(self.0);
            }
        };

        if !current.is_null() {
            unsafe {
                current.unlink();
                let guard = PanicGuard(current.right());
                self.drain_recurse(f, current.left());
                f(IntrusiveRef::from_raw(self.adaptor.get_container(current.0)));
                mem::forget(guard);
                self.drain_recurse(f, current.right());
            }
        }
    }

    /// Calls the given function for each element in the `RBTree` before
    /// removing it from the tree, in ascending key order.
    ///
    /// This will unlink all objects currently in the tree.
    ///
    /// If the given function panics then all elements in the `RBTree` will
    /// still be unlinked, but the function will not be called for any elements
    /// after the one that panicked.
    #[inline]
    pub fn drain<F>(&mut self, mut f: F)
        where F: FnMut(IntrusiveRef<A::Container>)
    {
        let root = self.root;
        self.root = NodePtr::null();
        self.drain_recurse(&mut f, root);
    }

    /// Removes all elements from the `RBTree`.
    ///
    /// This will unlink all object currently in the tree.
    #[inline]
    pub fn clear(&mut self) {
        self.drain(|_| {});
    }

    /// Empties the `RBTree` without unlinking objects in it.
    ///
    /// Since this does not unlink any objects, any attempts to link these
    /// objects into another `RBTree` will fail but will not cause any
    /// memory unsafety. To unlink those objects manually, you must call the
    /// `unsafe_unlink` function on them.
    ///
    /// This is the only function that can be safely called after an object has
    /// been moved or dropped while still being linked into this `RBTree`.
    #[inline]
    pub fn fast_clear(&mut self) {
        self.root = NodePtr::null();
    }

    /// Takes all the elements out of the `RBTree`, leaving it empty. The
    /// taken elements are returned as a new `RBTree`.
    #[inline]
    pub fn take(&mut self) -> RBTree<A>
        where A: Clone
    {
        let tree = RBTree {
            root: self.root,
            adaptor: self.adaptor.clone(),
        };
        self.root = NodePtr::null();
        tree
    }
}

// Allow read-only access from multiple threads
unsafe impl<A: for<'a> TreeAdaptor<'a> + Sync> Sync for RBTree<A> where A::Container: Sync {}

// We require Sync on objects here because they may belong to multiple collections
unsafe impl<A: for<'a> TreeAdaptor<'a> + Send> Send for RBTree<A> where A::Container: Send + Sync {}

impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> IntoIterator for &'a RBTree<A> {
    type Item = &'a A::Container;
    type IntoIter = Iter<'a, A>;

    #[inline]
    fn into_iter(self) -> Iter<'a, A> {
        self.iter()
    }
}

impl<A: for<'a> TreeAdaptor<'a> + Default> Default for RBTree<A> {
    fn default() -> RBTree<A> {
        RBTree::new(A::default())
    }
}

impl<A: for<'a> TreeAdaptor<'a>> fmt::Debug for RBTree<A>
    where A::Container: fmt::Debug
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
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

/// An iterator over references to the items of a `RBTree`.
pub struct Iter<'a, A: for<'b> TreeAdaptor<'b> + 'a> {
    raw: RawIter,
    tree: &'a RBTree<A>,
}
impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> Iterator for Iter<'a, A> {
    type Item = &'a A::Container;

    #[inline]
    fn next(&mut self) -> Option<&'a A::Container> {
        self.raw.next().map(|x| unsafe { &*self.tree.adaptor.get_container(x.0) })
    }
}
impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> DoubleEndedIterator for Iter<'a, A> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a A::Container> {
        self.raw.next_back().map(|x| unsafe { &*self.tree.adaptor.get_container(x.0) })
    }
}
impl<'a, A: for<'b> TreeAdaptor<'b> + 'a> Clone for Iter<'a, A> {
    #[inline]
    fn clone(&self) -> Iter<'a, A> {
        Iter {
            raw: self.raw,
            tree: self.tree,
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
    use Bound::*;
    use super::{RBTree, TreeAdaptor, Link};
    use std::fmt;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    extern crate rand;
    use self::rand::{XorShiftRng, Rng};

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
    intrusive_adaptor!(ObjAdaptor = Obj { link: Link });
    impl<'a> TreeAdaptor<'a> for ObjAdaptor {
        type Key = i32;
        fn get_key(&self, container: &'a Self::Container) -> i32 {
            container.value
        }
    }
    fn make_obj(value: i32) -> IntrusiveRef<Obj> {
        IntrusiveRef::from_box(Box::new(Obj {
            link: Link::new(),
            value: value,
        }))
    }

    #[test]
    fn test_link() {
        let a = make_obj(1);
        assert!(!a.link.is_linked());
        assert_eq!(format!("{:?}", a.link), "unlinked");

        let mut b = RBTree::<ObjAdaptor>::default();
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

        assert_eq!(b.front_mut().remove().unwrap().as_ref() as *const _,
                   a.as_ref() as *const _);
        assert!(b.is_empty());
        assert!(!a.link.is_linked());
    }

    #[test]
    fn test_cursor() {
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        let mut t = RBTree::new(ObjAdaptor);
        let mut cur = t.cursor_mut();
        assert!(cur.is_null());
        assert!(cur.get().is_none());
        assert!(cur.remove().is_none());

        cur.insert_before(a.clone());
        cur.insert_before(c.clone());
        cur.move_prev();
        cur.insert_before(b.clone());
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
        assert_eq!(cur.replace_with(a2.clone()).unwrap().as_ref() as *const _,
                   a.as_ref() as *const _);
        assert!(!a.link.is_linked());
        cur.move_next();
        assert_eq!(cur.replace_with(b2.clone()).unwrap().as_ref() as *const _,
                   b.as_ref() as *const _);
        assert!(!b.link.is_linked());
        cur.move_next();
        assert_eq!(cur.replace_with(c2.clone()).unwrap().as_ref() as *const _,
                   c.as_ref() as *const _);
        assert!(!c.link.is_linked());
        cur.move_next();
        assert_eq!(cur.replace_with(c.clone()).unwrap_err().as_ref() as *const _,
                   c.as_ref() as *const _);
    }

    #[test]
    fn test_insert_remove() {
        let v = (0..100)
            .map(make_obj)
            .collect::<Vec<_>>();
        assert!(v.iter().all(|x| !x.link.is_linked()));
        let mut t = RBTree::new(ObjAdaptor);
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
                    while let Some(x) = c.get() {
                        if x.value > v[i].value {
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
                    while let Some(x) = c.get() {
                        if x.value < v[i].value {
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
        let v = (0..10)
            .map(|x| make_obj(x * 10))
            .collect::<Vec<_>>();
        let mut t = RBTree::new(ObjAdaptor);
        for x in v.iter() {
            t.insert(x.clone());
        }

        assert_eq!(format!("{:?}", t),
                   "{0, 10, 20, 30, 40, 50, 60, 70, 80, 90}");

        assert_eq!(t.iter().clone().map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert_eq!((&t).into_iter().rev().map(|x| x.value).collect::<Vec<_>>(),
                   vec![90, 80, 70, 60, 50, 40, 30, 20, 10, 0]);
        assert_eq!(t.range(Unbounded, Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);

        assert_eq!(t.range(Included(&0), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert_eq!(t.range(Excluded(&0), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert_eq!(t.range(Included(&25), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70, 80, 90]);
        assert_eq!(t.range(Excluded(&25), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70, 80, 90]);
        assert_eq!(t.range(Included(&70), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![70, 80, 90]);
        assert_eq!(t.range(Excluded(&70), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![80, 90]);
        assert_eq!(t.range(Included(&100), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&100), Unbounded).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);

        assert_eq!(t.range(Unbounded, Included(&90)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert_eq!(t.range(Unbounded, Excluded(&90)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70, 80]);
        assert_eq!(t.range(Unbounded, Included(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20]);
        assert_eq!(t.range(Unbounded, Excluded(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20]);
        assert_eq!(t.range(Unbounded, Included(&70)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60, 70]);
        assert_eq!(t.range(Unbounded, Excluded(&70)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![0, 10, 20, 30, 40, 50, 60]);
        assert_eq!(t.range(Unbounded, Included(&-1)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Unbounded, Excluded(&-1)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);

        assert_eq!(t.range(Included(&25), Included(&80)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70, 80]);
        assert_eq!(t.range(Included(&25), Excluded(&80)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70]);
        assert_eq!(t.range(Excluded(&25), Included(&80)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70, 80]);
        assert_eq!(t.range(Excluded(&25), Excluded(&80)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![30, 40, 50, 60, 70]);

        assert_eq!(t.range(Included(&25), Included(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Included(&25), Excluded(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&25), Included(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&25), Excluded(&25)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);

        assert_eq!(t.range(Included(&50), Included(&50)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![50]);
        assert_eq!(t.range(Included(&50), Excluded(&50)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&50), Included(&50)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&50), Excluded(&50)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);

        assert_eq!(t.range(Included(&100), Included(&-2)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Included(&100), Excluded(&-2)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&100), Included(&-2)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);
        assert_eq!(t.range(Excluded(&100), Excluded(&-2)).map(|x| x.value).collect::<Vec<_>>(),
                   vec![]);

        let mut t2 = t.take();
        assert!(t.is_empty());

        let mut v2 = Vec::new();
        t2.drain(|x| {
            v2.push(x.value);
        });
        assert_eq!(v2, vec![0, 10, 20, 30, 40, 50, 60, 70, 80, 90]);
        assert!(t2.is_empty());
    }

    #[test]
    fn test_find() {
        let v = (0..10)
            .map(|x| make_obj(x * 10))
            .collect::<Vec<_>>();
        let mut t = RBTree::new(ObjAdaptor);
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
                assert_eq!(c.get().map(|x| x.value),
                           if i % 10 == 0 {
                               Some(i)
                           } else {
                               None
                           });
            }
            {
                let c = t.find_mut(&i);
                assert_eq!(c.get().map(|x| x.value),
                           if i % 10 == 0 {
                               Some(i)
                           } else {
                               None
                           });
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
                assert_eq!(c.get().map(|x| x.value),
                           if i >= 0 {
                               Some(i - mod10(i))
                           } else {
                               None
                           });
            }
            {
                let c = t.upper_bound_mut(Included(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i >= 0 {
                               Some(i - mod10(i))
                           } else {
                               None
                           });
            }
            {
                let c = t.upper_bound(Excluded(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i > 0 {
                               Some(i - 1 - mod10(i - 1))
                           } else {
                               None
                           });
            }
            {
                let c = t.upper_bound_mut(Excluded(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i > 0 {
                               Some(i - 1 - mod10(i - 1))
                           } else {
                               None
                           });
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
                assert_eq!(c.get().map(|x| x.value),
                           if i <= 90 {
                               Some((i + 9) - mod10(i + 9))
                           } else {
                               None
                           });
            }
            {
                let c = t.lower_bound_mut(Included(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i <= 90 {
                               Some((i + 9) - mod10(i + 9))
                           } else {
                               None
                           });
            }
            {
                let c = t.lower_bound(Excluded(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i < 90 {
                               Some((i + 10) - mod10(i + 10))
                           } else {
                               None
                           });
            }
            {
                let c = t.lower_bound_mut(Excluded(&i));
                assert_eq!(c.get().map(|x| x.value),
                           if i < 90 {
                               Some((i + 10) - mod10(i + 10))
                           } else {
                               None
                           });
            }
        }
    }

    #[test]
    fn test_unsafe_unlink() {
        let mut t = RBTree::new(ObjAdaptor);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        t.insert(a.clone());
        t.insert(b.clone());
        t.insert(c.clone());

        unsafe {
            t.fast_clear();
            a.link.unsafe_unlink();
            b.link.unsafe_unlink();
            c.link.unsafe_unlink();
        }
        assert!(t.is_empty());
        assert!(!a.link.is_linked());
        assert!(!b.link.is_linked());
        assert!(!c.link.is_linked());
    }

    #[test]
    fn test_panic() {
        let mut t = RBTree::new(ObjAdaptor);
        let a = make_obj(1);
        let b = make_obj(2);
        let c = make_obj(3);
        t.insert(a.clone());
        t.insert(b.clone());
        t.insert(c.clone());

        catch_unwind(AssertUnwindSafe(|| t.drain(|_| panic!("test")))).unwrap_err();

        assert!(t.is_empty());
        assert!(!a.link.is_linked());
        assert!(!b.link.is_linked());
        assert!(!c.link.is_linked());
    }

    #[test]
    fn test_non_static() {
        #[derive(Clone)]
        struct Obj<'a> {
            link: Link,
            value: &'a i32,
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
        impl<'a, 'b> TreeAdaptor<'a> for ObjAdaptor<'b> {
            type Key = &'a i32;
            fn get_key(&self, container: &'a Obj) -> &'a i32 {
                container.value
            }
        }

        let v = 5;
        let mut l = RBTree::new(ObjAdaptor(::std::marker::PhantomData));
        let o = Obj {
            link: Link::default(),
            value: &v,
        };
        let a = IntrusiveRef::from_box(Box::new(o.clone()));
        let b = IntrusiveRef::from_box(Box::new(o.clone()));
        l.insert(a);
        l.insert(b);
        assert_eq!(*l.front().get().unwrap().value, 5);
        assert_eq!(*l.back().get().unwrap().value, 5);
    }
}
