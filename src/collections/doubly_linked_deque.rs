//! A doubly-linked list with owned nodes.
//!
//! The `LinkedDeque` allows pushing, popping, and accessing elements at either
//! end in *constant* time.
//!
//! Using [Learn Rust With Entirely Too Many Linked Lists]
//!
//! [Learn Rust With Entirely Too Many Linked Lists]: https://rust-unofficial.github.io/too-many-lists/

use std::fmt;

use core::cmp::Ordering;
use core::hash::{Hash, Hasher};
use core::ptr::NonNull;
use core::{marker, mem};

/// Creates a `LinkedDeque` containing the arguments.
///
/// # Examples
///
/// ```
/// use dsa::collections::prelude::*;
///
/// let mut list = list![1 => 2 => 3];
/// assert_eq!(list.len(), 3);
/// assert!(list.iter().eq([&1, &2, &3]));
///
/// assert_eq!(list.pop_back(), Some(3));
/// assert_eq!(list.pop_back(), Some(2));
/// assert_eq!(list.pop_back(), Some(1));
/// ```
///
/// ```
/// use dsa::collections::prelude::*;
///
/// let list = list![1; 5];
/// assert_eq!(list.len(), 5);
/// assert!(list.iter().eq([&1, &1, &1, &1, &1]));
/// ```
#[macro_export]
macro_rules! list {
    () => {
        $crate::collections::doubly_linked_deque::LinkedDeque::new();
    };
    ($($elem:expr)=>*) => {{
        let mut list = $crate::collections::doubly_linked_deque::LinkedDeque::new();
        $(list.push_back($elem);)*
        list
    }};
    ($elem:expr; $n:expr) => {{
        // Ensure the expression is only evaluated once.
        let count = $n;

        let mut list = $crate::collections::doubly_linked_deque::LinkedDeque::new();
        list.extend(::core::iter::repeat($elem).take(count));
        list
    }};
}

/// A doubly-linked list with owned nodes.
///
/// The `LinkedDeque` allows pushing, popping, and accessing elements at either
/// end in *constant* time.
pub struct LinkedDeque<T> {
    /// Pointer to the head of the list.
    head: Option<NonNull<Node<T>>>,
    /// Pointer to the tail of the list.
    tail: Option<NonNull<Node<T>>>,
    /// Number of initialized nodes.
    len: usize,
    /// In order to tell the drop checker that we do own values of type T, and
    /// therefore may drop some T's when we drop.
    _marker: marker::PhantomData<T>,
}

#[derive(Debug)]
struct Node<T> {
    /// Pointer to the next node in sequence.
    next: Option<NonNull<Node<T>>>,
    /// Pointer to the previous node in sequence.
    prev: Option<NonNull<Node<T>>>,
    /// The node's data.
    elem: T,
}

/// An iterator that moves out of a `LinkedDeque<T>`.
#[derive(Debug)]
pub struct IntoIter<T> {
    list: LinkedDeque<T>,
}

/// An iterator that borrows a `LinkedDeque<T>` immutably.
#[derive(Debug)]
pub struct Iter<'a, T> {
    /// Pointer to the head of the list.
    head: Option<NonNull<Node<T>>>,
    /// Pointer to the tail of the list.
    tail: Option<NonNull<Node<T>>>,
    /// Number of initialized nodes.
    len: usize,
    _marker: marker::PhantomData<&'a T>,
}

/// An iterator that borrows a `LinkedDeque<T>` mutably.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    /// Pointer to the head of the list.
    head: Option<NonNull<Node<T>>>,
    /// Pointer to the tail of the list.
    tail: Option<NonNull<Node<T>>>,
    /// Number of initialized nodes.
    len: usize,
    _marker: marker::PhantomData<&'a mut T>,
}

/// A mutable cursor over a `LinkedDeque<T>`.
///
/// A `Cursor` is like an iterator, except that it can freely seek
/// back-and-forth.
///
/// Cursors always rest between two elements in the list, and index in a
/// logically circular way. To accommodate this, there is a "ghost" non-element
/// that yields [`None`] between the head and tail of the list.
///
/// When created, cursors start at the front of the list, or the "ghost"
/// non-element if the list is empty.
#[derive(Debug)]
pub struct CursorMut<'a, T> {
    /// Node the cursor is "on".
    curr: Option<NonNull<Node<T>>>,
    /// Mutable reference to the list.
    list: &'a mut LinkedDeque<T>,
    /// Index of the cursor relative to the list.
    idx: Option<usize>,
}

impl<T> LinkedDeque<T> {
    /// Constructs a new, empty `LinkedDeque<T>`.
    ///
    /// The list will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let list: LinkedDeque<i32> = LinkedDeque::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
            _marker: marker::PhantomData,
        }
    }

    /// Returns an immutable reference to the first element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.front(), Some(&4));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.front(), None);
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        unsafe { self.head.map(|head| &(*head.as_ptr()).elem) }
    }

    /// Returns a mutable reference to the first element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.front_mut(), Some(&mut 4));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.front_mut(), None);
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        unsafe { self.head.map(|head| &mut (*head.as_ptr()).elem) }
    }

    /// Prepends an element to the front of the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_front(3);
    /// list.push_front(4);
    /// assert_eq!(list.pop_front(), Some(4));
    /// ```
    pub fn push_front(&mut self, elem: T) {
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                next: None,
                prev: None,
                elem,
            })));

            if let Some(head) = self.head {
                // There is at least a valid `head` node.
                (*head.as_ptr()).prev = Some(new_node);
                (*new_node.as_ptr()).next = self.head;
            } else {
                self.tail = Some(new_node);
            }

            self.head = Some(new_node);
            self.len += 1;
        }
    }

    /// Removes the first element from the list and returns it, or [`None`] if
    /// it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// assert_eq!(list.pop_front(), None);
    ///
    /// list.push_front(3);
    /// list.push_front(4);
    /// list.push_front(5);
    ///
    /// assert_eq!(list.pop_front(), Some(5));
    /// assert_eq!(list.pop_front(), Some(4));
    /// assert_eq!(list.pop_front(), Some(3));
    /// assert_eq!(list.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|head| unsafe {
            // Node is boxed before being removed so the destructor for T can
            // be invoked when returning.
            let boxed_node = Box::from_raw(head.as_ptr());

            let elem = boxed_node.elem;
            self.head = boxed_node.next;

            if let Some(new_head) = self.head {
                // There are at least two valid nodes.
                (*new_head.as_ptr()).prev = None;
            } else {
                self.tail = None;
            }

            self.len -= 1;

            elem
            // `boxed_node` handles it's deallocation...
        })
    }

    /// Returns an immutable reference to the last element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.back(), Some(&3));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.back(), None);
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        unsafe { self.tail.map(|tail| &(*tail.as_ptr()).elem) }
    }

    /// Returns a mutable reference to the last element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.back_mut(), Some(&mut 3));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.back_mut(), None);
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        unsafe { self.tail.map(|tail| &mut (*tail.as_ptr()).elem) }
    }

    /// Appends an element to the back of the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    /// list.push_back(3);
    /// list.push_back(4);
    /// assert_eq!(list.pop_front(), Some(3));
    /// ```
    pub fn push_back(&mut self, elem: T) {
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                next: None,
                prev: None,
                elem,
            })));

            if let Some(tail) = self.tail {
                // There is at least a valid `tail` node.
                (*tail.as_ptr()).next = Some(new_node);
                (*new_node.as_ptr()).prev = self.tail;
            } else {
                self.head = Some(new_node);
            }

            self.tail = Some(new_node);
            self.len += 1;
        }
    }

    /// Removes the last element from the list and returns it, or [`None`] if
    /// it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. `LinkedDeque` allows pushing, popping, and accessing
    /// elements at either end in *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// assert_eq!(list.pop_back(), None);
    ///
    /// list.push_front(3);
    /// list.push_front(4);
    /// list.push_front(5);
    ///
    /// assert_eq!(list.pop_back(), Some(3));
    /// assert_eq!(list.pop_back(), Some(4));
    /// assert_eq!(list.pop_back(), Some(5));
    /// assert_eq!(list.pop_back(), None);
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|tail| unsafe {
            // Box the node being removed so the destructor for T can be
            // invoked when returning.
            let boxed_node = Box::from_raw(tail.as_ptr());

            let elem = boxed_node.elem;
            self.tail = boxed_node.prev;

            if let Some(new_tail) = self.tail {
                // There are at least two valid nodes.
                (*new_tail.as_ptr()).next = None;
            } else {
                self.head = None;
            }

            self.len -= 1;

            elem
            // `boxed_node` handles it's deallocation...
        })
    }

    /// Clears the list, removing all nodes.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*len*) time. The entire list needs to be traversed in order
    /// to remove all initialized nodes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// list.push_front(3);
    /// list.push_front(4);
    /// list.push_front(5);
    ///
    /// assert!(!list.is_empty());
    ///
    /// list.clear();
    ///
    /// assert!(list.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }

    /// Returns an immutable iterator over the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// let iter = list.iter();
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: marker::PhantomData,
        }
    }

    /// Returns a mutable iterator over the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// let iter_mut = list.iter_mut();
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            head: self.head,
            tail: self.tail,
            len: self.len,
            _marker: marker::PhantomData,
        }
    }

    /// Returns a mutable cursor over the list.
    ///
    /// Initially begins at the "ghost" non-element.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list: LinkedDeque<i32> = LinkedDeque::new();
    ///
    /// let cursor = list.cursor_mut();
    /// ```
    #[inline]
    pub fn cursor_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            curr: None,
            list: self,
            idx: None,
        }
    }

    /// Returns the number of nodes in the list.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list contains no nodes.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Drop for LinkedDeque<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

impl<T> Default for LinkedDeque<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Clone for LinkedDeque<T> {
    fn clone(&self) -> Self {
        let mut list = Self::new();
        for item in self {
            list.push_back(item.clone());
        }
        list
    }
}

impl<T> Extend<T> for LinkedDeque<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<T> FromIterator<T> for LinkedDeque<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T: fmt::Debug> fmt::Debug for LinkedDeque<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for LinkedDeque<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for LinkedDeque<T> {}

impl<T: PartialOrd> PartialOrd for LinkedDeque<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for LinkedDeque<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for LinkedDeque<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self {
            item.hash(state);
        }
    }
}

impl<T> IntoIterator for LinkedDeque<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter { list: self }
    }
}

impl<'a, T> IntoIterator for &'a LinkedDeque<T> {
    type IntoIter = Iter<'a, T>;
    type Item = &'a T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut LinkedDeque<T> {
    type IntoIter = IterMut<'a, T>;
    type Item = &'a mut T;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.list.len, Some(self.list.len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.list.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.list.len
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.head.map(|head| unsafe {
                self.len -= 1;
                self.head = (*head.as_ptr()).next;
                &(*head.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.tail.map(|tail| unsafe {
                self.len -= 1;
                self.tail = (*tail.as_ptr()).prev;
                &(*tail.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.head.map(|head| unsafe {
                self.len -= 1;
                self.head = (*head.as_ptr()).next;
                &mut (*head.as_ptr()).elem
            })
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> DoubleEndedIterator for IterMut<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.tail.map(|tail| unsafe {
                self.len -= 1;
                self.tail = (*tail.as_ptr()).prev;
                &mut (*tail.as_ptr()).elem
            })
        } else {
            None
        }
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

#[allow(dead_code)]
fn assert_properties() {
    fn is_send<T: Send>() {}
    fn is_sync<T: Sync>() {}

    is_send::<LinkedDeque<i32>>();
    is_sync::<LinkedDeque<i32>>();

    is_send::<IntoIter<i32>>();
    is_sync::<IntoIter<i32>>();

    is_send::<Iter<'_, i32>>();
    is_sync::<Iter<'_, i32>>();

    is_send::<IterMut<'_, i32>>();
    is_sync::<IterMut<'_, i32>>();

    fn linked_deque_covariant<'a, T>(x: LinkedDeque<&'static T>) -> LinkedDeque<&'a T> {
        x
    }
    fn iter_covariant<'i, 'a, T>(x: Iter<'i, &'static T>) -> Iter<'i, &'a T> {
        x
    }
    fn into_iter_covariant<'a, T>(x: IntoIter<&'static T>) -> IntoIter<&'a T> {
        x
    }
}

#[allow(dead_code)]
/// ```compile_fail
/// use dsa::collections::LinkedDequeIterMut as IterMut;
///
/// fn iter_mut_covariant<'i, 'a, T>(x: IterMut<'i, &'static T>) -> IterMut<'i, &'a T> { x }
/// ```
fn iter_mut_invariant() {}

unsafe impl<T: Send> Send for LinkedDeque<T> {}
unsafe impl<T: Sync> Sync for LinkedDeque<T> {}

unsafe impl<'a, T: Send> Send for Iter<'a, T> {}
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}

impl<'a, T> CursorMut<'a, T> {
    /// Returns the cursor position index within the `LinkedDeque`, or [`None`]
    /// if the cursor is currently pointing to the “ghost” non-element.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![1 => 2];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.index(), None);
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.index(), Some(0));
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.index(), Some(1));
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.index(), None);
    /// ```
    pub fn index(&self) -> Option<usize> {
        self.idx
    }

    /// Returns a mutable reference to the element that the cursor is currently
    /// pointing to, or [`None`] if the cursor is currently pointing to the
    /// "ghost" non-element.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![44 => 45];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.current(), None);
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), Some(&mut 44));
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), Some(&mut 45));
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), None);
    /// ```
    pub fn current(&mut self) -> Option<&mut T> {
        unsafe { self.curr.map(|curr| &mut (*curr.as_ptr()).elem) }
    }

    /// Returns a mutable reference to the next element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the first element of the `LinkedDeque`. If it is pointing to the last
    /// element of the `LinkedDeque` then this returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![44 => 45];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.peek_next(), Some(&mut 44));
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.peek_next(), Some(&mut 45));
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.peek_next(), None);
    /// ```
    pub fn peek_next(&mut self) -> Option<&mut T> {
        unsafe {
            match self.curr {
                Some(curr) => (*curr.as_ptr()).next,
                None => self.list.head,
            }
            .map(|node| &mut (*node.as_ptr()).elem)
        }
    }

    /// Returns a mutable reference to the previous element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this returns
    /// the last element of the `LinkedDeque`. If it is pointing to the first
    /// element of the `LinkedDeque` then this returns [`None`].
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![44 => 45];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.peek_prev(), Some(&mut 45));
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.peek_prev(), None);
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.peek_prev(), Some(&mut 44));
    /// ```
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        unsafe {
            match self.curr {
                Some(curr) => (*curr.as_ptr()).prev,
                None => self.list.tail,
            }
            .map(|node| &mut (*node.as_ptr()).elem)
        }
    }

    /// Moves the cursor to the next element of the `LinkedDeque`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move
    /// it to the first element of the `LinkedDeque`. If it is pointing to the
    /// last element of the `LinkedDeque` then this will move it to the "ghost"
    /// non-element.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![1 => 2 => 3];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.current(), None);
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), Some(&mut 1));
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), Some(&mut 2));
    ///
    /// cursor_mut.move_next();
    /// assert_eq!(cursor_mut.current(), Some(&mut 3));
    /// ```
    pub fn move_next(&mut self) {
        if let Some(curr) = self.curr {
            unsafe {
                self.curr = (*curr.as_ptr()).next;

                if self.curr.is_some() {
                    // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
                    *self.idx.as_mut().unwrap() += 1;
                } else {
                    // We have reached the "ghost" non-element.
                    self.idx = None;
                }
            }
        } else if !self.list.is_empty() {
            // Currently on the "ghost" non-element but the list has a head.
            self.curr = self.list.head;
            self.idx = Some(0);
        } else {
            // The only element is the "ghost" non-element...
        }
    }

    /// Moves the cursor to the previous element of the `LinkedDeque`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will move
    /// it to the last element of the `LinkedDeque`. If it is pointing to the
    /// first element of the `LinkedDeque` then this will move it to the "ghost"
    /// non-element.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list = list![1 => 2 => 3];
    ///
    /// let mut cursor_mut = list.cursor_mut();
    /// assert_eq!(cursor_mut.current(), None);
    ///
    /// cursor_mut.move_prev();
    /// assert_eq!(cursor_mut.current(), Some(&mut 3));
    ///
    /// cursor_mut.move_prev();
    /// assert_eq!(cursor_mut.current(), Some(&mut 2));
    ///
    /// cursor_mut.move_prev();
    /// assert_eq!(cursor_mut.current(), Some(&mut 1));
    /// ```
    pub fn move_prev(&mut self) {
        if let Some(curr) = self.curr {
            unsafe {
                self.curr = (*curr.as_ptr()).prev;

                if self.curr.is_some() {
                    // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
                    *self.idx.as_mut().unwrap() -= 1;
                } else {
                    // We have reached the "ghost" non-element.
                    self.idx = None;
                }
            }
        } else if !self.list.is_empty() {
            // Currently on the "ghost" non-element but the list has a tail.
            self.curr = self.list.tail;
            self.idx = Some(self.list.len - 1);
        } else {
            // The only element is the "ghost" non-element...
        }
    }

    /// Splits the list, returning everything before the current element as a
    /// new `LinkedDeque`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// return the entire `LinkedDeque` and leave the cursor's list empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list is split at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// assert!(list_1.iter().eq([&1, &2, &3, &4, &5]));
    ///
    /// let mut cursor = list_1.cursor_mut();
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// let list_2 = cursor.split_before();
    ///
    /// assert!(list_1.iter().eq([&3, &4, &5]));
    /// assert_eq!(list_1.len(), 3);
    ///
    /// assert!(list_2.iter().eq([&1, &2]));
    /// assert_eq!(list_2.len(), 2);
    /// ```
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// assert!(list_1.iter().eq([&1, &2, &3, &4, &5]));
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// let list_2 = cursor.split_before();
    ///
    /// assert!(list_1.is_empty());
    /// assert_eq!(list_1.len(), 0);
    ///
    /// assert!(list_2.iter().eq([&1, &2, &3, &4, &5]));
    /// assert_eq!(list_2.len(), 5);
    /// ```
    pub fn split_before(&mut self) -> LinkedDeque<T> {
        if let Some(curr) = self.curr {
            // Currently not on the "ghost" non-element.
            let old_len = self.list.len;
            // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
            let old_idx = self.idx.unwrap();

            let new_len = old_len - old_idx;

            let output_head = self.list.head;
            let output_tail = unsafe { (*curr.as_ptr()).prev };
            let output_len = old_len - new_len;

            if let Some(new_tail) = output_tail {
                unsafe {
                    (*curr.as_ptr()).prev = None;
                    (*new_tail.as_ptr()).next = None;
                }
            }

            self.list.len = new_len;
            self.list.head = Some(curr);
            self.idx = Some(0);

            if output_len == 0 {
                // The split contains no valid nodes (e.g, one node list)
                Default::default()
            } else {
                LinkedDeque {
                    head: output_head,
                    tail: output_tail,
                    len: output_len,
                    _marker: marker::PhantomData,
                }
            }
        } else {
            // Currently on the "ghost" non-element, so just replace the entire
            // list with the default.
            mem::take(self.list)
        }
    }

    /// Splits the list, returning everything after the current element as a
    /// new `LinkedDeque`.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// return the entire `LinkedDeque` and leave the cursor's list empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list is split at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// assert!(list_1.iter().eq([&1, &2, &3, &4, &5]));
    ///
    /// let mut cursor = list_1.cursor_mut();
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// let list_2 = cursor.split_after();
    ///
    /// assert!(list_1.iter().eq([&1, &2, &3]));
    /// assert_eq!(list_1.len(), 3);
    ///
    /// assert!(list_2.iter().eq([&4, &5]));
    /// assert_eq!(list_2.len(), 2);
    /// ```
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// assert!(list_1.iter().eq([&1, &2, &3, &4, &5]));
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// let list_2 = cursor.split_after();
    ///
    /// assert!(list_1.is_empty());
    /// assert_eq!(list_1.len(), 0);
    ///
    /// assert!(list_2.iter().eq([&1, &2, &3, &4, &5]));
    /// assert_eq!(list_2.len(), 5);
    /// ```
    pub fn split_after(&mut self) -> LinkedDeque<T> {
        if let Some(curr) = self.curr {
            // Currently not on the "ghost" non-element.
            let old_len = self.list.len;
            // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
            let new_len = self.idx.unwrap() + 1;

            let output_head = unsafe { (*curr.as_ptr()).next };
            let output_tail = self.list.tail;
            let output_len = old_len - new_len;

            if let Some(new_head) = output_head {
                unsafe {
                    (*new_head.as_ptr()).prev = None;
                    (*curr.as_ptr()).next = None;
                }
            }

            self.list.len = new_len;
            self.list.tail = Some(curr);
            self.idx = Some(self.list.len - 1);

            if output_len == 0 {
                // The split contains no valid nodes (e.g, one node list)
                Default::default()
            } else {
                LinkedDeque {
                    head: output_head,
                    tail: output_tail,
                    len: output_len,
                    _marker: marker::PhantomData,
                }
            }
        } else {
            // Currently on the "ghost" non-element, so just replace the entire
            // list with the default.
            mem::take(self.list)
        }
    }

    /// Splices the contents of the provided `LinkedDeque` before the current
    /// element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// append the provided `LinkedDeque`. If it is pointing to the first
    /// element then this will prepend the provided `LinkedDeque`.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The splice occurs at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// let list_2 = list![40 => 41 => 42];
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// cursor.splice_before(list_2);
    ///
    /// assert_eq!(list_1.len(), 8);
    /// assert!(list_1.iter().eq([&1, &2, &40, &41, &42, &3, &4, &5]));
    /// ```
    pub fn splice_before(&mut self, mut input: LinkedDeque<T>) {
        let (in_head, in_tail) = if input.is_empty() {
            // Provided list is empty, nothing to do...
            return;
        } else {
            (input.head.take().unwrap(), input.tail.take().unwrap())
        };

        unsafe {
            // Currently not on the "ghost" non-element.
            if let Some(curr) = self.curr {
                if let Some(prev) = (*curr.as_ptr()).prev {
                    // Splicing in the middle of the list.
                    (*prev.as_ptr()).next = Some(in_head);
                    (*in_head.as_ptr()).prev = Some(prev);

                    (*curr.as_ptr()).prev = Some(in_tail);
                    (*in_tail.as_ptr()).next = Some(curr);
                } else {
                    // No previous node, prepending the list.
                    (*curr.as_ptr()).prev = Some(in_tail);
                    (*in_tail.as_ptr()).next = Some(curr);

                    self.list.head = Some(in_head);
                }

                // Move index forward by the input's length.
                //
                // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
                *self.idx.as_mut().unwrap() += input.len;
            } else if let Some(tail) = self.list.tail {
                // Currently on the "ghost" non-element but the list is
                // non-empty. Appending input to the list.
                (*tail.as_ptr()).next = Some(in_head);
                (*in_head.as_ptr()).prev = Some(tail);

                self.list.tail = Some(in_tail);
            } else {
                // Current list is empty so consume the input and remain on
                // "ghost" non-element.
                mem::swap(self.list, &mut input);
            }
        }

        self.list.len += input.len;
        input.len = 0;

        // `input` handles it's deallocation...
    }

    /// Splices the contents of the provided `LinkedDeque` after the current
    /// element.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// prepend the provided `LinkedDeque`. If it is pointing to the last
    /// element then this will append the provided `LinkedDeque`.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The splice occurs at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// let list_2 = list![40 => 41 => 42];
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// cursor.splice_after(list_2);
    ///
    /// assert_eq!(list_1.len(), 8);
    /// assert!(list_1.iter().eq([&1, &2, &3, &40, &41, &42, &4, &5]));
    /// ```
    pub fn splice_after(&mut self, mut input: LinkedDeque<T>) {
        let (in_head, in_tail) = if input.is_empty() {
            // Provided list is empty, nothing to do...
            return;
        } else {
            (input.head.take().unwrap(), input.tail.take().unwrap())
        };

        unsafe {
            // Currently not on the "ghost" non-element.
            if let Some(curr) = self.curr {
                if let Some(next) = (*curr.as_ptr()).next {
                    // Splicing in the middle of the list.
                    (*next.as_ptr()).prev = Some(in_tail);
                    (*in_tail.as_ptr()).next = Some(next);

                    (*curr.as_ptr()).next = Some(in_head);
                    (*in_head.as_ptr()).prev = Some(curr);
                } else {
                    // No next node, appending the list.
                    (*curr.as_ptr()).next = Some(in_head);
                    (*in_head.as_ptr()).prev = Some(curr);

                    self.list.tail = Some(in_tail);
                }
            } else if let Some(head) = self.list.head {
                // Currently on the "ghost" non-element but the list is
                // non-empty. Prepending input to the list.
                (*head.as_ptr()).prev = Some(in_tail);
                (*in_tail.as_ptr()).next = Some(head);

                self.list.head = Some(in_head);
            } else {
                // Current list is empty so consume the input and remain on
                // "ghost" non-element.
                mem::swap(self.list, &mut input);
            }
        }

        self.list.len += input.len;
        input.len = 0;

        // `input` handles it's deallocation...
    }

    /// Inserts an element before the current cursor position.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// append the provided element. If it is pointing to the first element
    /// then this will prepend the provided element.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The insert occurs at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// cursor.insert_before(10);
    ///
    /// assert_eq!(list_1.len(), 6);
    /// assert!(list_1.iter().eq([&1, &2, &10, &3, &4, &5]));
    /// ```
    pub fn insert_before(&mut self, elem: T) {
        if let Some(curr) = self.curr {
            // Currently not on the "ghost" non-element.
            unsafe {
                let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                    next: None,
                    prev: None,
                    elem,
                })));

                if let Some(prev) = (*curr.as_ptr()).prev {
                    // Inserting in the middle of the list.
                    (*prev.as_ptr()).next = Some(new_node);
                    (*new_node.as_ptr()).prev = Some(prev);

                    (*curr.as_ptr()).prev = Some(new_node);
                    (*new_node.as_ptr()).next = Some(curr);
                } else {
                    // No previous node, prepending the list.
                    (*curr.as_ptr()).prev = Some(new_node);
                    (*new_node.as_ptr()).next = Some(curr);

                    self.list.head = Some(new_node);

                    // Move index forward by 1.
                    //
                    // SAFETY: `idx` is never `None` when `curr` is `Some(_)`.
                    *self.idx.as_mut().unwrap() += 1;
                }

                self.list.len += 1;
            }
        } else {
            // Currently on the "ghost" non-element, append the new node.
            self.list.push_back(elem);
        }
    }

    /// Inserts an element after the current cursor position.
    ///
    /// If the cursor is pointing to the "ghost" non-element then this will
    /// prepend the provided element. If it is pointing to the last element
    /// then this will append the provided element.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The insert occurs at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// cursor.insert_after(10);
    ///
    /// assert_eq!(list_1.len(), 6);
    /// assert!(list_1.iter().eq([&1, &2, &3, &10, &4, &5]));
    /// ```
    pub fn insert_after(&mut self, elem: T) {
        if let Some(curr) = self.curr {
            // Currently not on the "ghost" non-element.
            unsafe {
                let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                    next: None,
                    prev: None,
                    elem,
                })));

                if let Some(next) = (*curr.as_ptr()).next {
                    // Inserting in the middle of the list.
                    (*next.as_ptr()).prev = Some(new_node);
                    (*new_node.as_ptr()).next = Some(next);

                    (*curr.as_ptr()).next = Some(new_node);
                    (*new_node.as_ptr()).prev = Some(curr);
                } else {
                    // No previous node, appending the list.
                    (*curr.as_ptr()).next = Some(new_node);
                    (*new_node.as_ptr()).prev = Some(curr);

                    self.list.tail = Some(new_node);
                }

                self.list.len += 1;
            }
        } else {
            // Currently on the "ghost" non-element, prepend the new node.
            self.list.push_front(elem);
        }
    }

    /// Removes the current element from the list and returns it, or [`None`]
    /// if it is empty.
    ///
    /// If an element is removed, the cursor is moved to the next element, or
    /// the "ghost" non-element if the tail is removed.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The remove occurs at the current cursor index, making
    /// this operation *constant* time.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut list_1 = list![1 => 2 => 3 => 4 => 5];
    /// assert_eq!(list_1.len(), 5);
    ///
    /// let mut cursor = list_1.cursor_mut(); // current node ("ghost")
    ///
    /// cursor.move_next();
    /// cursor.move_next();
    /// cursor.move_next(); // current node (3)
    ///
    /// assert_eq!(cursor.current(), Some(&mut 3));
    /// assert_eq!(cursor.index(), Some(2));
    /// assert_eq!(cursor.remove_current(), Some(3));
    ///
    /// assert_eq!(cursor.current(), Some(&mut 4));
    /// // index remains the same relative to the length change
    /// assert_eq!(cursor.index(), Some(2));
    ///
    /// assert_eq!(list_1.len(), 4);
    /// assert!(list_1.iter().eq([&1, &2, &4, &5]));
    /// ```
    pub fn remove_current(&mut self) -> Option<T> {
        self.curr.map(|curr| {
            // Move cursor to the next element. Should be done before so `curr`
            // is not invalidated.
            self.move_next();

            match self.idx {
                // Means `curr` was the head node before move.
                Some(1) => {
                    // Update `idx` to be relative to the updated list length.
                    *self.idx.as_mut().unwrap() -= 1;

                    // SAFETY: list is non-empty when `curr` is `Some(_)`.
                    self.list.pop_front().unwrap()
                }
                // Means `curr` was a middle node before move.
                Some(_) => {
                    // Update `idx` to be relative to the updated list length.
                    *self.idx.as_mut().unwrap() -= 1;

                    unsafe {
                        (*(*curr.as_ptr()).prev.unwrap().as_ptr()).next = (*curr.as_ptr()).next;
                        (*(*curr.as_ptr()).next.unwrap().as_ptr()).prev = (*curr.as_ptr()).prev;

                        self.list.len -= 1;

                        let boxed_node = Box::from_raw(curr.as_ptr());

                        boxed_node.elem
                    }
                    // `boxed_node` handles it's deallocation...
                }
                // Means `curr` was the tail node before move.
                None => {
                    // SAFETY: list is non-empty when `curr` is `Some(_)`.
                    self.list.pop_back().unwrap()
                }
            }
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::collections::vector::Vector;

    fn generate_test() -> LinkedDeque<i32> {
        list_from(&[0, 1, 2, 3, 4, 5, 6])
    }

    fn list_from<T: Clone>(v: &[T]) -> LinkedDeque<T> {
        v.iter().map(|x| (*x).clone()).collect()
    }

    #[test]
    fn test_basic_front() {
        let mut list = LinkedDeque::new();

        // Try to break an empty list
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        // Try to break a one item list
        list.push_front(10);
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        // Mess around
        list.push_front(10);
        assert_eq!(list.len(), 1);
        list.push_front(20);
        assert_eq!(list.len(), 2);
        list.push_front(30);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(30));
        assert_eq!(list.len(), 2);
        list.push_front(40);
        assert_eq!(list.len(), 3);
        assert_eq!(list.pop_front(), Some(40));
        assert_eq!(list.len(), 2);
        assert_eq!(list.pop_front(), Some(20));
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);
    }

    #[test]
    fn test_basic() {
        let mut m = LinkedDeque::new();
        assert_eq!(m.pop_front(), None);
        assert_eq!(m.pop_back(), None);
        assert_eq!(m.pop_front(), None);
        m.push_front(1);
        assert_eq!(m.pop_front(), Some(1));
        m.push_back(2);
        m.push_back(3);
        assert_eq!(m.len(), 2);
        assert_eq!(m.pop_front(), Some(2));
        assert_eq!(m.pop_front(), Some(3));
        assert_eq!(m.len(), 0);
        assert_eq!(m.pop_front(), None);
        m.push_back(1);
        m.push_back(3);
        m.push_back(5);
        m.push_back(7);
        assert_eq!(m.pop_front(), Some(1));

        let mut n = LinkedDeque::new();
        n.push_front(2);
        n.push_front(3);
        {
            assert_eq!(n.front().unwrap(), &3);
            let x = n.front_mut().unwrap();
            assert_eq!(*x, 3);
            *x = 0;
        }
        {
            assert_eq!(n.back().unwrap(), &2);
            let y = n.back_mut().unwrap();
            assert_eq!(*y, 2);
            *y = 1;
        }
        assert_eq!(n.pop_front(), Some(0));
        assert_eq!(n.pop_front(), Some(1));
    }

    #[test]
    fn test_iterator() {
        let m = generate_test();
        for (i, elt) in m.iter().enumerate() {
            assert_eq!(i as i32, *elt);
        }
        let mut n = LinkedDeque::new();
        assert_eq!(n.iter().next(), None);
        n.push_front(4);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_iterator_double_end() {
        let mut n = LinkedDeque::new();
        assert_eq!(n.iter().next(), None);
        n.push_front(4);
        n.push_front(5);
        n.push_front(6);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(it.next().unwrap(), &6);
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(it.next_back().unwrap(), &4);
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next_back().unwrap(), &5);
        assert_eq!(it.next_back(), None);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_rev_iter() {
        let m = generate_test();
        for (i, elt) in m.iter().rev().enumerate() {
            assert_eq!(6 - i as i32, *elt);
        }
        let mut n = LinkedDeque::new();
        assert_eq!(n.iter().rev().next(), None);
        n.push_front(4);
        let mut it = n.iter().rev();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_mut_iter() {
        let mut m = generate_test();
        let mut len = m.len();
        for (i, elt) in m.iter_mut().enumerate() {
            assert_eq!(i as i32, *elt);
            len -= 1;
        }
        assert_eq!(len, 0);
        let mut n = LinkedDeque::new();
        assert!(n.iter_mut().next().is_none());
        n.push_front(4);
        n.push_back(5);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next().is_some());
        assert!(it.next().is_some());
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert!(it.next().is_none());
    }

    #[test]
    fn test_iterator_mut_double_end() {
        let mut n = LinkedDeque::new();
        assert!(n.iter_mut().next_back().is_none());
        n.push_front(4);
        n.push_front(5);
        n.push_front(6);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(*it.next().unwrap(), 6);
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(*it.next_back().unwrap(), 4);
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(*it.next_back().unwrap(), 5);
        assert!(it.next_back().is_none());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_eq() {
        let mut n: LinkedDeque<u8> = list_from(&[]);
        let mut m = list_from(&[]);
        assert!(n == m);
        n.push_front(1);
        assert!(n != m);
        m.push_back(1);
        assert!(n == m);

        let n = list_from(&[2, 3, 4]);
        let m = list_from(&[1, 2, 3]);
        assert!(n != m);
    }

    #[test]
    fn test_ord() {
        let n = list_from(&[]);
        let m = list_from(&[1, 2, 3]);
        assert!(n < m);
        assert!(m > n);
        assert!(n <= n);
        assert!(n >= n);
    }

    #[test]
    fn test_ord_nan() {
        let nan = 0.0f64 / 0.0;
        let n = list_from(&[nan]);
        let m = list_from(&[nan]);
        assert!(!(n < m));
        assert!(!(n > m));
        assert!(!(n <= m));
        assert!(!(n >= m));

        let n = list_from(&[nan]);
        let one = list_from(&[1.0f64]);
        assert!(!(n < one));
        assert!(!(n > one));
        assert!(!(n <= one));
        assert!(!(n >= one));

        let u = list_from(&[1.0f64, 2.0, nan]);
        let v = list_from(&[1.0f64, 2.0, 3.0]);
        assert!(!(u < v));
        assert!(!(u > v));
        assert!(!(u <= v));
        assert!(!(u >= v));

        let s = list_from(&[1.0f64, 2.0, 4.0, 2.0]);
        let t = list_from(&[1.0f64, 2.0, 3.0, 2.0]);
        assert!(!(s < t));
        assert!(s > one);
        assert!(!(s <= one));
        assert!(s >= one);
    }

    #[test]
    fn test_debug() {
        let list: LinkedDeque<i32> = (0..10).collect();
        assert_eq!(format!("{:?}", list), "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: LinkedDeque<&str> = vec!["just", "one", "test", "more"]
            .iter()
            .copied()
            .collect();
        assert_eq!(format!("{:?}", list), r#"["just", "one", "test", "more"]"#);
    }

    #[test]
    fn test_hashmap() {
        // Check that HashMap works with this as a key

        let list1: LinkedDeque<i32> = (0..10).collect();
        let list2: LinkedDeque<i32> = (1..11).collect();
        let mut map = std::collections::HashMap::new();

        assert_eq!(map.insert(list1.clone(), "list1"), None);
        assert_eq!(map.insert(list2.clone(), "list2"), None);

        assert_eq!(map.len(), 2);

        assert_eq!(map.get(&list1), Some(&"list1"));
        assert_eq!(map.get(&list2), Some(&"list2"));

        assert_eq!(map.remove(&list1), Some("list1"));
        assert_eq!(map.remove(&list2), Some("list2"));

        assert!(map.is_empty());
    }

    #[test]
    fn test_cursor_move_peek() {
        let mut m: LinkedDeque<u32> = LinkedDeque::new();
        m.extend([1, 2, 3, 4, 5, 6]);
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        assert_eq!(cursor.current(), Some(&mut 1));
        assert_eq!(cursor.peek_next(), Some(&mut 2));
        assert_eq!(cursor.peek_prev(), None);
        assert_eq!(cursor.index(), Some(0));
        cursor.move_prev();
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), Some(&mut 1));
        assert_eq!(cursor.peek_prev(), Some(&mut 6));
        assert_eq!(cursor.index(), None);
        cursor.move_next();
        cursor.move_next();
        assert_eq!(cursor.current(), Some(&mut 2));
        assert_eq!(cursor.peek_next(), Some(&mut 3));
        assert_eq!(cursor.peek_prev(), Some(&mut 1));
        assert_eq!(cursor.index(), Some(1));

        let mut cursor = m.cursor_mut();
        cursor.move_prev();
        assert_eq!(cursor.current(), Some(&mut 6));
        assert_eq!(cursor.peek_next(), None);
        assert_eq!(cursor.peek_prev(), Some(&mut 5));
        assert_eq!(cursor.index(), Some(5));
        cursor.move_next();
        assert_eq!(cursor.current(), None);
        assert_eq!(cursor.peek_next(), Some(&mut 1));
        assert_eq!(cursor.peek_prev(), Some(&mut 6));
        assert_eq!(cursor.index(), None);
        cursor.move_prev();
        cursor.move_prev();
        assert_eq!(cursor.current(), Some(&mut 5));
        assert_eq!(cursor.peek_next(), Some(&mut 6));
        assert_eq!(cursor.peek_prev(), Some(&mut 4));
        assert_eq!(cursor.index(), Some(4));
    }

    #[test]
    fn test_cursor_mut_insert() {
        let mut m: LinkedDeque<u32> = LinkedDeque::new();
        m.extend([1, 2, 3, 4, 5, 6]);
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.splice_before(Some(7).into_iter().collect());
        cursor.splice_after(Some(8).into_iter().collect());
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vector<_>>(),
            &[7, 1, 8, 2, 3, 4, 5, 6]
        );
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_prev();
        cursor.splice_before(Some(9).into_iter().collect());
        cursor.splice_after(Some(10).into_iter().collect());
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vector<_>>(),
            &[10, 7, 1, 8, 2, 3, 4, 5, 6, 9]
        );

        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_prev();
        assert_eq!(cursor.remove_current(), None);
        cursor.move_next();
        cursor.move_next();
        assert_eq!(cursor.remove_current(), Some(7));
        cursor.move_prev();
        cursor.move_prev();
        cursor.move_prev();
        assert_eq!(cursor.remove_current(), Some(9));
        cursor.move_next();
        assert_eq!(cursor.remove_current(), Some(10));
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vector<_>>(),
            &[1, 8, 2, 3, 4, 5, 6]
        );

        let mut m: LinkedDeque<u32> = LinkedDeque::new();
        m.extend([1, 8, 2, 3, 4, 5, 6]);
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        let mut p: LinkedDeque<u32> = LinkedDeque::new();
        p.extend([100, 101, 102, 103]);
        let mut q: LinkedDeque<u32> = LinkedDeque::new();
        q.extend([200, 201, 202, 203]);
        cursor.splice_after(p);
        cursor.splice_before(q);
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vector<_>>(),
            &[200, 201, 202, 203, 1, 100, 101, 102, 103, 8, 2, 3, 4, 5, 6]
        );
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_prev();
        let tmp = cursor.split_before();
        assert_eq!(m.into_iter().collect::<Vector<_>>(), &[]);
        m = tmp;
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        cursor.move_next();
        let tmp = cursor.split_after();
        assert_eq!(
            tmp.into_iter().collect::<Vector<_>>(),
            &[102, 103, 8, 2, 3, 4, 5, 6]
        );
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vector<_>>(),
            &[200, 201, 202, 203, 1, 100, 101]
        );
    }

    fn check_links<T: Eq + std::fmt::Debug>(list: &LinkedDeque<T>) {
        let from_front: Vector<_> = list.iter().collect();
        let from_back: Vector<_> = list.iter().rev().collect();
        let re_reved: Vector<_> = from_back.into_iter().rev().collect();

        assert_eq!(from_front, re_reved);
    }
}
