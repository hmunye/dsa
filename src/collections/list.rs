//! A doubly-linked list with owned nodes.
//!
//! # Time Complexities
//!
//! | push_* | pop_*  |
//! |--------|--------|
//! | *O*(1) | *O*(1) |

use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ptr::NonNull;
use std::{fmt, mem};

/*
* Reference:
* https://rust-unofficial.github.io/too-many-lists/sixth.html
*/

/// A doubly-linked list with owned nodes.
///
/// # Time Complexities
///
/// | push_* | pop_*  |
/// |--------|--------|
/// | *O*(1) | *O*(1) |
pub struct List<T> {
    /// Pointer to the first node of the list.
    head: Link<T>,
    /// Pointer to the last node of the list.
    tail: Link<T>,
    /// Specifies the number of actual elements within the list.
    len: usize,
    //
    // Since `List<T>` implements `Drop`, `dropck` will treat our type as
    // owning a `T`, and will assume that values of type `T` might be accessed
    // when dropping, making `PhantomData` unnecessary for that purpose.
}

/// Ensures pointers are covariant and "nullable".
type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug)]
struct Node<T> {
    /// Data of the node.
    data: T,
    /// Pointer to the next node in the sequence.
    next: Link<T>,
    /// Pointer to the previous node in the sequence.
    prev: Link<T>,
}

/// Iterator that yields references over the elements of a `List`.
#[derive(Debug)]
pub struct Iter<'a, T> {
    next: Link<T>,
    prev: Link<T>,
    len: usize,
    /// Ensures the lifetime is bounded.
    _boo: PhantomData<&'a T>,
}

/// Iterator that yields mutable references over the elements of a `List`.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    next: Link<T>,
    prev: Link<T>,
    len: usize,
    /// Ensures the lifetime is bounded.
    _boo: PhantomData<&'a mut T>,
}

/// Consuming iterator, that is, one that moves each value out of the `List`.
#[derive(Debug)]
#[repr(transparent)]
pub struct IntoIter<T>(List<T>);

impl<T> List<T> {
    /// Creates a new, empty `List<T>`.
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: None,
            tail: None,
            len: 0,
        }
    }

    /// Adds an element to the front of the list.
    pub fn push_front(&mut self, data: T) {
        // SAFETY: `Box::new` is guaranteed to return a well-aligned pointer to
        // an allocation, or OOM.
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                data,
                next: None,
                prev: None,
            })));

            if let Some(old_head) = self.head {
                (*new_node.as_ptr()).next = Some(old_head);
                (*old_head.as_ptr()).prev = Some(new_node);
            } else {
                self.tail = Some(new_node);
            }

            self.head = Some(new_node);
            self.len += 1;
        }
    }

    /// Removes the first element and returns it, or [`None`] if the list is
    /// empty.
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|head| {
            unsafe {
                // SAFETY: `head` was originally created from `Box::new` and is
                // only ever converted back to a `Box` when uniquely owned. No
                // aliasing occurs.
                let boxed_node = Box::from_raw(head.as_ptr());
                let out = boxed_node.data;

                self.head = boxed_node.next;
                if let Some(head) = self.head {
                    (*head.as_ptr()).prev = None;
                } else {
                    self.tail = None;
                }

                self.len -= 1;
                out

                // `boxed_node` handles deallocation of the node.
            }
        })
    }

    /// Provides a reference to the front element, or [`None`] if the list is
    /// empty.
    #[inline]
    pub fn front(&self) -> Option<&T> {
        self.head.map(|head| unsafe { &(*head.as_ptr()).data })
    }

    /// Provides a mutable reference to the front element, or [`None`] if the
    /// list is empty.
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.head.map(|head| unsafe { &mut (*head.as_ptr()).data })
    }

    /// Adds an element to the back of the list.
    pub fn push_back(&mut self, data: T) {
        // SAFETY: `Box::new` is guaranteed to return a well-aligned pointer to
        // an allocation, or OOM.
        unsafe {
            let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                data,
                next: None,
                prev: None,
            })));

            if let Some(old_tail) = self.tail {
                (*new_node.as_ptr()).prev = Some(old_tail);
                (*old_tail.as_ptr()).next = Some(new_node);
            } else {
                self.head = Some(new_node);
            }

            self.tail = Some(new_node);
            self.len += 1;
        }
    }

    /// Removes the last element and returns it, or [`None`] if the list is
    /// empty.
    pub fn pop_back(&mut self) -> Option<T> {
        self.tail.map(|tail| {
            unsafe {
                // SAFETY: `tail` was originally created from `Box::new` and is
                // only ever converted back to a `Box` when uniquely owned. No
                // aliasing occurs.
                let boxed_node = Box::from_raw(tail.as_ptr());
                let out = boxed_node.data;

                self.tail = boxed_node.prev;
                if let Some(tail) = self.tail {
                    (*tail.as_ptr()).next = None;
                } else {
                    self.head = None;
                }

                self.len -= 1;
                out

                // `boxed_node` handles deallocation of the node.
            }
        })
    }

    /// Provides a reference to the back element, or [`None`] if the list is
    /// empty.
    #[inline]
    pub fn back(&self) -> Option<&T> {
        self.tail.map(|tail| unsafe { &(*tail.as_ptr()).data })
    }

    /// Provides a mutable reference to the back element, or [`None`] if the
    /// list is empty.
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.tail.map(|tail| unsafe { &mut (*tail.as_ptr()).data })
    }

    /// Creates a forward iterator, yielding `&T`.
    #[inline]
    pub const fn iter(&self) -> Iter<'_, T> {
        Iter {
            next: self.head,
            prev: self.tail,
            len: self.len,
            _boo: PhantomData,
        }
    }

    /// Creates a forward iterator, yielding `&mut T`.
    #[inline]
    pub const fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            next: self.head,
            prev: self.tail,
            len: self.len,
            _boo: PhantomData,
        }
    }

    /// Creates a mutable cursor over the list.
    #[inline]
    pub const fn cursor_mut(&mut self) -> CursorMut<'_, T> {
        CursorMut {
            // Initially point to the "ghost" non-element.
            curr: None,
            list: self,
            index: 0,
        }
    }

    /// Returns the number of elements in the list.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the list contains no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all elements from the list.
    #[inline]
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }
}

// SAFETY: Each `List<T>` owns its nodes and `T`, allowing it to be safely
// transferred across threads, as long as `T` can also be safely transferred.
unsafe impl<T: Send> Send for List<T> {}

// SAFETY: `Iter` contains only shared references to `T`, so it can be safely
// transferred between threads if `T` is `Send`.
unsafe impl<'a, T: Send> Send for Iter<'a, T> {}

// SAFETY: `IterMut` contains exclusive references tied to `T`, so it can be
// safely transferred between threads if `T` is `Send`.
unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}

// SAFETY: Since public methods allow accessing `&T` from `&List<T>` without
// synchronization (e.g., via `front`), `T` must be `Sync` for `List<T>` to be
// `Sync`. `List<T>` uses no interior mutability, with all mutations happening
// through `&mut` references.
unsafe impl<T: Sync> Sync for List<T> {}

// SAFETY: Similar to `Iter: Send`, `Iter` can be safely shared between threads
// because it only contains shared references to `T`, and `T` must implement
// `Sync`.
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

// SAFETY: `IterMut` yields mutable references to its items (`&mut T`), but
// methods that produce these mutable references require exclusive access to the
// iterator (`&mut self`). Even if `IterMut` itself is shared across threads
// (`&IterMut`), it effectively becomes read-only. Therefore, `IterMut` is
// `Sync` iff `T: Sync`.
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}

impl<T> IntoIterator for List<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter(self)
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.pop_front()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.0.len, Some(self.0.len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop_back()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.0.len
    }
}

impl<'a, T> IntoIterator for &'a List<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.next.map(|node| unsafe {
                self.len -= 1;
                self.next = (*node.as_ptr()).next;
                &(*node.as_ptr()).data
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
            self.prev.map(|node| unsafe {
                self.len -= 1;
                self.prev = (*node.as_ptr()).prev;
                &(*node.as_ptr()).data
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

impl<'a, T> IntoIterator for &'a mut List<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.len > 0 {
            self.next.map(|node| unsafe {
                self.len -= 1;
                self.next = (*node.as_ptr()).next;
                &mut (*node.as_ptr()).data
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
            self.prev.map(|node| unsafe {
                self.len -= 1;
                self.prev = (*node.as_ptr()).prev;
                &mut (*node.as_ptr()).data
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

impl<T> Default for List<T> {
    fn default() -> Self {
        List::new()
    }
}

impl<T> Extend<T> for List<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            self.push_back(item);
        }
    }
}

impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        let mut list = Self::new();

        for item in self {
            list.push_back(item.clone())
        }

        list
    }
}

impl<T> FromIterator<T> for List<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        list.extend(iter);
        list
    }
}

impl<T: fmt::Debug> fmt::Debug for List<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for List<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for List<T> {}

impl<T: PartialOrd> PartialOrd for List<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for List<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for List<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for item in self {
            item.hash(state);
        }
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

/// A `Cursor` is similar to an iterator but allows bidirectional navigation
/// and safe mutation of the list during traversal.
///
/// Unlike standard iterators, it ties the lifetime of yielded references to
/// itself rather than the list, preventing multiple simultaneous borrows.
///
/// The cursor always sits between two elements and indexes the list in a
/// logically circular manner.
#[derive(Debug)]
pub struct CursorMut<'a, T> {
    curr: Link<T>,
    list: &'a mut List<T>,
    index: usize,
}

impl<'a, T> CursorMut<'a, T> {
    /// Moves the cursor to the next element of the `List`. If the cursor is
    /// pointing to the "ghost" non-element then this will move it to the first
    /// element of the list. If it is pointing to the last element of the list
    /// then this will move it to the "ghost" non-element.
    pub fn move_next(&mut self) {
        match self.curr.take() {
            // We are pointing to a real element, move to next.
            Some(node) => unsafe {
                if self.index == self.list.len - 1 {
                    self.curr = None
                } else {
                    self.curr = node.as_ref().next;
                    self.index += 1;
                }
            },
            // We are now pointing to the "ghost" non-element, next will point
            // to the head.
            None => {
                self.curr = self.list.head;
                self.index = 0;
            }
        }
    }

    /// Returns a mutable reference to the next element, or [`None`] if the
    /// cursor is currently pointing to the "ghost" non-element.
    pub fn peek_next(&mut self) -> Option<&mut T> {
        unsafe {
            // Match on `self.curr` first, since the "ghost" non-element should
            // yield "head" as its next.
            let next = match self.curr {
                None => self.list.head,
                Some(node) => node.as_ref().next,
            };

            next.map(|next| &mut (*next.as_ptr()).data)
        }
    }

    /// Moves the cursor to the previous element of the `List`. If the cursor is
    /// pointing to the "ghost" non-element then this will move it to the last
    /// element of the list. If it is pointing to the first element of the list
    /// then this will move it to the "ghost" non-element.
    pub fn move_prev(&mut self) {
        match self.curr.take() {
            // We are pointing to a real element, move to next.
            Some(node) => unsafe {
                if self.index == 0 {
                    self.curr = None;
                } else {
                    self.curr = node.as_ref().prev;
                    // So we don't underflow `index` when traversing back to the
                    // "ghost" non-element.
                    self.index = self.index.saturating_sub(1);
                }
            },
            // We are now pointing to the "ghost" non-element, next will point
            // to the tail.
            None => {
                self.curr = self.list.tail;
                // So we don't underflow `index` if the list is empty.
                self.index = self.list.len.saturating_sub(1);
            }
        }
    }

    /// Returns a mutable reference to the previous element, or [`None`] if the
    /// cursor is currently pointing to the "ghost" non-element.
    pub fn peek_prev(&mut self) -> Option<&mut T> {
        unsafe {
            // Match on `self.curr` first, since the "ghost" non-element should
            // yield "tail" as its prev.
            let prev = match self.curr {
                None => self.list.tail,
                Some(node) => node.as_ref().prev,
            };

            prev.map(|next| &mut (*next.as_ptr()).data)
        }
    }

    /// Splits the list into two _before_ the current element. This will return
    /// a new list consisting of everything before the cursor, with the original
    /// list retaining everything after.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire
    /// contents of the `List` are moved.
    pub fn split_before(&mut self) -> List<T> {
        if let Some(curr) = self.curr {
            unsafe {
                let out_head = self.list.head;
                let out_tail = curr.as_ref().prev;
                let out_len = self.index;

                if let Some(prev) = out_tail {
                    (*prev.as_ptr()).next = None;
                    (*curr.as_ptr()).prev = None;
                }

                self.list.head = Some(curr);
                self.list.len -= self.index;
                self.index = 0;

                List {
                    head: out_head,
                    tail: out_tail,
                    len: out_len,
                }
            }
        } else {
            // Cursor is on the "ghost" non-element, so replace and return the
            // entire list.
            mem::take(self.list)
        }
    }

    /// Splits the list into two _after_ the current element. This will return
    /// a new list consisting of everything after the cursor, with the original
    /// list retaining everything before.
    ///
    /// If the cursor is pointing at the "ghost" non-element then the entire
    /// contents of the `List` are moved.
    pub fn split_after(&mut self) -> List<T> {
        if let Some(curr) = self.curr {
            unsafe {
                let out_head = (*curr.as_ptr()).next;
                let out_tail = self.list.tail;
                let out_len = self.list.len - (self.index + 1);

                if let Some(next) = out_head {
                    (*next.as_ptr()).prev = None;
                    (*curr.as_ptr()).next = None;
                }

                self.list.tail = Some(curr);
                // `index` will be pointing to the "tail".
                self.list.len = self.index + 1;

                List {
                    head: out_head,
                    tail: out_tail,
                    len: out_len,
                }
            }
        } else {
            // Cursor is on the "ghost" non-element, so replace and return the
            // entire list.
            mem::take(self.list)
        }
    }

    /// Inserts the elements from the given `List` _before_ the current element.
    ///
    /// If the cursor is pointing at the “ghost” non-element then the new
    /// elements are inserted at the end of the `List`.
    pub fn splice_before(&mut self, mut input: List<T>) {
        // The `input` list is considered empty if it lacks a valid "head" and
        // "tail". We `take` them to avoid leaving dangling pointers when
        // `input` is dropped.
        if let (Some(input_head), Some(input_tail)) = (input.head.take(), input.tail.take()) {
            unsafe {
                if let Some(curr) = self.curr {
                    if self.index == 0 {
                        // Prepending to the current list.
                        (*curr.as_ptr()).prev = Some(input_tail);
                        (*input_tail.as_ptr()).next = Some(curr);
                        self.list.head = Some(input_head);
                    } else {
                        // Splicing in the middle of the current list.
                        if let Some(prev) = (*curr.as_ptr()).prev {
                            (*curr.as_ptr()).prev = Some(input_tail);
                            (*input_tail.as_ptr()).next = Some(curr);

                            (*prev.as_ptr()).next = Some(input_head);
                            (*input_head.as_ptr()).prev = Some(prev);
                        }
                    }

                    self.index += input.len;
                } else if let Some(tail) = self.list.tail {
                    // Appending to the current list. This needs to be a
                    // separate check since being on the "ghost" non-element
                    // does not mean the list is empty.

                    (*tail.as_ptr()).next = Some(input_head);
                    (*input_head.as_ptr()).prev = Some(tail);
                    self.list.tail = Some(input_tail);
                } else {
                    // List is empty, so become `input` and remain on "ghost".
                    // Restore `input`'s "head" and "tail" before moving it.
                    input.head = Some(input_head);
                    input.tail = Some(input_tail);
                    mem::swap(self.list, &mut input);
                }

                self.list.len += input.len;
                input.len = 0;
            }
        }
    }

    /// Inserts the elements from the given `List` _after_ the current element.
    ///
    /// If the cursor is pointing at the “ghost” non-element then the new
    /// elements are inserted at the beginning of the `List`.
    pub fn splice_after(&mut self, mut input: List<T>) {
        // The `input` list is considered empty if it lacks a valid "head" and
        // "tail". We `take` them to avoid leaving dangling pointers when
        // `input` is dropped.
        if let (Some(input_head), Some(input_tail)) = (input.head.take(), input.tail.take()) {
            unsafe {
                if let Some(curr) = self.curr {
                    if self.index == self.list.len - 1 {
                        // Appending to the current list.
                        (*curr.as_ptr()).next = Some(input_head);
                        (*input_head.as_ptr()).prev = Some(curr);
                        self.list.tail = Some(input_tail);
                    } else {
                        // Splicing in the middle of the current list.
                        if let Some(next) = (*curr.as_ptr()).next {
                            (*curr.as_ptr()).next = Some(input_head);
                            (*input_head.as_ptr()).prev = Some(curr);

                            (*next.as_ptr()).prev = Some(input_tail);
                            (*input_tail.as_ptr()).next = Some(next);
                        }
                    }

                    // `index` does not need to be updated.
                } else if let Some(head) = self.list.head {
                    // Prepending to the current list. This needs to be a
                    // separate check since being on the "ghost" non-element
                    // does not mean the list is empty.

                    (*head.as_ptr()).prev = Some(input_tail);
                    (*input_tail.as_ptr()).next = Some(head);
                    self.list.head = Some(input_head);
                } else {
                    // List is empty, so become `input` and remain on "ghost".
                    // Restore `input`'s "head" and "tail" before moving it.
                    input.head = Some(input_head);
                    input.tail = Some(input_tail);
                    mem::swap(self.list, &mut input);
                }

                self.list.len += input.len;
                input.len = 0;
            }
        }
    }

    /// Removes the currently pointed to element and returns it, or [`None`] if
    /// the cursor is currently pointing to the "ghost" non-element.
    ///
    /// The cursor is moved to point to the next element in the `List`.
    pub fn remove_current(&mut self) -> Option<T> {
        let current = self.curr?;

        unsafe {
            match self.index {
                // Pointing to "head".
                0 => {
                    if let Some(next) = current.as_ref().next {
                        (*next.as_ptr()).prev = None;
                        self.list.head = Some(next);
                    }
                }
                // Pointing to "tail".
                idx if idx == self.list.len - 1 => {
                    if let Some(prev) = current.as_ref().prev {
                        (*prev.as_ptr()).next = None;
                        self.list.tail = Some(prev);
                    }
                }
                _ => {
                    if let Some(next) = current.as_ref().next
                        && let Some(prev) = current.as_ref().prev
                    {
                        (*next.as_ptr()).prev = Some(prev);
                        (*prev.as_ptr()).next = Some(next);
                    }
                }
            }

            self.move_next();

            // SAFETY: `current` was originally created from `Box::new` and is
            // only ever converted back to a `Box` when uniquely owned. No
            // aliasing occurs.
            let boxed_node = Box::from_raw(current.as_ptr());
            let out = boxed_node.data;

            self.list.len -= 1;
            Some(out)
        }

        // `boxed_node` handles deallocation of the node.
    }

    /// Returns the cursor position index within the `List`, or [`None`] if the
    /// cursor is currently pointing to the "ghost" non-element.
    #[inline]
    pub const fn index(&self) -> Option<usize> {
        if self.curr.is_some() {
            Some(self.index)
        } else {
            None
        }
    }

    /// Returns a mutable reference to the current element, or [`None`] if the
    /// cursor is currently pointing to the "ghost" non-element.
    pub fn current(&mut self) -> Option<&mut T> {
        self.curr.map(|node| unsafe { &mut (*node.as_ptr()).data })
    }
}

#[allow(dead_code)]
fn assert_properties() {
    fn is_send<T: Send>() {}
    fn is_sync<T: Sync>() {}

    is_send::<List<i32>>();
    is_sync::<List<i32>>();

    is_send::<IntoIter<i32>>();
    is_sync::<IntoIter<i32>>();

    is_send::<Iter<'_, i32>>();
    is_sync::<Iter<'_, i32>>();

    is_send::<IterMut<'_, i32>>();
    is_sync::<IterMut<'_, i32>>();

    fn forward_list_covariant<'a, T>(x: List<&'static T>) -> List<&'a T> {
        x
    }
    fn iter_covariant<'i, 'a, T>(x: Iter<'i, &'static T>) -> Iter<'i, &'a T> {
        x
    }
    fn into_iter_covariant<'a, T>(x: IntoIter<&'static T>) -> IntoIter<&'a T> {
        x
    }
}

/// ```compile_fail
/// use dsa::collections::list::IterMut;
///
/// fn iter_mut_covariant<'i, 'a, T>(x: IterMut<'i, &'static T>) -> IterMut<'i, &'a T> { x }
/// ```
#[allow(dead_code)]
fn iter_mut_invariant() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn generate_test() -> List<i32> {
        list_from(&[0, 1, 2, 3, 4, 5, 6])
    }

    fn list_from<T: Clone>(v: &[T]) -> List<T> {
        v.iter().map(|x| (*x).clone()).collect()
    }

    #[test]
    fn test_basic_front() {
        let mut list = List::new();

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
        let mut m = List::new();
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

        let mut n = List::new();
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
        let mut n = List::new();
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
        let mut n = List::new();
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
        let mut n = List::new();
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
        let mut n = List::new();
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
        let mut n = List::new();
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
        let mut n: List<u8> = list_from(&[]);
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
        let list: List<i32> = (0..10).collect();
        assert_eq!(format!("{:?}", list), "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: List<&str> = vec!["just", "one", "test", "more"]
            .iter()
            .copied()
            .collect();
        assert_eq!(format!("{:?}", list), r#"["just", "one", "test", "more"]"#);
    }

    #[test]
    fn test_hash() {
        let list1: List<i32> = (0..10).collect();
        let list2: List<i32> = (1..11).collect();
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
        let mut m: List<u32> = List::new();
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
        let mut m: List<u32> = List::new();
        m.extend([1, 2, 3, 4, 5, 6]);
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.splice_before(Some(7).into_iter().collect());
        cursor.splice_after(Some(8).into_iter().collect());
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vec<_>>(),
            &[7, 1, 8, 2, 3, 4, 5, 6]
        );
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_prev();
        cursor.splice_before(Some(9).into_iter().collect());
        cursor.splice_after(Some(10).into_iter().collect());
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vec<_>>(),
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
            m.iter().cloned().collect::<Vec<_>>(),
            &[1, 8, 2, 3, 4, 5, 6]
        );

        let mut m: List<u32> = List::new();
        m.extend([1, 8, 2, 3, 4, 5, 6]);
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        let mut p: List<u32> = List::new();
        p.extend([100, 101, 102, 103]);
        let mut q: List<u32> = List::new();
        q.extend([200, 201, 202, 203]);
        cursor.splice_after(p);
        cursor.splice_before(q);
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vec<_>>(),
            &[200, 201, 202, 203, 1, 100, 101, 102, 103, 8, 2, 3, 4, 5, 6]
        );
        let mut cursor = m.cursor_mut();
        cursor.move_next();
        cursor.move_prev();
        let tmp = cursor.split_before();
        assert_eq!(m.into_iter().collect::<Vec<_>>(), &[]);
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
            tmp.into_iter().collect::<Vec<_>>(),
            &[102, 103, 8, 2, 3, 4, 5, 6]
        );
        check_links(&m);
        assert_eq!(
            m.iter().cloned().collect::<Vec<_>>(),
            &[200, 201, 202, 203, 1, 100, 101]
        );
    }

    fn check_links<T: Eq + std::fmt::Debug>(list: &List<T>) {
        let from_front: Vec<_> = list.iter().collect();
        let from_back: Vec<_> = list.iter().rev().collect();
        let re_reved: Vec<_> = from_back.into_iter().rev().collect();

        assert_eq!(from_front, re_reved);
    }
}
