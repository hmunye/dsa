//! A [singly-linked list] with owned nodes.
//!
//! [singly-linked list]: https://en.wikipedia.org/wiki/Linked_list

use core::marker::PhantomData;
use core::ptr;

/// Creates a `SinglyLinked` containing the arguments.
///
/// # Examples
///
/// ```
/// use dsa::prelude::*;
///
/// let mut list = singly![1 => 2 => 3];
/// assert_eq!(list.len(), 3);
///
/// assert_eq!(list.pop_front(), Some(1));
/// assert_eq!(list.pop_front(), Some(2));
/// assert_eq!(list.pop_front(), Some(3));
/// ```
#[macro_export]
macro_rules! singly {
    ($($elem:expr)=>*) => {{
        let mut singly = $crate::collections::singly_linked_list::SinglyLinked::new();
        $(singly.push_back($elem);)*
        singly
    }};
}

/// A [singly-linked list] with owned nodes.
///
/// [singly-linked list]: https://en.wikipedia.org/wiki/Linked_list
#[derive(Debug)]
pub struct SinglyLinked<T> {
    /// Pointer to the head of the list.
    head: *const Node<T>,
    /// Pointer to the tail of the list.
    tail: *const Node<T>,
    /// Number of allocated nodes in the list.
    len: usize,
    /// In order to tell the drop checker that we do own values of type `T`, and
    /// therefore may drop some `T`'s when we drop.
    _marker: PhantomData<T>,
}

struct Node<T> {
    /// Pointer to the next node.
    next: *const Node<T>,
    /// Data the node owns.
    data: T,
}

impl<T> SinglyLinked<T> {
    /// Creates a new, empty `SinglyLinked`.
    ///
    /// The list will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let list: SinglyLinked<i32> = SinglyLinked::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            head: ptr::null(),
            tail: ptr::null(),
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Returns an immutable reference to the first element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list maintains a reference to the `head`, or
    /// first node, making it a *constant* time operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 3];
    /// assert_eq!(list.len(), 2);
    ///
    /// assert_eq!(list.front(), Some(&4));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.front(), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    #[inline]
    pub fn front(&self) -> Option<&T> {
        if !self.head.is_null() {
            unsafe { Some(&(*self.head).data) }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the first element from the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list maintains a reference to the `head`, or
    /// first node, making it a *constant* time operation.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 3];
    /// assert_eq!(list.len(), 2);
    ///
    /// assert_eq!(list.front_mut(), Some(&mut 4));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.front_mut(), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    #[inline]
    pub fn front_mut(&mut self) -> Option<&mut T> {
        if !self.head.is_null() {
            unsafe { Some(&mut (*self.head.cast_mut()).data) }
        } else {
            None
        }
    }

    /// Prepends an element to the front of the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. A singly linked list can prepend nodes in *constant*
    /// time since only pointers are manipulated, regardless of the number of
    /// nodes within the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list: SinglyLinked<i32> = SinglyLinked::new();
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.len(), 2);
    /// assert_eq!(list.pop_front(), Some(4));
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn push_front(&mut self, data: T) {
        unsafe {
            let new_node: *const Node<T> = Box::into_raw(Box::new(Node {
                next: ptr::null(),
                data,
            }));

            if !self.head.is_null() {
                (*new_node.cast_mut()).next = self.head;
            } else {
                self.tail = new_node;
            }

            self.head = new_node;
            self.len += 1;
        }
    }

    /// Removes the first element from the list and returns it, or [`None`] if
    /// it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. A singly linked list can remove the `head` node in
    /// *constant* time since only pointers are manipulated, regardless of the
    /// number of nodes within the list.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list: SinglyLinked<i32> = SinglyLinked::new();
    ///
    /// assert_eq!(list.pop_front(), None);
    ///
    /// list.push_front(3);
    /// list.push_front(4);
    /// list.push_front(5);
    ///
    /// assert_eq!(list.len(), 3);
    /// assert_eq!(list.pop_front(), Some(5));
    /// assert_eq!(list.pop_front(), Some(4));
    /// assert_eq!(list.pop_front(), Some(3));
    /// assert_eq!(list.pop_front(), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        if !self.head.is_null() {
            unsafe {
                let boxed_node = Box::from_raw(self.head.cast_mut());
                let data = boxed_node.data;

                self.head = boxed_node.next;

                if self.head.is_null() {
                    self.tail = ptr::null();
                }

                self.len -= 1;

                Some(data)

                // `boxed_node` handles it's deallocation...
            }
        } else {
            None
        }
    }

    /// Returns an immutable reference to the last element of the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list maintains a reference to the `tail`, or
    /// last node, making it a *constant* time operation. If not `tail`
    /// reference was maintained, it would take *O*(*n*) time to traverse to
    /// the last node and return it's data.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 3];
    /// assert_eq!(list.len(), 2);
    ///
    /// assert_eq!(list.back(), Some(&3));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.back(), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    #[inline]
    pub fn back(&self) -> Option<&T> {
        if !self.tail.is_null() {
            unsafe { Some(&(*self.tail).data) }
        } else {
            None
        }
    }

    /// Returns an immutable reference to the last element of the list, or
    /// [`None`] if it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list maintains a reference to the `tail`, or
    /// last node, making it a *constant* time operation. If no `tail` reference
    /// was maintained, it would take *O*(*n*) time to traverse to the last node
    /// and return it's data.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 3];
    /// assert_eq!(list.len(), 2);
    ///
    /// assert_eq!(list.back(), Some(&3));
    ///
    /// list.pop_front();
    /// list.pop_front();
    ///
    /// assert_eq!(list.back(), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    #[inline]
    pub fn back_mut(&mut self) -> Option<&mut T> {
        if !self.tail.is_null() {
            unsafe { Some(&mut (*self.tail.cast_mut()).data) }
        } else {
            None
        }
    }

    /// Appends an element to the back of the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time. The list maintains a reference to the `tail`, or
    /// last node, making it a *constant* time operation. If no `tail` reference
    /// was maintained, it would take *O*(*n*) time to traverse to the last node
    /// and append the new node.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list: SinglyLinked<i32> = SinglyLinked::new();
    /// list.push_back(3);
    /// list.push_back(4);
    /// assert_eq!(list.len(), 2);
    /// assert_eq!(list.pop_front(), Some(3));
    /// assert_eq!(list.len(), 1);
    /// ```
    pub fn push_back(&mut self, data: T) {
        unsafe {
            let new_node: *const Node<T> = Box::into_raw(Box::new(Node {
                next: ptr::null(),
                data,
            }));

            if !self.tail.is_null() {
                (*self.tail.cast_mut()).next = new_node;
            } else {
                self.head = new_node;
            }

            self.tail = new_node;
            self.len += 1;
        }
    }

    /// Inserts an element at the provided `index` into the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the index. Insertion itself is
    /// a *constant* time operation, since only pointer manipulation occurs,
    /// regardless of the list's length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 2 => 1];
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.get(1), Some(&2));
    /// list.insert_at(3, 1);
    /// assert_eq!(list.len(), 4);
    /// assert_eq!(list.get(1), Some(&3));
    /// ```
    pub fn insert_at(&mut self, data: T, idx: usize) {
        if idx == 0 {
            return self.push_front(data);
        } else if idx == self.len() - 1 {
            return self.push_back(data);
        }

        // The case of `index` 0 is handled, meaning `prev` and `curr` should
        // not be aliasing. Out-of-bounds index should also be handled here.
        let (prev, curr) = self.traverse(idx);
        // `prev` should never be `null`, unless `curr` is already `null`.
        if prev.is_null() || curr.is_null() {
            return;
        }

        unsafe {
            let new_node = Box::into_raw(Box::new(Node {
                next: curr, // points to the node at `idx`
                data,
            }));

            (*prev.cast_mut()).next = new_node;

            self.len += 1;
        }
    }

    /// Removes an element at the provided `index` from the list, returning the
    /// removed node's data, or [`None`] if it could not be found.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the index. Removal itself is
    /// a *constant* time operation, since only pointer manipulation occurs,
    /// regardless of the list's length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 2 => 1];
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.get(1), Some(&2));
    /// list.insert_at(3, 1);
    /// assert_eq!(list.len(), 4);
    ///
    /// assert_eq!(list.remove_at(1), Some(3));
    /// assert_eq!(list.remove_at(2), Some(1));
    /// assert_eq!(list.remove_at(1), Some(2));
    /// assert_eq!(list.remove_at(0), Some(4));
    ///
    /// assert_eq!(list.remove_at(0), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn remove_at(&mut self, idx: usize) -> Option<T> {
        if idx == 0 {
            self.pop_front()
        } else {
            let (prev, curr) = self.traverse(idx);
            // `prev` could only be `null` if the index passed to the function
            // was 0, which is already handled, or the list is empty. `curr` is
            // also `null` when the list is empty or the index is invalid.
            if prev.is_null() || curr.is_null() {
                None
            } else {
                unsafe {
                    let mut boxed_node = Box::from_raw(curr.cast_mut());
                    let data = boxed_node.data;

                    // Removing the tail.
                    if boxed_node.next.is_null() {
                        (*prev.cast_mut()).next = ptr::null();
                        self.tail = prev;
                    } else {
                        (*prev.cast_mut()).next = boxed_node.next;
                    }

                    boxed_node.next = ptr::null();
                    self.len -= 1;

                    Some(data)
                    // `boxed_node` handles it's deallocation...
                }
            }
        }
    }

    /// Returns an immutable reference to the element at the provided index of
    /// the list, or [`None`] if it could not be found.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the index.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = SinglyLinked::new();
    /// assert_eq!(list.get(0), None);
    /// assert_eq!(list.len(), 0);
    ///
    /// list.push_front(2);
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.get(0), Some(&4));
    /// assert_eq!(list.get(1), Some(&3));
    /// assert_eq!(list.get(2), Some(&2));
    ///
    /// assert_eq!(list.get(20), None);
    /// assert_eq!(list.len(), 3);
    /// ```
    #[inline]
    pub fn get(&self, idx: usize) -> Option<&T> {
        // Out-of-bounds indexing is handled, `curr` would be equal to
        // `ptr::null`.
        let (_, curr) = self.traverse(idx);
        if curr.is_null() {
            None
        } else {
            unsafe { Some(&(*curr).data) }
        }
    }

    /// Returns a mutable reference to the element at the provided index of the
    /// list, or [`None`] if it could not be found.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the index.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = SinglyLinked::new();
    /// assert_eq!(list.get_mut(0), None);
    /// assert_eq!(list.len(), 0);
    ///
    /// list.push_front(2);
    /// list.push_front(3);
    /// list.push_front(4);
    ///
    /// assert_eq!(list.get_mut(0), Some(&mut 4));
    /// assert_eq!(list.get_mut(1), Some(&mut 3));
    /// assert_eq!(list.get_mut(2), Some(&mut 2));
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.get_mut(20), None);
    /// ```
    #[inline]
    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        // Out-of-bounds indexing is handled, `curr` would be equal to
        // `ptr::null` in that case.
        let (_, curr) = self.traverse(idx);
        if curr.is_null() {
            None
        } else {
            unsafe { Some(&mut (*curr.cast_mut()).data) }
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

    /// Traverses the list to the provided `index`. This function returns a pair
    /// of pointers, one to the previous node before the index node and one to
    /// the node at the index.
    ///
    /// Caller should check from the return value `(prev, curr)`, whether `curr`
    /// equals `ptr::null`, meaning the provided index was invalid. `prev` would
    /// in this case point to the `tail` of the list. If `prev` equals
    /// `ptr::null`, the index provided was 0, and `curr` would be pointing to
    /// the `head` of the list.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the index.
    fn traverse(&self, mut idx: usize) -> (*const Node<T>, *const Node<T>) {
        let mut curr = self.head;
        // So we don't fall in the case where `prev` and `curr` alias.
        let mut prev = ptr::null();

        while idx > 0 && !curr.is_null() {
            unsafe {
                prev = curr;
                curr = (*curr).next;
            }
            idx -= 1;
        }

        (prev, curr)
    }
}

impl<T: PartialEq> SinglyLinked<T> {
    /// Removes an element from the list, using a provided `key`, which is the
    /// data of the node. This function returns the removed node's data, or
    /// [`None`] if it could not be found.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the `key`. Removal itself is
    /// a *constant* time operation, since only pointer manipulation occurs,
    /// regardless of the list's length.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::prelude::*;
    ///
    /// let mut list = singly![4 => 2 => 1];
    /// assert_eq!(list.remove(&0), None);
    /// assert_eq!(list.len(), 3);
    ///
    /// assert_eq!(list.get(1), Some(&2));
    /// list.insert_at(3, 1);
    /// assert_eq!(list.remove(&4), Some(4));
    ///
    /// assert_eq!(list.remove(&2), Some(2));
    /// assert_eq!(list.remove(&1), Some(1));
    ///
    /// assert_eq!(list.remove(&3), Some(3));
    /// assert_eq!(list.remove(&3), None);
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn remove(&mut self, key: &T) -> Option<T> {
        let (prev, curr) = self.traverse_with_key(key);

        // When `curr` is `null`, either the list is empty or a node
        // corresponding to the key was not found.
        if curr.is_null() {
            None
        } else {
            unsafe {
                let mut boxed_node = Box::from_raw(curr.cast_mut());
                let data = boxed_node.data;

                // If `prev` is null, then `curr` is the head of the list or the
                // list is empty.
                if prev.is_null() {
                    self.head = boxed_node.next;

                    if self.head.is_null() {
                        self.tail = ptr::null();
                    }
                } else if boxed_node.next.is_null() {
                    // Removing the tail.
                    (*prev.cast_mut()).next = ptr::null();
                    self.tail = prev;
                } else {
                    (*prev.cast_mut()).next = boxed_node.next;
                }

                boxed_node.next = ptr::null();
                self.len -= 1;

                Some(data)
                // `boxed_node` handles it's deallocation...
            }
        }
    }

    /// Traverses the list using the provided `key`. This function returns a
    /// pair of pointers, one to the previous node before the found node and one
    /// to the node corresponding to the key.
    ///
    /// Caller should check from the return value `(prev, curr)`, whether `curr`
    /// equals `ptr::null`, meaning the provided key was not found. `prev`
    /// would in this case point to the `tail` of the list. If `prev` equals
    /// `ptr::null`, `curr` would point to the `head` of the list, which
    /// contained a matching key.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*n*) time. The list is linearly traversed, following pointers
    /// until reaching the node corresponding to the provided `key`.
    fn traverse_with_key(&self, key: &T) -> (*const Node<T>, *const Node<T>) {
        let mut curr = self.head;
        // So we don't fall in the case where `prev` and `curr` alias.
        let mut prev = ptr::null();

        // NOTE: Logical operators are short-circuiting, meaning the dereference
        // should always be safe.
        unsafe {
            while !curr.is_null() && (*curr).data != *key {
                prev = curr;
                curr = (*curr).next;
            }
        }

        (prev, curr)
    }
}

impl<T> Drop for SinglyLinked<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

impl<T> Default for SinglyLinked<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_basic_front() {
        let mut list = SinglyLinked::new();

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
}
