//! A singly-linked list with owned nodes.
//!
//! # Time Complexities
//!
//! | [push_front] | [pop_front] | [clear] | [reverse] | [find] |
//! |--------------|-------------|---------|-----------|--------|
//! |    *O*(1)    |   *O*(1)    |  *O*(n) |   *O*(n)  | *O*(n) |
//!
//! [push_front]: ForwardList::push_front
//! [pop_front]:  ForwardList::pop_front
//! [clear]:      ForwardList::clear
//! [reverse]:    ForwardList::reverse
//! [find]:       ForwardList::find

use std::borrow::Borrow;
use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ptr::NonNull;

/// A singly-linked list with owned nodes.
///
/// # Time Complexities
///
/// | [push_front] | [pop_front] | [clear] | [reverse] | [find] |
/// |--------------|-------------|---------|-----------|--------|
/// |    *O*(1)    |   *O*(1)    |  *O*(n) |   *O*(n)  | *O*(n) |
///
/// [push_front]: ForwardList::push_front
/// [pop_front]:  ForwardList::pop_front
/// [clear]:      ForwardList::clear
/// [reverse]:    ForwardList::reverse
/// [find]:       ForwardList::find
pub struct ForwardList<T> {
    /// Pointer to the first node of the list.
    head: Link<T>,
    /// Specifies the number of actual elements within the list.
    len: usize,
    //
    // Since `ForwardList` implements `Drop`, `dropck` will treat our type as
    // owning a `T`, and will assume that values of type `T` might be accessed
    // when dropping, making `PhantomData` unnecessary for that purpose.
}

/// Ensures pointers are covariant and "nullable".
type Link<T> = Option<NonNull<Node<T>>>;

struct Node<T> {
    /// Data of the node.
    data: T,
    /// Pointer to the next node in the sequence.
    next: Link<T>,
}

/// Iterator that yields references over the elements of a `ForwardList`.
#[derive(Debug)]
pub struct Iter<'a, T> {
    curr: Link<T>,
    len: usize,
    _boo: PhantomData<&'a T>,
}

/// Iterator that yields mutable references over the elements of a
/// `ForwardList`.
#[derive(Debug)]
pub struct IterMut<'a, T> {
    curr: Link<T>,
    len: usize,
    _boo: PhantomData<&'a mut T>,
}

/// Consuming iterator, that is, one that moves each value out of the
/// `ForwardList`.
#[derive(Debug)]
#[repr(transparent)]
pub struct IntoIter<T>(ForwardList<T>);

impl<T> ForwardList<T> {
    /// Creates a new, empty `ForwardList<T>`.
    #[inline]
    pub const fn new() -> Self {
        ForwardList { head: None, len: 0 }
    }

    /// Adds an element to the front of the list.
    pub fn push_front(&mut self, data: T) {
        // SAFETY: `Box::new` guarantees a non-null, properly aligned pointer.
        let new_node =
            unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node { data, next: None }))) };

        if let Some(old_head) = self.head {
            unsafe {
                (*new_node.as_ptr()).next = Some(old_head);
            }
        }

        self.head = Some(new_node);
        self.len += 1;
    }

    /// Removes the first element from the list and returns it, or [`None`] if
    /// it is empty.
    pub fn pop_front(&mut self) -> Option<T> {
        self.head.map(|head| {
            // SAFETY: All nodes are created from a `Box::new` allocation.
            let boxed_node = unsafe { Box::from_raw(head.as_ptr()) };
            let out = boxed_node.data;

            self.head = boxed_node.next;

            self.len -= 1;
            out

            // `boxed_node` handles deallocation after going out of scope.
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

    /// Reverses the order of the nodes in the list in-place.
    pub fn reverse(&mut self) {
        if self.is_empty() {
            return;
        }

        let mut prev = None;
        let mut curr = self.head;

        while let Some(node) = curr {
            unsafe {
                let next = (*node.as_ptr()).next;
                (*node.as_ptr()).next = prev;
                prev = curr;
                curr = next;
            }
        }

        self.head = prev;
    }

    /// Insert the given element at the provided `index` in the list.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    pub fn insert(&mut self, index: usize, data: T) {
        assert!(index <= self.len, "index out of bounds");

        if index == 0 {
            self.push_front(data);
            return;
        }

        let (prev, curr) = self.traverse(index);

        // SAFETY: `Box::new` guarantees a non-null, properly aligned pointer.
        let new_node =
            unsafe { NonNull::new_unchecked(Box::into_raw(Box::new(Node { data, next: None }))) };

        // Cases:
        //
        // - prepending (prev is `None`, curr is `head`)
        // - inserting before current node (prev is `Some`, curr is `Some`)
        // - appending (prev is `tail`, curr is `None`)
        unsafe {
            match (prev, curr) {
                (None, Some(curr)) => {
                    (*new_node.as_ptr()).next = Some(curr);
                    self.head = Some(new_node);
                }
                (Some(prev), Some(curr)) => {
                    (*prev.as_ptr()).next = Some(new_node);
                    (*new_node.as_ptr()).next = Some(curr);
                }
                (Some(prev), None) => {
                    (*prev.as_ptr()).next = Some(new_node);
                }
                (None, None) => unreachable!(),
            }
        }

        self.len += 1;
    }

    /// Removes the element from the list at `index` and returns it.
    ///
    /// # Panics
    ///
    /// Panics if `index >= len`.
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");

        let (prev, curr) = self.traverse(index);

        unsafe {
            // Since `index < len`, the list must contain at least one node,
            // `curr`, since it is either head or tail.
            let curr = curr.expect("current pointer should always be valid in remove");

            // SAFETY: All nodes are created from a `Box::new` allocation.
            let boxed_node = Box::from_raw(curr.as_ptr());
            let out = boxed_node.data;

            // Cases:
            //
            // - removing head (prev is `None`)
            // - removing current node (prev is `Some`)
            match prev {
                Some(prev) => {
                    (*prev.as_ptr()).next = boxed_node.next;
                }
                None => {
                    self.head = boxed_node.next;
                }
            }

            self.len -= 1;
            out

            // `boxed_node` handles deallocation after going out of scope.
        }
    }

    /// Returns the index to the value corresponding to a node in the list, or
    /// [`None`] if it could not be found.
    pub fn find<Q>(&self, data: &Q) -> Option<usize>
    where
        T: Borrow<Q>,
        Q: PartialEq + ?Sized,
    {
        let mut idx = 0;
        let mut curr = self.head;

        while let Some(node) = curr {
            unsafe {
                if (*node.as_ptr()).data.borrow() == data {
                    return Some(idx);
                }
                curr = (*node.as_ptr()).next;
            }

            idx += 1;
        }

        // `data` could not be found.
        None
    }

    /// Returns the middle element from the list, or [`None`] if it is empty.
    pub fn find_middle(&self) -> Option<&T> {
        unsafe {
            let mut slow = self.head;
            let mut fast = slow;

            while let Some(node) = fast
                && let Some(next) = (*node.as_ptr()).next
            {
                slow = (*slow.expect("slow pointer should always be valid").as_ptr()).next;
                // `fast` traverses twice as fast as `slow`.
                fast = (*next.as_ptr()).next;
            }

            slow.map(|node| &(*node.as_ptr()).data)
        }
    }

    /// Returns `true` if the list contains a node for the specified `data`.
    #[inline]
    pub fn contains<Q>(&self, data: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: PartialEq + ?Sized,
    {
        self.find(data).is_some()
    }

    /// Creates a forward iterator, yielding `&T`.
    #[inline]
    pub const fn iter(&self) -> Iter<'_, T> {
        Iter {
            curr: self.head,
            len: self.len,
            _boo: PhantomData,
        }
    }

    /// Creates a forward iterator, yielding `&mut T`.
    #[inline]
    pub const fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            curr: self.head,
            len: self.len,
            _boo: PhantomData,
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

    /// Returns a pair of pointers for the node at the given `index`: the first
    /// points to the previous node, and the second to the current node.
    fn traverse(&self, mut index: usize) -> (Link<T>, Link<T>) {
        let mut prev = None;
        let mut curr = self.head;

        while let Some(node) = curr
            && index > 0
        {
            prev = curr;
            curr = unsafe { (*node.as_ptr()).next };
            index -= 1;
        }

        (prev, curr)
    }
}

// SAFETY: Each `ForwardList<T>` owns its nodes and `T`, allowing it to be
// safely transferred across threads, as long as `T` can also be safely
// transferred.
unsafe impl<T: Send> Send for ForwardList<T> {}

// SAFETY: `Iter` contains only shared references tied to `T`, so it can be
// safely transferred between threads if `T` is `Send`.
unsafe impl<'a, T: Send> Send for Iter<'a, T> {}

// SAFETY: `IterMut` contains exclusive references tied to `T`, so it can be
// safely transferred between threads if `T` is `Send`.
unsafe impl<'a, T: Send> Send for IterMut<'a, T> {}

// SAFETY: Since public methods allow accessing `&T` from `&ForwardList<T>`
// without synchronization (e.g., via `front`), `T` must be `Sync` for
// `ForwardList<T>` to be `Sync`. `ForwardList<T>` uses no interior mutability,
// with all mutations happening through `&mut` references.
unsafe impl<T: Sync> Sync for ForwardList<T> {}

// SAFETY: Similar to `Send` for `Iter`, `Iter` can be safely shared between
// threads because it only contains shared references to `T`. This is safe if
// `T: Sync`.
unsafe impl<'a, T: Sync> Sync for Iter<'a, T> {}

// SAFETY: `IterMut` yields mutable references to its items (`&mut T`), but
// methods that produce these mutable references require exclusive access to the
// iterator (`&mut self`). Even if `IterMut` itself is shared across threads
// (`&IterMut`), it effectively becomes read-only. Therefore, `IterMut` is
// `Sync` iff `T: Sync`.
unsafe impl<'a, T: Sync> Sync for IterMut<'a, T> {}

impl<T> IntoIterator for ForwardList<T> {
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

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.0.len
    }
}

impl<'a, T> IntoIterator for &'a ForwardList<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.curr.map(|node| unsafe {
            self.len -= 1;
            self.curr = (*node.as_ptr()).next;
            &(*node.as_ptr()).data
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> ExactSizeIterator for Iter<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<'a, T> IntoIterator for &'a mut ForwardList<T> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<'a, T> Iterator for IterMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        self.curr.map(|node| unsafe {
            self.len -= 1;
            self.curr = (*node.as_ptr()).next;
            &mut (*node.as_ptr()).data
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.len, Some(self.len))
    }
}

impl<'a, T> ExactSizeIterator for IterMut<'a, T> {
    fn len(&self) -> usize {
        self.len
    }
}

impl<T> Default for ForwardList<T> {
    fn default() -> Self {
        ForwardList::new()
    }
}

impl<T: Clone> Clone for ForwardList<T> {
    fn clone(&self) -> Self {
        let mut list = Self::new();
        for item in self {
            list.push_front(item.clone())
        }

        // Since all items can only be prepended, reverse the list to obtain
        // the correct order.
        list.reverse();
        list
    }
}

impl<T> FromIterator<T> for ForwardList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut list = Self::new();
        for item in iter {
            list.push_front(item)
        }

        // Since all items can only be prepended, reverse the list to obtain
        // the correct order.
        list.reverse();
        list
    }
}

impl<T: fmt::Debug> fmt::Debug for ForwardList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self).finish()
    }
}

impl<T: PartialEq> PartialEq for ForwardList<T> {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len && self.iter().eq(other)
    }
}

impl<T: Eq> Eq for ForwardList<T> {}

impl<T: PartialOrd> PartialOrd for ForwardList<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other)
    }
}

impl<T: Ord> Ord for ForwardList<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other)
    }
}

impl<T: Hash> Hash for ForwardList<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len.hash(state);
        for item in self {
            item.hash(state);
        }
    }
}

impl<T> Drop for ForwardList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

#[allow(dead_code)]
fn assert_properties() {
    fn is_send<T: Send>() {}
    fn is_sync<T: Sync>() {}

    is_send::<ForwardList<i32>>();
    is_sync::<ForwardList<i32>>();

    is_send::<IntoIter<i32>>();
    is_sync::<IntoIter<i32>>();

    is_send::<Iter<'_, i32>>();
    is_sync::<Iter<'_, i32>>();

    is_send::<IterMut<'_, i32>>();
    is_sync::<IterMut<'_, i32>>();

    fn forward_list_covariant<'a, T>(x: ForwardList<&'static T>) -> ForwardList<&'a T> {
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
/// use dsa::collections::forward_list::IterMut;
///
/// fn iter_mut_covariant<'i, 'a, T>(x: IterMut<'i, &'static T>) -> IterMut<'i, &'a T> { x }
/// ```
#[allow(dead_code)]
fn iter_mut_invariant() {}

#[cfg(test)]
mod tests {
    use super::*;

    fn list_from<T: Clone>(v: &[T]) -> ForwardList<T> {
        v.iter().map(|x| (*x).clone()).collect()
    }

    fn generate_test() -> ForwardList<i32> {
        list_from(&[0, 1, 2, 3, 4, 5, 6])
    }

    #[test]
    fn test_basic_stack() {
        let mut list = ForwardList::new();

        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

        list.push_front(10);
        assert_eq!(list.len(), 1);
        assert_eq!(list.pop_front(), Some(10));
        assert_eq!(list.len(), 0);
        assert_eq!(list.pop_front(), None);
        assert_eq!(list.len(), 0);

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
        let mut m = ForwardList::new();

        assert_eq!(m.pop_front(), None);
        assert_eq!(m.pop_front(), None);
        m.push_front(1);
        assert_eq!(m.pop_front(), Some(1));
        assert_eq!(m.len(), 0);
        assert_eq!(m.pop_front(), None);

        let mut n = ForwardList::new();
        n.push_front(2);
        n.push_front(3);
        {
            assert_eq!(n.front().unwrap(), &3);
            let x = n.front_mut().unwrap();
            assert_eq!(*x, 3);
            *x = 0;
        }
        assert_eq!(n.pop_front(), Some(0));
        assert_eq!(n.pop_front(), Some(2));
    }

    #[test]
    fn test_iterator() {
        let m = generate_test();

        for (i, item) in m.iter().enumerate() {
            assert_eq!(i as i32, *item);
        }

        let mut n = ForwardList::new();
        assert_eq!(n.iter().next(), None);
        n.push_front(4);

        let mut it = n.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_reverse() {
        let mut list: ForwardList<i32> = (0..10).collect();
        list.reverse();
        assert_eq!(list, (0..10).rev().collect::<ForwardList<i32>>());
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

        let mut n = ForwardList::new();
        assert!(n.iter_mut().next().is_none());
        n.push_front(4);
        n.push_front(5);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next().is_some());
        assert!(it.next().is_some());
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert!(it.next().is_none());
    }

    #[test]
    fn test_eq() {
        let mut n: ForwardList<u8> = list_from(&[]);
        let mut m = list_from(&[]);
        assert!(n == m);
        n.push_front(1);
        assert!(n != m);
        m.push_front(1);
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
        let list: ForwardList<i32> = (0..10).collect();
        assert_eq!(format!("{:?}", list), "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: ForwardList<&str> = vec!["just", "one", "test", "more"]
            .iter()
            .copied()
            .collect();
        assert_eq!(format!("{:?}", list), r#"["just", "one", "test", "more"]"#);
    }

    #[test]
    fn test_hash() {
        let list1: ForwardList<i32> = (0..10).collect();
        let list2: ForwardList<i32> = (1..11).collect();

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
    fn test_insert() {
        let mut list = ForwardList::new();

        list.insert(0, 10);
        list.insert(1, 20);
        list.push_front(30);
        list.insert(1, 15);

        assert_eq!(list.len(), 4);
        assert!(list.contains(&30));
        assert!(list.contains(&15));
        assert!(list.contains(&10));
        assert!(list.contains(&20));

        assert!(list.iter().eq([30, 15, 10, 20].iter()))
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_insert_out_of_bounds() {
        let mut list = ForwardList::new();

        list.insert(0, 10);
        list.insert(1, 20);
        list.push_front(30);
        list.insert(1, 15);

        assert_eq!(list.len(), 4);

        list.insert(5, 10);
    }

    #[test]
    fn test_remove() {
        let mut list = ForwardList::new();

        list.push_front(10);
        list.push_front(20);
        list.push_front(30);

        assert_eq!(list.len(), 3);
        let removed = list.remove(1);
        assert_eq!(removed, 20);

        assert!(list.contains(&30));
        assert!(!list.contains(&20));
        assert!(list.contains(&10));

        assert_eq!(list.len(), 2);
        let removed = list.remove(0);
        assert_eq!(removed, 30);

        assert_eq!(list.len(), 1);
        let removed = list.remove(0);
        assert_eq!(removed, 10);
    }

    #[test]
    #[should_panic(expected = "index out of bounds")]
    fn test_remove_out_of_bounds() {
        let mut list = ForwardList::new();
        list.push_front(1);
        list.remove(1);
    }

    #[test]
    fn test_find() {
        let mut list = ForwardList::new();

        list.push_front('a');
        list.push_front('b');
        list.push_front('c');

        assert_eq!(list.find(&'c'), Some(0));
        assert_eq!(list.find(&'b'), Some(1));
        assert_eq!(list.find(&'a'), Some(2));
        assert_eq!(list.find(&'z'), None);
    }

    #[test]
    fn test_find_middle_empty() {
        let list: ForwardList<i32> = ForwardList::new();
        assert_eq!(list.find_middle(), None);
    }

    #[test]
    fn test_find_middle_one() {
        let mut list = ForwardList::new();
        list.push_front(42);
        assert_eq!(list.find_middle(), Some(&42));
    }

    #[test]
    fn test_find_middle_odd() {
        let mut list = ForwardList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        assert_eq!(list.find_middle(), Some(&2));
    }

    #[test]
    fn test_find_middle_even() {
        let mut list = ForwardList::new();
        list.push_front(1);
        list.push_front(2);
        list.push_front(3);
        list.push_front(4);
        assert_eq!(list.find_middle(), Some(&2));
    }
}
