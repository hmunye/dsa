use std::borrow::Borrow;
use std::cmp::Ordering;
use std::marker::PhantomData;
use std::ptr::NonNull;

/// Unbalanced binary search tree (BST) that maintains items in sorted order.
///
/// # Time Complexities
///
/// |  [insert]   |  [remove]   | [contains]  |
/// |-------------|-------------|-------------|
/// | *O*(log n)~ | *O*(log n)~ | *O*(log n)~ |
///
/// [insert]:   BSTree::insert
/// [remove]:   BSTree::remove
/// [contains]: BSTree::contains
#[derive(Debug)]
pub struct BSTree<T> {
    /// Pointer to the root node of the tree.
    root: Link<T>,
    /// Specifies the number of actual nodes within the tree.
    len: usize,
}

/// Ensures pointers are covariant and "nullable".
type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug)]
struct Node<T> {
    item: T,
    /// Pointer to the left child node.
    left: Link<T>,
    /// Pointer to the right child node.
    right: Link<T>,
}

/// Iterator that yields references over a `BSTree<T>` in sorted order.
#[derive(Debug)]
pub struct IterSorted<'a, T> {
    /// Explicit stack for depth-first search (DFS) traversal of nodes.
    inner: Vec<NonNull<Node<T>>>,
    /// Ensures the lifetime is bounded.
    _marker: PhantomData<&'a T>,
}

impl<T: Ord> BSTree<T> {
    /// Creates an empty `BSTree<T>`.
    #[inline]
    pub const fn new() -> Self {
        BSTree { root: None, len: 0 }
    }

    /// Insert the specified item into the binary tree, ensuring the tree
    /// remains sorted.
    pub fn insert(&mut self, item: T) {
        if let Some(root) = self.root {
            // Using an explicit stack for iterative pre-order traversal.
            let mut stack = vec![];

            stack.push(root);

            while let Some(node) = stack.pop() {
                unsafe {
                    match node.as_ref().item.cmp(&item) {
                        Ordering::Greater => {
                            if let Some(left) = node.as_ref().left {
                                stack.push(left);
                            } else {
                                // SAFETY: `Box::new` guarantees a non-null,
                                // properly aligned pointer.
                                let new_node =
                                    NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                                        item,
                                        left: None,
                                        right: None,
                                    })));

                                (*node.as_ptr()).left = Some(new_node);
                                break;
                            }
                        }
                        Ordering::Equal => return,
                        Ordering::Less => {
                            if let Some(right) = node.as_ref().right {
                                stack.push(right);
                            } else {
                                // SAFETY: `Box::new` guarantees a non-null,
                                // properly aligned pointer.
                                let new_node =
                                    NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                                        item,
                                        left: None,
                                        right: None,
                                    })));

                                (*node.as_ptr()).right = Some(new_node);
                                break;
                            }
                        }
                    }
                }
            }
        } else {
            // SAFETY: `Box::new` guarantees a non-null, properly aligned
            // pointer.
            let new_node = unsafe {
                NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                    item,
                    left: None,
                    right: None,
                })))
            };

            self.root = Some(new_node);
        }

        self.len += 1;
    }

    /// Removes the item associated with the given key and returns it, or
    /// [`None`] if the key could not be found.
    pub fn remove<Q>(&mut self, key: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        let (parent, node) = Self::search(None, self.root, key);

        node.map(|node| unsafe {
            let item = match (node.as_ref().left, node.as_ref().right) {
                // In-order successor will replace the node to be removed.
                (Some(_), Some(right)) => {
                    // Since the right sub-tree may have no children, we
                    // initialize parent with `None`.
                    let mut parent = None;
                    let mut successor = right;

                    // Finds the next largest node relative to the node being
                    // removed.
                    while let Some(left) = successor.as_ref().left {
                        parent = Some(successor);
                        successor = left;
                    }

                    // Ensure we can link the parent node with the remainder of
                    // the successor's sub-tree.
                    let right_sub = successor.as_ref().right;

                    // Swap the items of the node to be removed and the
                    // successor, so the node to remove can be kept in-place.
                    std::mem::swap(&mut (*node.as_ptr()).item, &mut (*successor.as_ptr()).item);

                    if let Some(parent) = parent {
                        // Link parent node to the remaining sub-tree.
                        (*parent.as_ptr()).left = right_sub;
                    } else {
                        // No parent node - `parent == successor`. Unlink the
                        // current node from its immediate successor.
                        (*node.as_ptr()).right = None;
                    }

                    let boxed_node = Box::from_raw(successor.as_ptr());
                    boxed_node.item

                    // `boxed_node` will handle its deallocation
                }
                // Right child-node will replace the node to be removed.
                (None, Some(right)) => {
                    if let Some(parent) = parent {
                        if parent.as_ref().left == Some(node) {
                            (*parent.as_ptr()).left = Some(right);
                        } else {
                            (*parent.as_ptr()).right = Some(right);
                        }
                    } else {
                        // Root is being removed.
                        self.root = Some(right);
                    }

                    let boxed_node = Box::from_raw(node.as_ptr());
                    boxed_node.item

                    // `boxed_node` will handle its deallocation
                }
                // Left child-node will replace the node to be removed.
                (Some(left), None) => {
                    if let Some(parent) = parent {
                        if parent.as_ref().left == Some(node) {
                            (*parent.as_ptr()).left = Some(left);
                        } else {
                            (*parent.as_ptr()).right = Some(left);
                        }
                    } else {
                        // Root is being removed.
                        self.root = Some(left);
                    }

                    let boxed_node = Box::from_raw(node.as_ptr());
                    boxed_node.item

                    // `boxed_node` will handle its deallocation
                }
                // Leaf node is being removed.
                (None, None) => {
                    if let Some(parent) = parent {
                        if parent.as_ref().left == Some(node) {
                            (*parent.as_ptr()).left = None;
                        } else {
                            (*parent.as_ptr()).right = None;
                        }
                    } else {
                        // Root is being removed.
                        self.root = None;
                    }

                    let boxed_node = Box::from_raw(node.as_ptr());
                    boxed_node.item

                    // `boxed_node` will handle its deallocation
                }
            };

            self.len -= 1;
            item
        })
    }

    /// Returns `true` if the binary tree contains the given key.
    #[inline]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        // Second item of the tuple is the matched node.
        Self::search(None, self.root, key).1.is_some()
    }

    /// Creates a forward iterator, yielding `&T` in sorted order.
    pub fn iter_sorted(&self) -> IterSorted<'_, T> {
        // Using an explicit stack for iterative traversal.
        let mut inner = vec![];
        let mut root = self.root;

        // Including the root, push all left nodes of the left sub-tree onto
        // the stack so iteration can begin from the smallest element.
        while let Some(node) = root {
            unsafe {
                inner.push(node);
                root = node.as_ref().left;
            }
        }

        IterSorted {
            inner,
            _marker: PhantomData,
        }
    }

    /// Returns the number of items in the tree.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the tree contains no items.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Removes all items from the tree.
    pub fn clear(&mut self) {
        if let Some(root) = self.root {
            // Queue for breadth-first search (BFS) removal of nodes, since
            // order does not need to be maintained.
            let mut queue = std::collections::VecDeque::new();

            queue.push_front(root);

            while let Some(node) = queue.pop_back() {
                unsafe {
                    if let Some(right) = node.as_ref().right {
                        queue.push_front(right);
                    }
                    if let Some(left) = node.as_ref().left {
                        queue.push_front(left);
                    }

                    let _ = Box::from_raw(node.as_ptr());
                    // `node` is deallocated here...
                }
            }

            self.len = 0;
        }
    }

    /// Perform a search with time complexity of *O*(log n) starting from the
    /// given `node`, returning a tuple containing the matched node and its
    /// parent, or (`None`, `None`) if the key is not found.
    ///
    /// A return value of (`None`, `Some(_)`) indicates that the root node was
    /// matched.
    fn search<Q>(parent: Link<T>, node: Link<T>, key: &Q) -> (Link<T>, Link<T>)
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        if let Some(node) = node {
            unsafe {
                match node.as_ref().item.borrow().cmp(key) {
                    Ordering::Greater => BSTree::search(Some(node), node.as_ref().left, key),
                    Ordering::Equal => (parent, Some(node)),
                    Ordering::Less => BSTree::search(Some(node), node.as_ref().right, key),
                }
            }
        } else {
            (None, None)
        }
    }
}

impl<T> Drop for BSTree<T> {
    fn drop(&mut self) {
        if let Some(root) = self.root {
            // Queue for breadth-first search (BFS) removal of nodes, since
            // order does not need to be maintained.
            let mut queue = std::collections::VecDeque::new();

            queue.push_front(root);

            while let Some(node) = queue.pop_back() {
                unsafe {
                    if let Some(right) = node.as_ref().right {
                        queue.push_front(right);
                    }
                    if let Some(left) = node.as_ref().left {
                        queue.push_front(left);
                    }

                    let _ = Box::from_raw(node.as_ptr());
                    // `node` is deallocated here...
                }
            }

            self.len = 0;
        }
    }
}

impl<'a, T: Ord> Iterator for IterSorted<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let node = self.inner.pop()?;

            // Beginning from the right sub-tree, traverse as far left to reach
            // the next minimum element.
            let mut next = node.as_ref().right;
            while let Some(n) = next {
                self.inner.push(n);
                next = n.as_ref().left;
            }

            Some(&node.as_ref().item)
        }
    }
}

impl<T: Ord> Default for BSTree<T> {
    fn default() -> Self {
        BSTree::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_contains() {
        let mut bst = BSTree::new();

        let values = vec![10, 5, 15, 3, 7, 12, 18];

        for &v in &values {
            bst.insert(v);
        }

        for &v in &values {
            assert!(bst.contains(&v));
        }

        for &v in &[0, 6, 11, 20] {
            assert!(!bst.contains(&v));
        }
    }

    #[test]
    fn test_iter_sorted() {
        let mut bst = BSTree::new();

        let mut values = vec![50, 30, 70, 20, 40, 60, 80];
        for &v in &values {
            bst.insert(v);
        }

        let inorder: Vec<_> = bst.iter_sorted().cloned().collect();

        values.sort();
        assert_eq!(inorder, values,);
    }

    #[test]
    fn test_duplicates() {
        let mut bst = BSTree::new();

        bst.insert(10);
        bst.insert(10);
        bst.insert(10);

        assert_eq!(bst.len(), 1);

        let inorder: Vec<_> = bst.iter_sorted().cloned().collect();
        assert_eq!(inorder, vec![10]);
    }

    #[test]
    fn test_remove_leaf() {
        let mut bst = BSTree::new();
        bst.insert(10);
        bst.insert(5);
        bst.insert(15);
        assert_eq!(bst.len(), 3);

        assert_eq!(bst.remove(&5), Some(5));
        assert_eq!(bst.len(), 2);
        assert!(!bst.contains(&5));

        assert_eq!(bst.remove(&15), Some(15));
        assert_eq!(bst.len(), 1);
        assert!(!bst.contains(&15));
        assert!(bst.contains(&10));
    }

    #[test]
    fn test_remove_node_one_child() {
        let mut bst = BSTree::new();
        bst.insert(10);
        bst.insert(5);
        bst.insert(15);
        bst.insert(12);
        assert_eq!(bst.len(), 4);

        assert_eq!(bst.remove(&15), Some(15));
        assert_eq!(bst.len(), 3);
        assert!(!bst.contains(&15));
        assert!(bst.contains(&12));
    }

    #[test]
    fn test_remove_node_two_children() {
        let mut bst = BSTree::new();
        bst.insert(10);
        bst.insert(5);
        bst.insert(15);
        bst.insert(12);
        bst.insert(18);
        assert_eq!(bst.len(), 5);

        assert_eq!(bst.remove(&15), Some(15));
        assert_eq!(bst.len(), 4);
        assert!(!bst.contains(&15));
    }

    #[test]
    fn test_remove_root() {
        let mut bst = BSTree::new();
        bst.insert(10);
        bst.insert(5);
        bst.insert(15);
        assert_eq!(bst.len(), 3);

        assert_eq!(bst.remove(&10), Some(10));
        assert_eq!(bst.len(), 2);
        assert!(!bst.contains(&10));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mut bst = BSTree::new();
        bst.insert(10);
        bst.insert(5);
        bst.insert(15);
        assert_eq!(bst.len(), 3);

        assert_eq!(bst.remove(&100), None);
        assert_eq!(bst.len(), 3);
    }

    #[test]
    fn test_remove_all() {
        let mut bst = BSTree::new();
        let values = vec![10, 5, 15, 3, 7, 12, 18];
        for &v in &values {
            bst.insert(v);
        }
        assert_eq!(bst.len(), values.len());

        for (i, &v) in values.iter().enumerate() {
            assert_eq!(bst.remove(&v), Some(v));
            assert_eq!(bst.len(), values.len() - i - 1);
            assert!(!bst.contains(&v));
        }

        assert_eq!(bst.len(), 0);
        assert_eq!(bst.iter_sorted().count(), 0);
    }

    #[test]
    fn test_iter_sorted_after_remove() {
        let mut bst = BSTree::new();
        let mut values = vec![50, 30, 70, 20, 40, 60, 80];
        for &v in &values {
            bst.insert(v);
        }

        let remove_nodes = vec![20, 70, 50];
        for &v in &remove_nodes {
            assert!(bst.remove(&v).is_some());
        }

        values.retain(|&x| !remove_nodes.contains(&x));
        values.sort();

        let inorder: Vec<_> = bst.iter_sorted().cloned().collect();

        assert_eq!(inorder, values);
    }
}
