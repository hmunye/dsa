use std::borrow::Borrow;
use std::cmp::Ordering;
use std::ptr::NonNull;

/// Binary search tree (BST) that maintains balance using [`AVL`] rotations.
///
/// # Time Complexities
///
/// |  [insert]  |  [remove]  | [contains] |
/// |------------|------------|------------|
/// | *O*(log n) | *O*(log n) | *O*(log n) |
///
/// [insert]:   AVL::insert
/// [remove]:   AVL::remove
/// [contains]: AVL::contains
///
/// [`AVL`]: https://en.wikipedia.org/wiki/AVL_tree
#[derive(Debug)]
pub struct AVL<T> {
    root: Link<T>,
    len: usize,
}

type Link<T> = Option<NonNull<Node<T>>>;

#[derive(Debug)]
struct Node<T> {
    item: T,
    left: Link<T>,
    right: Link<T>,
    /// Height of the node's sub-tree (longest path to a leaf). Used to compute
    /// balance factor in constant time.
    height: usize,
}

impl<T: Ord> AVL<T> {
    /// Creates a new, empty `AVL` tree.
    #[inline]
    pub const fn new() -> Self {
        AVL { root: None, len: 0 }
    }

    /// Inserts the given item into the tree, applying balancing rotations if
    /// needed.
    #[inline]
    pub fn insert(&mut self, item: T) {
        let (root, inserted) = AVL::insert_recursive(self.root, item);
        self.root = root;

        if inserted {
            self.len += 1;
        }
    }

    /// Removes the item associated with the given key and returns it, or
    /// [`None`] if the key could not be found.
    #[inline]
    pub fn remove<Q>(&mut self, key: &Q) -> Option<T>
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        let (root, item) = AVL::remove_recursive(self.root, key);
        // Assign to `self.root` since rotations may change the root node.
        self.root = root;

        if item.is_some() {
            self.len -= 1;

            if self.len == 0 {
                self.root = None;
            }
        }

        item
    }

    /// Returns `true` if the tree contains the given key.
    #[inline]
    pub fn contains<Q>(&self, key: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        AVL::find_node(None, self.root, key).1.is_some()
    }

    /// Removes all items from the tree.
    pub fn clear(&mut self) {
        if let Some(root) = self.root {
            // Explicit stack for depth-first search (DFS) removal of nodes,
            // since no re-balancing is required.
            let mut stack = Vec::with_capacity(self.len);
            stack.push(root);

            while let Some(node) = stack.pop() {
                unsafe {
                    if let Some(right) = node.as_ref().right {
                        stack.push(right);
                    }
                    if let Some(left) = node.as_ref().left {
                        stack.push(left);
                    }

                    let _ = Box::from_raw(node.as_ptr());

                    // `Box` handles the node's deallocation.
                }
            }

            self.len = 0;
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

    /// Recursively inserts the given item into the tree, ignoring duplicates,
    /// returning the updated root pointer and boolean indicating if insertion
    /// occurred.
    ///
    /// Handles height updates and tree rotations as needed.
    fn insert_recursive(root: Link<T>, item: T) -> (Link<T>, bool) {
        unsafe {
            if let Some(root) = root {
                let inserted = match root.as_ref().item.cmp(&item) {
                    Ordering::Greater => {
                        let (left, inserted) = AVL::insert_recursive(root.as_ref().left, item);
                        (*root.as_ptr()).left = left;
                        inserted
                    }
                    Ordering::Equal => return (Some(root), false),
                    Ordering::Less => {
                        let (right, inserted) = AVL::insert_recursive(root.as_ref().right, item);
                        (*root.as_ptr()).right = right;
                        inserted
                    }
                };

                (AVL::fix_invariant(root, inserted), inserted)
            } else {
                // SAFETY: `Box::new` guarantees a non-null, properly aligned pointer.
                let new_node = NonNull::new_unchecked(Box::into_raw(Box::new(Node {
                    item,
                    left: None,
                    right: None,
                    // Leaf-nodes have minimum height of 1.
                    height: 1,
                })));

                (Some(new_node), true)
            }
        }
    }

    /// Recursively removes the node corresponding to the given key from the
    /// tree, returning the removed item, or [`None`] if the key could not be
    /// found.
    ///
    /// Handles height updates and tree rotations as needed.
    fn remove_recursive<Q>(root: Link<T>, key: &Q) -> (Link<T>, Option<T>)
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        // TODO: fix dangling pointer during removal.
        if let Some(node) = root {
            unsafe {
                let item = match node.as_ref().item.borrow().cmp(key) {
                    Ordering::Greater => {
                        let (left, item) = AVL::remove_recursive(node.as_ref().left, key);
                        (*node.as_ptr()).left = left;
                        item
                    }
                    Ordering::Equal => {
                        match (node.as_ref().left, node.as_ref().right) {
                            // Matched node is a leaf - return `None` to break
                            // the link with parent node.
                            (None, None) => {
                                // SAFETY: `node` was originally created from
                                // `Box::new` and is only ever converted back
                                // to a `Box` when uniquely owned. No aliasing
                                // occurs.
                                let boxed_node = Box::from_raw(node.as_ptr());

                                return (None, Some(boxed_node.item));

                                // `boxed_node` handles it's deallocation.
                            }
                            // Node only has right child - find successor.
                            (None, Some(right)) => {
                                if let Some(successor) = AVL::in_order_successor(node) {
                                    std::mem::swap(
                                        &mut (*node.as_ptr()).item,
                                        &mut (*successor.as_ptr()).item,
                                    );
                                }

                                let (right, item) = AVL::remove_recursive(Some(right), key);
                                (*node.as_ptr()).right = right;
                                item
                            }
                            // Node has two children or only a left child -
                            // find predecessor.
                            (Some(left), None) | (Some(left), Some(_)) => {
                                if let Some(predecessor) = AVL::in_order_predecessor(node) {
                                    std::mem::swap(
                                        &mut (*node.as_ptr()).item,
                                        &mut (*predecessor.as_ptr()).item,
                                    );
                                }

                                let (left, item) = AVL::remove_recursive(Some(left), key);
                                (*node.as_ptr()).left = left;
                                item
                            }
                        }
                    }
                    Ordering::Less => {
                        let (right, item) = AVL::remove_recursive(node.as_ref().right, key);
                        (*node.as_ptr()).right = right;
                        item
                    }
                };

                (AVL::fix_invariant(node, true), item)
            }
        } else {
            (None, None)
        }
    }

    /// Perform a *O*(log n) search starting from the given `node`, returning a
    /// tuple containing the matched node and its parent, or (`None`, `None`) if
    /// the key is not found.
    ///
    /// A return value of (`None`, `Some(_)`) indicates a matching root node.
    fn find_node<Q>(parent: Link<T>, node: Link<T>, key: &Q) -> (Link<T>, Link<T>)
    where
        T: Borrow<Q>,
        Q: Ord,
    {
        if let Some(node) = node {
            unsafe {
                match node.as_ref().item.borrow().cmp(key) {
                    Ordering::Greater => AVL::find_node(Some(node), node.as_ref().left, key),
                    Ordering::Equal => (parent, Some(node)),
                    Ordering::Less => AVL::find_node(Some(node), node.as_ref().right, key),
                }
            }
        } else {
            (None, None)
        }
    }

    /// Restores AVL balance invariant at the given (sub)tree root by updating
    /// height and applying rotations as needed, returning a pointer to the new
    /// root of the rotated (sub)tree.
    fn fix_invariant(node: NonNull<Node<T>>, update_height: bool) -> Link<T> {
        unsafe {
            // Update the height of the node.
            if update_height {
                let left_height = AVL::height(node.as_ref().left);
                let right_height = AVL::height(node.as_ref().right);

                (*node.as_ptr()).height = 1 + std::cmp::max(left_height, right_height);
            }

            // Check if the tree needs re-balancing.
            let balance = AVL::balance_factor(Some(node));

            // AVL allows for a buffer of +-1 for either sub-tree.
            if balance > 1 {
                // Tree is left-heavy.
                if AVL::balance_factor(node.as_ref().left) >= 0 {
                    // `Left-Left` rotation.
                    AVL::rotate_right(node)
                } else {
                    debug_assert!(node.as_ref().left.is_some());

                    // `Left-Right` rotation. Should not panic since balance factor
                    // is non-zero, meaning left is `Some`.
                    (*node.as_ptr()).left = AVL::rotate_left(node.as_ref().left.unwrap());
                    AVL::rotate_right(node)
                }
            } else if balance < -1 {
                // Tree is right-heavy.
                if AVL::balance_factor(node.as_ref().right) <= 0 {
                    // `Right-Right` rotation.
                    AVL::rotate_left(node)
                } else {
                    debug_assert!(node.as_ref().right.is_some());

                    // `Right-Left` rotation. Should not panic since balance factor
                    // is non-zero, meaning left is `Some`.
                    (*node.as_ptr()).right = AVL::rotate_right(node.as_ref().right.unwrap());
                    AVL::rotate_left(node)
                }
            } else {
                // Both sub-tree heights are equal.
                Some(node)
            }
        }
    }

    /// Performs a right rotation on the given unbalanced node, returning a
    /// pointer to the new root of the rotated sub-tree.
    fn rotate_right(node: NonNull<Node<T>>) -> Link<T> {
        unsafe {
            // Use the left child of `node` as a "pivot". This pivot will
            // become the new root of this sub-tree.
            if let Some(left) = node.as_ref().left {
                // Save a pointer to the pivot's right sub-tree, since this
                // sub-tree will be moved under the original node.
                let left_right = left.as_ref().right;

                // The node's parent is now the pivot.
                (*left.as_ptr()).right = Some(node);

                // Node's left child pointer is updated to point to the pivot's
                // right sub-tree to preserve it.
                (*node.as_ptr()).left = left_right;

                // Update pivot and node heights.
                (*left.as_ptr()).height = 1 + std::cmp::max(
                    AVL::height(left.as_ref().left),
                    AVL::height(left.as_ref().right),
                );

                (*node.as_ptr()).height = 1 + std::cmp::max(
                    AVL::height(node.as_ref().left),
                    AVL::height(node.as_ref().right),
                );

                Some(left)
            } else {
                // If there is no left child, rotation can't be performed.
                None
            }
        }
    }

    /// Performs a left rotation on the given unbalanced node, returning a
    /// pointer to the new root of the rotated sub-tree.
    fn rotate_left(node: NonNull<Node<T>>) -> Link<T> {
        unsafe {
            // Use the right child of `node` as a "pivot". This pivot will
            // become the new root of this sub-tree.
            if let Some(right) = node.as_ref().right {
                // Save a pointer to the pivot's left sub-tree, since this
                // sub-tree will be moved under the original node.
                let right_left = right.as_ref().left;

                // The node's parent is now the pivot.
                (*right.as_ptr()).left = Some(node);

                // Node's right child pointer is updated to point to the pivot's
                // left sub-tree to preserve it.
                (*node.as_ptr()).right = right_left;

                // Update pivot and node heights.
                (*right.as_ptr()).height = 1 + std::cmp::max(
                    AVL::height(right.as_ref().left),
                    AVL::height(right.as_ref().right),
                );

                (*node.as_ptr()).height = 1 + std::cmp::max(
                    AVL::height(node.as_ref().left),
                    AVL::height(node.as_ref().right),
                );

                Some(right)
            } else {
                // If there is no right child, rotation can't be performed.
                None
            }
        }
    }

    /// Returns a pointer to the in-order successor of the given node
    /// (next largest value relative to the current node).
    const fn in_order_successor(node: NonNull<Node<T>>) -> Link<T> {
        unsafe {
            if let Some(mut root) = node.as_ref().right {
                while let Some(left) = root.as_ref().left {
                    root = left;
                }
                Some(root)
            } else {
                None
            }
        }
    }

    /// Returns a pointer to the in-order predecessor of the given node
    /// (next smallest value relative to the current node).
    const fn in_order_predecessor(node: NonNull<Node<T>>) -> Link<T> {
        unsafe {
            if let Some(mut root) = node.as_ref().left {
                while let Some(right) = root.as_ref().right {
                    root = right;
                }
                Some(root)
            } else {
                None
            }
        }
    }

    /// Returns the balance factor of a given root node, or 0 if [`None`].
    #[inline]
    const fn balance_factor(root: Link<T>) -> isize {
        match root {
            Some(n) => unsafe {
                AVL::height(n.as_ref().left) as isize - AVL::height(n.as_ref().right) as isize
            },
            None => 0,
        }
    }

    /// Returns the height of a given node, or 0 if [`None`].
    #[inline]
    const fn height(node: Link<T>) -> usize {
        match node {
            Some(n) => unsafe { n.as_ref().height },
            None => 0,
        }
    }
}

impl<T> Drop for AVL<T> {
    fn drop(&mut self) {
        if let Some(root) = self.root {
            // Explicit stack for depth-first search (DFS) removal of nodes,
            // since no re-balancing is required.
            let mut stack = Vec::with_capacity(self.len);
            stack.push(root);

            while let Some(node) = stack.pop() {
                unsafe {
                    if let Some(right) = node.as_ref().right {
                        stack.push(right);
                    }
                    if let Some(left) = node.as_ref().left {
                        stack.push(left);
                    }

                    let _ = Box::from_raw(node.as_ptr());

                    // `Box` handles the node's deallocation.
                }
            }

            self.len = 0;
        }
    }
}

impl<T: Ord> Default for AVL<T> {
    fn default() -> Self {
        AVL::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_contains() {
        let mut avl = AVL::new();

        let values = vec![10, 5, 15, 3, 7, 12, 18];
        for &v in &values {
            avl.insert(v);
        }

        assert_eq!(avl.len(), values.len());

        for &v in &values {
            assert!(avl.contains(&v));
        }

        for &v in &[0, 6, 11, 20] {
            assert!(!avl.contains(&v));
        }
    }

    #[test]
    fn test_duplicates() {
        let mut avl = AVL::new();

        avl.insert(10);
        avl.insert(10);
        avl.insert(10);

        assert_eq!(avl.len(), 1);
    }

    #[test]
    fn test_remove_leaf() {
        let mut avl = AVL::new();
        avl.insert(10);
        avl.insert(5);
        avl.insert(15);
        assert_eq!(avl.len(), 3);

        assert_eq!(avl.remove(&5), Some(5));
        assert_eq!(avl.len(), 2);
        assert!(!avl.contains(&5));

        assert_eq!(avl.remove(&15), Some(15));
        assert_eq!(avl.len(), 1);
        assert!(!avl.contains(&15));
        assert!(avl.contains(&10));
    }

    #[test]
    fn test_remove_node_one_child() {
        let mut avl = AVL::new();
        avl.insert(10);
        avl.insert(5);
        avl.insert(15);
        avl.insert(12);
        assert_eq!(avl.len(), 4);

        assert_eq!(avl.remove(&15), Some(15));
        assert_eq!(avl.len(), 3);
        assert!(!avl.contains(&15));
        assert!(avl.contains(&12));
    }

    #[test]
    fn test_remove_node_two_children() {
        let mut avl = AVL::new();
        avl.insert(10);
        avl.insert(5);
        avl.insert(15);
        avl.insert(12);
        avl.insert(18);
        assert_eq!(avl.len(), 5);

        assert_eq!(avl.remove(&15), Some(15));
        assert_eq!(avl.len(), 4);
        assert!(!avl.contains(&15));
    }

    #[test]
    fn test_remove_root() {
        let mut avl = AVL::new();
        avl.insert(10);
        avl.insert(5);
        avl.insert(15);
        assert_eq!(avl.len(), 3);

        assert_eq!(avl.remove(&10), Some(10));
        assert_eq!(avl.len(), 2);
        assert!(!avl.contains(&10));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mut avl = AVL::new();
        avl.insert(10);
        avl.insert(5);
        avl.insert(15);
        assert_eq!(avl.len(), 3);

        assert_eq!(avl.remove(&100), None);
        assert_eq!(avl.len(), 3);
    }

    #[test]
    fn test_remove_all() {
        let mut avl = AVL::new();
        let values = vec![10, 5, 15, 3, 7, 12, 18];
        for &v in &values {
            avl.insert(v);
        }
        assert_eq!(avl.len(), values.len());

        for (i, &v) in values.iter().enumerate() {
            assert_eq!(avl.remove(&v), Some(v));
            assert_eq!(avl.len(), values.len() - i - 1);
            assert!(!avl.contains(&v));
        }

        assert_eq!(avl.len(), 0);
    }
}
