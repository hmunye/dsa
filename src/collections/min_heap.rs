/// Priority queue implemented with a binary heap.
///
/// Maintains the property where the smallest element is at the root, and every
/// parent node is smaller than or equal to its children.
///
/// # Time Complexity
///
/// | [push]      | [pop]      | [peek] |
/// |-------------|-------- ---|--------|
/// | *O*(log n)~ | *O*(log n) | *O*(1) |
///
/// [push]: MinHeap::push
/// [pop]:  MinHeap::pop
/// [peek]: MinHeap::peek
#[derive(Debug)]
pub struct MinHeap<T> {
    // Contiguous buffer used for better cache-locality and index-based access.
    buf: Vec<T>,
}

/// Iterator that yields elements of a `MinHeap` in sorted order.
#[derive(Debug)]
pub struct IntoIterSorted<T> {
    inner: MinHeap<T>,
}

impl<T: Ord> Iterator for IntoIterSorted<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.pop()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.inner.len(), Some(self.inner.len()))
    }
}

/// Encodes the position of the item to "sift" from and in which direction. The
/// upper 63 bits store the position, and the lowest bit indicates the
/// direction: `1` for upward (sift-up), `0` for downward (sift-down).
#[repr(transparent)]
struct SiftInfo(u64);

impl SiftInfo {
    #[inline]
    const fn new(pos: usize, should_sift_up: bool) -> Self {
        // `usize` is platform-dependent in size (32-bit or 64-bit), so encoding
        // as a`u64` ensures consistency. The sift direction is stored starting
        // from the most significant bit (MSB), which won't interfere with valid
        // position indicies, since Rust collections limits allocations to
        // [`isize::MAX`], which fits within the lower 63 bits of a `u64`.
        let packed = (pos as u64) | ((should_sift_up as u64) << 63);

        SiftInfo(packed)
    }

    #[inline]
    const fn pos(&self) -> usize {
        (self.0 & !(1 << 63)) as usize
    }

    #[inline]
    const fn sift_up(&self) -> bool {
        ((self.0 >> 63) & 0x1) != 0
    }

    #[inline]
    #[allow(unused)]
    const fn sift_down(&self) -> bool {
        ((self.0 >> 63) & 0x1) == 0
    }
}

/// Guard used to `heapify` the `MinHeap` automatically on `Drop`.
///
/// <https://doc.rust-lang.org/src/alloc/collections/binary_heap/mod.rs.html#484>
struct HeapifyGuard<'a, T: Ord> {
    heap: &'a mut MinHeap<T>,
    sift_info: SiftInfo,
}

impl<T: Ord> Drop for HeapifyGuard<'_, T> {
    fn drop(&mut self) {
        let pos = self.sift_info.pos();

        if self.sift_info.sift_up() {
            debug_assert!(
                pos < self.heap.len(),
                "invalid position provided when sifting up: {pos}"
            );

            // SAFETY: `pos` is < `heap.len()`, making the range `0..=pos`
            // valid.
            unsafe {
                self.heap.sift_up(0, pos);
            }
        } else {
            debug_assert!(
                pos <= self.heap.len(),
                "invalid position provided when sifting down: {pos}"
            );

            // SAFETY: `pos` is <= `heap.len()`, making the range `0..pos`
            // valid.
            unsafe {
                self.heap.sift_down(0, pos);
            }
        }
    }
}

impl<T> MinHeap<T> {
    /// Creates an empty `MinHeap`.
    #[inline]
    #[must_use]
    pub const fn new() -> Self {
        MinHeap { buf: vec![] }
    }

    /// Returns a reference to the smallest item in the binary heap, or `None`
    /// if it is empty.
    #[inline]
    pub fn peek(&self) -> Option<&T> {
        self.buf.first()
    }

    /// Returns the number of items in the binary heap.
    #[inline]
    pub const fn len(&self) -> usize {
        self.buf.len()
    }

    /// Returns the number of items the binary heap can hold without
    /// reallocating.
    #[inline]
    #[allow(unused)]
    pub const fn capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Returns `true` if the binary heap contains no items.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.buf.is_empty()
    }
}

impl<T: Ord> MinHeap<T> {
    /// Pushes an item onto the binary heap.
    pub fn push(&mut self, item: T) {
        let guard = HeapifyGuard {
            // Item to sift up will be at this index.
            sift_info: SiftInfo::new(self.len(), true),
            heap: self,
        };

        // Appending `item` maintains the invariant of a complete binary tree:
        // every level, except possibly the last, is fully filled.
        guard.heap.buf.push(item);

        // `guard` rebuilds the heap on `Drop`...
    }

    /// Removes the smallest item from the binary heap and returns it, or `None`
    /// if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let guard = HeapifyGuard {
                // Item to sift down was at this index.
                sift_info: SiftInfo::new(self.len() - 1, false),
                heap: self,
            };

            // Removes the smallest element, replacing it with the last element
            // of the heap. Done in *O*(1) time, instead of `remove(0)` which is
            // *O*(n).
            Some(guard.heap.buf.swap_remove(0))

            // `guard` rebuilds the heap on `Drop`...
        }
    }

    /// Returns an iterator yielding elements in `min-heap` order.
    #[inline]
    #[allow(unused)]
    pub const fn into_iter_sorted(self) -> IntoIterSorted<T> {
        IntoIterSorted { inner: self }
    }

    /// Restores the min-heap invariant by fixing any violations caused after
    /// an insertion, returning the new position of the item.
    ///
    /// `start` specifies the upper bound (inclusive) for where sifting should
    /// stop. `pos` is the index of the item that is being moved.
    ///
    /// # Safety
    ///
    /// The range `start..=pos` must lie entirely within the bounds of the heap.
    /// This function may panic due to out-of-bounds access otherwise.
    unsafe fn sift_up(&mut self, start: usize, mut pos: usize) -> usize {
        // For an element at index `i`:
        //
        // - Parent: (i - 1) / 2
        while pos > start {
            let parent = (pos - 1) / 2;

            if self.buf[pos] >= self.buf[parent] {
                break;
            }

            // Swap item at `pos` with its parent.
            self.buf.swap(pos, parent);

            pos = parent;
        }

        pos
    }

    /// Restores the min-heap invariant by fixing any violations caused after
    /// a removal, returning the new position of the item.
    ///
    /// `pos` is the index of the item that is being moved. `end` specifies the
    /// upper bound (exclusive) for where the sifting should stop.     
    ///
    /// # Safety
    ///
    /// The range `pos..end` must lie entirely within the bounds of the heap.
    /// This function may panic due to out-of-bounds access otherwise.
    unsafe fn sift_down(&mut self, mut pos: usize, end: usize) -> usize {
        // For an element at index `i`:
        //
        // - Left child:  2i + 1
        // - Right child: 2i + 2
        loop {
            let left = 2 * pos + 1;
            let right = 2 * pos + 2;

            // Comparison must start with the left child.
            if left >= end {
                break;
            }

            let mut min = if self.buf[pos] >= self.buf[left] {
                left
            } else {
                pos
            };

            // Check if the right child exists before comparing.
            if right < end && self.buf[min] >= self.buf[right] {
                min = right;
            }

            // Check if a "smaller" child was encountered.
            if min == pos {
                // Can no longer sift down.
                break;
            } else {
                self.buf.swap(min, pos);
                pos = min;
            }
        }

        pos
    }
}

impl<T> Default for MinHeap<T> {
    fn default() -> Self {
        MinHeap::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let mut heap: MinHeap<i32> = MinHeap::new();
        assert!(heap.peek().is_none());
        assert!(heap.pop().is_none());
        assert_eq!(heap.len(), 0);
        assert_eq!(heap.capacity(), 0);
        assert!(heap.is_empty());
    }

    #[test]
    fn test_push_and_peek() {
        let mut heap = MinHeap::new();
        heap.push(10);
        assert_eq!(heap.peek(), Some(&10));
        heap.push(5);
        assert_eq!(heap.peek(), Some(&5));
        heap.push(15);
        assert_eq!(heap.peek(), Some(&5));
    }

    #[test]
    fn test_pop() {
        let mut heap = MinHeap::new();
        let mut values = vec![12, 3, 25, 7, 9, 1];

        for &v in &values {
            heap.push(v);
        }

        values.sort();

        for &v in &values {
            assert_eq!(heap.pop(), Some(v));
        }

        assert!(heap.is_empty());
        assert_eq!(heap.len(), 0);
    }

    #[test]
    fn test_duplicates() {
        let mut heap = MinHeap::new();

        heap.push(7);
        heap.push(7);
        heap.push(3);
        heap.push(3);
        heap.push(5);
        heap.push(5);

        assert_eq!(heap.peek(), Some(&3));

        let sorted: Vec<_> = heap.into_iter_sorted().collect();
        assert_eq!(sorted, vec![3, 3, 5, 5, 7, 7]);
    }

    #[test]
    fn test_len_and_capacity() {
        let mut heap = MinHeap::new();
        assert_eq!(heap.len(), 0);
        assert_eq!(heap.capacity(), 0);

        heap.push(5);
        assert_eq!(heap.len(), 1);
        assert!(heap.capacity() >= 1);

        heap.push(3);
        heap.push(8);
        assert_eq!(heap.len(), 3);
        assert!(heap.capacity() >= 3);
    }

    #[test]
    fn test_is_empty() {
        let mut heap: MinHeap<i32> = MinHeap::new();
        assert!(heap.is_empty());

        heap.push(1);
        assert!(!heap.is_empty());

        heap.pop();
        assert!(heap.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut heap = MinHeap::new();
        heap.push(42);
        assert_eq!(heap.peek(), Some(&42));
        assert_eq!(heap.pop(), Some(42));
        assert!(heap.is_empty());
    }

    #[test]
    fn test_into_iter_sorted() {
        let mut heap = MinHeap::new();
        heap.push(10);
        heap.push(20);
        heap.push(5);
        heap.push(15);
        heap.push(3);

        let sorted: Vec<_> = heap.into_iter_sorted().collect();
        assert_eq!(sorted, vec![3, 5, 10, 15, 20]);
    }

    #[test]
    fn test_pop_empty_heap() {
        let mut heap: MinHeap<i32> = MinHeap::new();
        assert!(heap.pop().is_none());
    }

    #[test]
    fn test_peek_after_pop_all() {
        let mut heap = MinHeap::new();
        heap.push(3);
        heap.push(1);
        heap.push(2);

        heap.pop();
        heap.pop();
        heap.pop();

        assert!(heap.peek().is_none());
    }

    #[test]
    fn test_negative_numbers() {
        let mut heap = MinHeap::new();
        heap.push(-1);
        heap.push(-3);
        heap.push(-2);

        assert_eq!(heap.pop(), Some(-3));
        assert_eq!(heap.pop(), Some(-2));
        assert_eq!(heap.pop(), Some(-1));
    }
}
