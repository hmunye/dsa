/// Sorts the provided slice in ascending order, in-place.
///
/// [Heap Sort] is an efficient, comparison-based sorting algorithm that
/// reorganizes an input array into a `heap` and then repeatedly removes the
/// largest node from that heap, placing it at the end of the array.
///
/// [Heap Sort]: https://en.wikipedia.org/wiki/Heapsort
pub fn heap_sort<T: Ord>(arr: &mut [T]) {
    let end = arr.len();

    // Build the max-heap by heapifying from the last non-leaf node up to the
    // root in *O*(n) time. This bottom-up approach skips leaf nodes, which
    // trivially satisfy the max-heap property.
    for i in (0..end / 2).rev() {
        heapify(arr, i, end);
    }

    // The array isn't contiguously sorted just by heapifying, so we repeatedly
    // swap the root (max) with the last element (min), then restore the
    // max-heap property for the reduced heap starting at the root. This process
    // sorts the array in-place within the range `end..1` in *O*(n log n).
    for i in (1..end).rev() {
        arr.swap(0, i);
        heapify(arr, 0, i);
    }
}

fn heapify<T: Ord>(arr: &mut [T], mut pos: usize, end: usize) {
    loop {
        let left = 2 * pos + 1;
        let right = 2 * pos + 2;

        let mut max = pos;

        if left < end && arr[pos] < arr[left] {
            max = left;
        }

        if right < end && arr[max] < arr[right] {
            max = right;
        }

        if max != pos {
            arr.swap(max, pos);
            pos = max;
        } else {
            // Can no longer sift down.
            break;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorted() {
        let mut arr = [1, 2, 3, 4, 5, 6];
        heap_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = [6, 5, 4, 3, 2, 1];
        heap_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_duplicate() {
        let mut arr = [7, 7, 7, 7, 7, 7];
        heap_sort(&mut arr);
        assert_eq!(arr, [7, 7, 7, 7, 7, 7]);
    }

    #[test]
    fn test_unsorted() {
        let mut arr = [3, 5, 2, 1, 4];
        heap_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = Vec::new();
        heap_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = [42];
        heap_sort(&mut arr);
        assert_eq!(arr, [42]);
    }

    #[test]
    fn test_mixed_sign() {
        let mut arr = [3, -1, 4, -2, 0, 5];
        heap_sort(&mut arr);
        assert_eq!(arr, [-2, -1, 0, 3, 4, 5]);
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (1..=1000).rev().collect();
        heap_sort(&mut arr);
        assert_eq!(arr, (1..=1000).collect::<Vec<_>>());
    }
}
