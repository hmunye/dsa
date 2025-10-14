/// Sorts the provided slice in ascending order, in-place.
///
/// [Quick Sort] is is a `divide-and-conquer` algorithm used for efficient,
/// general-purpose sorting.
///
/// [Quick Sort]: https://en.wikipedia.org/wiki/Quicksort
pub fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() > 1 {
        let pivot_idx = partition(arr);

        // The pivot is already in its correct position, so it's excluded from
        // each recursive call.
        quick_sort(&mut arr[..pivot_idx]);
        quick_sort(&mut arr[pivot_idx + 1..]);
    }
}

/// Sorts the provided slice in ascending order, in-place, without using
/// a recursive approach.
///
/// [Quick Sort] is is a `divide-and-conquer` algorithm used for efficient,
/// general-purpose sorting.
///
/// [Quick Sort]: https://en.wikipedia.org/wiki/Quicksort
pub fn quick_sort_iterative<T: Ord>(arr: &mut [T]) {
    // Preallocate the stack with capacity for the average case, where the
    // number of partitions is proportional to the logarithm of the array
    // length, *O*(log n), when the pivot is chosen well.
    let mut stack = Vec::with_capacity(arr.len().ilog2() as usize);

    // Initially begin with the full range of the array.
    stack.push(0..arr.len());

    while let Some(range) = stack.pop() {
        let start = range.start;
        let end = range.end;

        // Only process the range if it contains at least two elements.
        if end > start + 1 {
            let pivot_idx = partition(&mut arr[range]);
            // The pivot is already in its correct position, so it's excluded
            // from each range.
            stack.push(start + pivot_idx + 1..end);
            stack.push(start..start + pivot_idx);
        } else {
            continue;
        }
    }
}

/// Sorts the elements of the array in-place around a pivot, returning the final
/// index of the pivot.
fn partition<T: Ord>(arr: &mut [T]) -> usize {
    // The `pivot` is chosen as the median of the first, middle, and last
    // elements. Picking the first or last element instead can lead to the
    // worst-case time complexity, *O*(n^2), if the array is already sorted or
    // nearly sorted. In such cases, the partitions will be unbalanced, with one
    // split being very large and the other being very small. This leads to
    // deeper recursion and inefficient performance. By choosing the median of
    // three elements, we improve the chances of selecting a pivot that splits
    // the array more evenly, avoiding these worst-case scenarios.
    //
    // The pivot could also be chosen randomly to improve the chances of
    // partitioning the array more evenly.
    let pivot = median_of_three(arr);

    // Swap the pivot with the first element to make swapping simpler.
    if pivot != 0 {
        arr.swap(0, pivot);
    }

    // Track where the next element smaller than the pivot should be swapped.
    let mut i = 1;

    // Skip the first index to avoid comparing the pivot element with itself.
    for j in 1..arr.len() {
        if arr[j] < arr[pivot] {
            arr.swap(j, i);
            i += 1;
        }
    }

    // Swap the pivot (which starts at index 0) with the element at index
    // `i - 1`, placing the pivot in its correct position. The index `i - 1`
    // represents the boundary where elements smaller than the pivot end.
    arr.swap(pivot, i - 1);

    // Index of the pivot element.
    i - 1
}

/// Returns the pivot index in the array using the median-of-three method.
fn median_of_three<T: Ord>(arr: &[T]) -> usize {
    let first = &arr[0];
    let middle = &arr[arr.len() / 2];
    let last = &arr[arr.len() - 1];

    // Find the median of the first, middle, and last elements.
    if first <= middle && middle <= last {
        arr.len() / 2
    } else if first <= last && last <= middle {
        arr.len() - 1
    } else {
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorted() {
        let mut arr = [1, 2, 3, 4, 5, 6];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = [6, 5, 4, 3, 2, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_duplicate() {
        let mut arr = [7, 7, 7, 7, 7, 7];
        quick_sort(&mut arr);
        assert_eq!(arr, [7, 7, 7, 7, 7, 7]);
    }

    #[test]
    fn test_unsorted() {
        let mut arr = [3, 5, 2, 1, 4];
        quick_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = Vec::new();
        quick_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = [42];
        quick_sort(&mut arr);
        assert_eq!(arr, [42]);
    }

    #[test]
    fn test_mixed_sign() {
        let mut arr = [3, -1, 4, -2, 0, 5];
        quick_sort(&mut arr);
        assert_eq!(arr, [-2, -1, 0, 3, 4, 5]);
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (1..=1000).rev().collect();
        quick_sort(&mut arr);
        assert_eq!(arr, (1..=1000).collect::<Vec<_>>());
    }
}
