/// Sorts the provided slice in ascending order. Does not perform the sort
/// in-place, but is stable.
///
/// [Merge Sort] is an efficient, general-purpose, and comparison-based sorting
/// algorithm.
///
/// [Merge Sort]: https://en.wikipedia.org/wiki/Merge_sort
pub fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    // Merge Sort is a stable but not in-place sorting algorithm. It preserves
    // the relative order of equal elements, but requires additional space
    // beyond *O*(1) (usually *O*(n) for the temporary buffers). The algorithm
    // repeatedly splits the array into halves, recursively dividing it until
    // the sub-arrays each contain a single element, which is trivially sorted.
    // As the recursion unwinds, each pair of sub-arrays is merged back together
    // in sorted order. The process continues by merging the previously sorted
    // sub-arrays with new ones created at each recursion level. This results in
    // an overall time complexity of *O*(n log n): *O*(log n) for the recursive
    // splitting and *O*(n) for merging each pair of sub-arrays.
    //
    // The cloned slice is important for preserving the order of elements after
    // each merge.
    split_recursive(arr, &mut arr.to_vec(), 0, arr.len());
}

fn split_recursive<T>(out: &mut [T], buf: &mut [T], start: usize, end: usize)
where
    T: Ord + Clone,
{
    // Range containing one element is considered sorted, so begin unwinding.
    if end - start <= 1 {
        return;
    }

    let mid = start + (end - start) / 2;

    // `out` and `buf` are alternated at each recursive level. Without
    // alternating buffers, the merged results would need to be copied back into
    // the original slice at each recursion level. By alternating between the
    // original slice and the clone, one can hold the merged data while the
    // other is overwritten, avoiding unnecessary copying.
    split_recursive(buf, out, start, mid);
    split_recursive(buf, out, mid, end);

    // Merges two sorted subarrays: [start..mid] and [mid..end] from `buf` into
    // `out`.
    merge(out, buf, start, mid, end);
}

fn merge<T>(out: &mut [T], buf: &mut [T], start: usize, mid: usize, end: usize)
where
    T: Ord + Clone,
{
    let mut i = start; // Start of left sub-array.
    let mut j = mid; // Start of right sub-array.

    // Iterate over the range of both sub-arrays.
    for item in out.iter_mut().take(end).skip(start) {
        // Compare elements from the left and right sub-arrays, and append the
        // smaller element to `out` in sorted order.
        if i < mid && (j >= end || buf[i] <= buf[j]) {
            *item = buf[i].clone();
            i += 1;
        } else {
            // Once the left sub-array is exhausted, the remaining elements
            // from the right sub-array are written to `out`.
            *item = buf[j].clone();
            j += 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorted() {
        let mut arr = [1, 2, 3, 4, 5, 6];
        merge_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = [6, 5, 4, 3, 2, 1];
        merge_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_duplicate() {
        let mut arr = [7, 7, 7, 7, 7, 7];
        merge_sort(&mut arr);
        assert_eq!(arr, [7, 7, 7, 7, 7, 7]);
    }

    #[test]
    fn test_unsorted() {
        let mut arr = [3, 5, 2, 1, 4];
        merge_sort(&mut arr);
        assert_eq!(arr, [1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_empty() {
        let mut arr: Vec<i32> = Vec::new();
        merge_sort(&mut arr);
        assert_eq!(arr, Vec::<i32>::new());
    }

    #[test]
    fn test_single_element() {
        let mut arr = [42];
        merge_sort(&mut arr);
        assert_eq!(arr, [42]);
    }

    #[test]
    fn test_mixed_sign() {
        let mut arr = [3, -1, 4, -2, 0, 5];
        merge_sort(&mut arr);
        assert_eq!(arr, [-2, -1, 0, 3, 4, 5]);
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (1..=1000).rev().collect();
        merge_sort(&mut arr);
        assert_eq!(arr, (1..=1000).collect::<Vec<_>>());
    }

    #[test]
    fn test_owned() {
        let mut arr = [
            String::from("h"),
            String::from("a"),
            String::from("r"),
            String::from("c"),
        ];
        merge_sort(&mut arr);
        assert_eq!(&arr[..], &["a", "c", "h", "r"]);
    }
}
