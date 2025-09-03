//! [Binary Search]: A search algorithm that finds the position of a target
//! value within a sorted array.
//!
//! [Binary Search]: https://en.wikipedia.org/wiki/Binary_search

/// Returns the index of the `target` within the sorted array, or [`None`] if
/// it was not found.
///
/// # Time Complexity
///
/// Takes *O*(*log n*) time. Binary search uses a divide-and-conquer approach
/// and runs in logarithmic time in the worst case, making *O*(*log n*)
/// comparisons, where `n` is the number of elements in the array.
///
/// # Examples
///
/// ```
/// use dsa::prelude::*;
///
/// let arr = [4, 10, 12, 13, 20, 50, 66];
///
/// assert_eq!(binary_search(&arr, &4), Some(0));
/// assert_eq!(binary_search(&arr, &40), None);
/// ```
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut lo = 0;
    let mut hi = arr.len();

    while lo < hi {
        let mid = lo + ((hi - lo) >> 1);

        if arr[mid] == *target {
            return Some(mid);
        } else if arr[mid] < *target {
            lo = mid + 1;
        } else {
            hi = mid;
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_found_in_middle() {
        let arr = [1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, &5), Some(2));
    }

    #[test]
    fn test_found_at_start() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(binary_search(&arr, &1), Some(0));
    }

    #[test]
    fn test_found_at_end() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(binary_search(&arr, &5), Some(4));
    }

    #[test]
    fn test_not_found() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(binary_search(&arr, &6), None);
    }

    #[test]
    fn test_empty_array() {
        let arr: [i32; 0] = [];
        assert_eq!(binary_search(&arr, &1), None);
    }

    #[test]
    fn test_single_element_found() {
        let arr = [42];
        assert_eq!(binary_search(&arr, &42), Some(0));
    }

    #[test]
    fn test_single_element_not_found() {
        let arr = [42];
        assert_eq!(binary_search(&arr, &99), None);
    }

    #[test]
    fn test_duplicates_found_first_occurrence() {
        let arr = [1, 2, 4, 4, 4, 5, 6];
        let result = binary_search(&arr, &4);
        assert!(matches!(result, Some(2..=4)));
    }
}

