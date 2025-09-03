//! [Linear Search]: Method for finding an element within a list. It
//! sequentially checks each element of the list until a match is found or the
//! whole list has been searched.
//!
//! [Linear Search]: https://en.wikipedia.org/wiki/Linear_search

/// Returns the index of the `target` within the array, or [`None`] if it was
/// not found.
///
/// # Time Complexity
///
/// Takes *O*(*n*) time. Linear search sequentially checks each element of the
/// list until a match is found or the whole list has been searched.
///
/// # Examples
///
/// ```
/// use dsa::prelude::*;
///
/// let arr = [11, 4, 30, 110, 20, 2, 70, 45];
///
/// assert_eq!(linear_search(&arr, &4), Some(1));
/// assert_eq!(linear_search(&arr, &40), None);
/// ```
pub fn linear_search<T: PartialEq>(arr: &[T], target: &T) -> Option<usize> {
    for (i, elem) in arr.iter().enumerate() {
        if *elem == *target {
            return Some(i);
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
        assert_eq!(linear_search(&arr, &5), Some(2));
    }

    #[test]
    fn test_found_at_start() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(linear_search(&arr, &1), Some(0));
    }

    #[test]
    fn test_found_at_end() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(linear_search(&arr, &5), Some(4));
    }

    #[test]
    fn test_not_found() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(linear_search(&arr, &6), None);
    }

    #[test]
    fn test_empty_array() {
        let arr: [i32; 0] = [];
        assert_eq!(linear_search(&arr, &1), None);
    }

    #[test]
    fn test_single_element_found() {
        let arr = [42];
        assert_eq!(linear_search(&arr, &42), Some(0));
    }

    #[test]
    fn test_single_element_not_found() {
        let arr = [42];
        assert_eq!(linear_search(&arr, &99), None);
    }

    #[test]
    fn test_duplicates_found_first_occurrence() {
        let arr = [1, 2, 4, 4, 4, 5, 6];
        let result = linear_search(&arr, &4);
        assert!(matches!(result, Some(2..=4)));
    }
}
