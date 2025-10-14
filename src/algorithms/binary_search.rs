use std::borrow::Borrow;

/// Returns the index of `target` within the slice, or [`None`] if it could
/// not be found.
///
/// [Binary Search] is a search algorithm that finds the position of a target
/// value within a sorted array.
///
/// [Binary Search]: https://en.wikipedia.org/wiki/Binary_search
pub fn binary_search<T, Q>(arr: &[T], target: &Q) -> Option<usize>
where
    T: Ord + Borrow<Q>,
    Q: Ord,
{
    let mut lo = 0;
    let mut hi = arr.len();

    while lo < hi {
        let m = lo + (hi - lo) / 2;

        if arr[m].borrow() == target {
            return Some(m);
        } else if arr[m].borrow() < target {
            lo = m + 1;
        } else {
            hi = m;
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_found() {
        let arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        assert_eq!(binary_search(&arr, &5), Some(4));
        assert_eq!(binary_search(&arr, &10), Some(9));

        let arr = [1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25, 27, 29, 31];
        assert_eq!(binary_search(&arr, &19), Some(9));
        assert_eq!(binary_search(&arr, &1), Some(0));
        assert_eq!(binary_search(&arr, &31), Some(15));
        assert_eq!(binary_search(&arr, &13), Some(6));
    }

    #[test]
    fn test_first() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(binary_search(&arr, &1), Some(0));
    }

    #[test]
    fn test_last() {
        let arr = [1, 2, 3, 4, 5];
        assert_eq!(binary_search(&arr, &5), Some(4));
    }

    #[test]
    fn test_not_found() {
        let arr = [1, 3, 5, 7, 9, 11];
        assert_eq!(binary_search(&arr, &4), None);
        assert_eq!(binary_search(&arr, &6), None);
    }

    #[test]
    fn test_empty() {
        let arr: [i32; 0] = [];
        assert_eq!(binary_search(&arr, &1), None);
    }

    #[test]
    fn test_single_element() {
        let arr = [10];
        assert_eq!(binary_search(&arr, &10), Some(0));
        assert_eq!(binary_search(&arr, &5), None);
    }
}
