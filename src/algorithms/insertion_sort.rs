//! [Insertion Sort]: A simple sorting algorithm that builds the final sorted
//! array (or list) one item at a time by comparisons.
//!
//! [Insertion Sort]: https://en.wikipedia.org/wiki/Insertion_sort

/// Sorts the provided array in-place, in ascending order.
///
/// Insertion sort is `stable` meaning equal elements retain their original
/// relative position.
///
/// # Time Complexity
///
/// Takes *O*(*n^2*) time. For each element in the array, the algorithm works
/// backwards, comparing adjacent elements with each other and swapping when
/// needed.
///
/// # Example
///
/// ```
/// use dsa::prelude::*;
///
/// let mut arr = [10, 323, 11, 35, 76, 2, 11, 393, 14];
///
/// insertion_sort(&mut arr);
///
/// assert_eq!(arr, [2, 10, 11, 11, 14, 35, 76, 323, 393]);
/// ```
pub fn insertion_sort<T: PartialOrd>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let mut j = i;

        while j > 0 && arr[j - 1] > arr[j] {
            // Just `arr.swap()`
            unsafe {
                let ptr = &raw mut arr[j];
                let ptr_1 = &raw mut arr[j - 1];
                core::ptr::swap(ptr, ptr_1);
            }

            j -= 1;
        }
    }
}
