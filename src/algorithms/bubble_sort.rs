//! [Bubble Sort]: A simple sorting algorithm that repeatedly steps through the
//! input list element by element, comparing the current element with the one
//! after it, swapping their values if needed.
//!
//! [Bubble Sort]: https://en.wikipedia.org/wiki/Bubble_sort

/// Sorts the provided array in-place, in ascending order.
///
/// Bubble sort is `stable` meaning equal elements retain their original
/// relative position.
///
/// # Time Complexity
///
/// Takes *O*(*n^2*) time. For every element of the list, the algorithm compares
/// an adjacent pair and swaps them if the ordering is incorrect (ascending).
/// The list is linearly iterated over for every `n` elements.
///
/// # Example
///
/// ```
/// use dsa::prelude::*;
///
/// let mut arr = [10, 323, 11, 35, 76, 2, 11, 393, 14];
///
/// bubble_sort(&mut arr);
///
/// assert_eq!(arr, [2, 10, 11, 11, 14, 35, 76, 323, 393]);
/// ```
pub fn bubble_sort<T: PartialOrd>(arr: &mut [T]) {
    for i in 0..arr.len() {
        for j in 0..(arr.len() - i - 1) {
            if arr[j + 1] < arr[j] {
                // Just `arr.swap()`
                unsafe {
                    let ptr = &raw mut arr[j];
                    let ptr_1 = &raw mut arr[j + 1];
                    core::ptr::swap(ptr, ptr_1);
                }
            }
        }
    }
}
