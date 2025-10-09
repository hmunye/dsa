use std::alloc::{self, Layout};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr::{self, NonNull};
use std::{fmt, mem, slice};

/*
* Reference:
* https://doc.rust-lang.org/nomicon/vec/vec.html
*/

/// Creates a `DynArray` containing the arguments.
#[macro_export]
macro_rules! dyn_array {
    () => {
        $crate::prelude::DynArray::new()
    };
    ($($elem:expr),+ $(,)?) => {{
        let mut arr = $crate::prelude::DynArray::with_capacity($crate::count!(@COUNT, $($elem)+));
        $(arr.push($elem);)+
        arr
    }};
    ($elem:expr; $count:expr) => {{
        let count = $count;
        let mut arr = $crate::prelude::DynArray::with_capacity(count);
        for elem in ::std::iter::repeat($elem).take(count) {
          arr.push(elem);
        }
        arr
    }};
}

#[doc(hidden)]
#[macro_export]
macro_rules! count {
    // https://lukaswirth.dev/tlborm/decl-macros/building-blocks/counting.html
    (@COUNT, $($elem:expr)+) => {
        <[()]>::len(&[$($crate::count!(@SUB, $elem ())),+])
    };
    (@SUB, $_elem:tt $sub:expr) => { $sub };
}

/// A contiguous growable array type, with heap-allocated contents.
///
/// # Time Complexities
///
/// | [push]  | [pop]  | [insert] | [remove] |
/// |---------|--------|----------|----------|
/// | *O*(1)~ | *O*(1) | *O*(n)   | *O*(n)   |
///
/// [push]:    DynArray::push
/// [pop]:     DynArray::pop
/// [insert]:  DynArray::insert
/// [remove]:  DynArray::remove
pub struct DynArray<T> {
    inner: RawArray<T>,
    /// Specifies the number of actual elements within the array.
    len: usize,
}

impl<T> DynArray<T> {
    /// Creates a new, empty `DynArray<T>`.
    ///
    /// The array will not allocate until elements are pushed onto it.
    #[inline]
    pub const fn new() -> Self {
        DynArray {
            inner: RawArray::new(),
            len: 0,
        }
    }

    /// Constructs a new, empty `DynArray<T>` with at least the specified
    /// capacity.
    ///
    /// The array will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the array will not allocate.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        DynArray {
            inner: RawArray::with_capacity(capacity),
            len: 0,
        }
    }

    /// Appends an element to the back of the array.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds [`isize::MAX`] _bytes_.
    pub fn push(&mut self, elem: T) {
        if self.len == self.capacity() {
            self.inner.grow()
        }

        unsafe {
            // `ptr::write` ensures that the memory being written to is not
            // evaluated. Indexing will treat the memory as an instance of `T`,
            // and assignment will attempt to drop the value that is being
            // overwritten.
            ptr::write(self.as_mut_ptr().add(self.len), elem);
        }

        self.len += 1;
    }

    /// Removes the last element from the array and returns it, or [`None`] if
    /// it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;

            // Moving the value out through indexing is not allowed, as it would
            // leave the slot uninitialized. Instead, we read and interpret the
            // bits as a value of type `T` without moving it (copy). This leaves
            // the index logically uninitialized.
            Some(unsafe { ptr::read(self.as_mut_ptr().add(self.len)) })
        }
    }

    /// Inserts an element at position index within the array, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `idx > len`.
    pub fn insert(&mut self, idx: usize, elem: T) {
        // Inserting at `len` is equivalent to [`DynArray::push`].
        assert!(idx <= self.len, "index out of bounds");

        if self.len == self.capacity() {
            self.inner.grow()
        }

        unsafe {
            // Before:
            //
            //      [0, 1, 2, 3, 4, _] // len = 5
            //
            // self.insert(2, 5);
            //
            // Copy 3 elements starting at index 2 to index 3:
            //
            //      [0, 1, 2, 3, 4, _]  -->  [0, 1, 2, 2, 3, 4]
            //             ^  ^
            //       src --|  |-- dst
            //
            // Write 5 to index 2:
            //
            //      [0, 1, 5, 2, 3, 4]
            //
            // Increment `len`
            //
            //      len = 6
            ptr::copy(
                self.as_ptr().add(idx),
                self.as_mut_ptr().add(idx + 1),
                self.len - idx,
            );
            ptr::write(self.as_mut_ptr().add(idx), elem);
        }

        self.len += 1;
    }

    /// Removes and returns the element at position `idx` within the array,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `idx >= len`.
    pub fn remove(&mut self, idx: usize) -> T {
        assert!(idx < self.len, "index out of bounds");

        // SAFETY: `self.inner` contains properly initialized items within the
        // range `0..len` and is aligned, contiguous, and valid for `len` reads
        // and writes.
        unsafe {
            self.len -= 1;

            let out = ptr::read(self.as_ptr().add(idx));

            // Before:
            //
            //      [0, 1, 2, 3, 4, _] // len = 5
            //
            // self.remove(2);
            //
            // Decrement `len`
            //
            //      len = 4
            //
            // Read element at index 2:
            //
            //      2
            //
            // Copy 2 elements starting at index 3 into index 2:
            //
            //      [0, 1, 2, 3, 4, _]  -->  [0, 1, 3, 4, 4, _]
            //             ^  ^
            //       dst --|  |-- src
            ptr::copy(
                self.as_ptr().add(idx + 1),
                self.as_mut_ptr().add(idx),
                self.len - idx,
            );

            out
        }
    }

    /// Returns the total number of elements the array can hold without
    /// reallocating.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Returns a raw pointer to the array’s buffer, or a dangling raw pointer
    /// valid for zero sized reads if the array didn’t allocate.
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.inner.as_ptr()
    }

    /// Returns a raw mutable pointer to the array’s buffer, or a dangling raw
    /// pointer valid for zero sized reads if the array didn’t allocate.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.as_mut_ptr()
    }

    /// Extracts a slice containing the entire array.
    ///
    /// Equivalent to `&[..]`.
    #[inline]
    pub const fn as_slice(&self) -> &[T] {
        // SAFETY: `slice::from_raw_parts` requires a pointer to a contiguous,
        // aligned buffer of size `len` with properly initialized `T` elements.
        //
        // `self.inner` contains properly initialized items within the range
        // `0..len` and is aligned, contiguous, and valid for `len` reads.
        //
        // Since `&mut self` methods are the only way to create `&mut`
        // references to `self.inner`, borrow-check ensures no mutable aliasing
        // occurs within the returned lifetime.
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len) }
    }

    /// Extracts a mutable slice containing the entire array.
    ///
    /// Equivalent to `&mut [..]`.
    #[inline]
    pub const fn as_mut_slice(&mut self) -> &mut [T] {
        // SAFETY: `slice::from_raw_parts_mut` requires a pointer to a
        // contiguous, aligned buffer of size `len` with properly initialized
        // `T` elements.
        //
        // `self.inner` contains properly initialized items within the range
        // `0..len` and is aligned, contiguous, and valid for `len` reads and
        // writes.
        //
        // Since references to `self.inner` can only be created through `&self`
        // and `&mut self` methods, borrow-check ensures that no reference to
        // `self.inner` can be created within the returned lifetime.
        unsafe { slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }

    /// Forces the length of the array to `new_len`.
    ///
    /// This is a low-level operation that maintains none of the normal
    /// invariants of the type.
    ///
    /// # Safety
    ///
    /// - `new_len` must be less than or equal to [`DynArray::capacity()`].
    /// - Elements within `old_len..new_len` range must be initialized.
    #[inline]
    pub const unsafe fn set_len(&mut self, new_len: usize) {
        self.len = new_len;
    }
}

impl<T> IntoIterator for DynArray<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        // Need to use `ptr::read` to unsafely move `inner` since it does not
        // implement `Copy`.
        let inner = unsafe { ptr::read(&self.inner) };
        let len = self.len;

        // Ensures `self` is not dropped at the end of this scope, since
        // ownership is being transferred and we do not want to deallocate the
        // memory.
        mem::forget(self);

        IntoIter {
            start: inner.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                // Casting a pointer to an integer strips its provenance.
                // Using `with_addr` reconstructs a pointer at the new
                // address but retains the provenance of `inner.as_ptr()`.
                inner.as_ptr().with_addr(inner.as_ptr() as usize + len)
            } else if inner.capacity == 0 {
                inner.as_ptr()
            } else {
                unsafe { inner.as_ptr().add(len) }
            },
            inner,
        }
    }
}

impl<T> Deref for DynArray<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> DerefMut for DynArray<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut_slice()
    }
}

impl<T: fmt::Debug> fmt::Debug for DynArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T> Drop for DynArray<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            // SAFETY: See [`DynArray::as_mut_slice`].
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len));
            }
        }

        // deallocation is handled by `inner`...
    }
}

impl<T> Default for DynArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// Consuming iterator, that is, one that moves each value out of the array.
#[derive(Debug)]
pub struct IntoIter<T> {
    inner: RawArray<T>,
    start: *const T,
    end: *const T,
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    // Casting a pointer to an integer strips its provenance.
                    // Using `with_addr` reconstructs a pointer at the new
                    // address but retains the provenance of `self.start`.
                    self.start = self.start.with_addr(self.start as usize + 1);
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                } else {
                    let out = ptr::read(self.start);
                    self.start = self.start.offset(1);
                    Some(out)
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let elem_size = mem::size_of::<T>();
        let len =
            (self.end as usize - self.start as usize) / if elem_size == 0 { 1 } else { elem_size };
        (len, Some(len))
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    // Casting a pointer to an integer strips its provenance.
                    // Using `with_addr` reconstructs a pointer at the new
                    // address but retains the provenance of `self.end`.
                    self.end = self.end.with_addr(self.end as usize - 1);
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                } else {
                    self.end = self.end.offset(-1);
                    Some(ptr::read(self.end))
                }
            }
        }
    }
}

impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        if mem::needs_drop::<T>() {
            let elem_size = mem::size_of::<T>();
            let len = (self.end as usize - self.start as usize)
                / if elem_size == 0 { 1 } else { elem_size };
            // SAFETY: See [`DynArray::as_mut_slice`].
            unsafe {
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.inner.as_mut_ptr(), len));
            }
        }

        // deallocation is handled by `inner`...
    }
}

/// Abstraction over the logic of allocating, growing, and freeing the memory
/// associated with the array.
#[derive(Debug)]
struct RawArray<T> {
    inner: RawArrayInner,
    /// Specifies the amount of space allocated for any future elements that
    /// will be added onto the array.
    capacity: usize,
    /// Marker to indicate to the compiler we own `T`, since it is unused in the
    /// other fields.
    _marker: PhantomData<T>,
}

impl<T> RawArray<T> {
    #[inline]
    const fn new() -> Self {
        // `!0` is inferred as a `usize` with all bits set.
        let capacity = if mem::size_of::<T>() == 0 { !0 } else { 0 };
        let align = mem::align_of::<T>();

        // SAFETY: All Rust types have a minimum alignment of 1, so `align` is
        // guaranteed to be non-zero.
        let inner = unsafe { RawArrayInner::new_dangling(align) };

        RawArray {
            inner,
            capacity,
            _marker: PhantomData,
        }
    }

    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        if capacity == 0 || mem::size_of::<T>() == 0 {
            RawArray::new()
        } else {
            let (inner, capacity) = RawArrayInner::with_capacity(capacity, mem::size_of::<T>());

            RawArray {
                inner,
                capacity,
                _marker: PhantomData,
            }
        }
    }

    #[inline]
    const fn capacity(&self) -> usize {
        self.capacity
    }

    #[inline]
    const fn as_ptr(&self) -> *const T {
        self.inner.ptr.as_ptr() as *const T
    }

    #[inline]
    const fn as_mut_ptr(&mut self) -> *mut T {
        self.inner.ptr.as_ptr() as *mut T
    }

    #[inline]
    fn grow(&mut self) {
        let cap = self.capacity;
        self.capacity = self.inner.allocate(cap, mem::size_of::<T>());
    }
}

// SAFETY: Each `RawArray<T>` has its own unique pointer to its underlying
// allocation, allowing it to be safely transferred across threads, as long as
// `T` can also be safely transferred.
unsafe impl<T: Send> Send for RawArray<T> {}

// SAFETY: Since there are public methods to access `&T` from a `&RawArray<T>`
// in an unsynchronized manner (e.g., `first`, `get`), `T` must be `Sync` for
// `RawArray<T>` to be considered `Sync`. Additionally, `RawArray<T>` does not
// use any form of interior mutability. All mutations occur through exclusive
// references (`&mut`).
unsafe impl<T: Sync> Sync for RawArray<T> {}

impl<T> Drop for RawArray<T> {
    fn drop(&mut self) {
        // Capacity for zero-sized types is set to `usize::MAX`, so both values
        // must be checked.
        if self.capacity != 0 && mem::size_of::<T>() != 0 {
            // Converts the capacity from number of elements to total bytes in
            // the layout.
            let layout = Layout::array::<T>(self.capacity)
                .expect("layout size should never be greater than usize::MAX");
            self.inner.deallocate(layout);
        }
    }
}

/// Encapsulates non-generic logic to minimize monomorphization and code-gen.
#[derive(Debug)]
struct RawArrayInner {
    /// Covariant, non-null, pointer to the heap-allocation.
    ptr: NonNull<u8>,
}

impl RawArrayInner {
    /// # Safety
    ///
    /// Provided `align` must be non-zero.
    #[inline]
    const unsafe fn new_dangling(align: usize) -> Self {
        let addr = unsafe { std::num::NonZero::new_unchecked(align) };

        RawArrayInner {
            // Allows us to lazily allocate by creating a well-aligned pointer
            // with no provenance. `capacity` is used as a "not yet initialized"
            // sentinel value instead.
            //
            // We're not generic over `T`, so we must manually specify the
            // correct alignment so the pointer is well-aligned.
            ptr: NonNull::without_provenance(addr),
        }
    }

    /// Intended to be called when `capacity` is non-zero.
    #[inline]
    fn with_capacity(capacity: usize, size: usize) -> (Self, usize) {
        // When `T` is zero-sized, `size` is zero. Reaching this point implies
        // the array is overfull (`capacity` is `usize::MAX`).
        assert!(size != 0, "capacity overflow");

        // Use the correct alignment (`size`) to avoid misaligned pointer
        // access, which can cause undefined behavior.
        let layout = Layout::from_size_align(capacity * size, size)
            .expect("layout size should never be greater than usize::MAX");

        // `ptr::offset` has the semantics of LLVM's `GEP` (GetElementPtr)
        // inbounds instruction, which informs LLVM that the calculated offsets
        // are within a single allocation's bounds, enabling certain
        // optimizations. `GEP` uses signed integers when indexing, meaning all
        // allocations must be limited to `isize::MAX` elements.
        assert!(layout.size() <= isize::MAX as usize, "allocation too large");

        let ptr = unsafe { alloc::alloc(layout) };
        let ptr = match NonNull::new(ptr) {
            Some(p) => p,
            // If `ptr` is null, the program will abort in a platform-specific
            // manner, since panicking unwinds the stack and could lead to
            // further allocations.
            None => alloc::handle_alloc_error(layout),
        };

        (RawArrayInner { ptr }, capacity)
    }

    /// Allocates memory for the specified number of elements (`capacity`),
    /// where each element has the given `size` in bytes, returning the new
    /// allocated capacity in units of `T`.
    fn allocate(&mut self, capacity: usize, size: usize) -> usize {
        // When `T` is zero-sized, `size` is zero. Reaching this point implies
        // the array is overfull (`capacity` is `usize::MAX`).
        assert!(size != 0, "capacity overflow");

        let total_bytes = if capacity == 0 {
            // Allocate one `T` worth of bytes.
            size
        } else {
            // Double the previous capacity, converted to bytes.
            2 * (capacity * size)
        };

        // Use the correct alignment (`size`) to avoid misaligned pointer
        // access, which can cause undefined behavior.
        let layout = Layout::from_size_align(total_bytes, size)
            .expect("layout size should never be greater than usize::MAX");

        // `ptr::offset` has the semantics of LLVM's `GEP` (GetElementPtr)
        // inbounds instruction, which informs LLVM that the calculated offsets
        // are within a single allocation's bounds, enabling certain
        // optimizations. `GEP` uses signed integers when indexing, meaning all
        // allocations must be limited to `isize::MAX` elements.
        assert!(layout.size() <= isize::MAX as usize, "allocation too large");

        let ptr = if capacity == 0 {
            unsafe { alloc::alloc(layout) }
        } else {
            // Use the correct alignment (`size`) to avoid misaligned pointer
            // access, which can cause undefined behavior.
            let old_layout = Layout::from_size_align(capacity * size, size)
                .expect("layout size should never be greater than usize::MAX");
            unsafe { alloc::realloc(self.ptr.as_ptr(), old_layout, layout.size()) }
        };

        self.ptr = match NonNull::new(ptr) {
            Some(p) => p,
            // If `ptr` is null, the program will abort in a platform-specific
            // manner, since panicking unwinds the stack and could lead to
            // further allocations.
            None => alloc::handle_alloc_error(layout),
        };

        // Converts bytes to capacity in `T` units.
        total_bytes / size
    }

    /// Deallocates the owned allocation. Intended to be called from a `Drop`
    /// impl.
    fn deallocate(&mut self, layout: Layout) {
        // When `T` is zero-sized, `layout.size()` is zero. Reaching this point
        // implies the array was never allocated.
        assert!(
            layout.size() != 0,
            "pointer with no provenance cannot be deallocated"
        );

        unsafe { alloc::dealloc(self.ptr.as_ptr(), layout) }
    }
}

/// ```compile_fail
/// use dsa::prelude::DynArray;
///
/// struct Touch<T: std::fmt::Debug>(T);
///
/// impl<T: std::fmt::Debug> Drop for Touch<T> {
///     fn drop(&mut self) {
///         // Accessing the inner `T` when dropping! May cause undefined
///         // behavior.
///         println!("{:?}", self.0);
///     }
/// }
///
/// let mut s = String::from("hello");
///
/// let mut arr = DynArray::new();
/// arr.push(Touch(&mut s));
///
/// println!("{}", s); // cannot borrow `s` as immutable because it is also
///                    // borrowed as mutable. mutable borrow might be used
///                    // when `arr` is dropped and runs the `Drop` code for
///                    // type `DynArray`.
/// ```
///
/// This should not compile because `DynArray<T>` indicates to the compiler it
/// will drop `T` through just having a `Drop` impl, without needing a specific
/// [`PhantomData`] field, as of [RFC 1238]. This is counted as a use of `T`
/// (mutable use). Since `T` _can_ be invalidated when dropping, this would not
/// compile.
///
/// The `#[may_dangle]` attribute is the (unsafe, unstable) escape hatch that
/// suppresses the conservative `dropck` assumption for specified generics. Used
/// to assert (unsafely) that a generic type's `Drop` impl is guaranteed to not
/// access any expired data, even if it is able to do so.
///
/// [RFC 1238]: https://rust-lang.github.io/rfcs/1238-nonparametric-dropck.html
/// [`PhantomData`]: std::marker::PhantomData
#[cfg(doctest)]
#[allow(dead_code)]
fn dropck() {}

// https://github.com/rust-lang/rust/blob/master/library/alloctests/tests/vec.rs
#[cfg(test)]
mod tests {
    use super::*;

    struct DropCounter<'a> {
        count: &'a mut u32,
    }

    impl Drop for DropCounter<'_> {
        fn drop(&mut self) {
            *self.count += 1;
        }
    }

    #[test]
    fn test_small_array() {
        // `DynArray` should have a memory layout of three machine words.
        assert_eq!(size_of::<DynArray<u8>>(), size_of::<usize>() * 3);
    }

    #[test]
    fn test_double_drop() {
        struct TwoArray<T> {
            x: DynArray<T>,
            y: DynArray<T>,
        }

        let (mut count_x, mut count_y) = (0, 0);

        {
            let mut ta = TwoArray {
                x: DynArray::new(),
                y: DynArray::new(),
            };

            ta.x.push(DropCounter {
                count: &mut count_x,
            });

            ta.y.push(DropCounter {
                count: &mut count_y,
            });

            drop(ta.x);

            // Here `ta` goes out of scope, `ta.y` should be dropped, but not
            // `ta.x`.
        }

        assert_eq!(count_x, 1);
        assert_eq!(count_y, 1);
    }

    #[test]
    fn test_indexing() {
        let a: DynArray<isize> = dyn_array![10, 20];

        assert_eq!(a[0], 10);
        assert_eq!(a[1], 20);

        let mut x: usize = 0;
        assert_eq!(a[x], 10);
        assert_eq!(a[x + 1], 20);

        x = x + 1;
        assert_eq!(a[x], 20);
        assert_eq!(a[x - 1], 10);
    }

    #[test]
    fn test_debug_fmt() {
        let arr: DynArray<isize> = dyn_array![];
        assert_eq!("[]", format!("{:?}", arr));

        let arr = dyn_array![1; 3];
        assert_eq!("[1, 1, 1]", format!("{:?}", arr));
    }

    #[test]
    fn test_push() {
        let mut a = dyn_array![];
        a.push(1);
        assert!(a.iter().eq([1].iter()));
        a.push(2);
        assert!(a.iter().eq([1, 2].iter()));
        a.push(3);
        assert!(a.iter().eq([1, 2, 3].iter()));
    }

    #[test]
    fn test_slice_from_ref() {
        let values = dyn_array![1, 2, 3, 4, 5];
        let slice = &values[1..3];

        assert_eq!(slice, [2, 3]);
    }

    #[test]
    fn test_slice_from_mut() {
        let mut values = dyn_array![1, 2, 3, 4, 5];

        {
            let slice = &mut values[2..];
            assert!(slice == [3, 4, 5]);
            for p in slice {
                *p += 2;
            }
        }

        assert!(values.iter().eq([1, 2, 5, 6, 7].iter()));
    }

    #[test]
    fn test_slice_to_mut() {
        let mut values = dyn_array![1, 2, 3, 4, 5];

        {
            let slice = &mut values[..2];
            assert!(slice == [1, 2]);
            for p in slice {
                *p += 1;
            }
        }

        assert!(values.iter().eq([2, 3, 3, 4, 5].iter()));
    }

    #[test]
    fn test_zst() {
        assert_eq!(DynArray::<()>::new().capacity(), usize::MAX);

        let mut a = DynArray::new();
        assert_eq!(a.len(), 0);
        a.push(());
        assert_eq!(a.len(), 1);
        a.push(());
        assert_eq!(a.len(), 2);
        assert_eq!(a.pop(), Some(()));
        assert_eq!(a.pop(), Some(()));
        assert_eq!(a.pop(), None);

        assert_eq!(a.iter().count(), 0);
        a.push(());
        assert_eq!(a.iter().count(), 1);
        a.push(());
        assert_eq!(a.iter().count(), 2);

        for &() in a.iter() {}

        assert_eq!(a.iter_mut().count(), 2);
        a.push(());
        assert_eq!(a.iter_mut().count(), 3);
        a.push(());
        assert_eq!(a.iter_mut().count(), 4);

        for &mut () in a.iter_mut() {}
        unsafe {
            a.set_len(0);
        }
        assert_eq!(a.iter_mut().count(), 0);
    }

    #[test]
    fn test_index() {
        let arr = dyn_array![1, 2, 3];
        assert!(arr[1] == 2);
    }

    #[test]
    #[should_panic]
    fn test_index_out_of_bounds() {
        let arr = dyn_array![1, 2, 3];
        let _ = arr[3];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_1() {
        let x = dyn_array![1, 2, 3, 4, 5];
        let _ = &x[!0..];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_2() {
        let x = dyn_array![1, 2, 3, 4, 5];
        let _ = &x[..6];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_3() {
        let x = dyn_array![1, 2, 3, 4, 5];
        let _ = &x[!0..4];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_4() {
        let x = dyn_array![1, 2, 3, 4, 5];
        let _ = &x[1..6];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_5() {
        let x = dyn_array![1, 2, 3, 4, 5];
        let _ = &x[3..2];
    }

    #[test]
    fn test_move_items() {
        let arr = dyn_array![1, 2, 3];
        let mut arr2 = dyn_array![];
        for i in arr {
            arr2.push(i);
        }
        assert!(arr2.iter().eq([1, 2, 3].iter()));
    }

    #[test]
    fn test_move_items_zero_sized() {
        let arr = dyn_array![(), (), ()];

        let mut arr2 = dyn_array![];
        for i in arr {
            arr2.push(i);
        }

        assert!(arr2.iter().eq([(), (), ()].iter()));
    }

    #[test]
    fn test_into_iter() {
        let arr = dyn_array![10, 20, 30, 40];
        let mut iter = arr.into_iter();

        assert_eq!(iter.size_hint(), (4, Some(4)));

        assert_eq!(iter.next(), Some(10));
        assert_eq!(iter.size_hint(), (3, Some(3)));

        assert_eq!(iter.next_back(), Some(40));
        assert_eq!(iter.size_hint(), (2, Some(2)));

        assert_eq!(iter.next(), Some(20));
        assert_eq!(iter.size_hint(), (1, Some(1)));

        assert_eq!(iter.next_back(), Some(30));
        assert_eq!(iter.size_hint(), (0, Some(0)));

        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
        assert_eq!(iter.next(), None);
        assert_eq!(iter.next_back(), None);
    }
}
