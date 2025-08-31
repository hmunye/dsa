//! A contiguous growable array type with heap-allocated contents.
//!
//! Just use [`Vec`] instead.

use std::alloc::{self, Layout};
use std::fmt;

use core::cmp::{self, Ordering};
use core::hash::{Hash, Hasher};
use core::ops::{Deref, DerefMut};
use core::ptr::{self, NonNull};
use core::{marker, mem};

/// Creates a `Vector` containing the arguments.
///
/// # Examples
///
/// - Create a `Vector` containing a given list of elements:
///
/// ```
/// use dsa::vector;
/// use dsa::collections::Vector;
///
/// let v = vector![1, 2, 3];
/// assert_eq!(v, [1, 2, 3]);
/// ```
///
/// - Create a `Vector` from a given element and size:
///
/// ```
/// use dsa::vector;
/// use dsa::collections::Vector;
///
/// let v = vector![String::from("hello"); 3];
/// assert_eq!(v, ["hello", "hello", "hello"]);
/// ```
#[macro_export]
macro_rules! vector {
    () => {
        $crate::collections::Vector::new()
    };
    // `$(,)?` allows for a trailing comma.
    ($($elem:expr),* $(,)?) => {{
        // Capacity can be determined at compile time.
        const _: usize = $crate::count![@COUNT; $($elem),*];

        let mut v = $crate::collections::Vector::with_capacity($crate::count![@COUNT; $($elem),*]);
        $(v.push($elem);)*
        v
    }};
    ($elem:expr; $n:expr) => {{
        // Ensure the expression is only evaluated once.
        let count = $n;

        let mut v = $crate::collections::Vector::with_capacity(count);
        v.extend(::core::iter::repeat($elem).take(count));
        v
    }};
}

#[macro_export]
#[doc(hidden)]
macro_rules! count {
    (@COUNT; $($elem:expr),*) => {
        // For every `$elem`, create an array, substituting the `$elem` with
        // unit, take a reference to it, and invoke the len implementation for
        // a slice of unit values.
        <[()]>::len(&[$($crate::count![@SUBST; $elem]),*])
    };
    (@SUBST; $elem:expr) => { () };
}

/// A contiguous growable array type with heap-allocated contents.
///
/// Just use [`Vec`] instead.
pub struct Vector<T> {
    /// Internal buffer.
    buf: RawVector<T>,
    /// Number of initialized elements.
    len: usize,
}

/// An iterator that moves out of a `Vector<T>`.
///
/// Implemented as a C-style iterator so reads can happen from both sides.
#[derive(Debug)]
pub struct IntoIter<T> {
    /// Pointer to the start of the vector.
    start: *const T,
    /// Pointer to the end of the vector.
    end: *const T,
    /// Internal buffer of the vector. Needed since the iterator takes
    /// ownership and we want to ensure it does not invoke it's destructor.
    _buf: RawVector<T>,
}

impl<T> Vector<T> {
    /// Constructs a new, empty `Vector<T>`.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::Vector;
    ///
    /// let vec: Vector<i32> = Vector::new();
    /// ```
    #[inline]
    pub const fn new() -> Self {
        Self {
            buf: RawVector::new(),
            len: 0,
        }
    }

    /// Constructs a new, empty `Vector<T>` with at least the specified
    /// capacity.
    ///
    /// The vector will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is zero, the vector will not allocate.
    ///
    /// It is important to note that although the returned vector has the
    /// minimum *capacity* specified, the vector will have a zero *length*.
    ///
    /// For `Vector<T>` where `T` is a zero-sized type, there will be no
    /// allocation and the capacity will always be `usize::MAX`.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::Vector;
    ///
    /// let mut vec: Vector<i32> = Vector::with_capacity(10);
    ///
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.capacity() >= 10);
    ///
    /// for i in 0..10 {
    ///     vec.push(i);
    /// }
    ///
    /// assert_eq!(vec.len(), 10);
    /// assert!(vec.capacity() >= 10);
    ///
    /// vec.push(10);
    ///
    /// assert_eq!(vec.len(), 11);
    /// assert!(vec.capacity() >= 11);
    ///
    /// let vec_units = Vector::<()>::with_capacity(10);
    /// assert_eq!(vec_units.capacity(), usize::MAX);
    ///
    /// let empty: Vector<i32> = Vector::with_capacity(0);
    /// assert_eq!(empty.capacity(), 0);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            buf: RawVector::with_capacity(capacity),
            len: 0,
        }
    }

    /// Appends an element to the back of the vector.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds `isize::MAX` bytes.
    ///
    /// # Time Complexity
    ///
    /// Takes amortized *O*(1) time. If the vector's length would exceed its
    /// capacity after the push, *O*(*capacity*) time is taken to copy the
    /// vector's elements to a larger allocation. This expensive operation is
    /// offset by the *capacity* *O*(1) insertions it allows.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec: Vector<i32> = vector![1, 2];
    /// vec.push(3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    pub fn push(&mut self, elem: T) {
        if self.len == self.capacity() {
            self.buf.grow_one();
        }

        unsafe {
            // Offset by the previous `self.len` value.
            ptr::write(self.as_mut_ptr().add(self.len), elem);
        }

        self.len += 1;
    }

    /// Removes the last element from the vector and returns it, or [`None`] if
    /// it is empty.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(1) time, since there is only a length decrement and
    /// [`ptr::read`] occurring on the last element, regardless of the current
    /// size of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec: Vector<i32> = vector![1, 2];
    ///
    /// assert_eq!(vec.pop(), Some(2));
    /// assert_eq!(vec.pop(), Some(1));
    /// assert_eq!(vec.pop(), None);
    ///
    /// assert_eq!(vec.len(), 0);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            // Offset by the new `self.len` value.
            unsafe { Some(ptr::read(self.as_ptr().add(self.len))) }
        }
    }

    /// Inserts an element at position `index` within the vector, shifting all
    /// elements after it to the right.
    ///
    /// # Panics
    ///
    /// Panics if `index > len`.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*len*) time. All items after the insertion index must be
    /// shifted to the right. In the worst case, all elements are shifted when
    /// the insertion index is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec: Vector<i32> = Vector::with_capacity(10);
    ///
    /// vec.push(10);
    /// vec.push(11);
    /// vec.push(12);
    /// vec.push(13);
    ///
    /// assert_eq!(vec[2], 12);
    ///
    /// vec.insert(2, 44);
    ///
    /// assert_eq!(vec[2], 44);
    /// assert_eq!(vec[3], 12);
    /// ```
    pub fn insert(&mut self, index: usize, elem: T) {
        // Can be equal to `len` since inserting after all elements is valid.
        assert!(index <= self.len, "index out of bounds");

        if self.len == self.capacity() {
            self.buf.grow_one();
        }

        unsafe {
            // Effectively a `memmove`.
            //
            // https://en.cppreference.com/w/c/string/byte/memmove
            ptr::copy(
                self.as_ptr().add(index),
                self.as_mut_ptr().add(index + 1),
                self.len - index,
            );

            ptr::write(self.as_mut_ptr().add(index), elem);
        }

        self.len += 1;
    }

    /// Removes and returns the element at position `index` within the vector,
    /// shifting all elements after it to the left.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*len*) time. All items after the removal index must be
    /// shifted to the left. In the worst case, all elements are shifted when
    /// the removal index is 0.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec: Vector<i32> = Vector::with_capacity(10);
    ///
    /// vec.push(10);
    /// vec.push(11);
    /// vec.push(12);
    /// vec.push(13);
    ///
    /// assert_eq!(vec[2], 12);
    /// assert_eq!(vec.remove(2), 12);
    /// assert_eq!(vec[2], 13);
    /// ```
    pub fn remove(&mut self, index: usize) -> T {
        // Can't be equal to `len` since removing after all elements is not
        // valid.
        assert!(index < self.len, "index out of bounds");

        self.len -= 1;

        unsafe {
            let elem = ptr::read(self.as_ptr().add(index));

            // Effectively a `memmove` operation.
            //
            // https://en.cppreference.com/w/c/string/byte/memmove
            ptr::copy(
                self.as_ptr().add(index + 1),
                self.as_mut_ptr().add(index),
                self.len - index,
            );

            elem
        }
    }

    /// Shortens the vector, keeping the first `len` elements and dropping
    /// the rest.
    ///
    /// If `len` is greater or equal to the vector's current length, this has
    /// no effect. This method also has no effect on the allocated capacity of
    /// the vector.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*self.len - len*) time. All items after `len` must be dropped.
    /// In the worst case, all remaining items must invoke their destructors
    /// when `T: Drop`.
    ///
    /// # Examples
    ///
    /// Truncating a five element vector to two elements:
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec = vector![1, 2, 3, 4, 5];
    /// vec.truncate(2);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec, [1, 2]);
    /// ```
    ///
    /// No truncation occurs when `len` is greater than the vector's current
    /// length:
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec = vector![1, 2, 3];
    /// vec.truncate(8);
    /// assert_eq!(vec.len(), 3);
    /// assert_eq!(vec, [1, 2, 3]);
    /// ```
    ///
    /// Truncating when `len == 0` is equivalent to calling the [`clear`]
    /// method.
    ///
    /// [`clear`]: Vector::clear
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec = vector![1, 2, 3];
    /// vec.truncate(0);
    /// assert_eq!(vec.len(), 0);
    /// ```
    pub fn truncate(&mut self, len: usize) {
        if len >= self.len() {
            return;
        }

        let remaining_len = self.len - len;
        unsafe {
            let slice = core::slice::from_raw_parts_mut(self.as_mut_ptr().add(len), remaining_len);
            // Exception Safety:
            //
            // `self.len` is set before calling `drop_in_place` so if an
            // element's Drop impl panics, the vector's Drop impl will not
            // double-free.
            self.len = len;
            ptr::drop_in_place(slice);
        }
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the given `Vector<T>`. After calling `reserve`, capacity will be
    /// greater than or equal to `self.len() + additional`. Does nothing if
    /// capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity exceeds [`isize::MAX`] bytes.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut vec = vector![1];
    /// vec.reserve(10);
    /// assert!(vec.capacity() >= 11);
    /// ```
    ///
    /// ```
    /// use dsa::collections::Vector;
    ///
    /// let mut vec = Vector::with_capacity(10);
    /// assert!(vec.capacity() == 10);
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// vec.reserve(5);
    ///
    /// assert!(vec.capacity() == 10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.buf.reserve(self.len, additional);
    }

    /// Clears the vector, dropping all values.
    ///
    /// # Note
    ///
    /// This method has no effect on the allocated capacity of the vector.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*len*) time. All items must be dropped. In the worst case, all
    /// remaining items must invoke their destructors when `T: Drop`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::vector;
    /// use dsa::collections::Vector;
    ///
    /// let mut v = vector![1, 2, 3];
    ///
    /// v.clear();
    ///
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    pub fn clear(&mut self) {
        let elems: *mut [T] = &mut self[..];

        unsafe {
            // Exception Safety:
            //
            // `self.len` is set before calling `drop_in_place` so if an
            // element's Drop impl panics, the vector's Drop impl will not
            // double-free.
            self.len = 0;
            ptr::drop_in_place(elems);
        }
    }

    /// Returns a raw pointer to the vector's buffer, or a dangling raw pointer
    /// valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modifying the vector
    /// may cause its buffer to be reallocated, which would also make any
    /// pointers to it invalid.
    #[inline]
    pub const fn as_ptr(&self) -> *const T {
        self.buf.ptr.as_ptr()
    }

    /// Returns a raw mutable pointer to the vector’s buffer, or a dangling raw
    /// pointer valid for zero sized reads if the vector didn't allocate.
    ///
    /// The caller must ensure that the vector outlives the pointer this
    /// function returns, or else it will end up dangling. Modifying the vector
    /// may cause its buffer to be reallocated, which would also make any
    /// pointers to it invalid.
    #[inline]
    pub const fn as_mut_ptr(&mut self) -> *mut T {
        self.buf.ptr.as_ptr()
    }

    /// Returns the number of elements in the vector.
    #[inline]
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Returns the total number of elements the vector can hold without
    /// reallocating.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.buf.cap
    }

    /// Returns `true` if the vector contains no elements.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Drop for Vector<T> {
    fn drop(&mut self) {
        // Not needed when `T: !Drop`.
        if mem::needs_drop::<T>() {
            unsafe {
                // The mutable slice is treated as a `*mut [T]`, and the
                // destructor for each element of `T` is invoked in place.
                ptr::drop_in_place(&mut self[..]);
            }
        }

        // `RawVector` handles deallocation...
    }
}

impl<T> Default for Vector<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: fmt::Debug> fmt::Debug for Vector<T> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone> Clone for Vector<T> {
    fn clone(&self) -> Self {
        let mut v = Vector::with_capacity(self.len);
        v.extend(self.iter().cloned());
        v
    }
}

impl<T> Extend<T> for Vector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let mut iter = iter.into_iter();

        while let Some(elem) = iter.next() {
            let len = self.len();

            if len == self.capacity() {
                let (lower, _) = iter.size_hint();
                self.reserve(lower.saturating_add(1));
            }

            unsafe {
                ptr::write(self.as_mut_ptr().add(len), elem);
                self.len += 1;
            }
        }
    }
}

impl<T> Deref for Vector<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        unsafe { core::slice::from_raw_parts(self.as_ptr(), self.len) }
    }
}

impl<T> DerefMut for Vector<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { core::slice::from_raw_parts_mut(self.as_mut_ptr(), self.len) }
    }
}

impl<T> FromIterator<T> for Vector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Vector::new();
        v.extend(iter);
        v
    }
}

impl<T> IntoIterator for Vector<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        // Using `ptr::read` to move out of `Vector` without invoking its Drop
        // implementation.
        let buf = unsafe { ptr::read(&self.buf) };
        let len = self.len;

        // Ensures the destructor is not run since `IntoIter` will cleanup
        // unread elements in its Drop impl.
        mem::forget(self);

        IntoIter {
            start: buf.ptr.as_ptr(),
            end: if mem::size_of::<T>() == 0 {
                ((buf.ptr.as_ptr() as usize) + len) as *const _
            } else if len == 0 {
                buf.ptr.as_ptr()
            } else {
                unsafe { buf.ptr.as_ptr().add(len) }
            },
            _buf: buf,
        }
    }
}

// From `https://doc.rust-lang.org/src/alloc/vec/partial_eq.rs.html`
macro_rules! impl_slice_eq {
    ([$($vars:tt)*] $lhs:ty, $rhs:ty) => {
        impl<T, U, $($vars)*> PartialEq<$rhs> for $lhs
        where
            T: PartialEq<U>,
        {
            #[inline]
            fn eq(&self, other: &$rhs) -> bool { self[..] == other[..] }
        }
    }
}

impl_slice_eq! { [] Vector<T>, Vector<U> }
impl_slice_eq! { [] Vector<T>, &[U] }
impl_slice_eq! { [] Vector<T>, &mut [U] }
impl_slice_eq! { [] &[T], Vector<U> }
impl_slice_eq! { [] &mut [T], Vector<U> }
impl_slice_eq! { [] Vector<T>, [U] }
impl_slice_eq! { [] [T], Vector<U> }
impl_slice_eq! { [const N: usize] Vector<T>, [U; N] }
impl_slice_eq! { [const N: usize] Vector<T>, &[U; N] }

impl<T: Eq> Eq for Vector<T> {}

impl<T: PartialOrd> PartialOrd for Vector<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for Vector<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash> Hash for Vector<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);

        for elem in self.iter() {
            elem.hash(state);
        }
    }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    self.start = (self.start as usize + 1) as *const _;
                    Some(ptr::read(NonNull::<T>::dangling().as_ptr()))
                } else {
                    let old_ptr = self.start;
                    self.start = self.start.offset(1);
                    Some(ptr::read(old_ptr))
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
    fn next_back(&mut self) -> Option<T> {
        if self.start == self.end {
            None
        } else {
            unsafe {
                if mem::size_of::<T>() == 0 {
                    self.end = (self.end as usize - 1) as *const _;
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
        // Not needed when `T: !Drop`.
        if mem::needs_drop::<T>() {
            let elem_size = mem::size_of::<T>();

            let len = (self.end as usize - self.start as usize)
                / if elem_size == 0 { 1 } else { elem_size };

            unsafe {
                // The mutable slice is treated as a `*mut [T]`, and the
                // destructor for each element of `T` is invoked in place.
                ptr::drop_in_place(ptr::slice_from_raw_parts_mut(
                    // Casting to a `*mut T` should be fine since the initial
                    // pointer came from a `NonNull`.
                    self.start as *mut T,
                    len,
                ));
            }
        }

        // `RawVector` handles deallocation...
    }
}

/// Low-level utility for more ergonomically allocating, reallocating, and
/// deallocating a buffer of memory on the heap.
#[derive(Debug)]
struct RawVector<T> {
    /// Pointer to the allocation.
    ///
    /// [`NonNull`] is covariant over `T` and is null-pointer optimized.
    ptr: NonNull<T>,
    /// Size of the current allocation.
    cap: usize,
    /// In order to tell the drop checker that we do own values of type T, and
    /// therefore may drop some T's when we drop.
    _marker: marker::PhantomData<T>,
}

impl<T> RawVector<T> {
    #[inline]
    const fn new() -> Self {
        // For ZSTs, capacity is set to `usize::MAX` so the invariant
        // `len <= capacity` is always held, even memory is never allocated.
        let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };

        Self {
            // Leave `ptr` without provenance so the memory is lazily allocated.
            //
            // Initialization is tracked by `cap` instead.
            ptr: NonNull::dangling(),
            cap,
            _marker: marker::PhantomData,
        }
    }

    fn with_capacity(capacity: usize) -> Self {
        let layout = match Layout::array::<T>(capacity) {
            Ok(layout) => layout,
            Err(_) => panic!("capacity overflow"),
        };

        if layout.size() == 0 {
            return Self::new();
        }

        assert!(layout.size() <= isize::MAX as usize, "allocation too large");

        let result = unsafe { alloc::alloc(layout) };

        let ptr = match NonNull::new(result as *mut T) {
            Some(ptr) => ptr,
            // Abort the program if allocation fails.
            None => alloc::handle_alloc_error(layout),
        };

        Self {
            ptr,
            cap: capacity,
            _marker: marker::PhantomData,
        }
    }

    #[inline]
    fn reserve(&mut self, len: usize, additional: usize) {
        if len.saturating_add(additional) > self.cap && mem::size_of::<T>() != 0 {
            self.grow_amortized(len, additional);
        }
    }

    #[inline]
    fn grow_one(&mut self) {
        self.grow_amortized(self.cap, 1);
    }

    /// # Panics
    ///
    /// Panics if the requested capacity exceeds [`isize::MAX`] bytes.
    ///
    /// # Aborts
    ///
    /// Aborts on OOM.
    fn grow_amortized(&mut self, len: usize, additional: usize) {
        let required_cap = len.checked_add(additional).expect("capacity overflow");

        // The doubling cannot overflow because `cap <= isize::MAX` and the
        // type of `cap` is `usize`.
        let new_cap = cmp::max(self.cap * 2, required_cap);

        // `Layout::array` checks that `new_cap <= usize::MAX`, but since the
        // old layout.size() is <= `isize::MAX`, `unwrap` should never panic.
        let new_layout = Layout::array::<T>(new_cap).unwrap();

        assert!(
            new_layout.size() <= isize::MAX as usize,
            "allocation too large"
        );

        let new_ptr = if self.cap == 0 {
            unsafe { alloc::alloc(new_layout) }
        } else {
            let old_layout = Layout::array::<T>(self.cap).unwrap();
            let old_ptr = self.ptr.as_ptr() as *mut u8;
            unsafe { alloc::realloc(old_ptr, old_layout, new_layout.size()) }
        };

        self.ptr = match NonNull::new(new_ptr as *mut T) {
            Some(ptr) => ptr,
            // Abort the program if allocation fails.
            None => alloc::handle_alloc_error(new_layout),
        };

        self.cap = new_cap;
    }
}

impl<T> Drop for RawVector<T> {
    fn drop(&mut self) {
        let elem_size = mem::size_of::<T>();

        if self.cap != 0 && elem_size != 0 {
            let layout = Layout::array::<T>(self.cap).unwrap();
            unsafe {
                // Since `cap` > 0, there is memory allocated.
                alloc::dealloc(self.ptr.as_ptr() as *mut u8, layout);
            }
        }
    }
}

unsafe impl<T: Send> Send for IntoIter<T> {}
unsafe impl<T: Sync> Sync for IntoIter<T> {}

unsafe impl<T: Send> Send for RawVector<T> {}
unsafe impl<T: Sync> Sync for RawVector<T> {}

#[allow(dead_code)]
fn assert_properties() {
    fn is_send<T: Send>() {}
    fn is_sync<T: Sync>() {}

    is_send::<Vector<i32>>();
    is_sync::<Vector<i32>>();

    is_send::<IntoIter<i32>>();
    is_sync::<IntoIter<i32>>();

    fn vector_covariant<'a, T>(x: Vector<&'static T>) -> Vector<&'a T> {
        x
    }
    fn into_iter_covariant<'a, T>(x: IntoIter<&'static T>) -> IntoIter<&'a T> {
        x
    }
}

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
    fn test_macro_empty() {
        let v: Vector<String> = vector![];
        assert!(v.is_empty());
    }

    #[test]
    fn test_macro_single() {
        let v: Vector<u32> = vector![42];

        assert!(!v.is_empty());
        assert_eq!(v.len(), 1);
        assert_eq!(v[0], 42);
    }

    #[test]
    fn test_macro_double() {
        let v: Vector<u32> = vector![42, 43];

        assert!(!v.is_empty());
        assert_eq!(v.len(), 2);
        assert_eq!(v, [42, 43]);
    }

    #[test]
    fn test_macro_trailing() {
        let _: Vector<u32> = vector![42, 43, 44, 45, 46, 47,];
    }

    #[test]
    fn test_macro_clone() {
        let v: Vector<u32> = vector![42; 3];

        assert!(!v.is_empty());
        assert_eq!(v.len(), 3);
        assert_eq!(v, [42, 42, 42]);
    }

    #[test]
    fn test_small_vec() {
        assert_eq!(mem::size_of::<Vector<u8>>(), mem::size_of::<usize>() * 3);
    }

    #[test]
    fn test_double_drop() {
        struct TwoVector<T> {
            x: Vector<T>,
            y: Vector<T>,
        }

        let (mut count_x, mut count_y) = (0, 0);

        {
            let mut tv = TwoVector {
                x: Vector::new(),
                y: Vector::new(),
            };

            tv.x.push(DropCounter {
                count: &mut count_x,
            });

            tv.y.push(DropCounter {
                count: &mut count_y,
            });

            // If `Vector` had a drop flag, here is where it would be zeroed.
            // Instead, it should rely on its internal state to prevent doing
            // anything significant when dropped multiple times.
            drop(tv.x);

            // Here tv goes out of scope, tv.y should be dropped, but not tv.x.
        }

        assert_eq!(count_x, 1);
        assert_eq!(count_y, 1);
    }

    #[test]
    fn test_reserve() {
        let mut v = Vector::new();
        assert_eq!(v.capacity(), 0);

        v.reserve(2);
        assert!(v.capacity() >= 2);

        for i in 0..16 {
            v.push(i);
        }

        assert!(v.capacity() >= 16);
        v.reserve(16);
        assert!(v.capacity() >= 32);

        v.push(16);

        v.reserve(16);
        assert!(v.capacity() >= 33)
    }

    #[test]
    fn test_zst_cap() {
        assert_eq!(Vector::<()>::new().capacity(), usize::MAX);
    }

    #[test]
    fn test_zst_iter() {
        let mut vec = Vector::new();

        vec.push(());
        vec.push(());
        vec.push(());

        assert_eq!(vec.len(), 3);

        let mut iter = vec.into_iter();

        assert_eq!(iter.size_hint(), (3, Some(3)));
        assert_eq!(iter.next(), Some(()));
        assert_eq!(iter.next(), Some(()));
        assert_eq!(iter.next(), Some(()));
    }

    #[test]
    fn test_indexing() {
        let v: Vector<isize> = vector![10, 20];
        assert_eq!(v[0], 10);
        assert_eq!(v[1], 20);

        let mut x: usize = 0;
        assert_eq!(v[x], 10);
        assert_eq!(v[x + 1], 20);

        x = x + 1;
        assert_eq!(v[x], 20);
        assert_eq!(v[x - 1], 10);
    }

    #[test]
    fn test_debug_fmt() {
        let vec1: Vector<isize> = vector![];
        assert_eq!("[]", format!("{:?}", vec1));

        let vec2 = vector![0, 1];
        assert_eq!("[0, 1]", format!("{:?}", vec2));
    }

    #[test]
    fn test_push() {
        let mut v = vector![];
        v.push(1);
        assert_eq!(v, [1]);
        v.push(2);
        assert_eq!(v, [1, 2]);
        v.push(3);
        assert_eq!(v, [1, 2, 3]);
    }

    #[test]
    fn test_extend() {
        let mut v = Vector::new();
        let mut w = Vector::new();

        v.extend(w.clone());
        assert_eq!(v, &[]);

        v.extend(0..3);
        for i in 0..3 {
            w.push(i)
        }

        assert_eq!(v, w);

        v.extend(3..10);
        for i in 3..10 {
            w.push(i)
        }

        assert_eq!(v, w);

        v.extend(w.clone());
        assert!(v.iter().eq(w.iter().chain(w.iter())));

        // ZST
        #[derive(PartialEq, Debug)]
        struct Foo;

        let mut a = Vector::new();
        let b = vector![Foo, Foo];

        a.extend(b);
        assert_eq!(a, &[Foo, Foo]);

        // Double drop
        let mut count_x = 0;
        {
            let mut x = Vector::new();
            let y = vector![DropCounter {
                count: &mut count_x,
            }];
            x.extend(y);
        }
        assert_eq!(count_x, 1);
    }

    #[test]
    fn test_slice_from_ref() {
        let values = vector![1, 2, 3, 4, 5];
        let slice = &values[1..3];

        assert_eq!(slice, [2, 3]);
    }

    #[test]
    fn test_slice_from_mut() {
        let mut values = vector![1, 2, 3, 4, 5];
        {
            let slice = &mut values[2..];
            assert!(slice == [3, 4, 5]);
            for p in slice {
                *p += 2;
            }
        }

        assert!(values == [1, 2, 5, 6, 7]);
    }

    #[test]
    fn test_slice_to_mut() {
        let mut values = vector![1, 2, 3, 4, 5];
        {
            let slice = &mut values[..2];
            assert!(slice == [1, 2]);
            for p in slice {
                *p += 1;
            }
        }

        assert!(values == [2, 3, 3, 4, 5]);
    }

    #[test]
    fn test_clone() {
        let v: Vector<i32> = vector![];
        let w = vector![1, 2, 3];

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);

        // They should be disjoint in memory.
        assert!(w.as_ptr() != z.as_ptr())
    }

    #[test]
    fn test_clone_from() {
        let mut v = vector![];
        let three: Vector<Box<_>> = vector![Box::new(1), Box::new(2), Box::new(3)];
        let two: Vector<Box<_>> = vector![Box::new(4), Box::new(5)];

        v.clone_from(&three);
        assert_eq!(v, three);

        v.clone_from(&three);
        assert_eq!(v, three);

        v.clone_from(&two);
        assert_eq!(v, two);

        v.clone_from(&three);
        assert_eq!(v, three)
    }

    #[test]
    fn test_cmp() {
        let x: &[isize] = &[1, 2, 3, 4, 5];
        let cmp: &[isize] = &[1, 2, 3, 4, 5];
        assert_eq!(&x[..], cmp);
        let cmp: &[isize] = &[3, 4, 5];
        assert_eq!(&x[2..], cmp);
        let cmp: &[isize] = &[1, 2, 3];
        assert_eq!(&x[..3], cmp);
        let cmp: &[isize] = &[2, 3, 4];
        assert_eq!(&x[1..4], cmp);

        let x: Vector<isize> = vector![1, 2, 3, 4, 5];
        let cmp: &[isize] = &[1, 2, 3, 4, 5];
        assert_eq!(&x[..], cmp);
        let cmp: &[isize] = &[3, 4, 5];
        assert_eq!(&x[2..], cmp);
        let cmp: &[isize] = &[1, 2, 3];
        assert_eq!(&x[..3], cmp);
        let cmp: &[isize] = &[2, 3, 4];
        assert_eq!(&x[1..4], cmp);
    }

    #[test]
    #[should_panic]
    fn test_truncate_fail() {
        struct BadElem(i32);

        impl Drop for BadElem {
            fn drop(&mut self) {
                if let BadElem(0xbadbeef) = self {
                    panic!("BadElem panic: 0xbadbeef")
                }
            }
        }

        let mut v = vector![BadElem(1), BadElem(2), BadElem(0xbadbeef), BadElem(4)];
        v.truncate(0);
    }

    #[test]
    fn test_index() {
        let vec = vector![1, 2, 3];
        assert!(vec[1] == 2);
    }

    #[test]
    #[should_panic]
    fn test_index_out_of_bounds() {
        let vec = vector![1, 2, 3];
        let _ = vec[3];
    }

    #[test]
    #[should_panic]
    fn test_slice_out_of_bounds_1() {
        let x = vector![1, 2, 3, 4, 5];
        let _ = &x[!0..];
    }

    #[test]
    fn test_move_items() {
        let vec = vector![1, 2, 3];
        let mut vec2 = vector![];
        for i in vec {
            vec2.push(i);
        }
        assert_eq!(vec2, [1, 2, 3]);
    }

    #[test]
    fn test_move_items_zero_sized() {
        let vec = vector![(), (), ()];
        let mut vec2 = vector![];
        for i in vec {
            vec2.push(i);
        }
        assert_eq!(vec2, [(), (), ()]);
    }
}
