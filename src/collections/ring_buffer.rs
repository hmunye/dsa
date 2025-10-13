use std::mem::MaybeUninit;
use std::{fmt, ptr};

/// A fixed-size, circular queue providing efficient first-in, first-out (FIFO)
/// storage.
///
/// # Time Complexities
///
/// | [push_back] | [pop_front] | [clear] |
/// |-------------|-------------|---------|
/// |   *O*(1)    |   *O*(1)    |  *O*(n) |
///
/// [push_back]: RingBuffer::push_back
/// [pop_front]: RingBuffer::pop_front
/// [clear]:     RingBuffer::clear
#[derive(Debug)]
pub struct RingBuffer<T> {
    /// Fixed-size buffer allocated on the heap, using `MaybeUninit` for
    /// deferred initialization.
    inner: Box<[MaybeUninit<T>]>,
    /// Index of the slot to read from.
    read_idx: usize,
    /// Index of the slot to write into.
    write_idx: usize,
}

/// Error type indicating an operation failed due to a logically full buffer.
pub struct WriteError;

impl std::error::Error for WriteError {}

impl fmt::Debug for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WriteError")
            .field("error", &"buffer is logically full")
            .finish()
    }
}

impl fmt::Display for WriteError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "buffer is logically full")
    }
}

impl<T> RingBuffer<T> {
    /// Creates a new `RingBuffer<T>` with at least the specified capacity.
    ///
    /// This method is allowed to allocate for more items than `capacity` if it
    /// is not a power of two.
    ///
    /// # Panics
    ///
    /// Panics if the provided capacity is `0`.
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        assert!(capacity > 0, "invalid buffer capacity");

        // Round capacity up to the next power of two for fast index wrapping
        // using bit masking.
        let capacity = capacity.next_power_of_two();

        RingBuffer {
            inner: Box::<[T]>::new_uninit_slice(capacity),
            read_idx: 0,
            write_idx: 0,
        }
    }

    /// Writes an item into the buffer, returning a `WriteError` if the buffer
    /// is logically full.
    pub fn push_back(&mut self, item: T) -> Result<(), WriteError> {
        if self.is_full() {
            return Err(WriteError);
        }

        let entry = MaybeUninit::new(item);

        // Dropping a `MaybeUninit<T>` will never call `T`’s drop code, but we
        // can only write to uninitialized or already read from slots.
        self.inner[self.write_idx] = entry;
        self.write_idx = self.compute_next_index(self.write_idx);

        Ok(())
    }

    /// Removes and returns the next item to read, or [`None`] if the buffer
    /// is logically empty.
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            return None;
        }

        unsafe {
            // SAFETY: `self.inner` is backed by a `Box`, ensuring the pointer
            // is well-aligned and valid for reads. There's no double-free risk
            // because `read_idx` won't wraparound to the same index until it
            // has been overwritten. This ensures that `T` will not be dropped
            // twice, once when `out` is returned and dropped, and again when
            // `RingBuffer<T>` is dropped.
            let out = ptr::read(self.inner.as_ptr().add(self.read_idx));
            self.read_idx = self.compute_next_index(self.read_idx);

            // SAFETY: The buffer is not logically empty, so the value at
            // `read_idx` has been initialized and is safe to read.
            Some(out.assume_init())
        }
    }

    /// Returns a shared reference to the next item to read, or [`None`] if the
    /// buffer is logically empty.
    pub fn peek_front(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }

        // SAFETY: The buffer is not logically empty, so the value at `read_idx`
        // has been initialized and is safe to read. Index is not incremented.
        unsafe { Some(&(*self.inner[self.read_idx].as_ptr())) }
    }

    /// Clears the buffer, dropping all initialized items.
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }

    /// Returns the total number of items the buffer can hold.
    #[inline]
    pub const fn capacity(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the buffer is logically empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        // `write_idx` never wraps to equal `read_idx`, so this condition
        // reliably indicates there is no new data available to read.
        self.read_idx == self.write_idx
    }

    /// Returns `true` if the buffer is logically full.
    #[inline]
    pub const fn is_full(&self) -> bool {
        // The next write would overwrite the item at `read_idx`.
        self.compute_next_index(self.write_idx) == self.read_idx
    }

    /// Computes the next index after `idx`, wrapping to stay within the buffer
    /// capacity.
    ///
    /// Assumes the buffer capacity is a power of two.
    #[inline(always)]
    const fn compute_next_index(&self, idx: usize) -> usize {
        (idx + 1) & (self.inner.len() - 1)
    }
}

impl<T> Drop for RingBuffer<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_capacity() {
        let rb: RingBuffer<u32> = RingBuffer::with_capacity(8);
        assert_eq!(rb.capacity(), 8);
        assert!(rb.is_empty());
        assert!(!rb.is_full());
    }

    #[test]
    fn test_queue_basic() {
        let mut rb = RingBuffer::with_capacity(4);

        assert_eq!(rb.pop_front(), None);

        assert!(rb.push_back(String::from("hello")).is_ok());
        assert!(!rb.is_empty());
        assert_eq!(rb.peek_front(), Some(&"hello".to_string()));

        assert_eq!(rb.pop_front(), Some("hello".to_string()));
        assert!(rb.is_empty());
        assert_eq!(rb.peek_front(), None);
    }

    #[test]
    fn test_empty_full() {
        let mut rb = RingBuffer::with_capacity(3);

        assert_eq!(rb.is_empty(), true);
        assert_eq!(rb.is_full(), false);

        assert!(rb.push_back(1).is_ok());
        assert!(rb.push_back(2).is_ok());
        assert!(rb.push_back(3).is_ok());

        assert_eq!(rb.is_full(), true);
        assert_eq!(rb.push_back(4).is_err(), true);

        assert_eq!(rb.peek_front(), Some(&1));
        assert_eq!(rb.pop_front(), Some(1));

        assert_eq!(rb.is_full(), false);
        assert_eq!(rb.is_empty(), false);

        assert!(rb.push_back(4).is_ok());
        assert_eq!(rb.peek_front(), Some(&2));

        assert_eq!(rb.pop_front(), Some(2));
        assert_eq!(rb.pop_front(), Some(3));
        assert_eq!(rb.pop_front(), Some(4));
        assert_eq!(rb.pop_front(), None);

        assert!(rb.is_empty());
    }

    #[test]
    fn test_clear() {
        let mut rb = RingBuffer::with_capacity(8);

        for i in 0..7 {
            assert!(rb.push_back(i).is_ok());
        }

        assert!(rb.is_full());

        rb.clear();

        assert!(rb.is_empty());
        assert_eq!(rb.pop_front(), None);
        assert_eq!(rb.peek_front(), None);
    }

    #[test]
    fn test_order() {
        let mut rb = RingBuffer::with_capacity(5);

        for i in 1..=5 {
            assert!(rb.push_back(i).is_ok());
        }

        for expected in 1..=5 {
            assert_eq!(rb.peek_front(), Some(&expected));
            assert_eq!(rb.pop_front(), Some(expected));
        }

        assert!(rb.is_empty());
    }

    #[test]
    #[should_panic]
    fn test_zero_capacity() {
        let _ = RingBuffer::<u32>::with_capacity(0);
    }
}
