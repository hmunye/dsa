//! [Hash Table] implementation with open-addressing and quadratic probing.
//!
//! Just use [`HashMap`].
//!
//! [Hash Table]: https://en.wikipedia.org/wiki/Hash_table
//! [`HashMap`]: std::collections::HashMap

use std::fmt;

use core::hash::{BuildHasher, Hash, Hasher};
use core::mem::{self, MaybeUninit};
use core::ops::Index;
use core::ptr;

use crate::collections::prelude::*;

/// Fowler–Noll–Vo (FNV-1a) non-cryptographic hash function
#[derive(Debug, Copy, Clone)]
pub struct FnvHasher {
    hash: u64,
}

impl FnvHasher {
    const FNV_PRIME: u64 = 0x100000001B3;
    const FNV_OFFSET_BASIS: u64 = 0xCBF29CE484222325;

    /// Creates a new [`FnvHasher`], initialized with `FNV_OFFSET_BASIS`.
    pub fn new() -> Self {
        Self {
            hash: FnvHasher::FNV_OFFSET_BASIS,
        }
    }
}

impl Default for FnvHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher for FnvHasher {
    fn finish(&self) -> u64 {
        self.hash
    }

    fn write(&mut self, bytes: &[u8]) {
        for byte in bytes {
            self.hash ^= *byte as u64;
            self.hash = self.hash.wrapping_mul(Self::FNV_PRIME);
        }
    }
}

/// Builder for [`FnvHasher`]
#[derive(Debug, Copy, Clone)]
pub struct FnvBuildHasher {}

impl BuildHasher for FnvBuildHasher {
    type Hasher = FnvHasher;

    fn build_hasher(&self) -> Self::Hasher {
        Self::Hasher::new()
    }
}

/// [Hash Table] implementation with open-addressing and quadratic probing.
///
/// Just use [`HashMap`].
///
/// [Hash Table]: https://en.wikipedia.org/wiki/Hash_table
/// [`HashMap`]: std::collections::HashMap
pub struct HashTable<K: Eq + Hash, V, H = FnvBuildHasher> {
    /// Buffer to store key/value pairs and control bytes.
    ///
    /// ```text
    /// bucket[n], ..., bucket[1], bucket[0], ctrl[0], ctrl[1], ... [padding]
    /// ```
    buffer: Vector<MaybeUninit<(K, V)>>,
    /// Mask to get an index from a hash value. The value is one less than the
    /// number of buckets in the table.
    bucket_mask: usize,
    /// Number of elements that can be inserted before we need to resize.
    growth_left: usize,
    /// Number of elements in the table.
    entries: usize,
    /// Builds the hasher for per-key hashing.
    build_hasher: H,
}

/// An iterator that references a `HashTable<K, V>`.
#[derive(Debug)]
pub struct Iter<'a, K: Eq + Hash, V> {
    buckets: &'a [MaybeUninit<(K, V)>],
    ctrls: &'a [u8],
    idx: usize,
}

impl<K: Eq + Hash, V> HashTable<K, V, FnvBuildHasher> {
    /// Creates an empty `HashTable<K, V>`.
    ///
    /// The hash table is initially created with a capacity of 0, so it will not
    /// allocate until it is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table: HashTable<&str, i32> = HashTable::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Default::default()
    }

    /// Creates an empty `HashTable` with at least the specified capacity.
    ///
    /// The hash table will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the hash table will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table: HashTable<&str, i32> = HashTable::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, FnvBuildHasher {})
    }
}

impl<K: Eq + Hash, V, H: BuildHasher + Clone> HashTable<K, V, H> {
    /// Control byte representing an empty bucket.
    const CTRL_EMPTY: u8 = 0b10000000;

    /// Control byte representing a deleted bucket (tombstone).
    const CTRL_TOMBSTONE: u8 = 0b11111110;

    /// Creates an empty `HashTable` which will use the given hash builder to
    /// hash keys.
    ///
    /// The created table has the default initial capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    /// use std::hash::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut table = HashTable::with_hasher(s);
    /// table.insert(1, 2);
    /// ```
    #[inline]
    pub fn with_hasher(build_hasher: H) -> Self {
        Self::with_capacity_and_hasher(0, build_hasher)
    }

    /// Creates an empty `HashTable` with at least the specified capacity, using
    /// `hasher` to hash the keys.
    ///
    /// The hash table will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is zero, the hash table will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    /// use std::hash::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut table = HashTable::with_capacity_and_hasher(10, s);
    /// table.insert(1, 2);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, build_hasher: H) -> Self {
        if capacity == 0 {
            return Self {
                buffer: vector![], // Vector lazily allocates.
                bucket_mask: 0,
                growth_left: 0,
                entries: 0,
                build_hasher,
            };
        }

        // The load factor defines the threshold at which the table resizes to
        // avoid excessive collisions and probing sequence clustering.
        //
        // Supports `capacity` insertions without exceeding a load factor of
        // 87.5%. Also ensures there is at least one empty bucket so probing
        // can terminate.
        let adjusted_cap = (capacity << 3).div_ceil(7);

        // Allows for faster indexing with bitmasking.
        let buckets = adjusted_cap.next_power_of_two();

        // Need enough bucket-sized bytes to fit "buckets" control bytes .
        let ctrl = buckets.div_ceil(mem::size_of::<MaybeUninit<(K, V)>>());

        // Ensure it is aligned to `MaybeUninit<(K, V)>`.
        let mut buffer: Vector<MaybeUninit<(K, V)>> = Vector::with_capacity(buckets + ctrl);

        // Set all control bytes to initially `CTRL_EMPTY`.
        let offset = buckets * mem::size_of::<MaybeUninit<(K, V)>>();
        // SAFETY: just initialized the buffer.
        unsafe {
            let ptr = buffer.as_mut_ptr() as *mut u8;
            ptr::write_bytes(
                ptr.with_addr(ptr as usize + offset),
                Self::CTRL_EMPTY,
                buckets,
            )
        }

        Self {
            buffer,
            bucket_mask: buckets - 1,
            growth_left: (buckets * 7) / 8,
            entries: 0,
            build_hasher,
        }
    }

    /// Inserts a key-value pair into the table.
    ///
    /// If the table did not have this key present, [`None`] is returned.
    ///
    /// If the table did have this key present, the value is updated, and the
    /// old value is returned, but the key is not updated.
    ///
    /// # Time Complexity
    ///
    /// Takes amortized *O*(1) time. If the insert would exceed the table's load
    /// factor, *O*(*capacity*) time is taken to rehash and insert the table
    /// buckets to a larger allocation. This expensive operation is offset by
    /// the *O*(1) insertions it allows before reaching the load factor
    /// threshold.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// assert_eq!(table.insert(37, "a"), None);
    /// assert_eq!(table.is_empty(), false);
    ///
    /// table.insert(37, "b");
    /// assert_eq!(table.insert(37, "c"), Some("b"));
    /// ```
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        // Table resize needed.
        if self.growth_left == 0 {
            self.resize();
        }

        let mask = self.bucket_mask;
        let hash = self.hash_key(&key);

        // Lower 7-bits will be stored in the control byte of the matching
        // index.
        let (h1, h2) = (hash >> 7, hash & 0x7F);

        let mut probe = h1 as usize & mask;
        let mut step = 0;

        for i in 0..=mask {
            // Use triangular number increments to avoid cycles in the probe
            // sequence. Basic quadratic probing with a power-of-two capacity
            // can lead to short, repeating cycles. This approach prevents that
            // by ensuring better spread.
            step += i;
            probe = (probe + step) & mask;

            // SAFETY: table should already be initialized or resized before
            // getting here.
            let ctrl = unsafe { self.ctrl_slice()[probe] };

            // Either `EMPTY` or `TOMBSTONE`.
            if ctrl & Self::CTRL_EMPTY != 0 {
                // SAFETY: table should already be initialized or resized before
                // getting here.
                unsafe {
                    let _ = self.bucket_slice_mut()[probe].write((key, value));
                    // Set the `h2` of the current control byte.
                    self.ctrl_slice_mut()[probe] = h2 as u8;

                    self.growth_left -= 1;
                    self.entries += 1;

                    break;
                }
            // FULL - Check `h2` before loading the bucket.
            } else if ctrl == h2 as u8 {
                // SAFETY: table should already be initialized or resized before
                // getting here.
                let bucket = unsafe { self.bucket_slice_mut()[probe].assume_init_mut() };

                if bucket.0 == key {
                    // Replace the previous value and return it
                    return Some(mem::replace(&mut bucket.1, value));
                } else {
                    // Unlikely but continue probing.
                    continue;
                }
            } else {
                continue;
            }
        }

        None
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// # Time Complexity
    ///
    /// Takes average *O*(1) time. Worst case is *O*(*capacity*) if the hashing
    /// function is not well-distributed or results in clustering.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// table.insert(1, "a");
    /// assert_eq!(table.get(&1), Some(&"a"));
    /// assert_eq!(table.get(&2), None);
    /// ```
    pub fn get(&self, key: &K) -> Option<&V> {
        if self.capacity() == 0 {
            return None;
        }

        let mask = self.bucket_mask;
        let hash = self.hash_key(key);

        // Lower 7-bits will be stored in the control byte of the matching
        // index.
        let (h1, h2) = (hash >> 7, hash & 0x7F);

        let mut probe = h1 as usize & mask;
        let mut step = 0;

        for i in 0..=mask {
            // Use triangular number increments to avoid cycles in the probe
            // sequence. Basic quadratic probing with a power-of-two capacity
            // can lead to short, repeating cycles. This approach prevents that
            // by ensuring better spread.
            step += i;
            probe = (probe + step) & mask;

            // SAFETY: capacity is already checked to be non-zero, meaning an
            // allocation was made.
            let ctrl = unsafe { self.ctrl_slice()[probe] };

            // EMPTY - key not found.
            if ctrl == Self::CTRL_EMPTY {
                break;
            }

            // TOMBSTONE - mark last index of tombstone and continue.
            if ctrl == Self::CTRL_TOMBSTONE {
                continue;
            }

            // FULL - Check `h2` before loading the bucket.
            if ctrl & Self::CTRL_EMPTY == 0 && ctrl == h2 as u8 {
                // SAFETY: capacity is already checked to be non-zero, meaning
                // an allocation was made.
                let bucket = unsafe { self.bucket_slice()[probe].assume_init_ref() };

                if bucket.0 == *key {
                    return Some(&bucket.1);
                } else {
                    // Unlikely but continue probing.
                    continue;
                }
            }
        }

        None
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// # Time Complexity
    ///
    /// Takes average *O*(1) time. Worst case is *O*(*capacity*) if the hashing
    /// function is not well-distributed or results in clustering.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// table.insert(1, "a");
    /// if let Some(x) = table.get_mut(&1) {
    ///     *x = "b";
    /// }
    /// assert_eq!(table[&1], "b");
    /// ```
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if self.capacity() == 0 {
            return None;
        }

        let mask = self.bucket_mask;
        let hash = self.hash_key(key);

        // Lower 7-bits will be stored in the control byte of the matching
        // index.
        let (h1, h2) = (hash >> 7, hash & 0x7F);

        let mut probe = h1 as usize & mask;
        let mut step = 0;

        for i in 0..=mask {
            // Use triangular number increments to avoid cycles in the probe
            // sequence. Basic quadratic probing with a power-of-two capacity
            // can lead to short, repeating cycles. This approach prevents that
            // by ensuring better spread.
            step += i;
            probe = (probe + step) & mask;

            // SAFETY: capacity is already checked to be non-zero, meaning an
            // allocation was made.
            let ctrl = unsafe { self.ctrl_slice()[probe] };

            // EMPTY - key not found.
            if ctrl == Self::CTRL_EMPTY {
                break;
            } else if ctrl == Self::CTRL_TOMBSTONE {
                // TOMBSTONE - mark last index of tombstone and continue.
                continue;
            } else {
                // FULL - Check `h2` before loading the bucket.
                if ctrl & Self::CTRL_EMPTY == 0 && ctrl == h2 as u8 {
                    unsafe {
                        // SAFETY: capacity is already checked to be non-zero,
                        // meaning an allocation was made.
                        let bucket = self.bucket_slice_mut()[probe].as_mut_ptr();

                        if (*bucket).0 == *key {
                            return Some(&mut (*bucket).1);
                        } else {
                            // Unlikely but continue probing.
                            continue;
                        }
                    }
                }
            }
        }

        None
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// # Time Complexity
    ///
    /// Takes average *O*(1) time. Worst case is *O*(*capacity*) if the hashing
    /// function is not well-distributed or results in clustering.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::hash::{Hash, Hasher};
    ///
    /// use dsa::collections::prelude::*;
    ///
    /// #[derive(Clone, Copy, Debug)]
    /// struct S {
    ///     id: u32,
    /// #   #[allow(unused)] // prevents a "field `name` is never read" error
    ///     name: &'static str, // ignored by equality and hashing operations
    /// }
    ///
    /// impl PartialEq for S {
    ///     fn eq(&self, other: &S) -> bool {
    ///         self.id == other.id
    ///     }
    /// }
    ///
    /// impl Eq for S {}
    ///
    /// impl Hash for S {
    ///     fn hash<H: Hasher>(&self, state: &mut H) {
    ///         self.id.hash(state);
    ///     }
    /// }
    ///
    /// let j_a = S { id: 1, name: "Jessica" };
    /// let j_b = S { id: 1, name: "Jess" };
    /// let p = S { id: 2, name: "Paul" };
    /// assert_eq!(j_a, j_b);
    ///
    /// let mut table = HashTable::new();
    /// table.insert(j_a, "Paris");
    /// assert_eq!(table.get_key_value(&j_a), Some((&j_a, &"Paris")));
    /// assert_eq!(table.get_key_value(&j_b), Some((&j_a, &"Paris"))); // the notable case
    /// assert_eq!(table.get_key_value(&p), None);
    /// ```
    pub fn get_key_value(&self, key: &K) -> Option<(&K, &V)> {
        if self.capacity() == 0 {
            return None;
        }

        let mask = self.bucket_mask;
        let hash = self.hash_key(key);

        // Lower 7-bits will be stored in the control byte of the matching
        // index.
        let (h1, h2) = (hash >> 7, hash & 0x7F);

        let mut probe = h1 as usize & mask;
        let mut step = 0;

        for i in 0..=mask {
            // Use triangular number increments to avoid cycles in the probe
            // sequence. Basic quadratic probing with a power-of-two capacity
            // can lead to short, repeating cycles. This approach prevents that
            // by ensuring better spread.
            step += i;
            probe = (probe + step) & mask;

            // SAFETY: capacity is already checked to be non-zero, meaning an
            // allocation was made.
            let ctrl = unsafe { self.ctrl_slice()[probe] };

            // EMPTY - key not found.
            if ctrl == Self::CTRL_EMPTY {
                break;
            }

            // TOMBSTONE - mark last index of tombstone and continue.
            if ctrl == Self::CTRL_TOMBSTONE {
                continue;
            }

            // FULL - Check `h2` before loading the bucket.
            if ctrl & Self::CTRL_EMPTY == 0 && ctrl == h2 as u8 {
                // SAFETY: capacity is already checked to be non-zero, meaning
                // an allocation was made.
                let bucket = unsafe { self.bucket_slice()[probe].assume_init_ref() };

                if bucket.0 == *key {
                    return Some((&bucket.0, &bucket.1));
                } else {
                    // Unlikely but continue probing.
                    continue;
                }
            }
        }

        None
    }

    /// Removes a key from the table, returning the value at the key if the key
    /// was previously in the table.
    ///
    /// # Time Complexity
    ///
    /// Takes average *O*(1) time. Worst case is *O*(*capacity*) if the hashing
    /// function is not well-distributed or results in clustering.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// table.insert(1, "a");
    /// assert_eq!(table.remove(&1), Some("a"));
    /// assert_eq!(table.remove(&1), None);
    /// ```
    pub fn remove(&mut self, key: &K) -> Option<V> {
        if self.capacity() == 0 {
            return None;
        }

        let mask = self.bucket_mask;
        let hash = self.hash_key(key);

        // Lower 7-bits will be stored in the control byte of the matching
        // index.
        let (h1, h2) = (hash >> 7, hash & 0x7F);

        let mut probe = h1 as usize & mask;
        let mut step = 0;

        for i in 0..=mask {
            // Use triangular number increments to avoid cycles in the probe
            // sequence. Basic quadratic probing with a power-of-two capacity
            // can lead to short, repeating cycles. This approach prevents that
            // by ensuring better spread.
            step += i;
            probe = (probe + step) & mask;

            // SAFETY: capacity is already checked to be non-zero, meaning an
            // allocation was made.
            let ctrl = unsafe { self.ctrl_slice()[probe] };

            // EMPTY - key not found.
            if ctrl == Self::CTRL_EMPTY {
                break;
            }

            // TOMBSTONE - mark last index of tombstone and continue.
            if ctrl == Self::CTRL_TOMBSTONE {
                continue;
            }

            // FULL - Check `h2` before loading the bucket.
            if ctrl & Self::CTRL_EMPTY == 0 && ctrl == h2 as u8 {
                // SAFETY: capacity is already checked to be non-zero, meaning
                // an allocation was made.
                unsafe {
                    let bucket_key = &self.bucket_slice()[probe].assume_init_ref().0;

                    if *bucket_key == *key {
                        let kv = mem::replace(
                            &mut self.bucket_slice_mut()[probe],
                            MaybeUninit::uninit(),
                        );
                        let (mut key, value) = kv.assume_init();

                        // Ensure the key is dropped.
                        ptr::drop_in_place(&raw mut key);

                        // Mark bucket as a `TOMBSTONE`.
                        self.ctrl_slice_mut()[probe] = Self::CTRL_TOMBSTONE;

                        self.entries -= 1;

                        return Some(value);
                    } else {
                        // Unlikely but continue probing.
                        continue;
                    }
                }
            }
        }

        None
    }

    /// Returns an iterator referencing the hash table.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let table: HashTable<i32, &str> = HashTable::new();
    ///
    /// let mut iter = table.iter();
    ///
    /// assert_eq!(iter.next(), None);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, K, V> {
        // SAFETY: capacity is checked to be non-zero, meaning an allocation
        // was made.
        unsafe {
            Iter {
                buckets: if self.capacity() == 0 {
                    &[]
                } else {
                    self.bucket_slice()
                },
                ctrls: if self.capacity() == 0 {
                    &[]
                } else {
                    self.ctrl_slice()
                },
                idx: 0,
            }
        }
    }

    /// Returns `true` if the table contains a value for the specified key.
    ///
    /// # Time Complexity
    ///
    /// Takes average *O*(1) time. Worst case is *O*(*capacity*) if the hashing
    /// function is not well-distributed or results in clustering.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// table.insert(1, "a");
    /// assert_eq!(table.contains_key(&1), true);
    /// assert_eq!(table.contains_key(&2), false);
    /// ```
    #[inline]
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// Clears the table, removing all key-value pairs. Keeps the allocated
    /// memory for reuse.
    ///
    /// # Time Complexity
    ///
    /// Takes *O*(*len*) time. All items must be dropped. In the worst case, all
    /// remaining items must invoke their destructors when `T: Drop`.
    ///
    /// # Examples
    ///
    /// ```
    /// use dsa::collections::prelude::*;
    ///
    /// let mut table = HashTable::new();
    /// table.insert(1, "a");
    /// table.clear();
    /// assert!(table.is_empty());
    /// ```
    pub fn clear(&mut self) {
        if self.capacity() == 0 {
            return;
        }

        // Need to recompute the number of elements that can be inserted before
        // resize.
        self.growth_left = (self.buckets() * 7) / 8;
        self.entries = 0;

        self.buffer.clear();

        // SAFETY: capacity is already checked to be non-zero, meaning an
        // allocation was made.
        //
        // Set all control bytes to initially `CTRL_EMPTY`.
        unsafe {
            self.ctrl_slice_mut().fill(Self::CTRL_EMPTY);
        }
    }

    /// Returns the number of elements the table can hold without reallocating.
    ///
    /// This number is a lower bound; the table might be able to hold more, but
    /// is guaranteed to be able to hold at least this many.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.entries + self.growth_left
    }

    /// Returns the number of elements in the table.
    #[inline]
    pub fn len(&self) -> usize {
        self.entries
    }

    /// Returns `true` if the table contains no elements.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.entries == 0
    }

    /// Returns the number of buckets in the table.
    #[inline]
    fn buckets(&self) -> usize {
        self.bucket_mask + 1
    }

    /// Returns the hash value of the provided key.
    #[inline]
    fn hash_key(&self, key: &K) -> u64 {
        self.build_hasher.hash_one(key)
    }

    /// Returns an immutable slice of control bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the table has been properly initialized
    /// before calling this function. Invoking this function immediately after
    /// initializing a table with a capacity of 0 is `UB`.
    #[inline]
    unsafe fn ctrl_slice(&self) -> &[u8] {
        let offset = self.buckets() * mem::size_of::<MaybeUninit<(K, V)>>();
        let ptr = self.buffer.as_ptr() as *mut u8;

        unsafe { core::slice::from_raw_parts(ptr.with_addr(ptr as usize + offset), self.buckets()) }
    }

    /// Returns a mutable slice of control bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the table has been properly initialized
    /// before calling this function. Invoking this function immediately after
    /// initializing a table with a capacity of 0 is `UB`.
    #[inline]
    unsafe fn ctrl_slice_mut(&mut self) -> &mut [u8] {
        let offset = self.buckets() * mem::size_of::<MaybeUninit<(K, V)>>();
        let ptr = self.buffer.as_mut_ptr() as *mut u8;

        unsafe {
            core::slice::from_raw_parts_mut(ptr.with_addr(ptr as usize + offset), self.buckets())
        }
    }

    /// Returns an immutable slice of bucket key/value pairs.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the table has been properly initialized
    /// before calling this function. Invoking this function immediately after
    /// initializing a table with a capacity of 0 is `UB`.
    #[inline]
    unsafe fn bucket_slice(&self) -> &[MaybeUninit<(K, V)>] {
        unsafe { core::slice::from_raw_parts(self.buffer.as_ptr(), self.buckets()) }
    }

    /// Returns a mutable slice of bucket key/value pairs.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the table has been properly initialized
    /// before calling this function. Invoking this function immediately after
    /// initializing a table with a capacity of 0 is `UB`.
    #[inline]
    unsafe fn bucket_slice_mut(&mut self) -> &mut [MaybeUninit<(K, V)>] {
        unsafe { core::slice::from_raw_parts_mut(self.buffer.as_mut_ptr(), self.buckets()) }
    }

    /// Resizes the hash table by doubling its capacity and rehashing all
    /// occupied buckets.
    fn resize(&mut self) {
        let old_buckets = self.buckets();
        let align = mem::align_of::<MaybeUninit<(K, V)>>();

        let mut table =
            Self::with_capacity_and_hasher(align.max(old_buckets) * 2, self.build_hasher.clone());

        // The previous table had no entries.
        if self.capacity() != 0 {
            // Re-insert all previous buckets into the new table.
            for i in 0..old_buckets {
                // SAFETY: capacity is already checked to be non-zero, meaning
                // an allocation was made.
                unsafe {
                    let ctrl = self.ctrl_slice()[i];

                    // MSB == 0 -> FULL
                    if ctrl & Self::CTRL_EMPTY == 0 {
                        // Need to get ownership of the `MaybeUninit<_>` so I can
                        // successfully extract the key/value.
                        //
                        // Reading from the bucket would just cause a copy instead
                        // of move.
                        let kv =
                            mem::replace(&mut self.bucket_slice_mut()[i], MaybeUninit::uninit());
                        let (key, value) = kv.assume_init();
                        table.insert(key, value);
                    }
                }
            }
        }

        // Swap the existing hash table with the initialized one.
        mem::swap(self, &mut table);

        // `Vector` handles it's deallocation...
    }
}

impl<K: Eq + Hash, V> Default for HashTable<K, V, FnvBuildHasher> {
    fn default() -> Self {
        Self::with_hasher(FnvBuildHasher {})
    }
}

impl<K, V> Clone for HashTable<K, V, FnvBuildHasher>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    #[inline]
    fn clone(&self) -> Self {
        let mut ht = HashTable::with_capacity(self.capacity());
        self.iter().for_each(|(k, v)| {
            ht.insert(k.clone(), v.clone());
        });
        ht
    }
}

impl<K, V, H> fmt::Debug for HashTable<K, V, H>
where
    K: fmt::Debug + Eq + Hash,
    V: fmt::Debug,
    H: BuildHasher + Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'a, K, V, H> IntoIterator for &'a HashTable<K, V, H>
where
    K: Eq + Hash,
    H: BuildHasher + Clone,
{
    type IntoIter = Iter<'a, K, V>;
    type Item = (&'a K, &'a V);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, K, V> Iterator for Iter<'a, K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        while self.idx < self.buckets.len() {
            let i = self.idx;
            self.idx += 1;

            let ctrl = self.ctrls[i];

            // MSB == 0 -> FULL
            if ctrl & 0x80 == 0 {
                let bucket = unsafe { self.buckets[i].assume_init_ref() };
                return Some((&bucket.0, &bucket.1));
            }
        }

        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.buckets.len().div_ceil(self.idx);
        (size, Some(size))
    }
}

impl<K, V, H> Index<&K> for HashTable<K, V, H>
where
    K: Eq + Hash,
    H: BuildHasher + Clone,
{
    type Output = V;

    /// Returns a reference to the value corresponding to the supplied key.
    ///
    /// # Panics
    ///
    /// Panics if the key is not present in the `HashTable`.
    #[inline]
    fn index(&self, key: &K) -> &V {
        self.get(key).expect("no entry found for key")
    }
}

// https://github.com/rust-lang/rust/blob/master/library/std/src/collections/hash/map/tests.rs
#[cfg(test)]
mod tests {
    use std::hash::RandomState;

    use crate::collections::prelude::*;

    #[test]
    fn test_zero_capacities() {
        let m: HashTable<i32, i32> = HashTable::new();
        assert_eq!(m.capacity(), 0);

        let m: HashTable<i32, i32> = HashTable::default();
        assert_eq!(m.capacity(), 0);

        let m: HashTable<i32, i32, RandomState> = HashTable::with_hasher(RandomState::new());
        assert_eq!(m.capacity(), 0);

        let m: HashTable<i32, i32> = HashTable::with_capacity(0);
        assert_eq!(m.capacity(), 0);

        let m: HashTable<i32, i32, RandomState> =
            HashTable::with_capacity_and_hasher(0, RandomState::new());
        assert_eq!(m.capacity(), 0);

        let mut m: HashTable<i32, i32> = HashTable::new();
        m.insert(1, 1);
        m.insert(2, 2);
        m.remove(&1);
        m.remove(&2);
        // Capacity stay larger than `size_of::<(K, V)>`.
        assert!(m.capacity() >= 8);
    }

    #[test]
    fn test_create_capacity_zero() {
        let mut m = HashTable::with_capacity(0);

        assert!(m.insert(1, 1).is_none());

        assert!(m.contains_key(&1));
        assert!(!m.contains_key(&0));
    }

    #[test]
    fn test_insert() {
        let mut m = HashTable::new();

        assert_eq!(m.len(), 0);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert(2, 4).is_none());
        assert_eq!(m.len(), 2);
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&2).unwrap(), 4);
    }

    #[test]
    fn test_clone() {
        let mut m = HashTable::new();

        assert_eq!(m.len(), 0);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert(2, 4).is_none());
        assert_eq!(m.len(), 2);
        let m2 = m.clone();
        assert_eq!(*m2.get(&1).unwrap(), 2);
        assert_eq!(*m2.get(&2).unwrap(), 4);
        assert_eq!(m2.len(), 2);
    }

    #[test]
    fn test_empty_remove() {
        let mut m: HashTable<i32, bool> = HashTable::new();
        assert_eq!(m.remove(&0), None);
    }

    #[test]
    fn test_empty_iter() {
        let m: HashTable<i32, bool> = HashTable::new();

        assert_eq!(m.iter().next(), None);
        assert_eq!(m.len(), 0);
        assert!(m.is_empty());
    }

    #[test]
    fn test_insertions() {
        let mut m = HashTable::new();

        let loops = if cfg!(miri) { 2 } else { 10 };
        for _ in 0..loops {
            assert!(m.is_empty());

            let count = if cfg!(miri) { 66 } else { 1001 };

            for i in 1..count {
                assert!(m.insert(i, i).is_none());

                for j in 1..=i {
                    let r = m.get(&j);
                    assert_eq!(r, Some(&j));
                }

                for j in i + 1..count {
                    let r = m.get(&j);
                    assert_eq!(r, None);
                }
            }

            for i in count..(2 * count) {
                assert!(!m.contains_key(&i));
            }

            // remove forwards
            for i in 1..count {
                assert!(m.remove(&i).is_some());

                for j in 1..=i {
                    assert!(!m.contains_key(&j));
                }

                for j in i + 1..count {
                    assert!(m.contains_key(&j));
                }
            }

            for i in 1..count {
                assert!(!m.contains_key(&i));
            }

            for i in 1..count {
                assert!(m.insert(i, i).is_none());
            }

            // remove backwards
            for i in (1..count).rev() {
                assert!(m.remove(&i).is_some());

                for j in i..count {
                    assert!(!m.contains_key(&j));
                }

                for j in 1..i {
                    assert!(m.contains_key(&j));
                }
            }
        }
    }

    #[test]
    fn test_find_mut() {
        let mut m = HashTable::new();

        assert!(m.insert(1, 12).is_none());
        assert!(m.insert(2, 8).is_none());
        assert!(m.insert(5, 14).is_none());
        let new = 100;
        match m.get_mut(&5) {
            None => panic!(),
            Some(x) => *x = new,
        }
        assert_eq!(m.get(&5), Some(&new));
    }

    #[test]
    fn test_insert_overwrite() {
        let mut m = HashTable::new();
        assert!(m.insert(1, 2).is_none());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert!(!m.insert(1, 3).is_none());
        assert_eq!(*m.get(&1).unwrap(), 3);
    }

    #[test]
    fn test_insert_conflicts() {
        let mut m = HashTable::with_capacity(4);
        assert!(m.insert(1, 2).is_none());
        assert!(m.insert(5, 3).is_none());
        assert!(m.insert(9, 4).is_none());
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert_eq!(*m.get(&1).unwrap(), 2);
    }

    #[test]
    fn test_conflict_remove() {
        let mut m = HashTable::with_capacity(4);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert!(m.insert(5, 3).is_none());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert!(m.insert(9, 4).is_none());
        assert_eq!(*m.get(&1).unwrap(), 2);
        assert_eq!(*m.get(&5).unwrap(), 3);
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert!(m.remove(&1).is_some());
        assert_eq!(*m.get(&9).unwrap(), 4);
        assert_eq!(*m.get(&5).unwrap(), 3);
    }

    #[test]
    fn test_is_empty() {
        let mut m = HashTable::with_capacity(4);
        assert!(m.insert(1, 2).is_none());
        assert!(!m.is_empty());
        assert!(m.remove(&1).is_some());
        assert!(m.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut m = HashTable::new();
        m.insert(1, 2);
        assert_eq!(m.remove(&1), Some(2));
        assert_eq!(m.remove(&1), None);
    }

    #[test]
    fn test_iterate() {
        let mut m = HashTable::with_capacity(4);
        for i in 0..32 {
            assert!(m.insert(i, i * 2).is_none());
        }
        assert_eq!(m.len(), 32);

        let mut observed: u32 = 0;

        for (k, v) in m.iter() {
            assert_eq!(*v, *k * 2);
            observed |= 1 << *k;
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_find() {
        let mut m = HashTable::new();
        assert!(m.get(&1).is_none());
        m.insert(1, 2);
        match m.get(&1) {
            None => panic!(),
            Some(v) => assert_eq!(*v, 2),
        }
    }

    #[test]
    fn test_debug_print() {
        let mut table = HashTable::new();
        let empty: HashTable<i32, i32> = HashTable::new();

        table.insert(1, 2);
        table.insert(3, 4);

        let table_str = format!("{table:?}");

        assert!(table_str == "{1: 2, 3: 4}" || table_str == "{3: 4, 1: 2}");
        assert_eq!(format!("{empty:?}"), "{}");
    }

    #[test]
    fn test_size_hint() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];
        let mut table = HashTable::new();

        for (k, v) in xs.iter() {
            table.insert(k, v);
        }

        let mut iter = table.iter();

        for _ in iter.by_ref().take(3) {}

        assert_eq!(iter.size_hint(), (3, Some(3)));
    }

    #[test]
    fn test_index() {
        let mut table = HashTable::new();

        table.insert(1, 2);
        table.insert(2, 1);
        table.insert(3, 4);

        assert_eq!(table[&2], 1);
    }

    #[test]
    #[should_panic]
    fn test_index_nonexistent() {
        let mut table = HashTable::new();

        table.insert(1, 2);
        table.insert(2, 1);
        table.insert(3, 4);

        table[&4];
    }

    #[test]
    fn test_capacity_not_less_than_len() {
        let mut a = HashTable::new();
        let mut item = 0;

        for _ in 0..116 {
            a.insert(item, 0);
            item += 1;
        }

        assert!(a.capacity() > a.len());

        let free = a.capacity() - a.len();
        for _ in 0..free {
            a.insert(item, 0);
            item += 1;
        }

        assert_eq!(a.len(), a.capacity());

        // Insert at capacity should cause allocation.
        a.insert(item, 0);
        assert!(a.capacity() > a.len());
    }
}
