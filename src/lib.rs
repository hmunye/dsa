//! Data Structures & Algorithms

#![deny(missing_docs)]
#![warn(missing_debug_implementations)]
#![warn(rust_2018_idioms)]

pub mod algorithms;
pub mod collections;

/// Data Structures & Algorithms Prelude
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::{list, vector};

    #[doc(no_inline)]
    pub use super::collections::doubly_linked_deque::LinkedDeque;
    #[doc(no_inline)]
    pub use super::collections::hash_table::HashTable;
    #[doc(no_inline)]
    pub use super::collections::vector::Vector;

    #[doc(no_inline)]
    pub use super::algorithms::binary_search::*;
    #[doc(no_inline)]
    pub use super::algorithms::linear_search::*;
}
