//! Collection Types.

pub mod doubly_linked_deque;
pub mod hash_table;
pub mod vector;

/// Data Structures & Algorithms Prelude
pub mod prelude {
    #[doc(no_inline)]
    pub use crate::{list, vector};

    #[doc(no_inline)]
    pub use super::doubly_linked_deque::LinkedDeque;
    #[doc(no_inline)]
    pub use super::hash_table::HashTable;
    #[doc(no_inline)]
    pub use super::vector::Vector;
}
