//! Data Structures & Algorithms in Rust.

#![warn(
    missing_debug_implementations,
    missing_docs,
    rust_2018_idioms,
    unreachable_pub
)]
#![deny(unused_must_use)]

pub mod algorithms;
pub mod collections;

pub mod prelude {
    //! Data Structures & Algorithms Prelude.

    pub use super::algorithms;
    pub use super::collections;
}
