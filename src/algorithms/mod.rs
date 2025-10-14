//! Implementations of Algorithms.

mod extended_gcd;
mod gcd;
pub use extended_gcd::extended_gcd;
pub use gcd::gcd;

mod binary_power;
pub use binary_power::binary_power;

mod modular_inverse;
pub use modular_inverse::modular_inverse;

mod binary_search;
pub use binary_search::binary_search;
