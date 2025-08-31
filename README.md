# dsa

Data Structures & Algorithms in Rust

## Quick Start

To include the crate in your project as a dependency:

```bash
cargo add --git https://github.com/hmunye/dsa.git
```

## Testing

Using [`Miri`](https://github.com/rust-lang/miri): 

```bash
rustup +nightly component add miri
```

```bash
MIRIFLAGS="-Zmiri-permissive-provenance" cargo +nightly miri t
```
> `Vector` uses integer-to-pointer casts to handle ZST values when constructing an 
iterator to ensure it yields values properly. This flag silences those warnings.
