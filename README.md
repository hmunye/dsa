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
cargo +nightly miri t
```
