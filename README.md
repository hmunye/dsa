# dsa

Data Structures & Algorithms in Rust

## Testing

Using [`Miri`](https://github.com/rust-lang/miri): 

```bash
rustup +nightly component add miri
```

```bash
MIRIFLAGS=-Zmiri-permissive-provenance cargo +nightly miri t
```
> `Vector` uses integer-to-pointer casts to handle ZST values when constructing an 
iterator to ensure it yields values
