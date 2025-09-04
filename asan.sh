#!/usr/bin/env bash

RUSTFLAGS="-Zsanitizer=address" \
RUSTDOCFLAGS="-Zsanitizer=address" \
ASAN_OPTIONS=detect_leaks=1 \
cargo +nightly t -Zbuild-std --target x86_64-unknown-linux-gnu
