Build with:

```
RUSTFLAGS="-Z always-encode-mir" cargo build
```

Then in the seer top-level directory:

```
cargo run --bin run_symbolic --  -L dependency=./example/httparse/target/debug/deps --extern httparse=./example/httparse/target/debug/deps/libhttparse-f07a346cf686d3f4.rlib  ./example/httparse/src/main.rs
```

(You'll probably need to adjust the hash on the rlib.)