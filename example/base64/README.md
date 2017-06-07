Build with:

```
RUSTFLAGS="-Z always-encode-mir" cargo build
```

Then in the seer top-level directory:

```
cargo run --bin run_symbolic --  -L dependency=./example/base64/target/debug/deps --extern base64=./example/base64/target/debug/deps/libbase64-671f71aca8a0bd16.rlib  ./example/base64/src/main.rs
```

(You'll probably need to adjust the hash on the rlib.)