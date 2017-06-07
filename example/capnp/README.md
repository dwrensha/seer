NOTE: this example currently doesn't get very far before hitting an
error: `NoMirFor("std::fmt::format")`

Build with:

```
RUSTFLAGS="-Z always-encode-mir" cargo build
```

Then in the seer top-level directory:

```
cargo run --bin run_symbolic --  -L dependency=./example/capnp/target/debug/deps --extern capnp=./example/httparse/target/debug/deps/libcapnp  ./example/capnp/src/test_all_types.rs
```

(You'll probably need to adjust the hash on the rlib.)