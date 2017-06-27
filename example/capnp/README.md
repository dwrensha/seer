This example needs stdlib MIR to do anything interesting. Follow the xargo instructions in the
[miri readme](https://github.com/solson/miri).

Build with:

```
RUSTFLAGS="-Z always-encode-mir" xargo build
```

Then in the seer top-level directory:

```
cargo run --bin seer --  --sysroot ~/.xargo/HOME -L dependency=./example/capnp/target/debug/deps --extern capnp=./example/httparse/target/debug/deps/libcapnp  ./example/capnp/src/test_all_types.rs
```

(You'll probably need to adjust the hash on the rlib.)