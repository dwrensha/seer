Make sure you have cargo-seer installed:

```
cargo install seer --git https://github.com/dwrensha/seer
```

Then run seer in this directory, with:

```
RUSTFLAGS="-Z always-encode-mir" CFG_COMPILER_HOST_TRIPLE=x86_64-unknown-linux-gnu XARGO_RUST_SRC=/path/to/rust/repo/src xargo seer --target x86_64-unknown-linux-gnu
```

See https://github.com/japaric/xargo/issues/125#issuecomment-328300943 for more discussion about
why all these special options are needed.