This example needs stdlib MIR to do anything interesting. Follow the xargo instructions in the
[miri readme](https://github.com/solson/miri).

Make sure you have cargo-seer installed:

```
cargo install seer --git https://github.com/dwrensha/seer
```

Then run seer in this directory, with:

```
RUSTFLAGS="-Z always-encode-mir" xargo seer --target x86_64-apple-darwin
```

(We need to set `--target` so that the proc_macro stuff in the
fuzzy-pickles-derive crate works. See https://github.com/japaric/xargo/issues/125.)