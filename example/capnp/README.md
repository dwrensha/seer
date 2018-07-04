This example needs stdlib MIR to do anything interesting. Follow the xargo instructions in the
[miri readme](https://github.com/solson/miri).

Make sure you have cargo-seer installed:

```
cargo install seer --git https://github.com/dwrensha/seer
```

Then run seer in this directory, with:

```
RUSTFLAGS="-Z always-encode-mir" xargo seer
```

(It's weird that we need to set RUSTFLAGS like that, because
cargo-seer should already handle it. Is this a bug in xargo?)