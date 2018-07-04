# Seer: Symbolic Execution Engine for Rust

[![Build Status](https://travis-ci.org/dwrensha/seer.svg?branch=master)](https://travis-ci.org/dwrensha/seer)
[![crates.io](http://meritbadge.herokuapp.com/seer)](https://crates.io/crates/seer)

Seer is a fork of [miri](https://github.com/solson/miri)
that adds support for symbolic execution, using
[z3](https://github.com/Z3Prover/z3) as a solver backend.

Given a program written in Rust, Seer attempts to exhaustively
enumerate the possible execution paths through it.
To achieve this, Seer represents the program's input in a _symbolic_ form,
maintaining a set of constraints on it.
When Seer reaches a branch point in the program, it
invokes its solver backend to compute which continuations
are possible given the current constraints. The possible
continuations are then enqueued for exploration, augmented with the
respective new constraints learned from the branch condition.

Seer considers any bytes read in through `::std::io::stdin()`
as symbolic input. This means that once
Seer finds an interesting input for your program,
you can easily compile your program with
plain rustc and run it on that input.

## example: decode base64 given only an encoder

[[source code](/example/standalone/base64.rs)]

Suppose we are given a base64 encoder function:

```rust
fn base64_encode(input: &[u8]) -> String { ... }
```

and suppose that we would like to _decode_ a base64-encoded string,
but we don't want to bother to actually write the corresponding
`base64_decode()` function. We can write the following program and
ask Seer to execute it:


```rust
fn main() {
    let value_to_decode = "aGVsbG8gd29ybGQh";
    let mut data: Vec<u8> = vec![0; (value_to_decode.len() + 3) / 4 * 3];
    std::io::stdin().read_exact(&mut data[..]).unwrap();

    let result = base64_encode(&data[..]);

    if result.starts_with(value_to_decode) {
        panic!("we found it!");
    }
}
```

Seer will then attempt to find input values that can trigger the panic.
It succeeds after a few seconds:

```
$ cargo run --bin seer -- example/standalone/base64.rs
    Finished dev [unoptimized + debuginfo] target(s) in 0.0 secs
     Running `target/debug/seer example/standalone/base64.rs`
ExecutionComplete { input: [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33], result: Err(Panic) }
as string: Ok("hello world!")
hit an error. halting

```

There is our answer! Our string decodes as "hello world!"

## using the helper crate
The helper crate provides some extra conveniences. The input that triggers a panic can be split by variable and types that implement `Debug` are printed in their debug representation instead of using the underlying bytes:

```rust
#[macro_use]
extern crate seer_helper;
seer_helper_init!();

#[derive(Debug)]
struct MyStruct {
    a: u32,
    b: u64,
}

fn main() {
    let mut t = MyStruct { a: 0, b: 0 };
    seer_helper::mksym(&mut t);
    if t.a == 123 && t.b == 321 {
        panic!();
    }
}
```

For the formatting to work, it is necessary to build MIR for the standard library, so we will use [Xargo](https://github.com/japaric/xargo):
```
$ RUSTFLAGS="-Z always-encode-mir" xargo seer
...
ExecutionComplete { input: [stdin: [], t: "MyStruct { a: 123, b: 321 }"], result: Err(NoMirFor("std::sys::unix::fast_thread_local::register_dtor::::__cxa_thread_atexit_impl")) }
hit an error. halting
```

The full example crate can be found [here](/example/seer-helper-user).

# limitations

Seer is currently in the proof-of-concept stage
and therefore has lots of `unimplemented!()` holes in it.
In particular, it does not yet handle:

 - allocations with size depending on symbolic input
 - pointer-to-pointer with symbolic offset
 - overflow checking on symbolic arithmetic
 - ... lots of other things that you will quickly discover if you try to use it!

# long-term vision

The goal is that Seer will help in two primary use cases:

 - in exploratory tests, as a complementary approach to [fuzzing](https://github.com/rust-fuzz)
 - in program verification, to exhaustively check that error states cannot be reached
