# Seer: Symbolic Execution Engine for Rust

[![Build Status](https://travis-ci.org/dwrensha/seer.svg?branch=master)](https://travis-ci.org/dwrensha/seer)
[![crates.io](http://meritbadge.herokuapp.com/seer)](https://crates.io/crates/seer)

Seer is a fork of [miri](https://github.com/solson/miri)
that adds support for symbolic execution, using
[z3](https://github.com/Z3Prover/z3) as a solver backend.

Given a program, Seer attempts to exhaustively
enumerate the possible execution paths through that program.
Seer represents program input in a _symbolic_ form
and maintains a set of constraints on it.
When Seer reaches a branching point in the program, it
invokes its solver backend to compute which branches
are feasible given the current constraints. The feasible
branches are then enqueued for exploration, augmented with their
corresponding new constraints.

Seer considers any bytes read in through `::std::io::stdin()`
as symbolic input. This means that once
Seer finds an interesting input for your program,
you can easily run exactly the same program outside of Seer
on that input.

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
$ cargo run --bin run_symbolic -- example/standalone/base64.rs
    Finished dev [unoptimized + debuginfo] target(s) in 0.0 secs
     Running `target/debug/run_symbolic example/standalone/base64.rs`
ExecutionComplete { input: [104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33], result: Err(Panic) }
as string: Ok("hello world!")
hit an error. halting

```

There is our answer! Our string decodes as "hello world!"

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
