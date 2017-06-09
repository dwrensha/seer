# SEER: Symbolic Execution Engine for Rust

[![Build Status](https://travis-ci.org/dwrensha/seer.svg?branch=master)](https://travis-ci.org/dwrensha/seer)
[![crates.io](http://meritbadge.herokuapp.com/seer)](https://crates.io/crates/seer)

SEER is a fork of [miri](https://github.com/solson/miri)
that adds support for symbolic execution, using
[z3](https://github.com/Z3Prover/z3) as a solver backend.

Given a program, SEER attempts to exhaustively
enumerate the possible execution paths through that program.
SEER represents program input in a _symbolic_ form
and maintains a set of constraints on it.
When SEER reaches a branch in the program, it
invokes its solver backend to compute which branches
are feasible given the current constraints. The feasible
branches are then enqueued for exploration, augmented with new
constraints learned from the branch.

SEER considers any bytes read in through `::std::io::stdin()`
as symbolic input. This means that once
SEER finds an interesting input for your program,
you can easily run exactly the same program outside of SEER
on that input.





