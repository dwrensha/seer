#![feature(
    i128_type,
    rustc_private,
)]

extern crate core;

// From rustc.
#[macro_use]
extern crate log;
extern crate log_settings;
extern crate getopts;
#[macro_use]
extern crate rustc;
extern crate rustc_borrowck;
extern crate rustc_const_math;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate syntax;

// From crates.io.
extern crate z3;

pub mod byteorder;
mod cast;
mod constraints;
mod error;
mod eval_context;
mod executor;
mod lvalue;
mod memory;
mod operator;
mod step;
mod terminator;
mod traits;
mod value;
mod driver;

pub use error::{
    EvalError,
    EvalResult,
    StaticEvalError,
};

pub use eval_context::{
    EvalContext,
    Frame,
    ResourceLimits,
    StackPopCleanup,
};

pub use executor::{
    ExecutionComplete,
    ExecutionConfig,
};

pub use lvalue::{
    Lvalue,
    LvalueExtra,
};

pub use memory::{
    AllocId,
    Memory,
    Pointer,
};

pub use value::{
    PrimVal,
    PrimValKind,
    Value,
};
