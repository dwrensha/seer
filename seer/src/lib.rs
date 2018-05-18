#![feature(
    i128_type,
    inclusive_range,
    rustc_private,
)]

// From rustc.
#[macro_use]
extern crate log;
extern crate log_settings;
extern crate getopts;
#[macro_use]
extern crate rustc;
extern crate rustc_const_math;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_trans_utils;
extern crate syntax;

// From crates.io.
extern crate seer_z3 as z3;
extern crate byteorder;
extern crate regex;

mod cast;
mod constraints;
mod error;
mod eval_context;
mod executor;
mod format_executor;
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
    MemoryPointer,
};

pub use value::{
    PrimVal,
    PrimValKind,
    Value,
};
