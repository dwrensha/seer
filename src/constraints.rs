use rustc::mir;

use value::PrimValKind;

#[derive(Clone, Debug)]
pub struct ConstraintContext {
    variables: Vec<u8>,
    constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub enum Val {
    Variable(usize),
    Constant(u128),
}

#[derive(Clone, Debug)]
pub struct Constraint {
    operator: mir::BinOp,
    typ: PrimValKind,
}

impl ConstraintContext {
    pub fn new() -> Self {
        ConstraintContext {
            variables: Vec::new(),
            constraints: Vec::new(),
        }
    }
}
