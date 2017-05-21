use rustc::mir;
use z3;

use memory::{AbstractVariable, SByte};
use value::{PrimVal, PrimValKind};

#[derive(Clone, Debug)]
pub struct ConstraintContext {
    /// Each entry represents a variable. The index is the variable ID and
    /// the value is the number of bits in the variable.
    variables: Vec<u8>,

    constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub enum Val {
    _Variable(usize),
    _Constant(u128),
}

#[derive(Clone, Copy, Debug)]
pub enum Constraint {
    Binop {
        operator: mir::BinOp,
        kind: PrimValKind,
        rhs_operand1: PrimVal,
        rhs_operand2: PrimVal,
        lhs: PrimVal,
    },
    Compare { op: mir::BinOp, kind: PrimValKind, lhs: PrimVal, rhs: PrimVal, },
}

impl Constraint {
    pub fn new_binop(
        operator: mir::BinOp,
        kind: PrimValKind,
        rhs_operand1: PrimVal,
        rhs_operand2: PrimVal,
        lhs: PrimVal,
    ) -> Self {
        Constraint::Binop {
            operator, kind, rhs_operand1, rhs_operand2, lhs,
        }
    }

    pub fn new_compare(op: mir::BinOp, kind: PrimValKind, lhs: PrimVal, rhs: PrimVal) -> Self {
        Constraint::Compare { op, kind, lhs, rhs }
    }
}

impl ConstraintContext {
    pub fn new() -> Self {
        ConstraintContext {
            variables: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn allocate_abstract_byte(&mut self) -> SByte {
        let id = self.variables.len() as u32;
        self.variables.push(8);
        SByte::Abstract(AbstractVariable(id))
    }

    pub fn push_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// Creates a fresh abstract PrimVal `X` and adds a constraint
    /// `left binop right == X`. Returns `X`.
    pub fn add_binop_constraint(
        &mut self,
        bin_op: mir::BinOp,
        left: PrimVal,
        right: PrimVal,
        kind: PrimValKind) -> PrimVal {

        use value::PrimValKind::*;

        let num_bytes = match kind {
            U8 | I8 => 1,
            _ => unimplemented!(),
        };


        let mut buffer = [SByte::Concrete(0); 8];
        for idx in 0..num_bytes {
            buffer[idx] = self.allocate_abstract_byte();
        }

        let primval = PrimVal::Abstract(buffer);

        let constraint = Constraint::new_binop(bin_op, kind, left, right, primval);

        self.push_constraint(constraint);

        primval
    }

    pub fn get_satisfying_values(&self, len: usize) -> Vec<u8> {
        let cfg = z3::Config::new();
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);

        let mut consts = Vec::new();

        for (idx, bitsize) in self.variables.iter().enumerate() {
            consts.push(ctx.numbered_bitvector_const(idx as u32, *bitsize as u32));
        }

        for c in &self.constraints {
            solver.assert(&constraint_to_ast(&ctx, *c));
        }

        let mut result = Vec::new();
        assert!(solver.check());
        let model = solver.get_model();
        for idx in 0..len {
            result.push(model.eval(&consts[idx]).unwrap().as_u64().unwrap() as u8);
        }

        result
    }

    pub fn is_feasible_with(
        &self,
        constraints: &[Constraint])
        -> bool
    {
        let cfg = z3::Config::new();
        let ctx = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx);

        let mut consts = Vec::new();

        for (idx, bitsize) in self.variables.iter().enumerate() {
            consts.push(ctx.numbered_bitvector_const(idx as u32, *bitsize as u32));
        }

        let mut all_constraints: Vec<Constraint> = Vec::new();
        all_constraints.extend(self.constraints.iter().clone());
        all_constraints.extend(constraints.iter().clone());

        for c in all_constraints {
            solver.assert(&constraint_to_ast(&ctx, c));
        }

        solver.check()
    }

    pub fn _is_feasible(&self) -> bool {
        let cfg = z3::Config::new();
        let ctx = z3::Context::new(&cfg);

        for (idx, bitsize) in self.variables.iter().enumerate() {
            ctx.numbered_bitvector_const(idx as u32, *bitsize as u32);
        }

        let x = ctx.named_bitvector_const("x", 8 * 1024);
        let y = x.extract(15, 8);
        let z = x.extract(7, 0);

        let y1 = x.extract(151, 144);
        let z1 = x.extract(150, 143);

        let solver = z3::Solver::new(&ctx);
        solver.assert(&y._eq(&z).not());
        solver.assert(&y1._eq(&z1).not());

        assert!(solver.check());

        let model = solver.get_model();
        //    let xv = model.eval(&x).unwrap().as_i64().expect("1");
        let yv = model.eval(&y).unwrap().as_i64().expect("1");
        let zv = model.eval(&z).unwrap().as_i64().expect("2");
        //    println!("x: {:x}", xv);
        println!("y: {:x}", yv);
        println!("z: {:x}", zv);


        let yv1 = model.eval(&y1).unwrap().as_i64().expect("11");
        let zv1 = model.eval(&z1).unwrap().as_i64().expect("21");
        println!("y1: {:x}", yv1);
        println!("z1: {:x}", zv1);

        false
    }
}

fn constraint_to_ast<'a>(
    ctx: &'a z3::Context,
    constraint: Constraint)
    -> z3::Ast<'a>
{
    match constraint {
        Constraint::Binop { operator, kind, lhs, rhs_operand1,
                            rhs_operand2, .. } => {
            primval_to_ast(&ctx, lhs, kind)._eq(
                &mir_binop_to_ast(
                    &ctx,
                    operator,
                    primval_to_ast(&ctx, rhs_operand1, kind),
                    primval_to_ast(&ctx, rhs_operand2, kind)))
        }
        Constraint::Compare { op, lhs, rhs, .. } => {
            // TODO(cleanup) this duplicates some functionality of mir_binop_to_ast().
            // Can we consolidate?
            match op {
                mir::BinOp::Eq => {
                    primval_to_ast(&ctx, lhs, PrimValKind::U8)._eq( // HACK
                        &primval_to_ast(&ctx, rhs, PrimValKind::U8))
                }
                mir::BinOp::Ne => {
                    primval_to_ast(&ctx, lhs, PrimValKind::U8)._eq( // HACK
                        &primval_to_ast(&ctx, rhs, PrimValKind::U8)).not()
                }
                mir::BinOp::Gt => {
                    primval_to_ast(&ctx, lhs, PrimValKind::U8).bvugt( // HACK
                        &primval_to_ast(&ctx, rhs, PrimValKind::U8))
                }

                mir::BinOp::Lt => {
                    primval_to_ast(&ctx, lhs, PrimValKind::U8).bvult( // HACK
                        &primval_to_ast(&ctx, rhs, PrimValKind::U8))
                }

                _ => {
                    unimplemented!()
                }
            }
        }
    }
}

fn primval_to_ast<'a>(ctx: &'a z3::Context,
                      primval: PrimVal,
                      kind: PrimValKind)
                  -> z3::Ast<'a>
{
    match primval {
        PrimVal::Undef => {
            unimplemented!()
        }
        PrimVal::Ptr(_) => {
            unimplemented!()
        }
        PrimVal::Abstract(sbytes) => {
            if let PrimValKind::U8 = kind {
                match sbytes[0] {
                    SByte::Abstract(b) => {
                        ctx.numbered_bitvector_const(b.0, 8)
                    }
                    SByte::Concrete(_b) => {
                        unimplemented!()
                    }
                }
            } else {
                unimplemented!()
            }
        }
        PrimVal::Bytes(v) => {
            if let PrimValKind::U8 = kind {
                z3::Ast::bv_from_u64(&ctx, v as u64, 8)
            } else {
                unimplemented!()
            }
        }
    }
}

fn mir_binop_to_ast<'a>(
    ctx: &'a z3::Context,
    operator: mir::BinOp,
    left: z3::Ast<'a>,
    right: z3::Ast<'a>)
    -> z3::Ast<'a>
{
    match operator {
        mir::BinOp::Eq => {
            left._eq(&right)
                .ite(&z3::Ast::bv_from_u64(&ctx, 1, 8), /// HACK
                     &z3::Ast::bv_from_u64(&ctx, 0, 8))
        }
        mir::BinOp::Lt => {
            left.bvult(&right)
                .ite(&z3::Ast::bv_from_u64(&ctx, 1, 8), /// HACK
                     &z3::Ast::bv_from_u64(&ctx, 0, 8))
        }

        mir::BinOp::Add => left.bvadd(&right),
        mir::BinOp::BitXor => left.bvxor(&right),
        mir::BinOp::Mul => left.bvmul(&right),
        _ => {
            unimplemented!()
        }
    }
}
