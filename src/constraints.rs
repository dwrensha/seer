use rustc::mir;
use z3;

use memory::SByte;
use value::PrimValKind;

#[derive(Clone, Debug)]
pub struct ConstraintContext {
    variables: Vec<u8>,
    constraints: Vec<Constraint>,
}

#[derive(Clone, Debug)]
pub enum Val {
    _Variable(usize),
    _Constant(u128),
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

    pub fn allocate_abstract_byte(&mut self) -> SByte {
        SByte::Abstract // XXX
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
