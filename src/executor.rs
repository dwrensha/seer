use std::collections::VecDeque;

use rustc::hir::def_id::DefId;
use rustc::hir::map::definitions::DefPathData;
use rustc::mir;
use rustc::ty::{self, TyCtxt, Ty};
use rustc_data_structures::indexed_vec::Idx;
use syntax::codemap::{DUMMY_SP};

use constraints::Constraint;
use error::EvalError;
use lvalue::{Lvalue};
use memory::{Pointer};
use eval_context::{EvalContext, Frame, ResourceLimits, StackPopCleanup};
use value::{PrimVal, Value};

pub struct Executor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    queue: VecDeque<EvalContext<'a, 'tcx>>,
}

pub struct FinishStep<'tcx> {
    pub constraints: Vec<Constraint>,
    pub goto_block: mir::BasicBlock,
    pub set_lvalue: Option<(Lvalue<'tcx>, PrimVal, Ty<'tcx>)>,
}

impl <'a, 'tcx: 'a> Executor<'a, 'tcx> {
    pub fn new_main(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        def_id: DefId,
        limits: ResourceLimits,)
        -> Self
    {

        let mut result = Executor {
            tcx: tcx,
            queue: VecDeque::new(),
        };

        let mut ecx = EvalContext::new(tcx, limits);
        let instance = ty::Instance::mono(tcx, def_id);
        let mir = ecx.load_mir(instance.def).expect("main function's MIR not found");

        if !mir.return_ty.is_nil() || mir.arg_count > 0 {
            let msg = "seer does not support main functions without `fn()` type signatures";
            tcx.sess.err(&EvalError::Unimplemented(String::from(msg)).to_string());
            unimplemented!()
        }

        ecx.push_stack_frame(
            instance,
            DUMMY_SP,
            &mir,
            Lvalue::from_ptr(Pointer::zst_ptr()),
            StackPopCleanup::None,
        ).expect("could not allocate first stack frame");

        result.push_eval_context(ecx);

        result
    }

    pub fn new_symbolic(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        def_id: DefId,
        limits: ResourceLimits,) -> Self
    {
        let mut result = Executor {
            tcx: tcx,
            queue: VecDeque::new(),
        };

        let mut ecx = EvalContext::new(tcx, limits);
        let instance = ty::Instance::mono(tcx, def_id);
        let mir = ecx.load_mir(instance.def).expect("main function's MIR not found");

        if !mir.return_ty.is_nil() || mir.arg_count > 1 {
            let msg = "seer does not support functions without `fn(&[u8])` type signatures";
            tcx.sess.err(&EvalError::Unimplemented(String::from(msg)).to_string());
            unimplemented!()
        }

        ecx.push_stack_frame(
            instance,
            DUMMY_SP,
            &mir,
            Lvalue::from_ptr(Pointer::zst_ptr()),
            StackPopCleanup::None,
        ).expect("could not allocate first stack frame");

        let param_type = &mir.local_decls[mir::Local::new(1)].ty;
        match param_type.sty {
            ty::TyRef(_, ty::TypeAndMut { ty, .. }) => {
                match ty.sty {
                    ty::TySlice(ty) => {
                        match ty.sty {
                            ty::TyUint(::syntax::ast::UintTy::U8) => {
                                println!("OK");
                            }
                            _ => panic!("nope. the arg needs to be a &[u8]"),
                        }
                    }
                    _ => panic!("nope. the arg needs to be a &[u8]"),
                }
            }
            _ => panic!("nope. the arg needs to be a &[u8]"),
        }

        let len = 21;
        let ptr = ecx.memory.allocate_abstract(len, 8).unwrap();
        let val = Value::ByValPair(PrimVal::Ptr(ptr), PrimVal::from_u128(len as u128));
        let lvalue = ecx.eval_lvalue(&mir::Lvalue::Local(mir::Local::new(1))).unwrap();
        ecx.write_value(val, lvalue, *param_type).unwrap();
        ecx.memory.root_abstract_alloc = Some(ptr);

        result.push_eval_context(ecx);

        result
    }

    pub fn push_eval_context(&mut self, ecx: EvalContext<'a, 'tcx>) {
        self.queue.push_back(ecx);
    }

    fn pop_eval_context(&mut self) -> Option<EvalContext<'a, 'tcx>> {
        self.queue.pop_front()
    }

    pub fn run(&mut self) {
        while let Some(mut ecx) = self.pop_eval_context() {
            match ecx.step() {
                Ok((true, None)) => {
                    self.push_eval_context(ecx)
                }
                Ok((true, Some(branches))) => {
                    if branches.is_empty() {
                        // no feasible branch. should throw error
                        unimplemented!()
                    } else {
                        let iter = ::std::iter::repeat(ecx).zip(branches.into_iter());
                        for (mut cx, finish_step) in iter {
                            let FinishStep {constraints, goto_block, set_lvalue} = finish_step;
                            for constraint in constraints {
                                cx.memory.constraints.push_constraint(constraint);
                                if let Some((lvalue, prim, ty)) = set_lvalue {
                                    if let Err(_) = cx.write_primval(lvalue, prim, ty) {
                                        unimplemented!()
                                    }
                                }
                                cx.goto_block(goto_block);
                            }
                            self.push_eval_context(cx);
                        }
                    }
                }
                Ok((false, _)) => {
                    println!("DONE");
                    ecx.memory.constraints.dump_constraints();
                    ecx.memory.root_abstract_alloc.map(|p| ecx.memory.deallocate(p).unwrap());
                    let leaks = ecx.memory.leak_report();
                    if leaks != 0 {
                        self.tcx.sess.err("the evaluated program leaked memory");
                    }
                }
                Err(e) => {
                    println!("got an error! {:?}", e);
                    ecx.memory.constraints.dump_constraints();
//                    report(tcx, &ecx, e);
                }
            }
        }
    }
}


fn report(tcx: TyCtxt, ecx: &EvalContext, e: EvalError) {
    let frame = ecx.stack().last().expect("stackframe was empty");
    let block = &frame.mir.basic_blocks()[frame.block];
    let span = if frame.stmt < block.statements.len() {
        block.statements[frame.stmt].source_info.span
    } else {
        block.terminator().source_info.span
    };
    let mut err = tcx.sess.struct_span_err(span, &e.to_string());
    for &Frame { instance, span, .. } in ecx.stack().iter().rev() {
        if tcx.def_key(instance.def_id()).disambiguated_data.data == DefPathData::ClosureExpr {
            err.span_note(span, "inside call to closure");
            continue;
        }
        err.span_note(span, &format!("inside call to {}", instance));
    }
    err.emit();
}
