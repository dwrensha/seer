use std::collections::VecDeque;
use std::rc::Rc;
use std::cell::RefCell;

use rustc::hir::def_id::DefId;
use rustc::hir::map::definitions::DefPathData;
use rustc::mir;
use rustc::ty::{self, TyCtxt, Ty};
use syntax::codemap::{DUMMY_SP};

use constraints::{Constraint, SatisfiedVarGroup};
use error::{StaticEvalError, EvalError};
use lvalue::{Lvalue};
use eval_context::{EvalContext, Frame, ResourceLimits, StackPopCleanup};
use value::{PrimVal};

pub struct Executor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    queue: VecDeque<EvalContext<'a, 'tcx>>,
    config: ExecutionConfig,
}

pub struct FinishStep<'tcx> {
    pub constraints: Vec<Constraint>,
    pub variant: FinishStepVariant<'tcx>,
}

pub enum FinishStepVariant<'tcx> {
    Continue {
        goto_block: mir::BasicBlock,
        set_lvalue: Option<(Lvalue<'tcx>, PrimVal, Ty<'tcx>)>,
    },
    Error(EvalError<'tcx>),
}

#[derive(Clone)]
pub struct ExecutionConfig {
    consumer: Option<Rc<RefCell<FnMut(ExecutionComplete) -> bool>>>,
    emit_error: bool,
}

impl ExecutionConfig {
    pub fn new() -> Self {
        ExecutionConfig {
            consumer: None,
            emit_error: false,
        }
    }

    pub fn emit_error<'a>(&'a mut self, emit: bool) -> &'a mut Self {
        self.emit_error = emit;
        self
    }

    /// The consumer returns `true` if it wants the executor to continue.
    pub fn consumer<'a, F>(
        &'a mut self, consumer: F)
        -> &'a mut Self
        where F: FnMut(ExecutionComplete) -> bool + 'static
    {
        self.consumer = Some(Rc::new(RefCell::new(consumer)));
        self
    }

    pub fn run(&self, args: Vec<String>) {
        ::driver::main_helper(args, self.clone());
    }
}

#[derive(Debug)]
pub struct ExecutionComplete {
    pub input: Vec<SatisfiedVarGroup>,
    pub result: Result<(), StaticEvalError>,
}

impl <'a, 'tcx: 'a> Executor<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        def_id: DefId,
        limits: ResourceLimits,
        config: ExecutionConfig,
    )
        -> Self
    {

        let mut result = Executor {
            tcx: tcx,
            queue: VecDeque::new(),
            config: config,
        };

        let mut ecx = EvalContext::new(tcx, limits);
        let instance = ty::Instance::mono(tcx, def_id);
        let mir = ecx.load_mir(instance.def).expect("main function's MIR not found");

        if !mir.return_ty().is_nil() || mir.arg_count > 0 {
            let msg = "seer does not support main functions without `fn()` type signatures";
            tcx.sess.err(&EvalError::Unimplemented(String::from(msg)).to_string());
            unimplemented!()
        }

        ecx.push_stack_frame(
            instance,
            DUMMY_SP,
            &mir,
            Lvalue::undef(),
            StackPopCleanup::None,
        ).expect("could not allocate first stack frame");

        result.push_eval_context(ecx);

        result
    }

    pub fn push_eval_context(&mut self, ecx: EvalContext<'a, 'tcx>) {
        // Push onto the front so that we go depth-first.
        // Pushing onto the back consumes more memory and may be less
        // cache-friendly.
        self.queue.push_front(ecx);
    }

    fn pop_eval_context(&mut self) -> Option<EvalContext<'a, 'tcx>> {
        self.queue.pop_front()
    }

    // return true if we should continue with other executions
    fn report_error(&mut self, ecx: &EvalContext, e: EvalError) -> bool {
        if self.config.emit_error {
            report(self.tcx, &ecx, e.clone());
        }

        match self.config.consumer {
            Some(ref f) => {
                (&mut *f.borrow_mut())(ExecutionComplete {
                    input: ecx.memory.constraints.get_satisfying_values(),
                    result: Err(e.into())
                })
            }
            None => true,
        }
    }

    pub fn run(&mut self) {
        'main_loop: while let Some(mut ecx) = self.pop_eval_context() {
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
                            let FinishStep {constraints, variant} = finish_step;
                            for constraint in constraints {
                                cx.memory.constraints.push_constraint(constraint);
                                match variant {
                                    FinishStepVariant::Continue { goto_block, set_lvalue} => {
                                        if let Some((lvalue, prim, ty)) = set_lvalue {
                                            if let Err(_) = cx.write_primval(lvalue, prim, ty) {
                                                unimplemented!()
                                            }
                                        }
                                        cx.goto_block(goto_block);
                                    }
                                    FinishStepVariant::Error(ref e) => {
                                        if !self.report_error(&cx, e.clone()) {
                                            break 'main_loop;
                                        }
                                    }
                                }
                            }
                            self.push_eval_context(cx);
                        }
                    }
                }
                Ok((false, _)) => {
                    let go_on = match self.config.consumer {
                        Some(ref f) => {
                            (&mut *f.borrow_mut())(ExecutionComplete {
                                input: ecx.memory.constraints.get_satisfying_values(),
                                result: Ok(())
                            })
                        }
                        None => true,
                    };
                    let leaks = ecx.memory.leak_report();
                    if leaks != 0 {
                        self.tcx.sess.err("the evaluated program leaked memory");
                    }
                    if !go_on {
                        break 'main_loop;
                    }
                }
                Err(e) => {
                    if !self.report_error(&ecx, e) {
                        break;
                    }
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
