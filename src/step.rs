//! This module contains the `EvalContext` methods for executing a single step of the interpreter.
//!
//! The main entry point is the `step` method.

use rustc::hir::def_id::DefId;
use rustc::hir;
use rustc::mir::visit::{Visitor, PlaceContext};
use rustc::mir;
use rustc::ty::{subst, self};
use rustc::middle::const_val::ConstVal;

use error::{EvalResult, EvalError};
use eval_context::{EvalContext, StackPopCleanup};
use executor::FinishStep;
use place::{Global, GlobalId, Place};
use syntax::codemap::Span;

impl<'a, 'tcx> EvalContext<'a, 'tcx> {
    pub fn inc_step_counter_and_check_limit(&mut self, n: u64) -> EvalResult<'tcx> {
        self.steps_remaining = self.steps_remaining.saturating_sub(n);
        if self.steps_remaining > 0 {
            Ok(())
        } else {
            Err(EvalError::ExecutionTimeLimitReached)
        }
    }

    /// Takes a single step, possibly returning multiple branches.
    ///
    /// Returns (more_steps_to_take, maybe_finish_steps).
    ///
    /// If maybe_finish_steps in None, then there was no branching and `self` has the updated
    /// context. Otherwise we've hit a branch, and each of the FinishSteps must be applied to
    /// a clone of `self` to get the resulting branches.
    pub fn step(&mut self)
                -> EvalResult<'tcx, (bool, Option<Vec<FinishStep<'tcx>>>)>
    {
        // see docs on the `Memory::packed` field for why we do this
        self.memory.clear_packed();
        self.inc_step_counter_and_check_limit(1)?;
        if self.stack.is_empty() {
            return Ok((false, None));
        }

        let block = self.frame().block;
        let stmt_id = self.frame().stmt;
        let mir = self.mir();
        let basic_block = &mir.basic_blocks()[block];

        if let Some(stmt) = basic_block.statements.get(stmt_id) {
            let mut new = Ok(0);
            ConstantExtractor {
                span: stmt.source_info.span,
                instance: self.frame().instance,
                ecx: self,
                mir,
                new_constants: &mut new,
            }.visit_statement(block, stmt, mir::Location { block, statement_index: stmt_id });
            if new? == 0 {
                self.statement(stmt)?;
            }
            // if ConstantExtractor added new frames, we don't execute anything here
            // but await the next call to step
            return Ok((true, None));
        }

        let terminator = basic_block.terminator();
        let mut new = Ok(0);
        ConstantExtractor {
            span: terminator.source_info.span,
            instance: self.frame().instance,
            ecx: self,
            mir,
            new_constants: &mut new,
        }.visit_terminator(block, terminator, mir::Location { block, statement_index: stmt_id });
        if new? == 0 {
            Ok((true, self.terminator(terminator)?))
        } else {
            // if ConstantExtractor added new frames, we don't execute anything here
            // but await the next call to step
            Ok((true, None))
        }
    }

    fn statement(&mut self, stmt: &mir::Statement<'tcx>) -> EvalResult<'tcx> {
        trace!("{:?}", stmt);

        use rustc::mir::StatementKind::*;
        match stmt.kind {
            Assign(ref place, ref rvalue) => self.eval_rvalue_into_place(rvalue, place)?,

            SetDiscriminant {
                ref place,
                variant_index,
            } => {
                let dest = self.eval_place(place)?;
                let dest_ty = self.place_ty(place);
                self.write_discriminant_value(dest_ty, dest, variant_index)?;
            }

            // Miri can safely ignore these. Only translation needs it.
            StorageLive(_) |
            StorageDead(_) => {}

            // No dynamic semantics attached to `ReadForMatch`; MIR
            // interpreter is solely intended for borrowck'ed code.
            ReadForMatch(..) => {}

            // Validity checks.
            Validate(_op, ref _places) => {
                // TODO
            }

            UserAssertTy(..) => {}
            EndRegion(..) => {}

            // Defined to do nothing. These are added by optimization passes, to avoid changing the
            // size of MIR constantly.
            Nop => {}

            InlineAsm { .. } => return Err(EvalError::InlineAsm),
        }

        self.frame_mut().stmt += 1;
        Ok(())
    }

    fn terminator(&mut self,
                  terminator: &mir::Terminator<'tcx>)
                  -> EvalResult<'tcx, Option<Vec<FinishStep<'tcx>>>>
    {
        trace!("{:?}", terminator.kind);
        let result = self.eval_terminator(terminator)?;
        if !self.stack.is_empty() {
            trace!("// {:?}", self.frame().block);
        }
        Ok(result)
    }
}

// WARNING: make sure that any methods implemented on this type don't ever access ecx.stack
// this includes any method that might access the stack
// basically don't call anything other than `load_mir`, `alloc_ptr`, `push_stack_frame`
// The reason for this is, that `push_stack_frame` modifies the stack out of obvious reasons
struct ConstantExtractor<'a, 'b: 'a, 'tcx: 'b> {
    span: Span,
    ecx: &'a mut EvalContext<'b, 'tcx>,
    mir: &'tcx mir::Mir<'tcx>,
    instance: ty::Instance<'tcx>,
    new_constants: &'a mut EvalResult<'tcx, u64>,
}

impl<'a, 'b, 'tcx> ConstantExtractor<'a, 'b, 'tcx> {
    fn global_item(
        &mut self,
        def_id: DefId,
        substs: &'tcx subst::Substs<'tcx>,
        span: Span,
        shared: bool,
    ) {
        let instance = self.ecx.resolve_associated_const(def_id, substs);
        let cid = GlobalId { instance, promoted: None };
        if self.ecx.globals.contains_key(&cid) {
            return;
        }
        self.try(|this| {
            let mir = this.ecx.load_mir(instance.def)?;
            this.ecx.globals.insert(cid, Global::uninitialized(mir.return_ty()));
            let mutable = !shared ||
                !mir.return_ty().is_freeze(
                    this.ecx.tcx,
                    ty::ParamEnv::empty(),
                    span);
            let cleanup = StackPopCleanup::MarkStatic(mutable);
            let name = ty::tls::with(|tcx| tcx.item_path_str(def_id));
            trace!("pushing stack frame for global: {}", name);
            this.ecx.push_stack_frame(
                instance,
                span,
                mir,
                Place::Global(cid),
                cleanup,
            )
        });
    }
    fn try<F: FnOnce(&mut Self) -> EvalResult<'tcx>>(&mut self, f: F) {
        if let Ok(ref mut n) = *self.new_constants {
            *n += 1;
        } else {
            return;
        }
        if let Err(e) = f(self) {
            *self.new_constants = Err(e);
        }
    }
}

impl<'a, 'b, 'tcx> Visitor<'tcx> for ConstantExtractor<'a, 'b, 'tcx> {
    fn visit_constant(&mut self, constant: &mir::Constant<'tcx>, location: mir::Location) {
        self.super_constant(constant, location);
        match constant.literal {
            // already computed by rustc
            mir::Literal::Value { value: &ty::Const { val: ConstVal::Unevaluated(def_id, substs), .. } } => {
                self.global_item(def_id, substs, constant.span, true);
            }
            mir::Literal::Value { .. } => {}
            mir::Literal::Promoted { index } => {
                let cid = GlobalId {
                    instance: self.instance,
                    promoted: Some(index),
                };
                if self.ecx.globals.contains_key(&cid) {
                    return;
                }

                let mir = &self.mir.promoted[index];
                self.try(|this| {
                    let ty = this.ecx.monomorphize(mir.return_ty(), this.instance.substs);
                    this.ecx.globals.insert(cid, Global::uninitialized(ty));
                    trace!("pushing stack frame for {:?}", index);
                    this.ecx.push_stack_frame(this.instance,
                                              constant.span,
                                              mir,
                                              Place::Global(cid),
                                              StackPopCleanup::MarkStatic(false))
                });
            }
        }
    }

    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext<'tcx>,
        location: mir::Location
    ) {
        self.super_place(place, context, location);
        if let mir::Place::Static(ref static_) = *place {
            let def_id = static_.def_id;
            let substs = self.ecx.tcx.intern_substs(&[]);
            let span = self.span;
            if let Some(node_item) = self.ecx.tcx.hir.get_if_local(def_id) {
                if let hir::map::Node::NodeItem(&hir::Item { ref node, .. }) = node_item {
                    if let hir::ItemStatic(_, m, _) = *node {
                        self.global_item(def_id, substs, span, m == hir::MutImmutable);
                        return;
                    } else {
                        bug!("static def id doesn't point to static");
                    }
                } else {
                    bug!("static def id doesn't point to item");
                }
            } else {
                let def = self.ecx.tcx.describe_def(def_id).expect("static not found");
                if let hir::def::Def::Static(_, mutable) = def {
                    self.global_item(def_id, substs, span, !mutable);
                } else {
                    bug!("static found but isn't a static: {:?}", def);
                }
            }
        }
    }
}
