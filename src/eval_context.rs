use std::collections::HashMap;
use std::fmt::Write;

use rustc::hir::def_id::DefId;
use rustc::middle::const_val::ConstVal;
use rustc::mir;
use rustc::ty::layout::{self, Size, HasDataLayout, LayoutOf, TyLayout};
use rustc::ty::subst::{Subst, Substs, Kind};
use rustc::ty::{self, Ty, TyCtxt, TypeFoldable, Binder};
use rustc_data_structures::indexed_vec::Idx;
use syntax::codemap::{self, DUMMY_SP};

use error::{EvalError, EvalResult};
use lvalue::{Global, GlobalId, Lvalue, LvalueExtra};
use memory::{Memory, MemoryPointer};
use value::{PrimVal, PrimValKind, Value};


pub struct EvalContext<'a, 'tcx: 'a> {
    /// The results of the type checker, from rustc.
    pub(crate) tcx: TyCtxt<'a, 'tcx, 'tcx>,

    /// The virtual memory system.
    pub(crate) memory: Memory<'a, 'tcx>,

    /// Precomputed statics, constants and promoteds.
    pub(crate) globals: HashMap<GlobalId<'tcx>, Global<'tcx>>,

    /// The virtual call stack.
    pub(crate) stack: Vec<Frame<'tcx>>,

    /// The maximum number of stack frames allowed
    pub(crate) stack_limit: usize,

    /// The maximum number of operations that may be executed.
    /// This prevents infinite loops and huge computations from freezing up const eval.
    /// Remove once halting problem is solved.
    pub(crate) steps_remaining: u64,

    /// Environment variables set by `setenv`
    /// Miri does not expose env vars from the host to the emulated program
    pub(crate) env_vars: HashMap<Vec<u8>, MemoryPointer>,
}

impl <'a, 'tcx: 'a> Clone for EvalContext<'a, 'tcx> {
    fn clone(&self) -> Self {
        EvalContext {
            tcx: self.tcx,
            memory: self.memory.clone(),
            globals: self.globals.clone(),
            stack: self.stack.clone(),
            stack_limit: self.stack_limit,
            steps_remaining: self.steps_remaining,
            env_vars: self.env_vars.clone(),
        }
    }
}

/// A stack frame.
pub struct Frame<'tcx> {
    ////////////////////////////////////////////////////////////////////////////////
    // Function and callsite information
    ////////////////////////////////////////////////////////////////////////////////

    /// The MIR for the function called on this frame.
    pub mir: &'tcx mir::Mir<'tcx>,

    /// The def_id and substs of the current function
    pub instance: ty::Instance<'tcx>,

    /// The span of the call site.
    pub span: codemap::Span,

    ////////////////////////////////////////////////////////////////////////////////
    // Return lvalue and locals
    ////////////////////////////////////////////////////////////////////////////////

    /// The block to return to when returning from the current stack frame
    pub return_to_block: StackPopCleanup,

    /// The location where the result of the current stack frame should be written to.
    pub return_lvalue: Lvalue<'tcx>,

    /// The list of locals for this stack frame, stored in order as
    /// `[arguments..., variables..., temporaries...]`. The locals are stored as `Value`s, which
    /// can either directly contain `PrimVal` or refer to some part of an `Allocation`.
    ///
    /// Before being initialized, all locals are `Value::ByVal(PrimVal::Undef)`.
    pub locals: Vec<Value>,

    ////////////////////////////////////////////////////////////////////////////////
    // Current position within the function
    ////////////////////////////////////////////////////////////////////////////////

    /// The block that is currently executed (or will be executed after the above call stacks
    /// return).
    pub block: mir::BasicBlock,

    /// The index of the currently evaluated statment.
    pub stmt: usize,
}

impl <'tcx> Clone for Frame<'tcx> {
    fn clone(&self) -> Self {
        Frame {
            mir: &self.mir,
            instance: self.instance,
            span: self.span,
            return_to_block: self.return_to_block.clone(),
            return_lvalue: self.return_lvalue,
            locals: self.locals.clone(),
            block: self.block.clone(),
            stmt: self.stmt,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum StackPopCleanup {
    /// The stackframe existed to compute the initial value of a static/constant, make sure it
    /// isn't modifyable afterwards in case of constants.
    /// In case of `static mut`, mark the memory to ensure it's never marked as immutable through
    /// references or deallocated
    /// The bool decides whether the value is mutable (true) or not (false)
    MarkStatic(bool),
    /// A regular stackframe added due to a function call will need to get forwarded to the next
    /// block
    Goto(mir::BasicBlock),
    /// The main function and diverging functions have nowhere to return to
    None,
}

#[derive(Copy, Clone, Debug)]
pub struct ResourceLimits {
    pub memory_size: u64,
    pub step_limit: u64,
    pub stack_limit: usize,
}

impl Default for ResourceLimits {
    fn default() -> Self {
        ResourceLimits {
            memory_size: 100 * 1024 * 1024, // 100 MB
            step_limit: 1_000_000,
            stack_limit: 100,
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TyAndPacked<'tcx> {
    pub ty: Ty<'tcx>,
    pub packed: bool,
}

#[derive(Copy, Clone, Debug)]
pub struct ValTy<'tcx> {
    pub value: Value,
    pub ty: Ty<'tcx>,
}

impl<'tcx> ::std::ops::Deref for ValTy<'tcx> {
    type Target = Value;
    fn deref(&self) -> &Value {
        &self.value
    }
}

impl<'a, 'tcx> HasDataLayout for &'a EvalContext<'a, 'tcx> {
    #[inline]
    fn data_layout(&self) -> &layout::TargetDataLayout {
        &self.tcx.data_layout
    }
}

impl<'c, 'b, 'a, 'tcx> HasDataLayout
    for &'c &'b mut EvalContext<'a, 'tcx> {
    #[inline]
    fn data_layout(&self) -> &layout::TargetDataLayout {
        &self.tcx.data_layout
    }
}

impl<'a, 'tcx> layout::HasTyCtxt<'tcx> for &'a EvalContext<'a, 'tcx> {
    #[inline]
    fn tcx<'b>(&'b self) -> TyCtxt<'b, 'tcx, 'tcx> {
        self.tcx
    }
}

impl<'c, 'b, 'a, 'tcx> layout::HasTyCtxt<'tcx>
    for &'c &'b mut EvalContext<'a, 'tcx> {
    #[inline]
    fn tcx<'d>(&'d self) -> TyCtxt<'d, 'tcx, 'tcx> {
        self.tcx
    }
}

impl<'a, 'tcx> LayoutOf for &'a EvalContext<'a, 'tcx> {
    type Ty = Ty<'tcx>;
    type TyLayout = EvalResult<'tcx, TyLayout<'tcx>>;

    fn layout_of(self, ty: Ty<'tcx>) -> Self::TyLayout {
        self.tcx.layout_of(::rustc::ty::ParamEnv::empty().and(ty))
            .map_err(|layout| EvalError::Layout(layout).into())
    }
}

impl<'c, 'b, 'a, 'tcx> LayoutOf for &'c &'b mut EvalContext<'a, 'tcx> {
    type Ty = Ty<'tcx>;
    type TyLayout = EvalResult<'tcx, TyLayout<'tcx>>;

    #[inline]
    fn layout_of(self, ty: Ty<'tcx>) -> Self::TyLayout {
        (&**self).layout_of(ty)
    }
}

impl<'a, 'tcx> EvalContext<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, limits: ResourceLimits) -> Self {
        EvalContext {
            tcx,
            memory: Memory::new(&tcx.data_layout, limits.memory_size),
            globals: HashMap::new(),
            stack: Vec::new(),
            stack_limit: limits.stack_limit,
            steps_remaining: limits.step_limit,
            env_vars: HashMap::new(),
        }
    }

    pub fn alloc_ptr(&mut self, ty: Ty<'tcx>) -> EvalResult<'tcx, MemoryPointer> {
        let substs = self.substs();
        self.alloc_ptr_with_substs(ty, substs)
    }

    pub fn alloc_ptr_with_substs(
        &mut self,
        ty: Ty<'tcx>,
        substs: &'tcx Substs<'tcx>
    ) -> EvalResult<'tcx, MemoryPointer> {
        let size = self.type_size_with_substs(ty, substs)?.expect("cannot alloc memory for unsized type");
        let align = self.type_align_with_substs(ty, substs)?;
        self.memory.allocate(size, align)
    }

    pub fn memory(&self) -> &Memory<'a, 'tcx> {
        &self.memory
    }

    pub fn memory_mut(&mut self) -> &mut Memory<'a, 'tcx> {
        &mut self.memory
    }

    pub fn stack(&self) -> &[Frame<'tcx>] {
        &self.stack
    }

    /// Returns true if the current frame or any parent frame is part of a ctfe.
    ///
    /// Used to disable features in const eval, which do not have a rfc enabling
    /// them or which can't be written in a way that they produce the same output
    /// that evaluating the code at runtime would produce.
    pub fn const_env(&self) -> bool {
        for frame in self.stack.iter().rev() {
            if let StackPopCleanup::MarkStatic(_) = frame.return_to_block {
                return true;
            }
        }
        false
    }

    pub(crate) fn str_to_value(&mut self, s: &str) -> EvalResult<'tcx, Value> {
        let ptr = self.memory.allocate_cached(s.as_bytes())?;
        Ok(Value::ByValPair(PrimVal::Ptr(ptr), PrimVal::from_u128(s.len() as u128)))
    }

    fn rustc_primval_to_primval(&mut self, primval: mir::interpret::PrimVal) -> EvalResult<'tcx, PrimVal> {
        match primval {
            mir::interpret::PrimVal::Bytes(b) => {
                Ok(PrimVal::Bytes(b))
            }
            mir::interpret::PrimVal::Undef => {
                Ok(PrimVal::Undef)
            }
            mir::interpret::PrimVal::Ptr(ptr) => {
                let EvalContext { ref mut memory, ref tcx, .. } = *self;
                Ok(PrimVal::Ptr(memory.get_rustc_allocation(tcx, ptr)?))
            }
        }
    }

    pub(super) fn const_to_value(&mut self, const_val: &ConstVal<'tcx>) -> EvalResult<'tcx, Value> {
        Ok(match *const_val {
            ConstVal::Unevaluated(def_id, substs) => {
                let instance = self.resolve_associated_const(def_id, substs);
                let cid = GlobalId {
                    instance,
                    promoted: None,
                };
                self.globals.get(&cid).expect("static/const not cached").value
            }

            ConstVal::Value(mir::interpret::Value::ByRef(..)) => {
                unimplemented!()
            }
            ConstVal::Value(mir::interpret::Value::ByVal(prim_val)) => {
                Value::ByVal(self.rustc_primval_to_primval(prim_val)?)
            }
            ConstVal::Value(mir::interpret::Value::ByValPair(p1, p2)) => {
                Value::ByValPair(self.rustc_primval_to_primval(p1)?,
                                 self.rustc_primval_to_primval(p2)?)
            }
        })
    }

    pub(super) fn resolve(&self, def_id: DefId, substs: &'tcx Substs<'tcx>) -> EvalResult<'tcx, ty::Instance<'tcx>> {
        let substs = self.tcx.subst_and_normalize_erasing_regions(self.substs(), ::rustc::ty::ParamEnv::reveal_all(), &substs);
        ::rustc::ty::Instance::resolve(
            self.tcx,
            ::rustc::ty::ParamEnv::empty(), // XXX ?
            def_id,
            substs,
        ).ok_or_else(|| EvalError::TypeckError.into()) // turn error prop into a panic to expose associated type in const issue
    }

    pub(super) fn type_is_sized(&self, ty: Ty<'tcx>) -> bool {
        // generics are weird, don't run this function on a generic
        assert!(!ty.needs_subst());
        ty.is_sized(self.tcx.at(DUMMY_SP), ty::ParamEnv::empty())
    }

    pub fn load_mir(&self, instance: ty::InstanceDef<'tcx>) -> EvalResult<'tcx, &'tcx mir::Mir<'tcx>> {
        trace!("load mir {:?}", instance);
        match instance {
            ty::InstanceDef::Item(def_id) => self.tcx.maybe_optimized_mir(def_id).ok_or_else(|| EvalError::NoMirFor(self.tcx.item_path_str(def_id))),
            _ => Ok(self.tcx.instance_mir(instance)),
        }
    }

    pub fn monomorphize(&self, ty: Ty<'tcx>, substs: &'tcx Substs<'tcx>) -> Ty<'tcx> {
        // miri doesn't care about lifetimes, and will choke on some crazy ones
        // let's simply get rid of them
        let substituted = ty.subst(self.tcx, substs);
        self.tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), substituted)
    }

    pub fn erase_lifetimes<T>(&self, value: &Binder<T>) -> T
        where T : TypeFoldable<'tcx>
    {
        let value = self.tcx.erase_late_bound_regions(value);
        self.tcx.erase_regions(&value)
    }

    pub(super) fn type_size(&self, ty: Ty<'tcx>) -> EvalResult<'tcx, Option<u64>> {
        self.type_size_with_substs(ty, self.substs())
    }

    pub(super) fn type_align(&self, ty: Ty<'tcx>) -> EvalResult<'tcx, u64> {
        self.type_align_with_substs(ty, self.substs())
    }

    fn type_size_with_substs(
        &self,
        ty: Ty<'tcx>,
        substs: &'tcx Substs<'tcx>,
    ) -> EvalResult<'tcx, Option<u64>> {
        let layout = self.type_layout_with_substs(ty, substs)?;
        if layout.is_unsized() {
            Ok(None)
        } else {
            Ok(Some(layout.size.bytes()))
        }
    }

    fn type_align_with_substs(&self, ty: Ty<'tcx>, substs: &'tcx Substs<'tcx>) -> EvalResult<'tcx, u64> {
        self.type_layout_with_substs(ty, substs).map(|layout| {
            layout.align.abi()
        })
    }

    pub(super) fn type_layout(&self, ty: Ty<'tcx>) -> EvalResult<'tcx, TyLayout<'tcx>> {
        self.type_layout_with_substs(ty, self.substs())
    }

    fn type_layout_with_substs(&self, ty: Ty<'tcx>, substs: &'tcx Substs<'tcx>) -> EvalResult<'tcx, TyLayout<'tcx>> {
        // TODO(solson): Is this inefficient? Needs investigation.
        let ty = self.monomorphize(ty, substs);

        self.layout_of(ty)
    }

    pub fn push_stack_frame(
        &mut self,
        instance: ty::Instance<'tcx>,
        span: codemap::Span,
        mir: &'tcx mir::Mir<'tcx>,
        return_lvalue: Lvalue<'tcx>,
        return_to_block: StackPopCleanup,
    ) -> EvalResult<'tcx> {
        ::log_settings::settings().indentation += 1;

        // Subtract 1 because `local_decls` includes the ReturnPointer, but we don't store a local
        // `Value` for that.
        let num_locals = mir.local_decls.len() - 1;
        let locals = vec![Value::ByVal(PrimVal::Undef); num_locals];

        self.stack.push(Frame {
            mir,
            block: mir::START_BLOCK,
            return_to_block,
            return_lvalue,
            locals,
            span,
            instance,
            stmt: 0,
        });

        if self.stack.len() > self.stack_limit {
            Err(EvalError::StackFrameLimitReached)
        } else {
            Ok(())
        }
    }

    pub(super) fn pop_stack_frame(&mut self) -> EvalResult<'tcx> {
        let frame = self.stack.pop().expect("tried to pop a stack frame, but there were none");
        match frame.return_to_block {
            StackPopCleanup::MarkStatic(mutable) => if let Lvalue::Global(id) = frame.return_lvalue {
                let global_value = self.globals.get_mut(&id)
                    .expect("global should have been cached (static)");
                match global_value.value {
                    Value::ByRef(ptr) => self.memory.mark_static_initalized(ptr.alloc_id, mutable)?,
                    Value::ByVal(val) => if let PrimVal::Ptr(ptr) = val {
                        self.memory.mark_inner_allocation(ptr.alloc_id, mutable)?;
                    },
                    Value::ByValPair(val1, val2) => {
                        if let PrimVal::Ptr(ptr) = val1 {
                            self.memory.mark_inner_allocation(ptr.alloc_id, mutable)?;
                        }
                        if let PrimVal::Ptr(ptr) = val2 {
                            self.memory.mark_inner_allocation(ptr.alloc_id, mutable)?;
                        }
                    },
                }
                // see comment on `initialized` field
                assert!(!global_value.initialized);
                global_value.initialized = true;
                assert!(global_value.mutable);
                global_value.mutable = mutable;
            } else {
                bug!("StackPopCleanup::MarkStatic on: {:?}", frame.return_lvalue);
            },
            StackPopCleanup::Goto(target) => self.goto_block(target),
            StackPopCleanup::None => {},
        }
        // deallocate all locals that are backed by an allocation
        for local in frame.locals {
            if let Value::ByRef(ptr) = local {
                trace!("deallocating local");
                self.memory.dump_alloc(ptr.alloc_id);
                match self.memory.deallocate(ptr) {
                    // We could alternatively check whether the alloc_id is static before calling
                    // deallocate, but this is much simpler and is probably the rare case.
                    Ok(()) | Err(EvalError::DeallocatedStaticMemory) => {},
                    other => return other,
                }
            }
        }

        Ok(())
    }

    /// Evaluate an assignment statement.
    ///
    /// There is no separate `eval_rvalue` function. Instead, the code for handling each rvalue
    /// type writes its results directly into the memory specified by the lvalue.
    pub(super) fn eval_rvalue_into_lvalue(
        &mut self,
        rvalue: &mir::Rvalue<'tcx>,
        lvalue: &mir::Place<'tcx>,
    ) -> EvalResult<'tcx> {
        let dest = self.eval_lvalue(lvalue)?;
        let dest_ty = self.lvalue_ty(lvalue);

        use rustc::mir::Rvalue::*;
        match *rvalue {
            Use(ref operand) => {
                let value = self.eval_operand(operand)?;
                self.write_value(ValTy { value, ty: dest_ty }, dest)?;
            }

            BinaryOp(bin_op, ref left, ref right) => {
                // ignore overflow bit, rustc inserts check branches for us
                self.intrinsic_overflowing(bin_op, left, right, dest, dest_ty)?;
            }

            CheckedBinaryOp(bin_op, ref left, ref right) => {
                self.intrinsic_with_overflow(bin_op, left, right, dest, dest_ty)?;
            }

            UnaryOp(un_op, ref operand) => {
                let val = self.eval_operand_to_primval(operand)?;
                let kind = self.ty_to_primval_kind(dest_ty)?;
                let result = self.unary_op(un_op, val, kind)?;
                self.write_primval(dest, result, dest_ty)?;
            }

            // Skip everything for zsts
            Aggregate(..) if self.type_size(dest_ty)? == Some(0) => {}

            Aggregate(ref kind, ref operands) => {
                self.inc_step_counter_and_check_limit(operands.len() as u64)?;
                let mut layout = self.type_layout(dest_ty)?;
                let (dest, active_field_index) = match **kind {
                    mir::AggregateKind::Adt(adt_def, variant_index, _, active_field_index) => {
                        self.write_discriminant_value(dest_ty, dest, variant_index)?;
                        layout = layout.for_variant(&self, variant_index);
                        if adt_def.is_enum() {
                            (self.lvalue_downcast(dest, variant_index)?, active_field_index)
                        } else {
                            (dest, active_field_index)
                        }
                    }
                    _ => (dest, None)
                };

                for (i, operand) in operands.iter().enumerate() {
                    let value = self.eval_operand(operand)?;
                    let value_ty = self.operand_ty(operand);
                    // Ignore zero-sized fields.
                    if !self.type_layout(value_ty)?.is_zst() {
                        let field_index = active_field_index.unwrap_or(i);
                        let (field_dest, _) = self.lvalue_field(dest, mir::Field::new(field_index), layout)?;
                        self.write_value(ValTy { value, ty: value_ty }, field_dest)?;
                    }
                }
            }

            Repeat(ref operand, _) => {
                let (elem_ty, length) = match dest_ty.sty {
                    ty::TyArray(elem_ty, n) => (elem_ty, n.val.unwrap_u64()),
                    _ => bug!("tried to assign array-repeat to non-array type {:?}", dest_ty),
                };
                self.inc_step_counter_and_check_limit(length)?;
                let elem_size = self.type_size(elem_ty)?
                    .expect("repeat element type must be sized");
                let value = self.eval_operand(operand)?;

                // FIXME(solson)
                let dest = PrimVal::Ptr(self.force_allocation(dest)?.to_ptr()?);

                for i in 0..length {
                    let elem_dest = dest.offset(i * elem_size, self.memory.layout)?;
                    self.write_value_to_ptr(value, elem_dest, elem_ty)?;
                }
            }

            Len(ref lvalue) => {
                let src = self.eval_lvalue(lvalue)?;
                let ty = self.lvalue_ty(lvalue);
                let (_, len) = src.elem_ty_and_len(ty);
                self.write_primval(dest, PrimVal::from_u128(len as u128), dest_ty)?;
            }

            Ref(_, _, ref lvalue) => {
                let src = self.eval_lvalue(lvalue)?;
                let (ptr, extra) = self.force_allocation(src)?.to_ptr_and_extra();

                let val = match extra {
                    LvalueExtra::None => Value::ByVal(ptr),
                    LvalueExtra::Length(len) => Value::ByValPair(ptr, len),
                    LvalueExtra::Vtable(vtable) => Value::ByValPair(ptr, PrimVal::Ptr(vtable)),
                    LvalueExtra::DowncastVariant(..) =>
                        bug!("attempted to take a reference to an enum downcast lvalue"),
                };

                self.write_value(ValTy { value: val, ty: dest_ty }, dest)?;
            }

            NullaryOp(mir::NullOp::Box, ty) => {
                if self.const_env() {
                    unimplemented!();
                    //return Err(EvalError::NeedsRfc("\"heap\" allocations".to_string()));
                }
                // FIXME: call the `exchange_malloc` lang item if available
                if self.type_size(ty)?.expect("box only works with sized types") == 0 {
                    let align = self.type_align(ty)?;
                    self.write_primval(dest, PrimVal::Bytes(align.into()), dest_ty)?;
                } else {
                    let ptr = self.alloc_ptr(ty)?;
                    self.write_primval(dest, PrimVal::Ptr(ptr), dest_ty)?;
                }
            }

            NullaryOp(mir::NullOp::SizeOf, ty) => {
                if self.const_env() {
                    unimplemented!();
                    //return Err(EvalError::NeedsRfc("computing the size of types (size_of)".to_string()));
                }
                let size = self.type_size(ty)?.expect("SizeOf nullary MIR operator called for unsized type");
                self.write_primval(dest, PrimVal::from_u128(size as u128), dest_ty)?;
            }

            Cast(kind, ref operand, cast_ty) => {
                debug_assert_eq!(self.monomorphize(cast_ty, self.substs()), dest_ty);
                use rustc::mir::CastKind::*;
                match kind {
                    Unsize => {
                        let src = self.eval_operand(operand)?;
                        let src_ty = self.operand_ty(operand);
                        self.unsize_into(src, src_ty, dest, dest_ty)?;
                    }

                    Misc => {
                        let src = self.eval_operand(operand)?;
                        let src_ty = self.operand_ty(operand);
                        if self.type_is_fat_ptr(src_ty) {
                            match (src, self.type_is_fat_ptr(dest_ty)) {
                                (Value::ByRef(_), _) |
                                (Value::ByValPair(..), true) => {
                                    self.write_value(ValTy { value: src, ty: dest_ty }, dest)?;
                                },
                                (Value::ByValPair(data, _), false) => {
                                    self.write_value(ValTy { value: Value::ByVal(data), ty: dest_ty }, dest)?;
                                },
                                (Value::ByVal(v), false) => {
                                    self.write_value(ValTy { value: Value::ByVal(v), ty: dest_ty }, dest)?;
                                }
                                (Value::ByVal(_), true) => bug!("expected fat ptr"),
                            }
                        } else {
                            // First, try casting
                            let dest_val = self.value_to_primval(src, src_ty).and_then(
                                |src_val| { self.cast_primval(src_val, src_ty, dest_ty) })
                                // Alternatively, if the sizes are equal, try just reading at the target type
                                .or_else(|err| {
                                    let size = self.type_size(src_ty)?;
                                    if size.is_some() && size == self.type_size(dest_ty)? {
                                        self.value_to_primval(src, dest_ty)
                                    } else {
                                        Err(err)
                                    }
                                });
                            self.write_value(ValTy { value: Value::ByVal(dest_val?), ty: dest_ty}, dest)?;
                        }
                    }

                    ReifyFnPointer => match self.operand_ty(operand).sty {
                        ty::TyFnDef(def_id, substs) => {
                            let instance = self.resolve(def_id, substs)?;
                            let fn_ptr = self.memory.create_fn_alloc(instance);
                            self.write_value(ValTy { value: Value::ByVal(PrimVal::Ptr(fn_ptr)), ty: dest_ty }, dest)?;
                        },
                        ref other => bug!("reify fn pointer on {:?}", other),
                    },

                    UnsafeFnPointer => match dest_ty.sty {
                        ty::TyFnPtr(_) => {
                            let src = self.eval_operand(operand)?;
                            self.write_value(ValTy { value: src, ty: dest_ty }, dest)?;
                        },
                        ref other => bug!("fn to unsafe fn cast on {:?}", other),
                    },

                    ClosureFnPointer => match self.operand_ty(operand).sty {
                        ty::TyClosure(def_id, substs) => {
                            let instance = ::rustc::ty::Instance::resolve_closure(
                                self.tcx, def_id, substs, ty::ClosureKind::FnOnce);
                            let fn_ptr = self.memory.create_fn_alloc(instance);
                            self.write_value(ValTy { value: Value::ByVal(PrimVal::Ptr(fn_ptr)), ty: dest_ty}, dest)?;
                        },
                        ref other => bug!("reify fn pointer on {:?}", other),
                    },
                }
            }

            Discriminant(ref lvalue) => {
                let lval = self.eval_lvalue(lvalue)?;
                let ty = self.lvalue_ty(lvalue);

                // TODO: Why is this mask necessary? Does the need for it indicate some kind of bug
                // in rustc? Is there a better way to accomplish this?
                // (The mask was added to make tests/run-pass/issue-15523-big.rs pass.)
                let mut mask: u128 = 0;
                for idx in 0..self.layout_of(dest_ty)?.size.bytes() {
                    mask = mask | (0xffu128 << (idx * 8));
                }

                let discr_val = mask & self.read_discriminant_value(lval, ty)?;
                if let ty::TyAdt(adt_def, _) = ty.sty {
                    trace!("Read discriminant {}, valid discriminants {:?}", discr_val, adt_def.discriminants(self.tcx).collect::<Vec<_>>());
                    if adt_def.discriminants(self.tcx).all(|v| {
                        discr_val != v.val
                    })
                    {
                        return Err(EvalError::InvalidDiscriminant);
                    }
                    self.write_primval(dest, PrimVal::Bytes(discr_val), dest_ty)?;
                } else {
                    //bug!("rustc only generates Rvalue::Discriminant for enums");
                    // Getting here is no longer a bug. Is there something else we should be doing?
                    // See https://github.com/rust-lang/rust/pull/48092.
                }
            },
        }

        if log_enabled!(::log::Level::Trace) {
            self.dump_local(dest);
        }

        Ok(())
    }

    fn type_is_fat_ptr(&self, ty: Ty<'tcx>) -> bool {
        match ty.sty {
            ty::TyRawPtr(ty::TypeAndMut {ty, .. }) |
            ty::TyRef(_, ty, _) => {
                if let ty::TyForeign(def_id) =  ty.sty {
                    if "Opaque" == self.tcx.item_name(def_id) {
                        // TODO make this more picky. We want it to only match std::alloc::Opaque.
                        return false;
                    }
                }
                !self.type_is_sized(ty)
            }
            ty::TyAdt(def, _) if def.is_box() => !self.type_is_sized(ty.boxed_ty()),
            _ => false,
        }
    }

    pub fn layout_is_packed(&self, _layout: TyLayout<'tcx>) -> bool {
// TODO. See https://github.com/rust-lang/rust/pull/46436
//        for i in layout.fields.index_by_increasing_offset() {
//            let field = layout.field(ccx, i);
//            if layout.align.abi() < field.align.abi() {
//                return true;
//            }
//        }
        return false
    }

    /// Returns the field type and whether the field is packed
    pub fn get_field_ty(
        &self,
        ty: Ty<'tcx>,
        field_index: usize,
    ) -> EvalResult<'tcx, TyAndPacked<'tcx>> {
        let layout = self.type_layout(ty)?.field(self, field_index)?;
        Ok(TyAndPacked {
            ty: layout.ty,
            packed: self.layout_is_packed(layout)
        })
    }

    fn get_field_offset(&self, ty: Ty<'tcx>, field_index: usize) -> EvalResult<'tcx, Size> {
        Ok(self.type_layout(ty)?.fields.offset(field_index))
    }

    pub fn get_field_count(&self, ty: Ty<'tcx>) -> EvalResult<'tcx, u64> {
        Ok(self.type_layout(ty)?.fields.count() as u64)
    }

    pub(super) fn wrapping_pointer_offset(&self, ptr: PrimVal, pointee_ty: Ty<'tcx>, offset: i64) -> EvalResult<'tcx, PrimVal> {
        // FIXME: assuming here that type size is < i64::max_value()
        let pointee_size = self.type_size(pointee_ty)?.expect("cannot offset a pointer to an unsized type") as i64;
        let offset = offset.overflowing_mul(pointee_size).0;
        ptr.wrapping_signed_offset(offset, self.memory.layout)
    }

    pub(super) fn pointer_offset(&self, ptr: PrimVal, pointee_ty: Ty<'tcx>, offset: i64) -> EvalResult<'tcx, PrimVal> {
        // This function raises an error if the offset moves the pointer outside of its allocation.  We consider
        // ZSTs their own huge allocation that doesn't overlap with anything (and nothing moves in there because the size is 0).
        // We also consider the NULL pointer its own separate allocation, and all the remaining integers pointers their own
        // allocation.

        if ptr.is_null()? { // NULL pointers must only be offset by 0
            return if offset == 0 { Ok(ptr) } else { Err(EvalError::InvalidNullPointerUsage) };
        }
        // FIXME: assuming here that type size is < i64::max_value()
        let pointee_size = self.type_size(pointee_ty)?.expect("cannot offset a pointer to an unsized type") as i64;
        return if let Some(offset) = offset.checked_mul(pointee_size) {
            let ptr = ptr.signed_offset(offset, self.memory.layout)?;
            // Do not do bounds-checking for integers; they can never alias a normal pointer anyway.
            if let PrimVal::Ptr(ptr) = ptr {
                self.memory.check_bounds(ptr, false)?;
            } else if ptr.is_null()? {
                // We moved *to* a NULL pointer.  That seems wrong, LLVM considers the NULL pointer its own small allocation.  Reject this, for now.
                return Err(EvalError::InvalidNullPointerUsage);
            }
            Ok(ptr)
        } else {
            Err(EvalError::Overflow(mir::BinOp::Mul))
        }
    }

    pub(super) fn eval_operand_to_primval(&mut self, op: &mir::Operand<'tcx>) -> EvalResult<'tcx, PrimVal> {
        let value = self.eval_operand(op)?;
        let ty = self.operand_ty(op);
        self.value_to_primval(value, ty)
    }

    pub(super) fn eval_operand(&mut self, op: &mir::Operand<'tcx>) -> EvalResult<'tcx, Value> {
        use rustc::mir::Operand::*;
        match *op {
            Copy(ref lvalue) => self.eval_and_read_lvalue(lvalue),
            Move(ref lvalue) => self.eval_and_read_lvalue(lvalue),

            Constant(ref constant) => {
                use rustc::mir::Literal;
                let mir::Constant { ref literal, .. } = **constant;
                let value = match *literal {
                    Literal::Value { ref value } => self.const_to_value(&value.val)?,
                    Literal::Promoted { index } => {
                        let cid = GlobalId {
                            instance: self.frame().instance,
                            promoted: Some(index),
                        };
                        self.globals.get(&cid).expect("promoted not cached").value
                    }
                };

                Ok(value)
            }
        }
    }

    pub fn read_discriminant_value(
        &mut self,
        lvalue: Lvalue<'tcx>,
        ty: Ty<'tcx>,
    ) -> EvalResult<'tcx, u128> {
        let layout = self.type_layout(ty)?;
        match layout.variants {
            layout::Variants::Single { index } => {
                return Ok(index as u128);
            }
            layout::Variants::Tagged { .. } |
            layout::Variants::NicheFilling { .. } => {},
        }

        let (discr_lvalue, discr) = self.lvalue_field(lvalue, mir::Field::new(0), layout)?;
        let read_discr_lvalue = self.read_lvalue(discr_lvalue)?;
        let raw_discr_primval = self.value_to_primval(
            read_discr_lvalue,
            discr.ty)?;
        let discr_val = match layout.variants {
            layout::Variants::Single { .. } => bug!(),
            layout::Variants::Tagged { .. } => raw_discr_primval.to_bytes()?,
            layout::Variants::NicheFilling {
                dataful_variant,
                ref niche_variants,
                niche_start,
                ..
            } => {
                match raw_discr_primval {
                    PrimVal::Bytes(raw_discr) => {
                        let variants_start = *niche_variants.start() as u128;
                        let variants_end = *niche_variants.end() as u128;
                        let discr = raw_discr.wrapping_sub(niche_start)
                            .wrapping_add(variants_start);

                        if variants_start <= discr && discr <= variants_end {
                            discr
                        } else {
                            dataful_variant as u128
                        }
                    }
                    _ => dataful_variant as u128,
                }
            }
        };

        Ok(discr_val)
    }

    pub(crate) fn write_discriminant_value(
        &mut self,
        dest_ty: Ty<'tcx>,
        dest: Lvalue<'tcx>,
        variant_index: usize,
    ) -> EvalResult<'tcx> {
        let layout = self.type_layout(dest_ty)?;

        match layout.variants {
            layout::Variants::Single { index } => {
                if index != variant_index {
                    // If the layout of an enum is `Single`, all
                    // other variants are necessarily uninhabited.
                    assert_eq!(layout.for_variant(&self, variant_index).abi,
                               layout::Abi::Uninhabited);
                }
            }
            layout::Variants::Tagged { .. } => {
                let discr_val = dest_ty.ty_adt_def().unwrap()
                    .discriminant_for_variant(self.tcx, variant_index).val;

                let (discr_dest, discr) = self.lvalue_field(dest, mir::Field::new(0), layout)?;
                self.write_primval(discr_dest, PrimVal::Bytes(discr_val), discr.ty)?;
            }
            layout::Variants::NicheFilling {
                dataful_variant,
                ref niche_variants,
                niche_start,
                ..
            } => {
                if variant_index != dataful_variant {
                    let (niche_dest, niche) =
                        self.lvalue_field(dest, mir::Field::new(0), layout)?;
                    let niche_value = ((variant_index - *niche_variants.start()) as u128)
                        .wrapping_add(niche_start);
                    self.write_primval(niche_dest, PrimVal::Bytes(niche_value), niche.ty)?;
                }
            }
        }

        Ok(())
    }

    pub(super) fn operand_ty(&self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        self.monomorphize(operand.ty(self.mir(), self.tcx), self.substs())
    }

    fn copy(&mut self, src: PrimVal, dest: PrimVal, ty: Ty<'tcx>) -> EvalResult<'tcx> {
        let size = self.type_size(ty)?.expect("cannot copy from an unsized type");
        let align = self.type_align(ty)?;
        self.memory.copy(src, dest, size, align)?;
        Ok(())
    }

    pub(super) fn force_allocation(
        &mut self,
        lvalue: Lvalue<'tcx>,
    ) -> EvalResult<'tcx, Lvalue<'tcx>> {
        let new_lvalue = match lvalue {
            Lvalue::Local { frame, local } => {
                // -1 since we don't store the return value
                match self.stack[frame].locals[local.index() - 1] {
                    Value::ByRef(ptr) => {
                        Lvalue::from_ptr(ptr)
                    },
                    val => {
                        let ty = self.stack[frame].mir.local_decls[local].ty;
                        let ty = self.monomorphize(ty, self.stack[frame].instance.substs);
                        let substs = self.stack[frame].instance.substs;
                        let ptr = self.alloc_ptr_with_substs(ty, substs)?;
                        self.stack[frame].locals[local.index() - 1] = Value::ByRef(ptr);
                        self.write_value_to_ptr(val, PrimVal::Ptr(ptr), ty)?;
                        Lvalue::from_ptr(ptr)
                    }
                }
            }
            Lvalue::Ptr { .. } => lvalue,
            Lvalue::Global(cid) => {
                let global_val = *self.globals.get(&cid).expect("global not cached");
                match global_val.value {
                    Value::ByRef(ptr) => Lvalue::from_ptr(ptr),
                    _ => {
                        let ptr = self.alloc_ptr_with_substs(global_val.ty, cid.instance.substs)?;
                        self.memory.mark_static(ptr.alloc_id);
                        self.write_value_to_ptr(global_val.value, PrimVal::Ptr(ptr), global_val.ty)?;
                        // see comment on `initialized` field
                        if global_val.initialized {
                            self.memory.mark_static_initalized(ptr.alloc_id, global_val.mutable)?;
                        }
                        let lval = self.globals.get_mut(&cid).expect("already checked");
                        *lval = Global {
                            value: Value::ByRef(ptr),
                            .. global_val
                        };
                        Lvalue::from_ptr(ptr)
                    },
                }
            }
        };
        Ok(new_lvalue)
    }

    /// ensures this Value is not a ByRef
    pub(super) fn follow_by_ref_value(&mut self, value: Value, ty: Ty<'tcx>) -> EvalResult<'tcx, Value> {
        match value {
            Value::ByRef(ptr) => self.read_value(ptr, ty),
            other => Ok(other),
        }
    }

    pub(super) fn value_to_primval(&mut self, value: Value, ty: Ty<'tcx>) -> EvalResult<'tcx, PrimVal> {
        match self.follow_by_ref_value(value, ty)? {
            Value::ByRef(_) => bug!("follow_by_ref_value can't result in `ByRef`"),

            Value::ByVal(primval) => {
                self.ensure_valid_value(primval, ty)?;
                Ok(primval)
            }

            Value::ByValPair(..) => bug!("value_to_primval can't work with fat pointers"),
        }
    }

    pub(super) fn write_primval(
        &mut self,
        dest: Lvalue<'tcx>,
        val: PrimVal,
        dest_ty: Ty<'tcx>,
    ) -> EvalResult<'tcx> {
        self.write_value(ValTy { value: Value::ByVal(val), ty: dest_ty }, dest)
    }

    pub(super) fn write_value(
        &mut self,
        ValTy { value: src_val, ty: dest_ty } : ValTy<'tcx>,
        dest: Lvalue<'tcx>,
    ) -> EvalResult<'tcx> {
        match dest {
            Lvalue::Global(cid) => {
                let dest = *self.globals.get_mut(&cid).expect("global should be cached");
                if !dest.mutable {
                    return Err(EvalError::ModifiedConstantMemory);
                }
                let write_dest = |this: &mut Self, val| {
                    *this.globals.get_mut(&cid).expect("already checked") = Global {
                        value: val,
                        ..dest
                    }
                };
                self.write_value_possibly_by_val(src_val, write_dest, dest.value, dest_ty)
            },

            Lvalue::Ptr { ptr, extra } => {
                assert_eq!(extra, LvalueExtra::None);
                self.write_value_to_ptr(src_val, ptr, dest_ty)
            }

            Lvalue::Local { frame, local } => {
                let dest = self.stack[frame].get_local(local)?;
                self.write_value_possibly_by_val(
                    src_val,
                    |this, val| this.stack[frame].set_local(local, val),
                    dest,
                    dest_ty,
                )
            }
        }
    }

    // The cases here can be a bit subtle. Read carefully!
    fn write_value_possibly_by_val<F: FnOnce(&mut Self, Value)>(
        &mut self,
        src_val: Value,
        write_dest: F,
        old_dest_val: Value,
        dest_ty: Ty<'tcx>,
    ) -> EvalResult<'tcx> {
        if let Value::ByRef(dest_ptr) = old_dest_val {
            // If the value is already `ByRef` (that is, backed by an `Allocation`),
            // then we must write the new value into this allocation, because there may be
            // other pointers into the allocation. These other pointers are logically
            // pointers into the local variable, and must be able to observe the change.
            //
            // Thus, it would be an error to replace the `ByRef` with a `ByVal`, unless we
            // knew for certain that there were no outstanding pointers to this allocation.
            self.write_value_to_ptr(src_val, PrimVal::Ptr(dest_ptr), dest_ty)?;

        } else if let Value::ByRef(src_ptr) = src_val {
            // If the value is not `ByRef`, then we know there are no pointers to it
            // and we can simply overwrite the `Value` in the locals array directly.
            //
            // In this specific case, where the source value is `ByRef`, we must duplicate
            // the allocation, because this is a by-value operation. It would be incorrect
            // if they referred to the same allocation, since then a change to one would
            // implicitly change the other.
            //
            // It is a valid optimization to attempt reading a primitive value out of the
            // source and write that into the destination without making an allocation, so
            // we do so here.
            if let Ok(Some(src_val)) = self.try_read_value(src_ptr, dest_ty) {
                write_dest(self, src_val);
            } else {
                let dest_ptr = self.alloc_ptr(dest_ty)?;
                self.copy(PrimVal::Ptr(src_ptr), PrimVal::Ptr(dest_ptr), dest_ty)?;
                write_dest(self, Value::ByRef(dest_ptr));
            }
        } else {
            // Finally, we have the simple case where neither source nor destination are
            // `ByRef`. We may simply copy the source value over the the destintion.
            write_dest(self, src_val);
        }
        Ok(())
    }

    pub(super) fn write_value_to_ptr(
        &mut self,
        value: Value,
        dest: PrimVal,
        dest_ty: Ty<'tcx>,
    ) -> EvalResult<'tcx> {
        match value {
            Value::ByRef(ptr) => self.copy(PrimVal::Ptr(ptr), dest, dest_ty),
            Value::ByVal(primval) => {
                let size = self.type_size(dest_ty)?.expect("dest type must be sized");
                self.memory.write_primval(dest, primval, size)
            }
            Value::ByValPair(a, b) => self.write_pair_to_ptr(a, b, dest.to_ptr()?, dest_ty),
        }
    }

    pub(super) fn write_pair_to_ptr(
        &mut self,
        a: PrimVal,
        b: PrimVal,
        ptr: MemoryPointer,
        ty: Ty<'tcx>
    ) -> EvalResult<'tcx> {
        let mut layout = self.type_layout(ty)?;
        let mut _packed = self.layout_is_packed(layout);

        // er, this is kinda fishy
        while layout.fields.count() != 2
            || layout.field(&self, 0)?.size.bytes() == 0
            || layout.field(&self, 1)?.size.bytes() == 0 {
                layout = layout.field(&self, 0)?;
                _packed |= self.layout_is_packed(layout);
            }

        assert_eq!(layout.fields.count(), 2);
        let field_0 = layout.field(&self, 0)?;
        let field_1 = layout.field(&self, 1)?;
//        assert_eq!(
//            field_0.is_packed(),
//            field_1.is_packed(),
//            "the two fields must agree on being packed"
//        );
//        _packed |= field_0.is_packed();
        let field_0_ptr = ptr.offset(layout.fields.offset(0).bytes(), (&self).data_layout())?.into();
        let field_1_ptr = ptr.offset(layout.fields.offset(1).bytes(), (&self).data_layout())?.into();

        self.memory.write_primval(PrimVal::Ptr(field_0_ptr), a, field_0.size.bytes())?;
        self.memory.write_primval(PrimVal::Ptr(field_1_ptr), b, field_1.size.bytes())?;
        Ok(())
    }

    pub fn ty_to_primval_kind(&self, ty: Ty<'tcx>) -> EvalResult<'tcx, PrimValKind> {
        use syntax::ast::FloatTy;

        let kind = match ty.sty {
            ty::TyBool => PrimValKind::Bool,
            ty::TyChar => PrimValKind::Char,

            ty::TyInt(int_ty) => {
                use syntax::ast::IntTy::*;
                let size = match int_ty {
                    I8 => 1,
                    I16 => 2,
                    I32 => 4,
                    I64 => 8,
                    I128 => 16,
                    Isize => self.memory.pointer_size(),
                };
                PrimValKind::from_int_size(size)
            }

            ty::TyUint(uint_ty) => {
                use syntax::ast::UintTy::*;
                let size = match uint_ty {
                    U8 => 1,
                    U16 => 2,
                    U32 => 4,
                    U64 => 8,
                    U128 => 16,
                    Usize => self.memory.pointer_size(),
                };
                PrimValKind::from_uint_size(size)
            }

            ty::TyFloat(FloatTy::F32) => PrimValKind::F32,
            ty::TyFloat(FloatTy::F64) => PrimValKind::F64,

            ty::TyFnPtr(_) => PrimValKind::FnPtr,

            ty::TyRawPtr(ty::TypeAndMut { ty, .. }) |
            ty::TyRef(_, ty, _) if self.type_is_sized(ty) => PrimValKind::Ptr,

            ty::TyAdt(ref def, _) if def.is_box() => PrimValKind::Ptr,

            ty::TyAdt(..) => {
                match self.type_layout(ty)?.abi {
                    layout::Abi::Scalar(ref scalar) => {
                        use rustc::ty::layout::Primitive::*;
                        match scalar.value {
                            Int(i, false) => PrimValKind::from_uint_size(i.size().bytes()),
                            Int(i, true) => PrimValKind::from_int_size(i.size().bytes()),
                            F32 => PrimValKind::F32,
                            F64 => PrimValKind::F64,
                            Pointer => PrimValKind::Ptr,
                        }
                    }

                    _ => return Err(EvalError::TypeNotPrimitive(ty)),
                }
            }

            _ => return Err(EvalError::TypeNotPrimitive(ty)),
        };

        Ok(kind)
    }

    fn ensure_valid_value(&self, val: PrimVal, ty: Ty<'tcx>) -> EvalResult<'tcx> {
        match ty.sty {
            ty::TyBool if val.is_concrete() && val.to_bytes()? > 1 => Err(EvalError::InvalidBool),

            ty::TyChar if val.is_concrete() && ::std::char::from_u32(val.to_bytes()? as u32).is_none()
                => Err(EvalError::InvalidChar(val.to_bytes()? as u32 as u128)),

            _ => Ok(()),
        }
    }

    pub(super) fn read_value(&mut self, ptr: MemoryPointer, ty: Ty<'tcx>) -> EvalResult<'tcx, Value> {
        if let Some(val) = self.try_read_value(ptr, ty)? {
            Ok(val)
        } else {
            bug!("primitive read failed for type: {:?}", ty);
        }
    }

    pub(crate) fn read_ptr(&mut self, ptr: MemoryPointer, pointee_ty: Ty<'tcx>) -> EvalResult<'tcx, Value> {
        let p = self.memory.read_ptr(ptr)?;
        if self.type_is_sized(pointee_ty) {
            Ok(Value::ByVal(p))
        } else {
            trace!("reading fat pointer extra of type {}", pointee_ty);
            let extra = ptr.offset(self.memory.pointer_size(), self.memory.layout)?;
            let extra = match self.tcx.struct_tail(pointee_ty).sty {
                ty::TyDynamic(..) => self.memory.read_ptr(extra)?,
                ty::TySlice(..) |
                ty::TyStr => {
                    let usize_bytes = self.memory.pointer_size();
                    if self.memory.points_to_concrete(extra, usize_bytes)? {
                        PrimVal::from_u128(self.memory.read_usize(extra)? as u128)
                    } else {
                        self.memory.read_abstract(PrimVal::Ptr(extra), usize_bytes)?
                    }
                }
                _ => bug!("unsized primval ptr read from {:?}", pointee_ty),
            };
            Ok(Value::ByValPair(p, extra))
        }
    }

    fn try_read_value(&mut self, ptr: MemoryPointer, ty: Ty<'tcx>) -> EvalResult<'tcx, Option<Value>> {
        use syntax::ast::FloatTy;

        if !ptr.has_concrete_offset() {
            return Ok(None);
        }

        let val = match ty.sty {
            ty::TyBool => {
                if !self.memory.points_to_concrete(ptr, 1)? {
                    self.memory.read_abstract(PrimVal::Ptr(ptr), 1)?
                } else {
                    self.memory.read_bool(ptr)?
                }
            }
            ty::TyChar => {
                if !self.memory.points_to_concrete(ptr, 4)? {
                    self.memory.read_abstract(PrimVal::Ptr(ptr), 4)?
                } else {
                    let c = self.memory.read_uint(ptr, 4)? as u32;
                    match ::std::char::from_u32(c) {
                        Some(ch) => PrimVal::from_char(ch),
                        None => return Err(EvalError::InvalidChar(c as u128)),
                    }
                }
            }

            ty::TyInt(int_ty) => {
                use syntax::ast::IntTy::*;
                let size = match int_ty {
                    I8 => 1,
                    I16 => 2,
                    I32 => 4,
                    I64 => 8,
                    I128 => 16,
                    Isize => self.memory.pointer_size(),
                };

                if !self.memory.points_to_concrete(ptr, size)? {
                    self.memory.read_abstract(PrimVal::Ptr(ptr), size)?
                } else {
                    // if we transmute a ptr to an isize, reading it back into a primval shouldn't panic
                    // Due to read_ptr ignoring the sign, we need to jump around some hoops
                    match self.memory.read_int(ptr, size) {
                        Err(EvalError::ReadPointerAsBytes) if size == self.memory.pointer_size() => self.memory.read_ptr(ptr)?,
                        other => PrimVal::from_i128(other?),
                    }
                }
            }

            ty::TyUint(uint_ty) => {
                use syntax::ast::UintTy::*;
                let size = match uint_ty {
                    U8 => 1,
                    U16 => 2,
                    U32 => 4,
                    U64 => 8,
                    U128 => 16,
                    Usize => self.memory.pointer_size(),
                };

                if !self.memory.points_to_concrete(ptr, size)? {
                    self.memory.read_abstract(PrimVal::Ptr(ptr), size)?
                } else {
                    PrimVal::from_u128(self.memory.read_uint(ptr, size)?)
                }
            }

            ty::TyFloat(FloatTy::F32) => PrimVal::from_f32(self.memory.read_f32(ptr)?),
            ty::TyFloat(FloatTy::F64) => PrimVal::from_f64(self.memory.read_f64(ptr)?),

            ty::TyFnPtr(_) => self.memory.read_ptr(ptr)?,
            ty::TyRef(_, ty, _) |
            ty::TyRawPtr(ty::TypeAndMut {ty, ..}) => return self.read_ptr(ptr, ty).map(Some),

            ty::TyAdt(def, _) => {
                if def.is_box() {
                    return self.read_ptr(ptr, ty.boxed_ty()).map(Some);
                }

                if let layout::Abi::Scalar(ref scalar) = self.type_layout(ty)?.abi {
                    let mut signed = false;
                    if let layout::Int(_, s) = scalar.value {
                        signed = s;
                    }
                    let size = scalar.value.size(&self).bytes();
                    if self.memory.points_to_concrete(ptr, size)? {
                        self.memory.read_primval(ptr, size, signed)?
                    } else {
                        return Ok(None);
                    }
                } else {
                    return Ok(None);
                }
            },

            _ => return Ok(None),
        };

        Ok(Some(Value::ByVal(val)))
    }

    pub(super) fn frame(&self) -> &Frame<'tcx> {
        self.stack.last().expect("no call frames exist")
    }

    pub(super) fn frame_mut(&mut self) -> &mut Frame<'tcx> {
        self.stack.last_mut().expect("no call frames exist")
    }

    pub(super) fn mir(&self) -> &'tcx mir::Mir<'tcx> {
        self.frame().mir
    }

    pub(super) fn substs(&self) -> &'tcx Substs<'tcx> {
        self.frame().instance.substs
    }

    fn unsize_into_ptr(
        &mut self,
        src: Value,
        src_ty: Ty<'tcx>,
        dest: Lvalue<'tcx>,
        dest_ty: Ty<'tcx>,
        sty: Ty<'tcx>,
        dty: Ty<'tcx>,
    ) -> EvalResult<'tcx> {
        // A<Struct> -> A<Trait> conversion
        let (src_pointee_ty, dest_pointee_ty) = self.tcx.struct_lockstep_tails(sty, dty);

        match (&src_pointee_ty.sty, &dest_pointee_ty.sty) {
            (&ty::TyArray(_, length), &ty::TySlice(_)) => {
                let ptr = src.read_ptr(&self.memory)?;
                let len = PrimVal::from_u128(length.val.to_raw_bits().unwrap());
                self.write_value(ValTy { value: Value::ByValPair(ptr, len), ty: dest_ty }, dest)
            }
            (&ty::TyDynamic(..), &ty::TyDynamic(..)) => {
                // For now, upcasts are limited to changes in marker
                // traits, and hence never actually require an actual
                // change to the vtable.
                self.write_value(ValTy { value: src, ty: dest_ty }, dest)
            },
            (_, &ty::TyDynamic(ref data, _)) => {
                let trait_ref = data.principal().unwrap().with_self_ty(self.tcx, src_pointee_ty);
                let trait_ref = self.tcx.erase_regions(&trait_ref);
                let vtable = self.get_vtable(src_pointee_ty, trait_ref)?;
                let ptr = src.read_ptr(&self.memory)?;
                let extra = PrimVal::Ptr(vtable);
                self.write_value(ValTy { value: Value::ByValPair(ptr, extra), ty: dest_ty}, dest)
            },

            _ => bug!("invalid unsizing {:?} -> {:?}", src_ty, dest_ty),
        }
    }

    fn unsize_into(
        &mut self,
        src: Value,
        src_ty: Ty<'tcx>,
        dest: Lvalue<'tcx>,
        dest_ty: Ty<'tcx>,
    ) -> EvalResult<'tcx> {
        match (&src_ty.sty, &dest_ty.sty) {
            (&ty::TyRef(_, s, _), &ty::TyRef(_, d, _)) |
            (&ty::TyRef(_, s, _), &ty::TyRawPtr(ty::TypeAndMut {ty: d, ..})) |
            (&ty::TyRawPtr(ty::TypeAndMut {ty: s, ..}), &ty::TyRawPtr(ty::TypeAndMut {ty: d, ..})) =>
                self.unsize_into_ptr(src, src_ty, dest, dest_ty, s, d),
            (&ty::TyAdt(def_a, substs_a), &ty::TyAdt(def_b, substs_b)) => {
                if def_a.is_box() || def_b.is_box() {
                    if !def_a.is_box() || !def_b.is_box() {
                        panic!("invalid unsizing between {:?} -> {:?}", src_ty, dest_ty);
                    }
                    return self.unsize_into_ptr(src, src_ty, dest, dest_ty, src_ty.boxed_ty(), dest_ty.boxed_ty());
                }
                if self.ty_to_primval_kind(src_ty).is_ok() {
                    let sty = self.get_field_ty(src_ty, 0)?.ty;
                    let dty = self.get_field_ty(dest_ty, 0)?.ty;
                    return self.unsize_into(src, sty, dest, dty);
                }
                // unsizing of generic struct with pointer fields
                // Example: `Arc<T>` -> `Arc<Trait>`
                // here we need to increase the size of every &T thin ptr field to a fat ptr

                assert_eq!(def_a, def_b);

                let src_fields = def_a.variants[0].fields.iter();
                let dst_fields = def_b.variants[0].fields.iter();

                //let src = adt::MaybeSizedValue::sized(src);
                //let dst = adt::MaybeSizedValue::sized(dst);
                let src_ptr = match src {
                    Value::ByRef(ptr) => ptr,
                    _ => bug!("expected pointer, got {:?}", src),
                };

                // FIXME(solson)
                let dest = self.force_allocation(dest)?.to_ptr()?;
                let iter = src_fields.zip(dst_fields).enumerate();
                for (i, (src_f, dst_f)) in iter {
                    let src_fty = monomorphize_field_ty(self.tcx, src_f, substs_a);
                    let dst_fty = monomorphize_field_ty(self.tcx, dst_f, substs_b);
                    if self.type_size(dst_fty)? == Some(0) {
                        continue;
                    }
                    let src_field_offset = self.get_field_offset(src_ty, i)?.bytes();
                    let dst_field_offset = self.get_field_offset(dest_ty, i)?.bytes();
                    let src_f_ptr = src_ptr.offset(src_field_offset, self.memory.layout)?;
                    let dst_f_ptr = dest.offset(dst_field_offset, self.memory.layout)?;
                    if src_fty == dst_fty {
                        self.copy(PrimVal::Ptr(src_f_ptr), PrimVal::Ptr(dst_f_ptr), src_fty)?;
                    } else {
                        self.unsize_into(Value::ByRef(src_f_ptr), src_fty, Lvalue::from_ptr(dst_f_ptr), dst_fty)?;
                    }
                }
                Ok(())
            }
            _ => bug!("unsize_into: invalid conversion: {:?} -> {:?}", src_ty, dest_ty),
        }
    }

    pub(super) fn dump_local(&self, lvalue: Lvalue<'tcx>) {
        if let Lvalue::Local { frame, local } = lvalue {
            let mut allocs = Vec::new();
            let mut msg = format!("{:?}", local);
            let last_frame = self.stack.len() - 1;
            if frame != last_frame {
                write!(msg, " ({} frames up)", last_frame - frame).unwrap();
            }
            write!(msg, ":").unwrap();

            match self.stack[frame].get_local(local) {
                Err(err) => {
                    panic!("Failed to access local: {:?}", err);
                }
                Ok(Value::ByRef(ptr)) => {
                    write!(msg, " by ref:").unwrap();
                    allocs.push(ptr.alloc_id);
                }
                Ok(Value::ByVal(val)) => {
                    write!(msg, " {:?}", val).unwrap();
                    if let PrimVal::Ptr(ptr) = val { allocs.push(ptr.alloc_id); }
                }
                Ok(Value::ByValPair(val1, val2)) => {
                    write!(msg, " ({:?}, {:?})", val1, val2).unwrap();
                    if let PrimVal::Ptr(ptr) = val1 { allocs.push(ptr.alloc_id); }
                    if let PrimVal::Ptr(ptr) = val2 { allocs.push(ptr.alloc_id); }
                }
            }

            trace!("{}", msg);
            self.memory.dump_allocs(allocs);
        }
    }

    /// Convenience function to ensure correct usage of globals and code-sharing with locals.
    pub fn modify_global<F>(&mut self, cid: GlobalId<'tcx>, f: F) -> EvalResult<'tcx>
        where F: FnOnce(&mut Self, Value) -> EvalResult<'tcx, Value>,
    {
        let mut val = *self.globals.get(&cid).expect("global not cached");
        if !val.mutable {
            return Err(EvalError::ModifiedConstantMemory);
        }
        val.value = f(self, val.value)?;
        *self.globals.get_mut(&cid).expect("already checked") = val;
        Ok(())
    }

    /// Convenience function to ensure correct usage of locals and code-sharing with globals.
    pub fn modify_local<F>(
        &mut self,
        frame: usize,
        local: mir::Local,
        f: F,
    ) -> EvalResult<'tcx>
        where F: FnOnce(&mut Self, Value) -> EvalResult<'tcx, Value>,
    {
        let val = self.stack[frame].get_local(local)?;
        let new_val = f(self, val)?;
        self.stack[frame].set_local(local, new_val);
        // FIXME(solson): Run this when setting to Undef? (See previous version of this code.)
        // if let Value::ByRef(ptr) = self.stack[frame].get_local(local) {
        //     self.memory.deallocate(ptr)?;
        // }
        Ok(())
    }
}

impl<'tcx> Frame<'tcx> {
    pub fn get_local(&self, local: mir::Local) -> EvalResult<'tcx, Value> {
        // Subtract 1 because we don't store a value for the ReturnPointer, the local with index 0.
        Ok(self.locals[local.index() - 1])
    }

    fn set_local(&mut self, local: mir::Local, value: Value) {
        // Subtract 1 because we don't store a value for the ReturnPointer, the local with index 0.
        self.locals[local.index() - 1] = value;
    }
}

// TODO(solson): Upstream these methods into rustc::ty::layout.

pub(super) trait IntegerExt {
    fn size(self) -> Size;
}

impl IntegerExt for layout::Integer {
    fn size(self) -> Size {
        use rustc::ty::layout::Integer::*;
        match self {
            I8 => Size::from_bits(8),
            I16 => Size::from_bits(16),
            I32 => Size::from_bits(32),
            I64 => Size::from_bits(64),
            I128 => Size::from_bits(128),
        }
    }
}


pub fn monomorphize_field_ty<'a, 'tcx:'a >(tcx: TyCtxt<'a, 'tcx, 'tcx>, f: &ty::FieldDef, substs: &'tcx Substs<'tcx>) -> Ty<'tcx> {
    let substituted = f.ty(tcx, substs);
    tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), substituted)
}

pub fn is_inhabited<'a, 'tcx: 'a>(tcx: TyCtxt<'a, 'tcx, 'tcx>, ty: Ty<'tcx>) -> bool {
    !tcx.is_ty_uninhabited_from_all_modules(ty)
}

pub trait IntoValTyPair<'tcx> {
    fn into_val_ty_pair<'a>(self, ecx: &mut EvalContext<'a, 'tcx>) -> EvalResult<'tcx, (Value, Ty<'tcx>)> where 'tcx: 'a;
}

impl<'tcx> IntoValTyPair<'tcx> for (Value, Ty<'tcx>) {
    fn into_val_ty_pair<'a>(self, _: &mut EvalContext<'a, 'tcx>) -> EvalResult<'tcx, (Value, Ty<'tcx>)> where 'tcx: 'a {
        Ok(self)
    }
}

impl<'b, 'tcx: 'b> IntoValTyPair<'tcx> for &'b mir::Operand<'tcx> {
    fn into_val_ty_pair<'a>(self, ecx: &mut EvalContext<'a, 'tcx>) -> EvalResult<'tcx, (Value, Ty<'tcx>)> where 'tcx: 'a {
        let value = ecx.eval_operand(self)?;
        let value_ty = ecx.operand_ty(self);
        Ok((value, value_ty))
    }
}

/// Monomorphizes a type from the AST by first applying the in-scope
/// substitutions and then normalizing any associated types.
pub fn apply_param_substs<'a, 'tcx, T>(tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                       param_substs: &Substs<'tcx>,
                                       value: &T)
                                       -> T
    where T: TypeFoldable<'tcx>
{
    debug!("apply_param_substs(param_substs={:?}, value={:?})", param_substs, value);
    let substituted = value.subst(tcx, param_substs);
    let substituted = tcx.erase_regions(&substituted);
    AssociatedTypeNormalizer{ tcx }.fold(&substituted)
}


struct AssociatedTypeNormalizer<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
}

impl<'a, 'tcx> AssociatedTypeNormalizer<'a, 'tcx> {
    fn fold<T: TypeFoldable<'tcx>>(&mut self, value: &T) -> T {
        if !value.has_projections() {
            value.clone()
        } else {
            value.fold_with(self)
        }
    }
}

impl<'a, 'tcx> ::rustc::ty::fold::TypeFolder<'tcx, 'tcx> for AssociatedTypeNormalizer<'a, 'tcx> {
    fn tcx<'c>(&'c self) -> TyCtxt<'c, 'tcx, 'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        if !ty.has_projections() {
            ty
        } else {
            self.tcx.normalize_erasing_regions(ty::ParamEnv::reveal_all(), &ty)
        }
    }
}

pub fn resolve_drop_in_place<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    ty: Ty<'tcx>,
) -> ty::Instance<'tcx>
{
    let def_id = tcx.require_lang_item(::rustc::middle::lang_items::DropInPlaceFnLangItem);
    let substs = tcx.intern_substs(&[Kind::from(ty)]);
    ::rustc::ty::Instance::resolve(tcx, ::rustc::ty::ParamEnv::empty(), def_id, substs).unwrap()
}
