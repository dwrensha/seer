use rustc::mir;
use rustc::ty::layout::{HasDataLayout, TyLayout};
use rustc::ty::{self, Ty};
use rustc_data_structures::indexed_vec::Idx;

use error::{EvalError, EvalResult};
use eval_context::{EvalContext};
use memory::{MemoryPointer};
use value::{PrimVal, PrimValKind, Value};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Lvalue<'tcx> {
    /// An lvalue referring to a value allocated in the `Memory` system.
    Ptr {
        ptr: PrimVal,
        extra: LvalueExtra,
    },

    /// An lvalue referring to a value on the stack. Represented by a stack frame index paired with
    /// a Mir local index.
    Local {
        frame: usize,
        local: mir::Local,
    },

    /// An lvalue referring to a global
    Global(GlobalId<'tcx>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum LvalueExtra {
    None,
    Length(PrimVal),
    Vtable(MemoryPointer),
    DowncastVariant(usize),
}

/// Uniquely identifies a specific constant or static.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct GlobalId<'tcx> {
    /// For a constant or static, the `Instance` of the item itself.
    /// For a promoted global, the `Instance` of the function they belong to.
    pub(super) instance: ty::Instance<'tcx>,

    /// The index for promoted globals within their function's `Mir`.
    pub(super) promoted: Option<mir::Promoted>,
}

#[derive(Copy, Clone, Debug)]
pub struct Global<'tcx> {
    pub(super) value: Value,
    /// Only used in `force_allocation` to ensure we don't mark the memory
    /// before the static is initialized. It is possible to convert a
    /// global which initially is `Value::ByVal(PrimVal::Undef)` and gets
    /// lifted to an allocation before the static is fully initialized
    pub(super) initialized: bool,
    pub(super) mutable: bool,
    pub(super) ty: Ty<'tcx>,
}

impl<'tcx> Lvalue<'tcx> {
    /// Produces an Lvalue that will error if attempted to be read from
    pub fn undef() -> Self {
        Self::from_primval_ptr(PrimVal::Undef)
    }

    fn from_primval_ptr(ptr: PrimVal) -> Self {
        Lvalue::Ptr { ptr, extra: LvalueExtra::None }
    }

    pub fn from_ptr(ptr: MemoryPointer) -> Self {
        Self::from_primval_ptr(PrimVal::Ptr(ptr))
    }

    pub(super) fn to_ptr_and_extra(self) -> (PrimVal, LvalueExtra) {
        match self {
            Lvalue::Ptr { ptr, extra } => (ptr, extra),
            _ => bug!("to_ptr_and_extra: expected Lvalue::Ptr, got {:?}", self),

        }
    }

    pub(super) fn to_ptr(self) -> EvalResult<'tcx, MemoryPointer> {
        let (ptr, extra) = self.to_ptr_and_extra();
        assert_eq!(extra, LvalueExtra::None);
        ptr.to_ptr()
    }

    pub(super) fn elem_ty_and_len(self, ty: Ty<'tcx>) -> (Ty<'tcx>, u64) {
        match ty.sty {
            ty::TyArray(elem, n) => (elem, n.val.unwrap_u64()),

            ty::TySlice(elem) => {
                match self {
                    Lvalue::Ptr { extra: LvalueExtra::Length(len), .. } => {
                        match len {
                            PrimVal::Bytes(n) => (elem, n as u64),
                            _ => unimplemented!(),
                        }
                    }
                    _ => bug!("elem_ty_and_len of a TySlice given non-slice lvalue: {:?}", self),
                }
            }

            _ => bug!("elem_ty_and_len expected array or slice, got {:?}", ty),
        }
    }
}

impl<'tcx> Global<'tcx> {
    pub(super) fn uninitialized(ty: Ty<'tcx>) -> Self {
        Global {
            value: Value::ByVal(PrimVal::Undef),
            mutable: true,
            ty,
            initialized: false,
        }
    }
}

impl<'a, 'tcx> EvalContext<'a, 'tcx> {
    /// Reads a value from the lvalue without going through the intermediate step of obtaining
    /// a `miri::Lvalue`
    pub fn try_read_lvalue(&mut self, lvalue: &mir::Place<'tcx>) -> EvalResult<'tcx, Option<Value>> {
        use rustc::mir::Place::*;
        match *lvalue {
            // Might allow this in the future, right now there's no way to do this from Rust code anyway
            Local(mir::RETURN_PLACE) => Err(EvalError::ReadFromReturnPointer),
            // Directly reading a local will always succeed
            Local(local) => self.frame().get_local(local).map(Some),
            // Directly reading a static will always succeed
            Static(ref static_) => {
                let instance = ty::Instance::mono(self.tcx, static_.def_id);
                let cid = GlobalId { instance, promoted: None };
                Ok(Some(self.globals.get(&cid).expect("global not cached").value))
            },
            Projection(ref proj) => self.try_read_lvalue_projection(proj),
        }
    }

    fn try_read_lvalue_projection(&mut self, proj: &mir::PlaceProjection<'tcx>) -> EvalResult<'tcx, Option<Value>> {
        use rustc::mir::ProjectionElem::*;
        let base = match self.try_read_lvalue(&proj.base)? {
            Some(base) => base,
            None => return Ok(None),
        };
        let base_ty = self.lvalue_ty(&proj.base);
        match proj.elem {
            Field(field, _) => match (field.index(), base) {
                // the only field of a struct
                (0, Value::ByVal(val)) => Ok(Some(Value::ByVal(val))),
                // split fat pointers, 2 element tuples, ...
                (0...1, Value::ByValPair(a, b)) if self.get_field_count(base_ty)? == 2 => {
                    let val = [a, b][field.index()];
                    Ok(Some(Value::ByVal(val)))
                },
                // the only field of a struct is a fat pointer
                (0, Value::ByValPair(..)) => Ok(Some(base)),
                _ => Ok(None),
            },
            // The NullablePointer cases should work fine, need to take care for normal enums
            Downcast(..) |
            Subslice { .. } |
            // reading index 0 or index 1 from a ByVal or ByVal pair could be optimized
            ConstantIndex { .. } | Index(_) |
            // No way to optimize this projection any better than the normal lvalue path
            Deref => Ok(None),
        }
    }

    pub(super) fn eval_and_read_lvalue(&mut self, lvalue: &mir::Place<'tcx>) -> EvalResult<'tcx, Value> {
        let ty = self.lvalue_ty(lvalue);
        // Shortcut for things like accessing a fat pointer's field,
        // which would otherwise (in the `eval_lvalue` path) require moving a `ByValPair` to memory
        // and returning an `Lvalue::Ptr` to it
        if let Some(val) = self.try_read_lvalue(lvalue)? {
            return Ok(val);
        }
        let lvalue = self.eval_lvalue(lvalue)?;

        if ty.is_never() {
            return Err(EvalError::Unreachable);
        }

        match lvalue {
            Lvalue::Ptr { ptr, extra } => {
                assert_eq!(extra, LvalueExtra::None);
                Ok(Value::ByRef(ptr.to_ptr()?))
            }
            Lvalue::Local { frame, local } => {
                self.stack[frame].get_local(local)
            }
            Lvalue::Global(cid) => {
                Ok(self.globals.get(&cid).expect("global not cached").value)
            }
        }
    }

    pub fn read_lvalue(&self, lvalue: Lvalue) -> EvalResult<'tcx, Value> {
        match lvalue {
            Lvalue::Ptr { ptr, extra } => {
                assert_eq!(extra, LvalueExtra::None);
                Ok(Value::ByRef(ptr.to_ptr()?))
            }
            Lvalue::Local { frame, local } => self.stack[frame].get_local(local),
            Lvalue::Global(cid) => {
                Ok(self.globals.get(&cid).expect("global not cached").value)
            }
        }
    }

    pub(super) fn eval_lvalue(&mut self, mir_lvalue: &mir::Place<'tcx>) -> EvalResult<'tcx, Lvalue<'tcx>> {
        use rustc::mir::Place::*;
        let lvalue = match *mir_lvalue {
            Local(mir::RETURN_PLACE) => self.frame().return_lvalue,
            Local(local) => Lvalue::Local { frame: self.stack.len() - 1, local },

            Static(ref static_) => {
                let instance = ty::Instance::mono(self.tcx, static_.def_id);
                Lvalue::Global(GlobalId { instance, promoted: None })
            }

            Projection(ref proj) => {
                let ty = self.lvalue_ty(&proj.base);
                let lvalue = self.eval_lvalue(&proj.base)?;
                return self.eval_lvalue_projection(lvalue, ty, &proj.elem);
            }
        };

        if log_enabled!(::log::Level::Trace) {
            self.dump_local(lvalue);
        }

        Ok(lvalue)
    }

    pub fn lvalue_field(
        &mut self,
        base: Lvalue<'tcx>,
        field: mir::Field,
        base_layout: TyLayout<'tcx>,
    ) -> EvalResult<'tcx, (Lvalue<'tcx>, TyLayout<'tcx>)> {
        let base_layout: TyLayout<'tcx> = match base {
            Lvalue::Ptr { extra: LvalueExtra::DowncastVariant(n), .. } => {
                base_layout.for_variant(&self, n)
            }
            _ => base_layout,
        };
        let field_index = field.index();
        let field = base_layout.field(&self, field_index)?;
        let offset = base_layout.fields.offset(field_index);

        // Do not allocate in trivial cases
        let (base_ptr, base_extra) = match base {
            Lvalue::Ptr { ptr, extra } => (ptr, extra),
            Lvalue::Local { frame, local } => {
                match self.stack[frame].get_local(local)? {
                    // in case the field covers the entire type, just return the value
                    Value::ByVal(_) if offset.bytes() == 0 &&
                                       field.size == base_layout.size => {
                        return Ok((base, field));
                    }
                    Value::ByRef { .. } |
                    Value::ByValPair(..) |
                    Value::ByVal(_) => self.force_allocation(base)?.to_ptr_and_extra(),
                }
            }
            Lvalue::Global(_cid) => {
                self.force_allocation(base)?.to_ptr_and_extra()
            }
        };

        let offset = match base_extra {
            LvalueExtra::Vtable(tab) => {
                let (_, align) = self.size_and_align_of_dst(
                    base_layout.ty,
                    base_ptr.to_ptr()?.to_value_with_vtable(tab),
                )?;
                offset.abi_align(align).bytes()
            }
            _ => offset.bytes(),
        };

        let ptr = base_ptr.to_ptr()?.offset(offset, (&self).data_layout())?;
        // if we were unaligned, stay unaligned
        // no matter what we were, if we are packed, we must not be aligned anymore
        //ptr.aligned &= !base_layout.is_packed();

        let extra = if !field.is_unsized() {
            LvalueExtra::None
        } else {
            match base_extra {
                LvalueExtra::None => bug!("expected fat pointer"),
                LvalueExtra::DowncastVariant(..) => {
                    bug!("Rust doesn't support unsized fields in enum variants")
                }
                LvalueExtra::Vtable(_) |
                LvalueExtra::Length(_) => {}
            }
            base_extra
        };

        Ok((Lvalue::Ptr { ptr: PrimVal::Ptr(ptr), extra }, field))
    }

    pub(super) fn val_to_lvalue(&self, val: Value, ty: Ty<'tcx>) -> EvalResult<'tcx, Lvalue<'tcx>> {
        Ok(match self.tcx.struct_tail(ty).sty {
            ty::TyDynamic(..) => {
                let (ptr, vtable) = val.into_ptr_vtable_pair(&self.memory)?;
                Lvalue::Ptr {
                    ptr: ptr,
                    extra: LvalueExtra::Vtable(vtable),
                }
            }
            ty::TyStr | ty::TySlice(_) => {
                let (ptr, len) = val.into_slice(&self.memory)?;
                Lvalue::Ptr {
                    ptr: ptr,
                    extra: LvalueExtra::Length(len),
                }
            }
            _ => Lvalue::from_primval_ptr(val.read_ptr(&self.memory)?),
        })
    }

    pub(super) fn lvalue_index(
        &mut self,
        base: Lvalue<'tcx>,
        outer_ty: Ty<'tcx>,
        idx: PrimVal,
    ) -> EvalResult<'tcx, Lvalue<'tcx>> {
        // Taking the outer type here may seem odd; it's needed because for array types, the outer type gives away the length.
        let base = self.force_allocation(base)?;
        let (base_ptr, _) = base.to_ptr_and_extra();

        let (elem_ty, len) = base.elem_ty_and_len(outer_ty);
        let elem_size = self.type_size(elem_ty)?.expect(
            "slice element must be sized",
        );
        if idx.is_concrete() {
            let n = idx.to_u64()?;
            assert!(
                n < len,
                "Tried to access element {} of array/slice with length {}",
                n,
                len
            );
            let ptr_primval = match (base_ptr.to_ptr(), elem_size) {
                (Ok(p), _) => PrimVal::Ptr(p.offset(n * elem_size, (&self).data_layout())?),
                (Err(_), 0) => base_ptr,
                (Err(e), _) => return Err(e),
            };
            Ok(Lvalue::Ptr {
                ptr: ptr_primval,
                extra: LvalueExtra::None,
            })
        } else {
            let ptr_primval = if elem_size == 0 {
                base_ptr
            } else {
                let p = base_ptr.to_ptr()?;
                let byte_index = self.memory.constraints.add_binop_constraint(
                    mir::BinOp::Mul,
                    idx,
                    PrimVal::Bytes(elem_size as u128),
                    PrimValKind::U64);

                let offset = self.memory.constraints.add_binop_constraint(
                    mir::BinOp::Add,
                    p.offset.as_primval(),
                    byte_index,
                    PrimValKind::U64);
                PrimVal::Ptr(MemoryPointer::with_primval_offset(p.alloc_id, offset))
            };

            Ok(Lvalue::Ptr {
                ptr: ptr_primval,
                extra: LvalueExtra::None,
            })
        }
    }

    pub(super) fn lvalue_downcast(
        &mut self,
        base: Lvalue<'tcx>,
        variant: usize,
    ) -> EvalResult<'tcx, Lvalue<'tcx>> {
        // FIXME(solson)
        let base = self.force_allocation(base)?;
        let (ptr, _) = base.to_ptr_and_extra();
        let extra = LvalueExtra::DowncastVariant(variant);
        Ok(Lvalue::Ptr { ptr, extra })
    }

    pub(super) fn eval_lvalue_projection(
        &mut self,
        base: Lvalue<'tcx>,
        base_ty: Ty<'tcx>,
        proj_elem: &mir::ProjectionElem<'tcx, mir::Local, Ty<'tcx>>,
    ) -> EvalResult<'tcx, Lvalue<'tcx>> {
        use rustc::mir::ProjectionElem::*;
        let (ptr, extra) = match *proj_elem {
            Field(field, _) => {
                let layout = self.type_layout(base_ty)?;
                return Ok(self.lvalue_field(base, field, layout)?.0);
            }

            Downcast(_, variant) => {
                return self.lvalue_downcast(base, variant);
            }

            Deref => {
                let val = self.read_lvalue(base)?;

                let pointee_type = match base_ty.sty {
                    ty::TyRawPtr(ty::TypeAndMut {ty, ..}) |
                    ty::TyRef(_, ty, _) => ty,
                    ty::TyAdt(def, _) if def.is_box() => base_ty.boxed_ty(),
                    _ => bug!("can only deref pointer types"),
                };

                trace!("deref to {} on {:?}", pointee_type, val);

                return self.val_to_lvalue(val, pointee_type);
            }

            Index(local) => {
                let value = self.frame().get_local(local)?;
                let ty = self.tcx.types.usize;
                let idx = self.value_to_primval(value, ty)?;
                return self.lvalue_index(base, base_ty, idx);
            }

            ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                // FIXME(solson)
                let base = self.force_allocation(base)?;
                let (base_ptr, _) = base.to_ptr_and_extra();

                let (elem_ty, n) = base.elem_ty_and_len(base_ty);
                let elem_size = self.type_size(elem_ty)?.expect(
                    "sequence element must be sized",
                );
                assert!(n >= min_length as u64);

                let index = if from_end {
                    n - u64::from(offset)
                } else {
                    u64::from(offset)
                };

                let ptr = base_ptr.to_ptr()?.offset(index * elem_size, (&self).data_layout())?;
                (ptr, LvalueExtra::None)
            }

            Subslice { from, to } => {
                // FIXME(solson)
                let base = self.force_allocation(base)?;
                let (base_ptr, _) = base.to_ptr_and_extra();

                let (elem_ty, n) = base.elem_ty_and_len(base_ty);
                let elem_size = self.type_size(elem_ty)?.expect(
                    "slice element must be sized",
                );
                assert!(u64::from(from) <= n - u64::from(to));
                let ptr = base_ptr.to_ptr()?.offset(u64::from(from) * elem_size, (&self).data_layout())?;
                // sublicing arrays produces arrays
                let extra = if self.type_is_sized(base_ty) {
                    LvalueExtra::None
                } else {
                    LvalueExtra::Length(PrimVal::Bytes((n - u64::from(to) - u64::from(from)) as u128))
                };
                (ptr, extra)
            }
        };

        Ok(Lvalue::Ptr { ptr: PrimVal::Ptr(ptr), extra })
    }

    pub(super) fn lvalue_ty(&self, lvalue: &mir::Place<'tcx>) -> Ty<'tcx> {
        self.monomorphize(lvalue.ty(self.mir(), self.tcx).to_ty(self.tcx), self.substs())
    }
}
