use rustc::mir;
use rustc::ty::layout::{HasDataLayout, LayoutOf, TyLayout};
use rustc::ty::{self, Ty, TyCtxt};
use rustc_data_structures::indexed_vec::Idx;

use error::{EvalError, EvalResult};
use eval_context::{EvalContext, ValTy};
use memory::{MemoryPointer};
use value::{PrimVal, PrimValKind, Value};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Place<'tcx> {
    /// A place referring to a value allocated in the `Memory` system.
    Ptr {
        ptr: PrimVal,
        extra: PlaceExtra,
    },

    /// A place referring to a value on the stack. Represented by a stack frame index paired with
    /// a Mir local index.
    Local {
        frame: usize,
        local: mir::Local,
    },

    /// A place referring to a global
    Global(GlobalId<'tcx>),
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum PlaceExtra {
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

impl<'tcx> Place<'tcx> {
    /// Produces an Place that will error if attempted to be read from
    pub fn undef() -> Self {
        Self::from_primval_ptr(PrimVal::Undef)
    }

    fn from_primval_ptr(ptr: PrimVal) -> Self {
        Place::Ptr { ptr, extra: PlaceExtra::None }
    }

    pub fn from_ptr(ptr: MemoryPointer) -> Self {
        Self::from_primval_ptr(PrimVal::Ptr(ptr))
    }

    pub(super) fn to_ptr_and_extra(self) -> (PrimVal, PlaceExtra) {
        match self {
            Place::Ptr { ptr, extra } => (ptr, extra),
            _ => bug!("to_ptr_and_extra: expected Place::Ptr, got {:?}", self),

        }
    }

    pub(super) fn to_ptr(self) -> EvalResult<'tcx, MemoryPointer> {
        let (ptr, extra) = self.to_ptr_and_extra();
        assert_eq!(extra, PlaceExtra::None);
        ptr.to_ptr()
    }

    pub(super) fn elem_ty_and_len(self, ty: Ty<'tcx>, tcx: TyCtxt<'_, 'tcx, '_>) -> (Ty<'tcx>, u64) {
        match ty.sty {
            ty::TyArray(elem, n) => (elem, n.unwrap_usize(tcx)),

            ty::TySlice(elem) => {
                match self {
                    Place::Ptr { extra: PlaceExtra::Length(len), .. } => {
                        match len {
                            PrimVal::Bytes(n) => (elem, n as u64),
                            _ => unimplemented!(),
                        }
                    }
                    _ => bug!("elem_ty_and_len of a TySlice given non-slice place: {:?}", self),
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
    /// Reads a value from the place without going through the intermediate step of obtaining
    /// a `miri::Place`
    pub fn try_read_place(&mut self, place: &mir::Place<'tcx>) -> EvalResult<'tcx, Option<Value>> {
        use rustc::mir::Place::*;
        match *place {
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
            Projection(ref proj) => self.try_read_place_projection(proj),
        }
    }

    pub fn read_field(
        &self,
        base: Value,
        variant: Option<usize>,
        field: mir::Field,
        base_ty: Ty<'tcx>,
    ) -> EvalResult<'tcx, ValTy<'tcx>> {
        let mut base_layout = self.layout_of(base_ty)?;
        if let Some(variant_index) = variant {
            base_layout = base_layout.for_variant(self, variant_index);
        }
        let field_index = field.index();
        let field = base_layout.field(self, field_index)?;
        if field.size.bytes() == 0 {
            return Ok(ValTy {
                value: Value::ByVal(PrimVal::Undef),
                ty: field.ty,
            });
        }
        let offset = base_layout.fields.offset(field_index);
        let value = match base {
            // the field covers the entire type
            Value::ByValPair(..) |
            Value::ByVal(_) if offset.bytes() == 0 && field.size == base_layout.size => base,
            // extract fields from types with `ScalarPair` ABI
            Value::ByValPair(a, b) => {
                let val = if offset.bytes() == 0 { a } else { b };
                Value::ByVal(val)
            },
            Value::ByRef(base_ptr) => {
                let offset = base_layout.fields.offset(field_index);
                let ptr = base_ptr.offset(offset.bytes(), self.memory.layout)?;
                assert!(!field.is_unsized());
                Value::ByRef(ptr)
            },
            Value::ByVal(val) => bug!("field access on non aggregate {:?}, {:?}", val, base_ty),
        };
        Ok(ValTy {
            value,
            ty: field.ty,
        })
    }

    fn try_read_place_projection(&mut self, proj: &mir::PlaceProjection<'tcx>) -> EvalResult<'tcx, Option<Value>> {
        use rustc::mir::ProjectionElem::*;
        let base = match self.try_read_place(&proj.base)? {
            Some(base) => base,
            None => return Ok(None),
        };
        let base_ty = self.place_ty(&proj.base);
        match proj.elem {
            Field(field, _) => Ok(Some(self.read_field(base, None, field, base_ty)?.value)),
            // The NullablePointer cases should work fine, need to take care for normal enums
            Downcast(..) |
            Subslice { .. } |
            // reading index 0 or index 1 from a ByVal or ByVal pair could be optimized
            ConstantIndex { .. } | Index(_) |
            // No way to optimize this projection any better than the normal place path
            Deref => Ok(None),
        }
    }

    pub(super) fn eval_and_read_place(&mut self, place: &mir::Place<'tcx>) -> EvalResult<'tcx, Value> {
        let ty = self.place_ty(place);
        // Shortcut for things like accessing a fat pointer's field,
        // which would otherwise (in the `eval_place` path) require moving a `ByValPair` to memory
        // and returning an `Place::Ptr` to it
        if let Some(val) = self.try_read_place(place)? {
            return Ok(val);
        }
        let place = self.eval_place(place)?;

        if ty.is_never() {
            return Err(EvalError::Unreachable);
        }

        match place {
            Place::Ptr { ptr, extra } => {
                assert_eq!(extra, PlaceExtra::None);
                Ok(Value::ByRef(ptr.to_ptr()?))
            }
            Place::Local { frame, local } => {
                self.stack[frame].get_local(local)
            }
            Place::Global(cid) => {
                Ok(self.globals.get(&cid).expect("global not cached").value)
            }
        }
    }

    pub fn read_place(&self, place: Place) -> EvalResult<'tcx, Value> {
        match place {
            Place::Ptr { ptr, extra } => {
                assert_eq!(extra, PlaceExtra::None);
                Ok(Value::ByRef(ptr.to_ptr()?))
            }
            Place::Local { frame, local } => self.stack[frame].get_local(local),
            Place::Global(cid) => {
                Ok(self.globals.get(&cid).expect("global not cached").value)
            }
        }
    }

    pub(super) fn eval_place(&mut self, mir_place: &mir::Place<'tcx>) -> EvalResult<'tcx, Place<'tcx>> {
        use rustc::mir::Place::*;
        let place = match *mir_place {
            Local(mir::RETURN_PLACE) => self.frame().return_place,
            Local(local) => Place::Local { frame: self.stack.len() - 1, local },

            Static(ref static_) => {
                let instance = ty::Instance::mono(self.tcx, static_.def_id);
                Place::Global(GlobalId { instance, promoted: None })
            }

            Projection(ref proj) => {
                let ty = self.place_ty(&proj.base);
                let place = self.eval_place(&proj.base)?;
                return self.eval_place_projection(place, ty, &proj.elem);
            }
        };

        if log_enabled!(::log::Level::Trace) {
            self.dump_local(place);
        }

        Ok(place)
    }

    pub fn place_field(
        &mut self,
        base: Place<'tcx>,
        field: mir::Field,
        base_layout: TyLayout<'tcx>,
    ) -> EvalResult<'tcx, (Place<'tcx>, TyLayout<'tcx>)> {
        let base_layout: TyLayout<'tcx> = match base {
            Place::Ptr { extra: PlaceExtra::DowncastVariant(n), .. } => {
                base_layout.for_variant(&self, n)
            }
            _ => base_layout,
        };
        let field_index = field.index();
        let field = base_layout.field(&self, field_index)?;
        let offset = base_layout.fields.offset(field_index);

        // Do not allocate in trivial cases
        let (base_ptr, base_extra) = match base {
            Place::Ptr { ptr, extra } => (ptr, extra),
            Place::Local { frame, local } => {
                match self.stack[frame].get_local(local)? {
                    // in case the field covers the entire type, just return the value
                    Value::ByVal(_) if offset.bytes() == 0 &&
                                       field.size == base_layout.size => {
                        return Ok((base, field));
                    }
                    Value::ByValPair(..) if offset.bytes() == 0 &&
                                            field.size == base_layout.size => {
                        return Ok((base, field));
                    }
                    Value::ByRef { .. } |
                    Value::ByValPair(..) |
                    Value::ByVal(_) => self.force_allocation(base)?.to_ptr_and_extra(),
                }
            }
            Place::Global(_cid) => {
                self.force_allocation(base)?.to_ptr_and_extra()
            }
        };

        let offset = match base_extra {
            PlaceExtra::Vtable(tab) => {
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
            PlaceExtra::None
        } else {
            match base_extra {
                PlaceExtra::None => bug!("expected fat pointer"),
                PlaceExtra::DowncastVariant(..) => {
                    bug!("Rust doesn't support unsized fields in enum variants")
                }
                PlaceExtra::Vtable(_) |
                PlaceExtra::Length(_) => {}
            }
            base_extra
        };

        Ok((Place::Ptr { ptr: PrimVal::Ptr(ptr), extra }, field))
    }

    pub(super) fn val_to_place(&self, val: Value, ty: Ty<'tcx>) -> EvalResult<'tcx, Place<'tcx>> {
        Ok(match self.tcx.struct_tail(ty).sty {
            ty::TyDynamic(..) => {
                let (ptr, vtable) = val.into_ptr_vtable_pair(&self.memory)?;
                Place::Ptr {
                    ptr: ptr,
                    extra: PlaceExtra::Vtable(vtable),
                }
            }
            ty::TyStr | ty::TySlice(_) => {
                let (ptr, len) = val.into_slice(&self.memory)?;
                Place::Ptr {
                    ptr: ptr,
                    extra: PlaceExtra::Length(len),
                }
            }
            _ => Place::from_primval_ptr(val.read_ptr(&self.memory)?),
        })
    }

    pub(super) fn place_index(
        &mut self,
        base: Place<'tcx>,
        outer_ty: Ty<'tcx>,
        idx: PrimVal,
    ) -> EvalResult<'tcx, Place<'tcx>> {
        // Taking the outer type here may seem odd; it's needed because for array types, the outer type gives away the length.
        let base = self.force_allocation(base)?;
        let (base_ptr, _) = base.to_ptr_and_extra();

        let (elem_ty, len) = base.elem_ty_and_len(outer_ty, self.tcx);
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
            Ok(Place::Ptr {
                ptr: ptr_primval,
                extra: PlaceExtra::None,
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

            Ok(Place::Ptr {
                ptr: ptr_primval,
                extra: PlaceExtra::None,
            })
        }
    }

    pub(super) fn place_downcast(
        &mut self,
        base: Place<'tcx>,
        variant: usize,
    ) -> EvalResult<'tcx, Place<'tcx>> {
        // FIXME(solson)
        let base = self.force_allocation(base)?;
        let (ptr, _) = base.to_ptr_and_extra();
        let extra = PlaceExtra::DowncastVariant(variant);
        Ok(Place::Ptr { ptr, extra })
    }

    pub(super) fn eval_place_projection(
        &mut self,
        base: Place<'tcx>,
        base_ty: Ty<'tcx>,
        proj_elem: &mir::ProjectionElem<'tcx, mir::Local, Ty<'tcx>>,
    ) -> EvalResult<'tcx, Place<'tcx>> {
        use rustc::mir::ProjectionElem::*;
        let (ptr, extra) = match *proj_elem {
            Field(field, _) => {
                let layout = self.type_layout(base_ty)?;
                return Ok(self.place_field(base, field, layout)?.0);
            }

            Downcast(_, variant) => {
                return self.place_downcast(base, variant);
            }

            Deref => {
                let val = self.read_place(base)?;

                let pointee_type = match base_ty.sty {
                    ty::TyRawPtr(ty::TypeAndMut {ty, ..}) |
                    ty::TyRef(_, ty, _) => ty,
                    ty::TyAdt(def, _) if def.is_box() => base_ty.boxed_ty(),
                    _ => bug!("can only deref pointer types"),
                };

                trace!("deref to {} on {:?}", pointee_type, val);

                return self.val_to_place(val, pointee_type);
            }

            Index(local) => {
                let value = self.frame().get_local(local)?;
                let ty = self.tcx.types.usize;
                let idx = self.value_to_primval(value, ty)?;
                return self.place_index(base, base_ty, idx);
            }

            ConstantIndex {
                offset,
                min_length,
                from_end,
            } => {
                // FIXME(solson)
                let base = self.force_allocation(base)?;
                let (base_ptr, _) = base.to_ptr_and_extra();

                let (elem_ty, n) = base.elem_ty_and_len(base_ty, self.tcx);
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
                (ptr, PlaceExtra::None)
            }

            Subslice { from, to } => {
                // FIXME(solson)
                let base = self.force_allocation(base)?;
                let (base_ptr, _) = base.to_ptr_and_extra();

                let (elem_ty, n) = base.elem_ty_and_len(base_ty, self.tcx);
                let elem_size = self.type_size(elem_ty)?.expect(
                    "slice element must be sized",
                );
                assert!(u64::from(from) <= n - u64::from(to));
                let ptr = base_ptr.to_ptr()?.offset(u64::from(from) * elem_size, (&self).data_layout())?;
                // sublicing arrays produces arrays
                let extra = if self.type_is_sized(base_ty) {
                    PlaceExtra::None
                } else {
                    PlaceExtra::Length(PrimVal::Bytes((n - u64::from(to) - u64::from(from)) as u128))
                };
                (ptr, extra)
            }
        };

        Ok(Place::Ptr { ptr: PrimVal::Ptr(ptr), extra })
    }

    pub(super) fn place_ty(&self, place: &mir::Place<'tcx>) -> Ty<'tcx> {
        self.monomorphize(place.ty(self.mir(), self.tcx).to_ty(self.tcx), self.substs())
    }
}
