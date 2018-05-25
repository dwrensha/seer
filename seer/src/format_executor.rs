use eval_context::{EvalContext, ResourceLimits, StackPopCleanup};

use std::str;

use rustc::ty::{self, Ty, TyCtxt};
use rustc::ty::layout::LayoutOf;
use rustc::hir::def_id::DefId;

use rustc::hir;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use syntax::codemap::{DUMMY_SP, Span, CodeMap};
use syntax::ast;

use value::{PrimVal, Value};
use lvalue::Lvalue;
use error::EvalResult;
use executor::{FinishStep, FinishStepVariant};
use memory::{SByte, MemoryPointer};

pub struct FormatExecutor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    entry_def_id: DefId,
    initial_ecx: EvalContext<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> FormatExecutor<'a, 'tcx> {
    pub fn new(
        tcx: TyCtxt<'a, 'tcx, 'tcx>,
        limits: ResourceLimits,
        codemap: &'a CodeMap
    )
        -> Self
    {
        // TODO: find the right function
        let (entry_node_id, _) = find_fn_by_name(&tcx, "print").expect("failed to find entry function for output formatter");
        let entry_def_id = tcx.hir.local_def_id(entry_node_id);

        let ecx = EvalContext::new(tcx, limits, codemap);
        FormatExecutor {
            tcx: tcx,
            entry_def_id: entry_def_id,
            initial_ecx: ecx,
        }
    }

    pub fn debug_repr(&self, data: &[u8], ty: Ty<'tcx>) -> EvalResult<'tcx, String> {
        let (ecx, return_ptr, string_ty) = self.prepare(data, ty)?;

        // execute until the entry function returns
        let ecx = self.run(ecx)?;

        // find field by name, return Ty and offset
        // panics if ty is not of the TyAdt variant
        let field_ty_and_offset = |ty: Ty<'tcx>, field_substs: &ty::subst::Substs<'tcx>, name: &str|  {
            for (field_num, field_def) in ty.ty_adt_def().unwrap().all_fields().enumerate() {
                if field_def.name == name {
                    let field_ty = field_def.ty(self.tcx, field_substs);
                    let field_offset = ecx.layout_of(ty)?.fields.offset(field_num).bytes();
                    return Ok(Some((field_ty, field_offset)))
                }
            }
            Ok(None)
        };

        // find offsets for s.vec.len and s.vec.buf.ptr
        let (len_offset, ptr_offset) = {
            let substs_u8 = self.tcx.mk_substs([ty::subst::Kind::from(self.tcx.types.u8)].iter());
            let (vec_ty, vec_offset) = field_ty_and_offset(string_ty, substs_u8, "vec")?.unwrap();
            let (_, len_offset) = field_ty_and_offset(vec_ty, substs_u8, "len")?.unwrap();
            let len_offset_total = vec_offset + len_offset;

            let (buf_ty, buf_offset) = field_ty_and_offset(vec_ty, substs_u8, "buf")?.unwrap();
            let (_, ptr_offset) = field_ty_and_offset(buf_ty, substs_u8, "ptr")?.unwrap();
            let ptr_offset_total = vec_offset + buf_offset + ptr_offset;

            (len_offset_total, ptr_offset_total)
        };

        // get result from finished execution
        let len_ptr = MemoryPointer::new(return_ptr.alloc_id, len_offset);
        let len = match &ecx.memory.read_ptr(len_ptr)? {
            &PrimVal::Bytes(b) => b as usize,
            _ => {
                panic!("could not read string length")
            }
        };

        // pointer to s.vec.buf.ptr
        let buf_ptr = MemoryPointer::new(return_ptr.alloc_id, ptr_offset);
        // value at s.vec.buf.ptr (a pointer to the string data)
        let primval_ptr = &ecx.memory.read_ptr(buf_ptr)?;
        match primval_ptr {
            &PrimVal::Ptr(mem_ptr) => {
                let concrete_bytes = &ecx.memory.get(mem_ptr.alloc_id)?.bytes;
                let bytes: Vec<u8>= concrete_bytes.iter().take(len).map(|c| {
                    match c {
                        &SByte::Concrete(b) => b,
                        _ => panic!("non-concrete byte"),
                    }
                }).collect();
                let s = str::from_utf8(&bytes);
                match s {
                    Ok(s) => Ok(s.to_string()),
                    Err(e) => panic!("formatted string utf8 error: {:?}", e)
                }
            }
            _ => bug!("string buffer pointer was not a pointer: {:?}", primval_ptr)
        }
    }

    fn prepare(&self, data: &[u8], ty: Ty<'tcx>) -> EvalResult<'tcx, (EvalContext<'a, 'tcx>, MemoryPointer, Ty<'tcx>)> {
        let mut ecx = self.initial_ecx.clone();
        let substs = self.tcx.mk_substs([ty::subst::Kind::from(ty)].iter());
        let instance = ty::Instance::new(self.entry_def_id, substs);
        let mir = ecx.load_mir(instance.def).expect("entry function's MIR not found");

        let instance_ty = instance.ty(self.tcx);
        let sig = instance_ty.fn_sig(self.tcx);
        let sig = ecx.erase_lifetimes(&sig);
        let string_ty = sig.output();
        let size = ecx.type_size_with_substs(string_ty, instance.substs)?.unwrap();
        let align = ecx.type_align_with_substs(string_ty, instance.substs)?;
        let return_ptr = ecx.memory.allocate(size as u64, align as u64)?;
        let return_lvalue = Lvalue::from_ptr(return_ptr);

        ecx.push_stack_frame(
            instance,
            DUMMY_SP,
            &mir,
            return_lvalue,
            StackPopCleanup::None,
        ).expect("could not allocate first stack frame");

        // setup args
        let ptr_arg0 = ecx.alloc_ptr(ty)?; ecx.memory_mut().write_bytes(ptr_arg0, &data)?;
        ecx.stack[0].locals[0] = Value::ByRef(ptr_arg0);

        Ok((ecx, return_ptr, string_ty))
    }

    fn run(&self, mut ecx: EvalContext<'a, 'tcx>) -> EvalResult<'tcx, EvalContext<'a, 'tcx>>{
        loop {
            match ecx.step()? {
                (true, None) => {}
                (true, Some(branches)) => {
                    assert_eq!(branches.len(), 1, "there should be exactly feasible branch, found {}", branches.len());
                    for finish_step in branches {
                        let FinishStep {constraints, variant} = finish_step;
                        for constraint in constraints {
                            ecx.memory.constraints.push_constraint(constraint);
                            match variant {
                                FinishStepVariant::Continue {goto_block, set_lvalue} => {
                                    if let Some((lvalue, prim, ty)) = set_lvalue {
                                        ecx.write_primval(lvalue, prim, ty)?;
                                        ecx.goto_block(goto_block);
                                    }
                                }
                                FinishStepVariant::Error(ref e) => {
                                    return Err(e.clone());
                                }
                            }
                        }
                    }
                }
                (false, _) => {
                    return Ok(ecx);
                }
            }
        }
    }
}

fn find_fn_by_name(tcx: &TyCtxt, name: &str) -> Option<(ast::NodeId, Span)> {
    // TODO: find things outside the user crate
    let mut visitor = FunctionVisitor::new(name);
    //println!("\n\n{:#?}\n\n", tcx.hir.krate());
    tcx.hir.krate().visit_all_item_likes(&mut visitor);
    //visitor.display_fn.map(|(node_id, _span)| node_id);
    println!("formatter: {:?}", visitor.display_fn.is_some());
    visitor.display_fn
}

struct FunctionVisitor<'a> {
    display_fn: Option<(ast::NodeId, Span)>,
    name: &'a str,
}

impl<'a> FunctionVisitor<'a> {
    fn new(name: &'a str) -> FunctionVisitor {
        FunctionVisitor {
            display_fn: None,
            name: name,
        }
    }
}

impl<'a, 'tcx> ItemLikeVisitor<'tcx> for FunctionVisitor<'a> {
    fn visit_item(&mut self, i: &'tcx hir::Item){
        match i.node {
            hir::ItemFn(..) => {
                println!("visited fn: {}", i.name);
                if i.name == self.name {
                    self.display_fn = Some((i.id, i.span));
                }
            }
            hir::ItemExternCrate(opt_original_name) => {
                let name = match opt_original_name {
                    Some(original) => original.as_str(),
                    None => i.name.as_str(),
                };
                println!("visited extern crate '{}'", name);
                if name == "seer_helper" {
                    println!("found helper crate: {:?}", i);
                }
            }
            _ => {
                //println!("visited other: {:?}", i);
            }
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'tcx hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, _impl_item: &'tcx hir::ImplItem) {
    }
}
