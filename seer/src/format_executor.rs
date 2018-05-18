use eval_context::{EvalContext, ResourceLimits, StackPopCleanup};

use std::str;

use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;

use rustc::hir;
use rustc::hir::itemlikevisit::ItemLikeVisitor;
use syntax::codemap::{DUMMY_SP, Span, CodeMap};
use syntax::ast;
//use rustc::ty::TyCtxt;
//use rustc_data_structures::indexed_vec::Idx;

use value::{PrimVal, Value};
use lvalue::Lvalue;
use error::EvalResult;
use executor::{FinishStep, FinishStepVariant};
//use constraints::SatisfiedVarGroup;
use memory::{SByte, MemoryPointer, AllocId};

pub struct FormatExecutor<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    entry_def_id: DefId,
    initial_ecx: EvalContext<'a, 'tcx>,
}

impl<'a, 'tcx: 'a> FormatExecutor<'a, 'tcx> {
    // only driver.rs has enough info to call us
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

    //fn debug_repr(&self, var: SatisfiedVarGroup) -> EvalResult<'tcx, String> {
    //    self._debug_repr(var.data, var.ty)
    //}

    pub fn debug_repr(&self, data: &[u8], ty: Ty<'tcx>) -> EvalResult<'tcx, String> {
        let mut ecx = self.initial_ecx.clone();
        let substs = self.tcx.mk_substs([ty::subst::Kind::from(ty)].iter());
        let instance = ty::Instance::new(self.entry_def_id, substs);
        let mir = ecx.load_mir(instance.def).expect("entry function's MIR not found");

        // TODO: get this from rustc instead so it works even if the seer analysis is for
        // a target different from the host
        use std::mem;
        let size = mem::size_of::<String>();
        let align = mem::align_of::<String>();
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

        let ecx = self.run(ecx)?;

        //let concrete_bytes = &ecx.memory.get(return_ptr.alloc_id)?.bytes;
        //let bytes: Vec<u8>= concrete_bytes.iter().map(|c| {
        //    match c {
        //        &SByte::Concrete(b) => b,
        //        _ => panic!("non-concrete byte"),
        //    }
        //}).collect();
        //let s = str::from_utf8(&bytes);
        //println!("formatter!!!");
        //println!("{:?}", bytes);
        //println!("{:?}", s);
        // String
        // 0000 0000, 32 000 0000, 23 000 0000
        // the formatted string is 23 chars long with 32 capacity
        // but the pointer doesn't read nicely this way

        // get result from finished execution
        // this is very fragile; the compiler could choose to order the fields of String
        // differently
        let s_len_ptr = MemoryPointer::new(return_ptr.alloc_id, align as u64 * 2);
        let s_len = match &ecx.memory.read_ptr(s_len_ptr)? {
            &PrimVal::Bytes(b) => b as usize,
            _ => {
                // TODO don't panic, return an error
                panic!("could not read string length")
            }
        };

        // this is also sensitive to the way the struct is laid out in memory
        let s_primval_ptr = &ecx.memory.read_ptr(return_ptr)?;
        match s_primval_ptr {
            &PrimVal::Ptr(s_ptr) => {
                //let s_len = 23;
                let concrete_bytes = &ecx.memory.get(s_ptr.alloc_id)?.bytes;
                let bytes: Vec<u8>= concrete_bytes.iter().take(s_len).map(|c| {
                    match c {
                        &SByte::Concrete(b) => b,
                        _ => panic!("non-concrete byte"),
                    }
                }).collect();
                let s = str::from_utf8(&bytes);
                match s {
                    Ok(s) => Ok(s.to_string()),
                    // TODO: don't panic
                    Err(e) => panic!("formatted string utf8 error: {:?}", e)
                }
            }
            _ => bug!("string buffer pointer was not a pointer: {:?}", s_primval_ptr)
        }
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
            _ => {}
        }
    }

    fn visit_trait_item(&mut self, _trait_item: &'tcx hir::TraitItem) {
    }

    fn visit_impl_item(&mut self, _impl_item: &'tcx hir::ImplItem) {
    }
}
