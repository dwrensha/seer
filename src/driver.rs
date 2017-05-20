use getopts;
use rustc::session::Session;
use rustc_driver::{self, Compilation, CompilerCalls, RustcDefaultCalls};
use rustc_driver::driver::{CompileState, CompileController};
use rustc_errors;
use rustc::session::config::{self, Input, ErrorOutputType};
use rustc::hir::{self, itemlikevisit};
use rustc::ty::TyCtxt;
use syntax;
use syntax::ast::{MetaItemKind, NestedMetaItemKind, self};
use std::path::PathBuf;
use std;

pub enum Mode {
    RunMain,
    RunSymbolic,
}

struct SeerCompilerCalls(RustcDefaultCalls, Mode);

impl<'a> CompilerCalls<'a> for SeerCompilerCalls {
    fn early_callback(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &ast::CrateConfig,
        descriptions: &rustc_errors::registry::Registry,
        output: ErrorOutputType
    ) -> Compilation {
        self.0.early_callback(matches, sopts, cfg, descriptions, output)
    }
    fn no_input(
        &mut self,
        matches: &getopts::Matches,
        sopts: &config::Options,
        cfg: &ast::CrateConfig,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>,
        descriptions: &rustc_errors::registry::Registry
    ) -> Option<(Input, Option<PathBuf>)> {
        self.0.no_input(matches, sopts, cfg, odir, ofile, descriptions)
    }
    fn late_callback(
        &mut self,
        matches: &getopts::Matches,
        sess: &Session,
        input: &Input,
        odir: &Option<PathBuf>,
        ofile: &Option<PathBuf>
    ) -> Compilation {
        self.0.late_callback(matches, sess, input, odir, ofile)
    }
    fn build_controller(&mut self, sess: &Session, matches: &getopts::Matches) -> CompileController<'a> {
        let mut control = self.0.build_controller(sess, matches);
        control.after_hir_lowering.callback = Box::new(after_hir_lowering);
        control.after_analysis.callback = match self.1 {
            Mode::RunMain => Box::new(after_analysis_run_main),
            Mode::RunSymbolic => Box::new(after_analysis_run_symbolic),
        };
        if std::env::var("MIRI_HOST_TARGET") != Ok("yes".to_owned()) {
            // only fully compile targets on the host
            control.after_analysis.stop = Compilation::Stop;
        }
        control
    }
}

fn after_hir_lowering(state: &mut CompileState) {
    let attr = (String::from("miri"), syntax::feature_gate::AttributeType::Whitelisted);
    state.session.plugin_attributes.borrow_mut().push(attr);
}

fn after_analysis_run_main<'a, 'tcx>(state: &mut CompileState<'a, 'tcx>) {
    state.session.abort_if_errors();

    let tcx = state.tcx.unwrap();
    let limits = resource_limits_from_attributes(state);

    if let Some((entry_node_id, _)) = *state.session.entry_fn.borrow() {
        let entry_def_id = tcx.hir.local_def_id(entry_node_id);

        let mut executor = ::executor::Executor::new();
        executor.eval_main(tcx, entry_def_id, limits);

        state.session.abort_if_errors();
    } else {
        println!("no main function found, assuming auxiliary build");
    }
}

fn after_analysis_run_symbolic<'a, 'tcx>(state: &mut CompileState<'a, 'tcx>) {
    state.session.abort_if_errors();

    let tcx = state.tcx.unwrap();
    let limits = resource_limits_from_attributes(state);

    struct Visitor<'a, 'tcx: 'a>(::ResourceLimits, TyCtxt<'a, 'tcx, 'tcx>, &'a CompileState<'a, 'tcx>);
    impl<'a, 'tcx: 'a, 'hir> itemlikevisit::ItemLikeVisitor<'hir> for Visitor<'a, 'tcx> {
        fn visit_item(&mut self, i: &'hir hir::Item) {
            if let hir::Item_::ItemFn(_, _, _, _, _, body_id) = i.node {
                if i.attrs.iter().any(|attr| attr.name().map_or(false, |n| n == "symbolic_execution_entry_point")) {
                    let did = self.1.hir.body_owner_def_id(body_id);
                    let mut executor = ::executor::Executor::new();
                    executor.eval_main(self.1, did, self.0);
                    self.2.session.abort_if_errors();
                }
            }
        }
        fn visit_trait_item(&mut self, _trait_item: &'hir hir::TraitItem) {}
        fn visit_impl_item(&mut self, _impl_item: &'hir hir::ImplItem) {}
    }
    state.hir_crate.unwrap().visit_all_item_likes(&mut Visitor(limits, tcx, state));
}

fn resource_limits_from_attributes(state: &CompileState) -> ::ResourceLimits {
    let mut limits = ::ResourceLimits::default();
    let krate = state.hir_crate.as_ref().unwrap();
    let err_msg = "miri attributes need to be in the form `miri(key = value)`";
    let extract_int = |lit: &syntax::ast::Lit| -> u128 {
        match lit.node {
            syntax::ast::LitKind::Int(i, _) => i,
            _ => state.session.span_fatal(lit.span, "expected an integer literal"),
        }
    };

    for attr in krate.attrs.iter().filter(|a| a.name().map_or(false, |n| n == "miri")) {
        if let Some(items) = attr.meta_item_list() {
            for item in items {
                if let NestedMetaItemKind::MetaItem(ref inner) = item.node {
                    if let MetaItemKind::NameValue(ref value) = inner.node {
                        match &inner.name().as_str()[..] {
                            "memory_size" => limits.memory_size = extract_int(value) as u64,
                            "step_limit" => limits.step_limit = extract_int(value) as u64,
                            "stack_limit" => limits.stack_limit = extract_int(value) as usize,
                            _ => state.session.span_err(item.span, "unknown miri attribute"),
                        }
                    } else {
                        state.session.span_err(inner.span, err_msg);
                    }
                } else {
                    state.session.span_err(item.span, err_msg);
                }
            }
        } else {
            state.session.span_err(attr.span, err_msg);
        }
    }
    limits
}

fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .expect("need to specify RUST_SYSROOT env var or use rustup or multirust")
            .to_owned(),
    }
}

fn main_helper(mut args: Vec<String>, mode: Mode) {
    let sysroot_flag = String::from("--sysroot");
    if !args.contains(&sysroot_flag) {
        args.push(sysroot_flag);
        args.push(find_sysroot());
    }

    // TODO(cleanup) is this still necessary?
    args.push("-Zmir-opt-level=0".to_owned());
    // for auxilary builds in unit tests
    args.push("-Zalways-encode-mir".to_owned());

    rustc_driver::run_compiler(&args, &mut SeerCompilerCalls(RustcDefaultCalls, mode), None, None);
}

pub fn run_main(args: Vec<String>) {
    main_helper(args, Mode::RunMain);
}

pub fn run_symbolic(args: Vec<String>) {
    main_helper(args, Mode::RunSymbolic);
}
