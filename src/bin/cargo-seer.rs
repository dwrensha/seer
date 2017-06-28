// The code in this file is based on cargo-clippy, which is licensed under
// the [Mozilla Public License, 2.0](https://www.mozilla.org/MPL/2.0/).
// See https://github.com/Manishearth/rust-clippy.

#![feature(rustc_private)]

extern crate getopts;
extern crate rustc;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_plugin;
extern crate syntax;
extern crate seer;

use rustc_driver::{RustcDefaultCalls};
use std::path::PathBuf;
use std::process::{self, Command};
use std::io::{self, Write};

extern crate cargo_metadata;

use std::path::Path;

const CARGO_SEER_HELP: &str = r#"Attempts to run all possible execution paths through a program.

Usage:
    cargo seer [options] [--] [<opts>...]

Common options:
    -h, --help               Print this message
    --features               Features to compile for the package
    -V, --version            Print version info and exit

Other options are the same as `cargo rustc`.

The feature `cargo-seer` is automatically defined for convenience.
"#;

fn show_help() {
    println!("{}", CARGO_SEER_HELP);
}

fn show_version() {
    println!("{}", env!("CARGO_PKG_VERSION"));
}

pub fn main() {
    use std::env;

    // Check for version and help flags even when invoked as 'cargo-seer'
    if std::env::args().any(|a| a == "--help" || a == "-h") {
        show_help();
        return;
    }
    if std::env::args().any(|a| a == "--version" || a == "-V") {
        show_version();
        return;
    }

    if let Some("seer") = std::env::args().nth(1).as_ref().map(AsRef::as_ref) {
        // this arm is executed on the initial call to `cargo seer`

        let manifest_path_arg = std::env::args()
            .skip(2)
            .find(|val| val.starts_with("--manifest-path="));

        let mut metadata =
            if let Ok(metadata) = cargo_metadata::metadata(manifest_path_arg.as_ref().map(AsRef::as_ref)) {
                metadata
            } else {
                let _ = io::stderr().write_fmt(format_args!("error: Could not obtain cargo metadata.\n"));
                process::exit(101);
            };

        let manifest_path = manifest_path_arg.map(|arg| PathBuf::from(Path::new(&arg["--manifest-path=".len()..])));

        let current_dir = std::env::current_dir();

        let package_index = metadata
            .packages
            .iter()
            .position(|package| {
                let package_manifest_path = Path::new(&package.manifest_path);
                if let Some(ref manifest_path) = manifest_path {
                    package_manifest_path == manifest_path
                } else {
                    let current_dir = current_dir
                        .as_ref()
                        .expect("could not read current directory");
                    let package_manifest_directory = package_manifest_path
                        .parent()
                        .expect("could not find parent directory of package manifest");
                    package_manifest_directory == current_dir
                }
            })
            .expect("could not find matching package");
        let package = metadata.packages.remove(package_index);
        for target in package.targets {
            let args = std::env::args().skip(2);
            if let Some(first) = target.kind.get(0) {
                if target.kind.len() > 1 || first.ends_with("lib") {
                    if let Err(code) = process(std::iter::once("--lib".to_owned()).chain(args)) {
                        std::process::exit(code);
                    }
                } else if ["bin", "example", "test", "bench"].contains(&&**first) {
                    if let Err(code) = process(vec![format!("--{}", first), target.name]
                                                   .into_iter()
                                                   .chain(args)) {
                        std::process::exit(code);
                    }
                }
            } else {
                panic!("badly formatted cargo metadata: target::kind is an empty array");
            }
        }
    } else {
        // this arm is executed when cargo-seer runs `cargo rustc` with the `RUSTC`
        // env var set to itself

        let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
        let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));
        let sys_root = if let (Some(home), Some(toolchain)) = (home, toolchain) {
            format!("{}/toolchains/{}", home, toolchain)
        } else {
            option_env!("SYSROOT")
                .map(|s| s.to_owned())
                .or_else(|| {
                    Command::new("rustc")
                        .arg("--print")
                        .arg("sysroot")
                        .output()
                        .ok()
                        .and_then(|out| String::from_utf8(out.stdout).ok())
                        .map(|s| s.trim().to_owned())
                })
                .expect("need to specify SYSROOT env var during seer compilation, or use rustup or multirust")
        };

        rustc_driver::in_rustc_thread(|| {
            // this conditional check for the --sysroot flag is there so users can call
            // `cargo-seer` directly
            // without having to pass --sysroot or anything
            let mut args: Vec<String> = if env::args().any(|s| s == "--sysroot") {
                env::args().collect()
            } else {
                env::args()
                    .chain(Some("--sysroot".to_owned()))
                    .chain(Some(sys_root))
                    .collect()
            };


            args.extend_from_slice(&["--cfg".to_owned(), r#"feature="cargo-seer""#.to_owned()]);

            args.extend_from_slice(&["-Z".to_owned(), "always-encode-mir".to_owned()]);

            // this check ensures that dependencies are built but not linted and the final
            // crate is
            // linted but not built
            let seer_enabled = env::args().any(|s| s == "-Zno-trans");

            if seer_enabled {
                let consumer = |complete: ::seer::ExecutionComplete | {
                    println!("{:?}", complete);
                    println!("as string: {:?}", ::std::str::from_utf8(&complete.input));
                    if let Err(_) = complete.result {
                        println!("hit an error. halting");
                        false
                    } else {
                        true
                    }
                };

                ::seer::ExecutionConfig::new()
                    .emit_error(false)
                    .consumer(consumer)
                    .run(args);
            } else {
                let mut rdc = RustcDefaultCalls;
                let (result, _) = rustc_driver::run_compiler(&args, &mut rdc, None, None);
                if let Err(err_count) = result {
                    if err_count > 0 {
                        std::process::exit(1);
                    }
                }
            }
        }).expect("rustc_thread failed");
    }
}

fn process<I>(old_args: I) -> Result<(), i32>
    where I: Iterator<Item = String>
{

    let mut args = vec!["rustc".to_owned()];

    let mut found_dashes = false;
    for arg in old_args {
        found_dashes |= arg == "--";
        args.push(arg);
    }
    if !found_dashes {
        args.push("--".to_owned());
    }
    args.push("-Zno-trans".to_owned());

    let path = std::env::current_exe().expect("current executable path invalid");
    let exit_status = std::process::Command::new("cargo")
        .args(&args)
        .env("RUSTC", path)
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo?");

    if exit_status.success() {
        Ok(())
    } else {
        Err(exit_status.code().unwrap_or(-1))
    }
}
