extern crate seer;
extern crate env_logger;
extern crate log_settings;
extern crate log;

fn init_logger() {
    let format = |record: &log::LogRecord| {
        if record.level() == log::LogLevel::Trace {
            // prepend spaces to indent the final string
            let indentation = log_settings::settings().indentation;
            format!(
                "{lvl}:{module}:{indent:<indentation$} {text}",
                lvl = record.level(),
                module = record.location().module_path(),
                indentation = indentation,
                indent = "",
                text = record.args(),
            )
        } else {
            format!(
                "{lvl}:{module}: {text}",
                lvl = record.level(),
                module = record.location().module_path(),
                text = record.args(),
            )
        }
    };

    let mut builder = env_logger::LogBuilder::new();
    builder.format(format).filter(None, log::LogLevelFilter::Info);

    if std::env::var("MIRI_LOG").is_ok() {
        builder.parse(&std::env::var("MIRI_LOG").unwrap());
    }

    builder.init().unwrap();
}

fn main() {
    let mut args: Vec<String> = ::std::env::args().collect();

    init_logger();
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

    let mut config = ::seer::ExecutionConfig::new();

    let mut emit_error_idx = None;
    for (idx, arg) in args.iter().enumerate() {
        if arg == "--emit-error" {
            emit_error_idx = Some(idx);
            break;
        }
    }
    if let Some(idx) = emit_error_idx {
        config.emit_error(true);
        args.remove(idx);
    } else {
        config.consumer(consumer);
    }

    config.run(args);
}
