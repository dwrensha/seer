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
    init_logger();
    let consumer = |complete: ::seer::ExecutionComplete | {
        println!("complete! {:?}", complete);
        if let Err(_) = complete.result {
            println!("hit an error. halting");
            false
        } else {
            true
        }
    };
    ::seer::run_symbolic(::std::env::args().collect(), consumer);
}
