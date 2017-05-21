extern crate seer;

#[test]
fn symbolic_simple() {
    let consumer = |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                assert_eq!(input[0], 43);
                false
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), "tests/symbolic/simple.rs".to_string()];
    ::seer::run_symbolic(args, consumer);
}


#[test]
fn symbolic_manticore() {
    let consumer = |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                assert_eq!(
                    &input[..],
                    &[61, 77, 65, 78, 84, 73, 67, 79, 82, 69,
                      61, 0, 1, 2, 3, 4, 5, 50, 51, 29, 212]);

                false
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), "tests/symbolic/manticore.rs".to_string()];
    ::seer::run_symbolic(args, consumer);
}


#[test]
fn symbolic_comparisons() {
    let consumer = |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                assert_eq!(
                    &input[..5],
                    &[17, 18, 38, 37, 101]);

                false
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), "tests/symbolic/comparisons.rs".to_string()];
    ::seer::run_symbolic(args, consumer);
}


#[test]
fn symbolic_write_mem() {
    let consumer = |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                assert_eq!(
                    &input[..4],
                    &[7, 3, 21, 21]);

                false
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), "tests/symbolic/write_mem.rs".to_string()];
    ::seer::run_symbolic(args, consumer);
}
