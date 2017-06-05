extern crate seer;

fn expect_panic(filename: &str, expected_result: Vec<u8>) {
    let consumer = move |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                assert_eq!(input, expected_result);
                false
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), filename.to_string()];
    ::seer::ExecutionConfig::new()
        .consumer(consumer)
        .run(args);
}

#[test]
fn symbolic_simple() {
    expect_panic("tests/symbolic/simple.rs", vec![43]);
}

#[test]
fn symbolic_manticore() {
    expect_panic(
        "tests/symbolic/manticore.rs",
        vec![61, 77, 65, 78, 84, 73, 67, 79, 82, 69, 61, 0, 1, 2, 3, 4, 5, 50, 51, 29, 212]);
}

#[test]
fn symbolic_comparisons() {
    expect_panic("tests/symbolic/comparisons.rs", vec![17, 18, 38, 37, 101]);
}

#[test]
fn symbolic_write_mem() {
    expect_panic("tests/symbolic/write_mem.rs", vec![7, 3, 21, 21]);
}

#[test]
fn symbolic_read_u16() {
    expect_panic("tests/symbolic/read_u16.rs", vec![0xee, 0xff]);
}

#[test]
fn symbolic_read_u32() {
    expect_panic("tests/symbolic/read_u32.rs", vec![0x11, 0x22, 0x33, 0x44]);
}

#[test]
fn symbolic_read_u64() {
    expect_panic(
        "tests/symbolic/read_u64.rs",
        vec![0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]);
}

#[test]
fn symbolic_indexing() {
    expect_panic(
        "tests/symbolic/indexing.rs",
        vec![73]);
}

