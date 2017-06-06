extern crate seer;

use std::rc::Rc;
use std::cell::RefCell;

fn expect_single_panic(filename: &str, expected_result: Vec<u8>) {
    expect_panics(filename, vec![expected_result]);
}

fn expect_panics(filename: &str, mut expected_results: Vec<Vec<u8>>) {
    let found = Rc::new(RefCell::new(Vec::new()));
    let found1 = found.clone();
    let consumer = move |complete| {
        match complete {
            ::seer::ExecutionComplete { result: Err(::seer::StaticEvalError::Panic),
                                        input } => {
                found1.borrow_mut().push(input);
                true
            }
            _ => true,
        }
    };

    let args = vec!["run_symbolic".to_string(), filename.to_string()];
    ::seer::ExecutionConfig::new()
        .consumer(consumer)
        .run(args);

    let mut found = ::std::mem::replace(&mut *found.borrow_mut(), Vec::new());
    found.sort();
    expected_results.sort();

    assert_eq!(found, expected_results);
}


#[test]
fn symbolic_simple() {
    expect_single_panic("tests/symbolic/simple.rs", vec![43]);
}

#[test]
fn symbolic_manticore() {
    expect_single_panic(
        "tests/symbolic/manticore.rs",
        vec![61, 77, 65, 78, 84, 73, 67, 79, 82, 69, 61, 0, 1, 2, 3, 4, 5, 50, 51, 29, 212]);
}

#[test]
fn symbolic_comparisons() {
    expect_single_panic("tests/symbolic/comparisons.rs", vec![17, 18, 38, 37, 101]);
}

#[test]
fn symbolic_write_mem() {
    expect_single_panic("tests/symbolic/write_mem.rs", vec![7, 3, 21, 21]);
}

#[test]
fn symbolic_read_u16() {
    expect_single_panic("tests/symbolic/read_u16.rs", vec![0xee, 0xff]);
}

#[test]
fn symbolic_read_u32() {
    expect_single_panic("tests/symbolic/read_u32.rs", vec![0x11, 0x22, 0x33, 0x44]);
}

#[test]
fn symbolic_read_u64() {
    expect_single_panic(
        "tests/symbolic/read_u64.rs",
        vec![0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11]);
}

#[test]
fn symbolic_read_bool() {
    expect_single_panic(
        "tests/symbolic/read_bool.rs",
        vec![0, 63]);
}

#[test]
fn symbolic_indexing() {
    expect_single_panic(
        "tests/symbolic/indexing.rs",
        vec![73]);
}

#[test]
fn symbolic_infeasible() {
    expect_panics("tests/symbolic/infeasible.rs", vec![]);
}
