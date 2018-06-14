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

    let args = vec!["seer".to_string(), filename.to_string()];
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
fn symbolic_read_char() {
    expect_single_panic(
        "tests/symbolic/read_char.rs",
        vec![0x3a, 0x26]);
}

#[test]
fn symbolic_read_signed_int() {
    expect_single_panic(
        "tests/symbolic/read_signed_int.rs",
        vec![0x80,
             67, 254,
             0x55, 0x66, 0x77, 0x88,
             0x99, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22]);
}

#[test]
fn symbolic_indexing() {
    expect_single_panic(
        "tests/symbolic/indexing.rs",
        vec![73, 158]);
}

#[test]
fn symbolic_infeasible() {
    expect_panics("tests/symbolic/infeasible.rs", vec![]);
}

#[test]
fn symbolic_memcmp() {
    expect_single_panic(
        "tests/symbolic/memcmp.rs",
        vec![10,11,12,13, 21,22,23,24, 10,11,12,13, 21,22,23,24]);
}

#[test]
fn symbolic_str_starts_with() {
    expect_single_panic(
        "tests/symbolic/str_starts_with.rs",
        "hello world".as_bytes().into());
}

#[test]
fn symbolic_bitwise_bool() {
    expect_single_panic(
        "tests/symbolic/bitwise_bool.rs",
        vec![1,1, 0,0, 0,1]);
}

#[test]
fn symbolic_div() {
    expect_single_panic(
        "tests/symbolic/div.rs",
        vec![57, 199]);
}

#[test]
fn symbolic_ptr_offset() {
    expect_single_panic(
        "tests/symbolic/ptr_offset.rs",
        vec![2, 4]);
}

#[test]
fn symbolic_ptr_offset_field() {
    expect_single_panic(
        "tests/symbolic/ptr_offset_field.rs",
        vec![3, 5]);
}

#[test]
fn symbolic_array_offset_field() {
    expect_single_panic(
        "tests/symbolic/array_offset_field.rs",
        vec![1, 4]);
}

#[test]
fn symbolic_slice() {
    expect_single_panic(
        "tests/symbolic/slice.rs",
        vec![35]);
}

#[test]
fn symbolic_cast_bool() {
    expect_single_panic(
        "tests/symbolic/bool_cast.rs",
        vec![18, 102]);

}

#[test]
fn symbolic_neg() {
    expect_single_panic(
        "tests/symbolic/neg.rs",
        vec![75]);

}

#[test]
fn symbolic_trailing_zeros() {
    expect_single_panic(
        "tests/symbolic/trailing_zeros.rs",
        vec![128]);

}

#[test]
fn symbolic_leading_zeros() {
    expect_single_panic(
        "tests/symbolic/leading_zeros.rs",
        vec![1]);

}

#[test]
fn symbolic_count_ones() {
    expect_single_panic(
        "tests/symbolic/count_ones.rs",
        vec![255]);

}
