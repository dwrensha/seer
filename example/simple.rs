#![feature(custom_attribute)]
#![no_main]

#[symbolic_execution_entry_point]
fn simple(data: &[u8]) {
    if data.len() > 12 {
        panic!()
    }

    if data.len() < 1 {
        panic!()
    }

    if data[0] == 43 {
        panic!()
    }
}
