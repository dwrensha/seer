#![feature(custom_attribute)]
#![no_main]

#[symbolic_execution_entry_point]
fn simple(data: &[u8]) {
    if data.len() > 10 {
        panic!()
    }
}
