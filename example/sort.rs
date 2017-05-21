#![feature(custom_attribute)]
#![no_main]

#[symbolic_execution_entry_point]
fn sort(data: &[u8]) {
    let mut data2 = data.to_owned();

    data2.sort();
}
