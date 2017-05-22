#![feature(custom_attribute)]
#![no_main]

#[symbolic_execution_entry_point]
fn sort(data: &[u8]) {
    let mut data2 = data[..5].to_owned();

    data2.sort();

    let mut floor = 0;
    for d in data2 {
        if d < floor {
            panic!()
        }
        floor = d;
    }
}
