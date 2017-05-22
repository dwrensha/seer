#![feature(custom_attribute)]
#![no_main]

use std::collections::BTreeSet;

#[symbolic_execution_entry_point]
fn btreeset(data: &[u8]) {
    let data2 = data.to_owned();

    let mut heap = BTreeSet::new();
    for d in data2 {
        heap.insert(d);
    }

    let mut floor = 0;
    for d in heap.iter() {
        if *d < floor {
            panic!()
        }
        floor = *d;
    }
}
