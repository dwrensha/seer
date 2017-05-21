#![feature(custom_attribute)]
#![no_main]

use std::collections::BinaryHeap;

#[symbolic_execution_entry_point]
fn heap(data: &[u8]) {
    let mut data2 = data[..7].to_owned();

    let mut heap = BinaryHeap::new();
    for d in data2 {
        heap.push(d);
    }


    let mut ceiling = 255;
    while let Some(d) = heap.pop() {
        if d > ceiling {
            panic!()
        }
        ceiling = d;
    }
}
