#![feature(custom_attribute)]
#![no_main]

#[symbolic_execution_entry_point]
fn simple(data: &[u8]) {

    // should panic on [ 17, 18, 38, 37, 101, .. ];

    if data.len() >= 5 {
        if 16 < data[0] && data[0] < data[1] && data[1] <= 18 {
            if 39 > data[2] && data[2] > data[3] && data[3] >= 37 {
                let x = data[4];
                if x != 100 {
                    if !(x == 102) {
                        if x > 100 && x < 103 {
                            panic!()
                        }
                    }
                }
            }
        }
    }
}
