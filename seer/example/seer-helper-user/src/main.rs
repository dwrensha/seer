extern crate seer_helper;

use std::fmt;

#[derive(Debug)]
struct Test {
    a: u32,
    b: u64,
}

fn main() {
    let mut t = Test {a:0,b:0};
    seer_helper::mksym(&mut t);
    if t.a == 123 && t.b == 321 {panic!()}
}

#[allow(dead_code)]
fn print<T: fmt::Debug>(t: T) -> String {
    format!("{:?}", t)
}
