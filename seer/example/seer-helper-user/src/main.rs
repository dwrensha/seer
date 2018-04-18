extern crate seer_helper;

use std::fmt;

#[derive(Debug)]
struct Test {
    a: u32,
    b: u64,
}

fn main() {
    //let s = "abc".to_string();
    //let s = format!("abc");
    //let s = "abc";
    //seer_helper::test(s);
    seer_helper::test(&print(Test {a: 321, b: 123}));
}

fn print<T: fmt::Debug>(t: T) -> String {
    format!("{:?}", t)
}
