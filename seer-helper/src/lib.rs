#[allow(unused_variables)]
pub fn mksym<T>(var: &mut T) {
}

#[allow(unused_variables)]
pub fn test(s: &str) {
}

use std::fmt;
pub fn print<T: fmt::Debug>(t: T) -> String{
    format!("{:?}", t)
}
