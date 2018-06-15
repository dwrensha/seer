union Slices<'a> {
    str: &'a str,
    slice: &'a [u8],
}

fn main() {
    let _v: &[u8] = unsafe { Slices { str: "abc" }.slice };
}
