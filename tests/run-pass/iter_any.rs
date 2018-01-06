pub fn main() {
    let g = |(), x: &u8| { 10u8 == *x };
    g((), &1u8);

    let f = |x: &u8| { 10u8 == *x };
    f(&1u8);

    [1, 2, 3u8].into_iter().any(|elt| 10 == *elt);
}
