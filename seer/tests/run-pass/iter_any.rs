pub fn main() {
    let f = |x: &u8| { 10u8 == *x };
    f(&1u8);

    let g = |(), x: &u8| { 10u8 == *x };
    g((), &1u8);

    let h = |(), (), x: &u8| { 10u8 == *x };
    h((), (), &1u8);

    let h2 = |(), (), x: ((), &u8)| { 10u8 == *x.1 };
    h2((), (), ((), &1u8));

    [1, 2, 3u8].into_iter().any(|elt| 10 == *elt);
}
