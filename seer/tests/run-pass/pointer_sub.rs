pub fn main() {
    let buf = [0u8; 100];

    let p0 = &buf[0] as *const _ as isize;
    let p1 = &buf[1] as *const _ as isize;

    assert_eq!(p1.wrapping_sub(p0), 1);
}
