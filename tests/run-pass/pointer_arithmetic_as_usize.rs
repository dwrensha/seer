fn main() {
    let v: &[u8] = &[0,1,2,3,4,5,6,7,8,9];
    let p = v.as_ptr() as usize;
    for offset in 0..v.len() {
        let p1: *const u8 = unsafe { ::std::mem::transmute(p + offset) };
        let x = unsafe { *p1 };
        assert_eq!(x, offset as u8);
    }
}
