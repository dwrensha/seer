fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 1];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let v: &[u32] = &[111, 222, 333, 444, 555];

    let mut p = v.as_ptr();

    let d0 = data[0]; // 2

    if d0 as usize >= v.len() {
        return;
    }

    p = unsafe { p.offset(d0 as isize) };

    let _ps: &[*const u32] = &[::std::ptr::null(), p];

    if unsafe { *p } == 333 {
        panic!()
    }
}
