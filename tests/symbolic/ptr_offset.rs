fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 2];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let v: &[u32] = &[111, 222, 333, 444, 555, 666, 777, 888, 999, 101010, ];

    let mut p = v.as_ptr();

    let d0 = data[0]; // 2
    let d1 = data[1]; // 4

    if (d0 + d1) as usize >= v.len() {
        return;
    }

    p = unsafe { p.offset(d0 as isize) };

    let ps: &[*const u32] = &[::std::ptr::null(), p];

    let q = unsafe { p.offset(d1 as isize) };

    if unsafe { *ps[1] } == 333 {
        if p > v.as_ptr() && p >= v.as_ptr() && v.as_ptr() < p && v.as_ptr() <= p {
            if unsafe { *q } == 777 {
                panic!()
            }
        }
    }
}
