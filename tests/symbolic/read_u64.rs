fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 8];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let eight_bytes =
        (data[0] as u64) +
        ((data[1] as u64) << 8) +
        ((data[2] as u64) << 16) +
        ((data[3] as u64) << 24) +
        ((data[4] as u64) << 32)+
        ((data[5] as u64) << 40) +
        ((data[6] as u64) << 48) +
        ((data[7] as u64) << 56);

    if eight_bytes == 0x1122334455667788u64 && eight_bytes.swap_bytes() == 0x8877665544332211u64 {
        panic!()
    }
}
