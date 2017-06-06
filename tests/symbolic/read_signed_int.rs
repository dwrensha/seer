fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 3];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let one_byte = data[0] as i8;

    if one_byte & 1 == 0 && (one_byte >> 1) == -64i8 { // data[0] = 0x80

        let two_bytes = ((data[1] as u16) + ((data[2] as u16) << 8)) as i16;

        if two_bytes & 255 == 67 && two_bytes >> 8 == -2 { // data[1] = 67, data[2] = 254
            panic!()
        }
    }
}
