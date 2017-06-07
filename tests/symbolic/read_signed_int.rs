fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 15];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    let one_byte = data[0] as i8;

    if one_byte & 1 == 0 && (one_byte >> 1) == -64i8 { // data[0] = 0x80

        let two_bytes = ((data[1] as u16) + ((data[2] as u16) << 8)) as i16;

        if two_bytes & 255 == 67 && two_bytes >> 8 == -2 { // data[1] = 67, data[2] = 254

            let four_bytes =
                ((data[3] as u32) + // 0x55
                 ((data[4] as u32) << 8) + // 0x66
                 ((data[5] as u32) << 16) + // 0x77
                 ((data[6] as u32) << 24)) as i32; // 0x88

            if four_bytes & 0xfff == 0x655 && four_bytes >> 12 == (0xfff88776u32 as i32) {

                let eight_bytes =
                    ((data[7] as u64) +                 // 0x99
                     ((data[8] as u64) << 8) +          // 0x88
                     ((data[9] as u64) << 16) +         // 0x77
                     ((data[10] as u64) << 24) +        // 0x66
                     ((data[11] as u64) << 32)+         // 0x55
                     ((data[12] as u64) << 40) +        // 0x44
                     ((data[13] as u64) << 48) +        // 0x33
                     ((data[14] as u64) << 56)) as i64; // 0x22


                if eight_bytes & 0xf == 0x9 && eight_bytes >> 4 == 0x223344556677889 {
                    panic!()
                }
            }
        }
    }
}
