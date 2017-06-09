// SEER lets us decode base64, given only an encoder function!

fn main() {
    use std::io::Read;
    let value_to_decode = "aGVsbG8gd29ybGQh";
    let mut data: Vec<u8> = vec![0; (value_to_decode.len() + 3) / 4 * 3];
    std::io::stdin().read_exact(&mut data[..]).unwrap();

    let result = base64_encode(&data[..]);
    if result.starts_with(value_to_decode) {
        // This will panic on the input that encodes to `value_to_decode`.
        panic!("we found it!");
    }
}

// copied from rustc_serialize
fn base64_encode(input: &[u8]) -> String {
    static BYTES: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let mut result = String::new();
    {
        let len = input.len();
        let output = unsafe { result.as_mut_vec() };
        *output = vec![b'='; (len + 2) / 3 * 4];
        let mod_len = len % 3;
        {
            let mut s_in = input[..len - mod_len].iter().map(|&x| x as u32);
            let mut s_out = output.iter_mut();
            let enc = |val| BYTES[val as usize];
            let mut write = |val| *s_out.next().unwrap() = val;

            while let (Some(first), Some(second), Some(third)) =
                (s_in.next(), s_in.next(), s_in.next())
            {
                let n = first << 16 | second << 8 | third;
                write(enc((n >> 18) & 63));
                write(enc((n >> 12) & 63));
                write(enc((n >> 6 ) & 63));
                write(enc((n >> 0 ) & 63));
            }

            match mod_len {
                0 => (),
                1 => {
                    let n = (input[len-1] as u32) << 16;
                    write(enc((n >> 18) & 63));
                    write(enc((n >> 12) & 63));
                }
                2 => {
                    let n = (input[len-2] as u32) << 16 |
                    (input[len-1] as u32) << 8;
                    write(enc((n >> 18) & 63));
                    write(enc((n >> 12) & 63));
                    write(enc((n >> 6 ) & 63));
                }
                _ => unreachable!(),
            }
        }
    }
    result
}
