// SEER lets us decode base64, given only an encoder function!

fn main() {
    use std::io::Read;
    let mut data: Vec<u8> = vec![0; 12];
    let mut stdin = ::std::io::stdin();
    stdin.read_exact(&mut data[..]).unwrap();

    let result_bytes: &[u8] = &to_base64(&data[..]);

    // str::from_utf8() requires stdlib MIR :(
    let result_str: &str = unsafe { ::std::mem::transmute(result_bytes) };

    let value_to_decode = "aGVsbG8gd29ybGQ";
    if result_str.starts_with(value_to_decode) {
        // This will panic on the input that encodes to `value_to_decode`.
        panic!("we found it!");
    }
}

// copied from rustc_serialize
fn to_base64(in_buf: &[u8]) -> Vec<u8> {
    static BYTES: &[u8] = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
    let len = in_buf.len();
    let mut out_bytes = vec![b'='; (len + 2) / 3 * 4];
    let mod_len = len % 3;
    {
        let mut s_in = in_buf[..len - mod_len].iter().map(|&x| x as u32);
        let mut s_out = out_bytes.iter_mut();
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
                let n = (in_buf[len-1] as u32) << 16;
                write(enc((n >> 18) & 63));
                write(enc((n >> 12) & 63));
            }
            2 => {
                let n = (in_buf[len-2] as u32) << 16 |
                (in_buf[len-1] as u32) << 8;
                write(enc((n >> 18) & 63));
                write(enc((n >> 12) & 63));
                write(enc((n >> 6 ) & 63));
            }
            _ => unreachable!(),
        }
    }
    out_bytes
}
