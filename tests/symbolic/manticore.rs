// Example adapted from https://blog.trailofbits.com/2017/05/15/magic-with-manticore/
// libfuzzer fails to find the panic quickly.

fn check_char_0(mut ch: u8) -> Result<(), ()> {
    ch ^= 97;

    if ch == 92 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_1(mut ch: u8) -> Result<(), ()> {
    ch ^= 107;
    ch += 67;

    if ch == 105 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_2(mut ch: u8) -> Result<(), ()> {
    ch += 61;
    ch *= 2;

    if ch == 252 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_3(mut ch: u8) -> Result<(), ()> {
    ch ^= 149;

    if ch == 219 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_4(mut ch: u8) -> Result <(), ()> {
    ch ^= 19;
    ch *= 2;

    if ch == 142 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_5(mut ch: u8) -> Result<(), ()> {
    ch ^= 5;
    ch *= 3;

    if ch == 228 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_6(mut ch: u8) -> Result<(), ()> {
    ch += 71;

    if ch == 138 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_7(mut ch: u8) -> Result<(), ()> {
    ch ^= 41;

    if ch == 102 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_8(mut ch: u8) -> Result<(), ()> {
    ch += 41;
    ch += 53;

    if ch == 176 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_9(mut ch: u8) -> Result<(), ()> {
    ch ^= 61;
    ch += 41;
    ch += 11;

    if ch == 172 {
        Ok(())
    } else {
        Err(())
    }
}

fn check_char_10(mut ch: u8) -> Result<(), ()> {
    ch ^= 47;
    ch += 29;
    ch += 67;

    if ch == 114 {
        Ok(())
    } else {
        Err(())
    }
}


fn check(buf: &[u8]) -> Result<(), ()> {
    if buf.len() < 12 { return Err(()) }

    check_char_0(buf[0])?;
    check_char_1(buf[1])?;
    check_char_2(buf[2])?;
    check_char_3(buf[3])?;
    check_char_4(buf[4])?;
    check_char_5(buf[5])?;
    check_char_6(buf[6])?;
    check_char_7(buf[7])?;
    check_char_8(buf[8])?;
    check_char_9(buf[9])?;
    check_char_10(buf[10])?;

    Ok(())
}


pub fn main() {
    use std::io::Read;

    let mut data: Vec<u8> = vec![0; 21];
    let mut stdin = ::std::io::stdin();
    stdin.read(&mut data[..]).unwrap();

    if Ok(()) == check(&data[..]) && &data[12..] == &[1,2,3,4,5,50,51,29,212] {
        panic!("found the secret code");
    }
}
