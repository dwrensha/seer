/*
horrible hack: we include the byteorder crate inline, so that
we can use the 'i128' feature and publish to crates.io

https://github.com/BurntSushi/byteorder/issues/89
*/


use core::fmt::Debug;
use core::hash::Hash;
use core::mem::transmute;
use core::ptr::copy_nonoverlapping;

pub use self::new::{ReadBytesExt, WriteBytesExt};

mod new;

#[inline]
fn extend_sign(val: u64, nbytes: usize) -> i64 {
    let shift = (8 - nbytes) * 8;
    (val << shift) as i64 >> shift
}

#[inline]
fn extend_sign128(val: u128, nbytes: usize) -> i128 {
    let shift = (16 - nbytes) * 8;
    (val << shift) as i128 >> shift
}

#[inline]
fn unextend_sign(val: i64, nbytes: usize) -> u64 {
    let shift = (8 - nbytes) * 8;
    (val << shift) as u64 >> shift
}

#[inline]
fn unextend_sign128(val: i128, nbytes: usize) -> u128 {
    let shift = (16 - nbytes) * 8;
    (val << shift) as u128 >> shift
}

#[inline]
fn pack_size(n: u64) -> usize {
    if n < 1 << 8 {
        1
    } else if n < 1 << 16 {
        2
    } else if n < 1 << 24 {
        3
    } else if n < 1 << 32 {
        4
    } else if n < 1 << 40 {
        5
    } else if n < 1 << 48 {
        6
    } else if n < 1 << 56 {
        7
    } else {
        8
    }
}

#[inline]
fn pack_size128(n: u128) -> usize {
    if n < 1 << 8 {
        1
    } else if n < 1 << 16 {
        2
    } else if n < 1 << 24 {
        3
    } else if n < 1 << 32 {
        4
    } else if n < 1 << 40 {
        5
    } else if n < 1 << 48 {
        6
    } else if n < 1 << 56 {
        7
    } else if n < 1 << 64 {
        8
    } else if n < 1 << 72 {
        9
    } else if n < 1 << 80 {
        10
    } else if n < 1 << 88 {
        11
    } else if n < 1 << 96 {
        12
    } else if n < 1 << 104 {
        13
    } else if n < 1 << 112 {
        14
    } else if n < 1 << 120 {
        15
    } else {
        16
    }
}

mod private {
    /// Sealed stops crates other than byteorder from implementing any traits that use it.
    pub trait Sealed{}
    impl Sealed for super::LittleEndian {}
    impl Sealed for super::BigEndian {}
}

pub trait ByteOrder
    : Clone + Copy + Debug + Default + Eq + Hash + Ord + PartialEq + PartialOrd + private::Sealed {
    fn read_u16(buf: &[u8]) -> u16;

    fn read_u32(buf: &[u8]) -> u32;

    fn read_u64(buf: &[u8]) -> u64;

    fn read_u128(buf: &[u8]) -> u128;

    fn read_uint(buf: &[u8], nbytes: usize) -> u64;
    fn read_uint128(buf: &[u8], nbytes: usize) -> u128;

    fn write_u16(buf: &mut [u8], n: u16);

    fn write_u32(buf: &mut [u8], n: u32);

    fn write_u64(buf: &mut [u8], n: u64);

    fn write_u128(buf: &mut [u8], n: u128);
    fn write_uint(buf: &mut [u8], n: u64, nbytes: usize);

    fn write_uint128(buf: &mut [u8], n: u128, nbytes: usize);

    #[inline]
    fn read_i16(buf: &[u8]) -> i16 {
        Self::read_u16(buf) as i16
    }

    #[inline]
    fn read_i32(buf: &[u8]) -> i32 {
        Self::read_u32(buf) as i32
    }

    #[inline]
    fn read_i64(buf: &[u8]) -> i64 {
        Self::read_u64(buf) as i64
    }

    #[inline]
    fn read_i128(buf: &[u8]) -> i128 {
        Self::read_u128(buf) as i128
    }

    #[inline]
    fn read_int(buf: &[u8], nbytes: usize) -> i64 {
        extend_sign(Self::read_uint(buf, nbytes), nbytes)
    }

    #[inline]
    fn read_int128(buf: &[u8], nbytes: usize) -> i128 {
        extend_sign128(Self::read_uint128(buf, nbytes), nbytes)
    }

    #[inline]
    fn read_f32(buf: &[u8]) -> f32 {
        unsafe { transmute(Self::read_u32(buf)) }
    }

    #[inline]
    fn read_f64(buf: &[u8]) -> f64 {
        unsafe { transmute(Self::read_u64(buf)) }
    }

    #[inline]
    fn write_i16(buf: &mut [u8], n: i16) {
        Self::write_u16(buf, n as u16)
    }

    #[inline]
    fn write_i32(buf: &mut [u8], n: i32) {
        Self::write_u32(buf, n as u32)
    }

    #[inline]
    fn write_i64(buf: &mut [u8], n: i64) {
        Self::write_u64(buf, n as u64)
    }

    #[inline]
    fn write_i128(buf: &mut [u8], n: i128) {
        Self::write_u128(buf, n as u128)
    }

    #[inline]
    fn write_int(buf: &mut [u8], n: i64, nbytes: usize) {
        Self::write_uint(buf, unextend_sign(n, nbytes), nbytes)
    }

    #[inline]
    fn write_int128(buf: &mut [u8], n: i128, nbytes: usize) {
        Self::write_uint128(buf, unextend_sign128(n, nbytes), nbytes)
    }

    #[inline]
    fn write_f32(buf: &mut [u8], n: f32) {
        Self::write_u32(buf, unsafe { transmute(n) })
    }

    #[inline]
    fn write_f64(buf: &mut [u8], n: f64) {
        Self::write_u64(buf, unsafe { transmute(n) })
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum BigEndian {}

impl Default for BigEndian {
    fn default() -> BigEndian {
        panic!("BigEndian default")
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum LittleEndian {}

impl Default for LittleEndian {
    fn default() -> LittleEndian {
        panic!("LittleEndian default")
    }
}

pub type NetworkEndian = BigEndian;

#[cfg(target_endian = "little")]
pub type NativeEndian = LittleEndian;

/// Defines system native-endian serialization.
///
/// Note that this type has no value constructor. It is used purely at the
/// type level.
#[cfg(target_endian = "big")]
pub type NativeEndian = BigEndian;

macro_rules! read_num_bytes {
    ($ty:ty, $size:expr, $src:expr, $which:ident) => ({
        assert!($size == ::core::mem::size_of::<$ty>());
        assert!($size <= $src.len());
        let mut data: $ty = 0;
        unsafe {
            copy_nonoverlapping(
                $src.as_ptr(),
                &mut data as *mut $ty as *mut u8,
                $size);
        }
        data.$which()
    });
}

macro_rules! write_num_bytes {
    ($ty:ty, $size:expr, $n:expr, $dst:expr, $which:ident) => ({
        assert!($size <= $dst.len());
        unsafe {
            // N.B. https://github.com/rust-lang/rust/issues/22776
            let bytes = transmute::<_, [u8; $size]>($n.$which());
            copy_nonoverlapping((&bytes).as_ptr(), $dst.as_mut_ptr(), $size);
        }
    });
}

impl ByteOrder for BigEndian {
    #[inline]
    fn read_u16(buf: &[u8]) -> u16 {
        read_num_bytes!(u16, 2, buf, to_be)
    }

    #[inline]
    fn read_u32(buf: &[u8]) -> u32 {
        read_num_bytes!(u32, 4, buf, to_be)
    }

    #[inline]
    fn read_u64(buf: &[u8]) -> u64 {
        read_num_bytes!(u64, 8, buf, to_be)
    }

    #[inline]
    fn read_u128(buf: &[u8]) -> u128 {
        read_num_bytes!(u128, 16, buf, to_be)
    }

    #[inline]
    fn read_uint(buf: &[u8], nbytes: usize) -> u64 {
        assert!(1 <= nbytes && nbytes <= 8 && nbytes <= buf.len());
        let mut out = [0u8; 8];
        let ptr_out = out.as_mut_ptr();
        unsafe {
            copy_nonoverlapping(
                buf.as_ptr(), ptr_out.offset((8 - nbytes) as isize), nbytes);
            (*(ptr_out as *const u64)).to_be()
        }
    }

    #[inline]
    fn read_uint128(buf: &[u8], nbytes: usize) -> u128 {
        assert!(1 <= nbytes && nbytes <= 16 && nbytes <= buf.len());
        let mut out = [0u8; 16];
        let ptr_out = out.as_mut_ptr();
        unsafe {
            copy_nonoverlapping(
                buf.as_ptr(), ptr_out.offset((16 - nbytes) as isize), nbytes);
            (*(ptr_out as *const u128)).to_be()
        }
    }

    #[inline]
    fn write_u16(buf: &mut [u8], n: u16) {
        write_num_bytes!(u16, 2, n, buf, to_be);
    }

    #[inline]
    fn write_u32(buf: &mut [u8], n: u32) {
        write_num_bytes!(u32, 4, n, buf, to_be);
    }

    #[inline]
    fn write_u64(buf: &mut [u8], n: u64) {
        write_num_bytes!(u64, 8, n, buf, to_be);
    }

    #[inline]
    fn write_u128(buf: &mut [u8], n: u128) {
        write_num_bytes!(u128, 16, n, buf, to_be);
    }

    #[inline]
    fn write_uint(buf: &mut [u8], n: u64, nbytes: usize) {
        assert!(pack_size(n) <= nbytes && nbytes <= 8);
        assert!(nbytes <= buf.len());
        unsafe {
            let bytes: [u8; 8] = transmute(n.to_be());
            copy_nonoverlapping(
                bytes.as_ptr().offset((8 - nbytes) as isize),
                buf.as_mut_ptr(),
                nbytes);
        }
    }

    #[inline]
    fn write_uint128(buf: &mut [u8], n: u128, nbytes: usize) {
        assert!(pack_size128(n) <= nbytes && nbytes <= 16);
        assert!(nbytes <= buf.len());
        unsafe {
            let bytes: [u8; 16] = transmute(n.to_be());
            copy_nonoverlapping(
                bytes.as_ptr().offset((16 - nbytes) as isize),
                buf.as_mut_ptr(),
                nbytes);
        }
    }
}

impl ByteOrder for LittleEndian {
    #[inline]
    fn read_u16(buf: &[u8]) -> u16 {
        read_num_bytes!(u16, 2, buf, to_le)
    }

    #[inline]
    fn read_u32(buf: &[u8]) -> u32 {
        read_num_bytes!(u32, 4, buf, to_le)
    }

    #[inline]
    fn read_u64(buf: &[u8]) -> u64 {
        read_num_bytes!(u64, 8, buf, to_le)
    }

    #[inline]
    fn read_u128(buf: &[u8]) -> u128 {
        read_num_bytes!(u128, 16, buf, to_le)
    }

    #[inline]
    fn read_uint(buf: &[u8], nbytes: usize) -> u64 {
        assert!(1 <= nbytes && nbytes <= 8 && nbytes <= buf.len());
        let mut out = [0u8; 8];
        let ptr_out = out.as_mut_ptr();
        unsafe {
            copy_nonoverlapping(buf.as_ptr(), ptr_out, nbytes);
            (*(ptr_out as *const u64)).to_le()
        }
    }

    #[inline]
    fn read_uint128(buf: &[u8], nbytes: usize) -> u128 {
        assert!(1 <= nbytes && nbytes <= 16 && nbytes <= buf.len());
        let mut out = [0u8; 16];
        let ptr_out = out.as_mut_ptr();
        unsafe {
            copy_nonoverlapping(buf.as_ptr(), ptr_out, nbytes);
            (*(ptr_out as *const u128)).to_le()
        }
    }

    #[inline]
    fn write_u16(buf: &mut [u8], n: u16) {
        write_num_bytes!(u16, 2, n, buf, to_le);
    }

    #[inline]
    fn write_u32(buf: &mut [u8], n: u32) {
        write_num_bytes!(u32, 4, n, buf, to_le);
    }

    #[inline]
    fn write_u64(buf: &mut [u8], n: u64) {
        write_num_bytes!(u64, 8, n, buf, to_le);
    }

    #[inline]
    fn write_u128(buf: &mut [u8], n: u128) {
        write_num_bytes!(u128, 16, n, buf, to_le);
    }

    #[inline]
    fn write_uint(buf: &mut [u8], n: u64, nbytes: usize) {
        assert!(pack_size(n as u64) <= nbytes && nbytes <= 8);
        assert!(nbytes <= buf.len());
        unsafe {
            let bytes: [u8; 8] = transmute(n.to_le());
            copy_nonoverlapping(bytes.as_ptr(), buf.as_mut_ptr(), nbytes);
        }
    }

    #[inline]
    fn write_uint128(buf: &mut [u8], n: u128, nbytes: usize) {
        assert!(pack_size128(n as u128) <= nbytes && nbytes <= 16);
        assert!(nbytes <= buf.len());
        unsafe {
            let bytes: [u8; 16] = transmute(n.to_le());
            copy_nonoverlapping(bytes.as_ptr(), buf.as_mut_ptr(), nbytes);
        }
    }
}
