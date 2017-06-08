use std::io::{self, Result};

use ::byteorder::ByteOrder;

pub trait ReadBytesExt: io::Read {
    #[inline]
    fn read_u8(&mut self) -> Result<u8> {
        let mut buf = [0; 1];
        try!(self.read_exact(&mut buf));
        Ok(buf[0])
    }

    #[inline]
    fn read_i8(&mut self) -> Result<i8> {
        let mut buf = [0; 1];
        try!(self.read_exact(&mut buf));
        Ok(buf[0] as i8)
    }

    #[inline]
    fn read_u16<T: ByteOrder>(&mut self) -> Result<u16> {
        let mut buf = [0; 2];
        try!(self.read_exact(&mut buf));
        Ok(T::read_u16(&buf))
    }

    #[inline]
    fn read_i16<T: ByteOrder>(&mut self) -> Result<i16> {
        let mut buf = [0; 2];
        try!(self.read_exact(&mut buf));
        Ok(T::read_i16(&buf))
    }

    #[inline]
    fn read_u32<T: ByteOrder>(&mut self) -> Result<u32> {
        let mut buf = [0; 4];
        try!(self.read_exact(&mut buf));
        Ok(T::read_u32(&buf))
    }

    #[inline]
    fn read_i32<T: ByteOrder>(&mut self) -> Result<i32> {
        let mut buf = [0; 4];
        try!(self.read_exact(&mut buf));
        Ok(T::read_i32(&buf))
    }

    #[inline]
    fn read_u64<T: ByteOrder>(&mut self) -> Result<u64> {
        let mut buf = [0; 8];
        try!(self.read_exact(&mut buf));
        Ok(T::read_u64(&buf))
    }

    #[inline]
    fn read_i64<T: ByteOrder>(&mut self) -> Result<i64> {
        let mut buf = [0; 8];
        try!(self.read_exact(&mut buf));
        Ok(T::read_i64(&buf))
    }

    #[inline]
    fn read_u128<T: ByteOrder>(&mut self) -> Result<u128> {
        let mut buf = [0; 16];
        try!(self.read_exact(&mut buf));
        Ok(T::read_u128(&buf))
    }

    #[inline]
    fn read_i128<T: ByteOrder>(&mut self) -> Result<i128> {
        let mut buf = [0; 16];
        try!(self.read_exact(&mut buf));
        Ok(T::read_i128(&buf))
    }

    #[inline]
    fn read_uint<T: ByteOrder>(&mut self, nbytes: usize) -> Result<u64> {
        let mut buf = [0; 8];
        try!(self.read_exact(&mut buf[..nbytes]));
        Ok(T::read_uint(&buf[..nbytes], nbytes))
    }

    #[inline]
    fn read_int<T: ByteOrder>(&mut self, nbytes: usize) -> Result<i64> {
        let mut buf = [0; 8];
        try!(self.read_exact(&mut buf[..nbytes]));
        Ok(T::read_int(&buf[..nbytes], nbytes))
    }

    /// Reads an unsigned n-bytes integer from the underlying reader.
    #[inline]
    fn read_uint128<T: ByteOrder>(&mut self, nbytes: usize) -> Result<u128> {
        let mut buf = [0; 16];
        try!(self.read_exact(&mut buf[..nbytes]));
        Ok(T::read_uint128(&buf[..nbytes], nbytes))
    }

    /// Reads a signed n-bytes integer from the underlying reader.
    #[inline]
    fn read_int128<T: ByteOrder>(&mut self, nbytes: usize) -> Result<i128> {
        let mut buf = [0; 16];
        try!(self.read_exact(&mut buf[..nbytes]));
        Ok(T::read_int128(&buf[..nbytes], nbytes))
    }

    #[inline]
    fn read_f32<T: ByteOrder>(&mut self) -> Result<f32> {
        let mut buf = [0; 4];
        try!(self.read_exact(&mut buf));
        Ok(T::read_f32(&buf))
    }

    /// Reads a IEEE754 double-precision (8 bytes) floating point number from
    /// the underlying reader.
    #[inline]
    fn read_f64<T: ByteOrder>(&mut self) -> Result<f64> {
        let mut buf = [0; 8];
        try!(self.read_exact(&mut buf));
        Ok(T::read_f64(&buf))
    }
}

/// All types that implement `Read` get methods defined in `ReadBytesExt`
/// for free.
impl<R: io::Read + ?Sized> ReadBytesExt for R {}

pub trait WriteBytesExt: io::Write {
    #[inline]
    fn write_u8(&mut self, n: u8) -> Result<()> {
        self.write_all(&[n])
    }

    #[inline]
    fn write_i8(&mut self, n: i8) -> Result<()> {
        self.write_all(&[n as u8])
    }

    #[inline]
    fn write_u16<T: ByteOrder>(&mut self, n: u16) -> Result<()> {
        let mut buf = [0; 2];
        T::write_u16(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_i16<T: ByteOrder>(&mut self, n: i16) -> Result<()> {
        let mut buf = [0; 2];
        T::write_i16(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_u32<T: ByteOrder>(&mut self, n: u32) -> Result<()> {
        let mut buf = [0; 4];
        T::write_u32(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_i32<T: ByteOrder>(&mut self, n: i32) -> Result<()> {
        let mut buf = [0; 4];
        T::write_i32(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_u64<T: ByteOrder>(&mut self, n: u64) -> Result<()> {
        let mut buf = [0; 8];
        T::write_u64(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_i64<T: ByteOrder>(&mut self, n: i64) -> Result<()> {
        let mut buf = [0; 8];
        T::write_i64(&mut buf, n);
        self.write_all(&buf)
    }

    /// Writes an unsigned 128 bit integer to the underlying writer.
    #[inline]
    fn write_u128<T: ByteOrder>(&mut self, n: u128) -> Result<()> {
        let mut buf = [0; 16];
        T::write_u128(&mut buf, n);
        self.write_all(&buf)
    }

    /// Writes a signed 128 bit integer to the underlying writer.
    #[inline]
    fn write_i128<T: ByteOrder>(&mut self, n: i128) -> Result<()> {
        let mut buf = [0; 16];
        T::write_i128(&mut buf, n);
        self.write_all(&buf)
    }

    #[inline]
    fn write_uint<T: ByteOrder>(
        &mut self,
        n: u64,
        nbytes: usize,
    ) -> Result<()> {
        let mut buf = [0; 8];
        T::write_uint(&mut buf, n, nbytes);
        self.write_all(&buf[0..nbytes])
    }

    /// Writes a signed n-bytes integer to the underlying writer.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    ///
    /// # Panics
    ///
    /// If the given integer is not representable in the given number of bytes,
    /// this method panics. If `nbytes > 8`, this method panics.
    #[inline]
    fn write_int<T: ByteOrder>(
        &mut self,
        n: i64,
        nbytes: usize,
    ) -> Result<()> {
        let mut buf = [0; 8];
        T::write_int(&mut buf, n, nbytes);
        self.write_all(&buf[0..nbytes])
    }

    /// Writes an unsigned n-bytes integer to the underlying writer.
    ///
    /// If the given integer is not representable in the given number of bytes,
    /// this method panics. If `nbytes > 16`, this method panics.
    #[inline]
    fn write_uint128<T: ByteOrder>(
        &mut self,
        n: u128,
        nbytes: usize,
    ) -> Result<()> {
        let mut buf = [0; 16];
        T::write_uint128(&mut buf, n, nbytes);
        self.write_all(&buf[0..nbytes])
    }

    /// Writes a signed n-bytes integer to the underlying writer.
    ///
    /// If the given integer is not representable in the given number of bytes,
    /// this method panics. If `nbytes > 16`, this method panics.
    #[inline]
    fn write_int128<T: ByteOrder>(
        &mut self,
        n: i128,
        nbytes: usize,
    ) -> Result<()> {
        let mut buf = [0; 16];
        T::write_int128(&mut buf, n, nbytes);
        self.write_all(&buf[0..nbytes])
    }

    /// Writes a IEEE754 single-precision (4 bytes) floating point number to
    /// the underlying writer.
    ///
    /// # Errors
    ///
    /// This method returns the same errors as [`Write::write_all`].
    ///
    /// [`Write::write_all`]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    #[inline]
    fn write_f32<T: ByteOrder>(&mut self, n: f32) -> Result<()> {
        let mut buf = [0; 4];
        T::write_f32(&mut buf, n);
        self.write_all(&buf)
    }

    /// Writes a IEEE754 double-precision (8 bytes) floating point number to
    /// the underlying writer.
    #[inline]
    fn write_f64<T: ByteOrder>(&mut self, n: f64) -> Result<()> {
        let mut buf = [0; 8];
        T::write_f64(&mut buf, n);
        self.write_all(&buf)
    }
}

/// All types that implement `Write` get methods defined in `WriteBytesExt`
/// for free.
impl<W: io::Write + ?Sized> WriteBytesExt for W {}
