//! Minimal unsigned LEB128 (canonical: shortest form enforced on decode).

pub fn write_u64(out: &mut Vec<u8>, mut v: u64) {
    loop {
        let mut b = (v & 0x7f) as u8;
        v >>= 7;
        if v != 0 {
            b |= 0x80;
        }
        out.push(b);
        if v == 0 {
            break;
        }
    }
}

pub fn write_usize(out: &mut Vec<u8>, v: usize) {
    write_u64(out, v as u64)
}

pub fn write_bytes(out: &mut Vec<u8>, bytes: &[u8]) {
    write_usize(out, bytes.len());
    out.extend_from_slice(bytes);
}

pub fn write_str(out: &mut Vec<u8>, s: &str) {
    write_bytes(out, s.as_bytes())
}

#[derive(Debug, Clone)]
pub struct DecodeError(pub String);

impl std::fmt::Display for DecodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "decode error: {}", self.0)
    }
}
impl std::error::Error for DecodeError {}

pub type DResult<T> = Result<T, DecodeError>;

pub struct Reader<'a> {
    pub data: &'a [u8],
    pub pos: usize,
}

impl<'a> Reader<'a> {
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }
    pub fn remaining(&self) -> usize {
        self.data.len() - self.pos
    }
    pub fn is_done(&self) -> bool {
        self.pos == self.data.len()
    }
    pub fn byte(&mut self) -> DResult<u8> {
        if self.pos >= self.data.len() {
            return Err(DecodeError("unexpected end of input".into()));
        }
        let b = self.data[self.pos];
        self.pos += 1;
        Ok(b)
    }
    pub fn bytes(&mut self, n: usize) -> DResult<&'a [u8]> {
        if self.remaining() < n {
            return Err(DecodeError("unexpected end of input".into()));
        }
        let s = &self.data[self.pos..self.pos + n];
        self.pos += n;
        Ok(s)
    }
    pub fn u64(&mut self) -> DResult<u64> {
        let mut result: u64 = 0;
        let mut shift = 0u32;
        loop {
            let b = self.byte()?;
            if shift == 63 && b > 1 {
                return Err(DecodeError("LEB128 value overflows u64".into()));
            }
            result |= ((b & 0x7f) as u64) << shift;
            if b & 0x80 == 0 {
                // canonical minimal form: a multi-byte encoding may not end in 0 group
                if shift > 0 && (b & 0x7f) == 0 && result != 0 {
                    // final zero group means encoding was not minimal unless value fits shorter
                    // Detect: value must need this many bytes.
                    let needed = 64 - result.leading_zeros();
                    let used = (shift / 7) + 1;
                    let minimal = ((needed + 6) / 7).max(1);
                    if used != minimal {
                        return Err(DecodeError("non-minimal LEB128 encoding".into()));
                    }
                }
                return Ok(result);
            }
            shift += 7;
            if shift >= 70 {
                return Err(DecodeError("LEB128 encoding too long".into()));
            }
        }
    }
    pub fn usize(&mut self) -> DResult<usize> {
        let v = self.u64()?;
        usize::try_from(v).map_err(|_| DecodeError("integer does not fit usize".into()))
    }
    pub fn take_bytes(&mut self) -> DResult<Vec<u8>> {
        let n = self.usize()?;
        if n > self.remaining() {
            return Err(DecodeError("length-delimited field exceeds input".into()));
        }
        Ok(self.bytes(n)?.to_vec())
    }
    pub fn string(&mut self) -> DResult<String> {
        let b = self.take_bytes()?;
        String::from_utf8(b).map_err(|_| DecodeError("invalid UTF-8".into()))
    }
}
