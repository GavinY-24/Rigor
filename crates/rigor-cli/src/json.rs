//! Minimal JSON parser for the dependency-free machine protocol.
//! It implements the JSON data model needed by `rigor machine`; it is not a
//! serializer for arbitrary Rust values.

use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    Null,
    Bool(bool),
    Number(String),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}

impl Json {
    pub fn get(&self, key: &str) -> Option<&Json> {
        match self {
            Json::Object(map) => map.get(key),
            _ => None,
        }
    }
    pub fn as_str(&self) -> Option<&str> {
        match self {
            Json::String(s) => Some(s),
            _ => None,
        }
    }
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Json::Bool(b) => Some(*b),
            _ => None,
        }
    }
    pub fn as_array(&self) -> Option<&[Json]> {
        match self {
            Json::Array(a) => Some(a),
            _ => None,
        }
    }
}

pub fn parse(src: &str) -> Result<Json, String> {
    let mut p = Parser { bytes: src.as_bytes(), pos: 0 };
    p.ws();
    let value = p.value()?;
    p.ws();
    if p.pos != p.bytes.len() {
        return Err(format!("trailing data at byte {}", p.pos));
    }
    Ok(value)
}

struct Parser<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn ws(&mut self) {
        while matches!(self.bytes.get(self.pos), Some(b' ' | b'\t' | b'\r' | b'\n')) {
            self.pos += 1;
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.pos).copied()
    }

    fn bump(&mut self) -> Option<u8> {
        let b = self.peek()?;
        self.pos += 1;
        Some(b)
    }

    fn expect(&mut self, b: u8) -> Result<(), String> {
        if self.bump() == Some(b) {
            Ok(())
        } else {
            Err(format!("expected '{}' at byte {}", b as char, self.pos))
        }
    }

    fn value(&mut self) -> Result<Json, String> {
        self.ws();
        match self.peek() {
            Some(b'n') => self.literal("null", Json::Null),
            Some(b't') => self.literal("true", Json::Bool(true)),
            Some(b'f') => self.literal("false", Json::Bool(false)),
            Some(b'\"') => self.string().map(Json::String),
            Some(b'[') => self.array(),
            Some(b'{') => self.object(),
            Some(b'-' | b'0'..=b'9') => self.number(),
            Some(other) => Err(format!("unexpected byte '{}' at byte {}", other as char, self.pos)),
            None => Err("unexpected end of input".into()),
        }
    }

    fn literal(&mut self, word: &str, value: Json) -> Result<Json, String> {
        if self.bytes.len() >= self.pos + word.len() && &self.bytes[self.pos..self.pos + word.len()] == word.as_bytes() {
            self.pos += word.len();
            Ok(value)
        } else {
            Err(format!("invalid literal at byte {}", self.pos))
        }
    }

    fn array(&mut self) -> Result<Json, String> {
        self.expect(b'[')?;
        let mut out = Vec::new();
        self.ws();
        if self.peek() == Some(b']') {
            self.pos += 1;
            return Ok(Json::Array(out));
        }
        loop {
            out.push(self.value()?);
            self.ws();
            match self.bump() {
                Some(b',') => {}
                Some(b']') => return Ok(Json::Array(out)),
                _ => return Err(format!("expected ',' or ']' at byte {}", self.pos)),
            }
        }
    }

    fn object(&mut self) -> Result<Json, String> {
        self.expect(b'{')?;
        let mut out = BTreeMap::new();
        self.ws();
        if self.peek() == Some(b'}') {
            self.pos += 1;
            return Ok(Json::Object(out));
        }
        loop {
            self.ws();
            let key = self.string()?;
            self.ws();
            self.expect(b':')?;
            let value = self.value()?;
            out.insert(key, value);
            self.ws();
            match self.bump() {
                Some(b',') => {}
                Some(b'}') => return Ok(Json::Object(out)),
                _ => return Err(format!("expected ',' or '}}' at byte {}", self.pos)),
            }
        }
    }

    fn number(&mut self) -> Result<Json, String> {
        let start = self.pos;
        if self.peek() == Some(b'-') {
            self.pos += 1;
        }
        match self.peek() {
            Some(b'0') => self.pos += 1,
            Some(b'1'..=b'9') => {
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
            }
            _ => return Err(format!("bad number at byte {start}")),
        }
        if self.peek() == Some(b'.') {
            self.pos += 1;
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return Err(format!("bad fraction at byte {}", self.pos));
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.pos += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.pos += 1;
            }
            if !matches!(self.peek(), Some(b'0'..=b'9')) {
                return Err(format!("bad exponent at byte {}", self.pos));
            }
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.pos += 1;
            }
        }
        String::from_utf8(self.bytes[start..self.pos].to_vec())
            .map(Json::Number)
            .map_err(|_| "number is not utf-8".into())
    }

    fn string(&mut self) -> Result<String, String> {
        self.expect(b'\"')?;
        let mut out = String::new();
        loop {
            let b = self.bump().ok_or_else(|| "unterminated string".to_string())?;
            match b {
                b'\"' => return Ok(out),
                b'\\' => {
                    let esc = self.bump().ok_or_else(|| "unterminated escape".to_string())?;
                    match esc {
                        b'\"' => out.push('\"'),
                        b'\\' => out.push('\\'),
                        b'/' => out.push('/'),
                        b'b' => out.push('\u{0008}'),
                        b'f' => out.push('\u{000c}'),
                        b'n' => out.push('\n'),
                        b'r' => out.push('\r'),
                        b't' => out.push('\t'),
                        b'u' => {
                            let first = self.hex4()?;
                            let cp = if (0xD800..0xDC00).contains(&first) {
                                let save = self.pos;
                                if self.bump() == Some(b'\\') && self.bump() == Some(b'u') {
                                    let second = self.hex4()?;
                                    if (0xDC00..0xE000).contains(&second) {
                                        0x10000 + ((first - 0xD800) << 10) + (second - 0xDC00)
                                    } else {
                                        return Err("lone high surrogate in string escape".into());
                                    }
                                } else {
                                    self.pos = save;
                                    return Err("lone high surrogate in string escape".into());
                                }
                            } else if (0xDC00..0xE000).contains(&first) {
                                return Err("lone low surrogate in string escape".into());
                            } else {
                                first
                            };
                            out.push(char::from_u32(cp).ok_or("invalid unicode scalar in string escape")?);
                        }
                        other => return Err(format!("bad escape \\{} at byte {}", other as char, self.pos)),
                    }
                }
                0x00..=0x1f => return Err("unescaped control byte in string".into()),
                b if b < 0x80 => out.push(b as char),
                b => {
                    // JSON text is UTF-8. Continue a multibyte scalar here.
                    let needed = if b >= 0xF0 { 3 } else if b >= 0xE0 { 2 } else if b >= 0xC0 { 1 } else { return Err("bad UTF-8 continuation".into()); };
                    let mut buf = vec![b];
                    for _ in 0..needed {
                        buf.push(self.bump().ok_or_else(|| "truncated UTF-8 in string".to_string())?);
                    }
                    let s = std::str::from_utf8(&buf).map_err(|_| "invalid UTF-8 in string".to_string())?;
                    out.push_str(s);
                }
            }
        }
    }

    fn hex4(&mut self) -> Result<u32, String> {
        let mut value = 0u32;
        for _ in 0..4 {
            let b = self.bump().ok_or_else(|| "truncated unicode escape".to_string())?;
            let digit = match b {
                b'0'..=b'9' => (b - b'0') as u32,
                b'a'..=b'f' => (b - b'a' + 10) as u32,
                b'A'..=b'F' => (b - b'A' + 10) as u32,
                _ => return Err("bad unicode escape".into()),
            };
            value = (value << 4) | digit;
        }
        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_nested_values_and_escapes() {
        let value = parse(r#"{"s":"line\n\u03bb\uD835\uDC9C","a":[true,null,-1.25e2],"utf8":"λ"}"#).unwrap();
        assert_eq!(value.get("s").and_then(|v| v.as_str()), Some("line\nλ𝒜"));
        assert_eq!(value.get("utf8").and_then(|v| v.as_str()), Some("λ"));
        assert_eq!(value.get("a").and_then(|v| v.as_array()).map(|a| a.len()), Some(3));
    }

    #[test]
    fn rejects_malformed_input() {
        assert!(parse(r#"{"x":01}"#).is_err());
        assert!(parse("{\"x\":\"lone\\uD800\"}").is_err());
        assert!(parse("[1,").is_err());
    }
}
