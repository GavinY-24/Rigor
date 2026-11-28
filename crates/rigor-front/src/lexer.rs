//! Tokenizer for `.rigor` sources. Newlines are significant (tactic blocks
//! are line-oriented), so they are emitted as tokens.

use rigor_spec::BigUint;

#[derive(Debug, Clone, PartialEq)]
pub enum Tok {
    Ident(String),
    Num(BigUint),
    Str(String),
    /// End of line; payload is the indentation (leading spaces) of the next line.
    Newline(usize),
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Colon,
    Assign, // :=
    Arrow,  // ->
    FatArrow, // =>
    Pipe,
    Dot,
    Underscore,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    EqEq, // = (comparison/sugar in term position)
    Ne,
    Le,
    Lt,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Bang,
}

pub fn describe(t: &Tok) -> String {
    match t {
        Tok::Ident(s) => format!("'{s}'"),
        Tok::Num(n) => format!("number {}", n.decimal()),
        Tok::Str(s) => format!("string {s:?}"),
        Tok::Newline(_) => "end of line".into(),
        other => format!("{other:?}"),
    }
}

fn is_ident_start(c: char) -> bool {
    c.is_alphabetic() || c == '_'
}
fn is_ident_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

pub fn lex(src: &str) -> Result<Vec<Tok>, String> {
    let chars: Vec<char> = src.chars().collect();
    let mut toks = Vec::new();
    let mut i = 0usize;
    let mut line = 1usize;
    while i < chars.len() {
        let c = chars[i];
        match c {
            '\n' => {
                line += 1;
                i += 1;
                let mut indent = 0usize;
                let mut j = i;
                while j < chars.len() && (chars[j] == ' ' || chars[j] == '\t') {
                    indent += 1;
                    j += 1;
                }
                toks.push(Tok::Newline(indent));
            }
            c if c.is_whitespace() => i += 1,
            '-' if chars.get(i + 1) == Some(&'-') => {
                // line comment
                while i < chars.len() && chars[i] != '\n' {
                    i += 1;
                }
            }
            '/' if chars.get(i + 1) == Some(&'*') => {
                let mut depth = 1;
                i += 2;
                while i < chars.len() && depth > 0 {
                    if chars[i] == '/' && chars.get(i + 1) == Some(&'*') {
                        depth += 1;
                        i += 2;
                    } else if chars[i] == '*' && chars.get(i + 1) == Some(&'/') {
                        depth -= 1;
                        i += 2;
                    } else {
                        if chars[i] == '\n' {
                            line += 1;
                        }
                        i += 1;
                    }
                }
                if depth > 0 {
                    return Err(format!("line {line}: unterminated block comment"));
                }
            }
            c if is_ident_start(c) => {
                let mut s = String::new();
                while i < chars.len() && is_ident_char(chars[i]) {
                    s.push(chars[i]);
                    i += 1;
                }
                // Dotted names: Nat.add, Foo.Bar.baz — a dot joins only when
                // directly followed by another identifier start.
                while i + 1 < chars.len() && chars[i] == '.' && is_ident_start(chars[i + 1]) {
                    s.push('.');
                    i += 1;
                    while i < chars.len() && is_ident_char(chars[i]) {
                        s.push(chars[i]);
                        i += 1;
                    }
                }
                if s == "_" {
                    toks.push(Tok::Underscore);
                } else {
                    toks.push(Tok::Ident(s));
                }
            }
            c if c.is_ascii_digit() => {
                let mut n = BigUint::zero();
                while i < chars.len() && chars[i].is_ascii_digit() {
                    let d = (chars[i] as u32 - '0' as u32) as u64;
                    n = n.mul(&BigUint::from_u64(10)).add(&BigUint::from_u64(d));
                    i += 1;
                }
                toks.push(Tok::Num(n));
            }
            '"' => {
                i += 1;
                let mut s = String::new();
                loop {
                    match chars.get(i) {
                        None => return Err(format!("line {line}: unterminated string")),
                        Some('"') => {
                            i += 1;
                            break;
                        }
                        Some('\\') => {
                            i += 1;
                            match chars.get(i) {
                                Some('n') => s.push('\n'),
                                Some('t') => s.push('\t'),
                                Some('"') => s.push('"'),
                                Some('\\') => s.push('\\'),
                                Some(other) => return Err(format!("line {line}: bad escape \\{other}")),
                                None => return Err(format!("line {line}: unterminated string")),
                            }
                            i += 1;
                        }
                        Some(ch) => {
                            s.push(*ch);
                            i += 1;
                        }
                    }
                }
                toks.push(Tok::Str(s));
            }
            '(' => {
                toks.push(Tok::LParen);
                i += 1;
            }
            ')' => {
                toks.push(Tok::RParen);
                i += 1;
            }
            '[' => {
                toks.push(Tok::LBracket);
                i += 1;
            }
            ']' => {
                toks.push(Tok::RBracket);
                i += 1;
            }
            '{' => {
                toks.push(Tok::LBrace);
                i += 1;
            }
            '}' => {
                toks.push(Tok::RBrace);
                i += 1;
            }
            ',' => {
                toks.push(Tok::Comma);
                i += 1;
            }
            ':' => {
                if chars.get(i + 1) == Some(&'=') {
                    toks.push(Tok::Assign);
                    i += 2;
                } else {
                    toks.push(Tok::Colon);
                    i += 1;
                }
            }
            '-' => {
                if chars.get(i + 1) == Some(&'>') {
                    toks.push(Tok::Arrow);
                    i += 2;
                } else {
                    toks.push(Tok::Minus);
                    i += 1;
                }
            }
            '=' => {
                if chars.get(i + 1) == Some(&'>') {
                    toks.push(Tok::FatArrow);
                    i += 2;
                } else {
                    toks.push(Tok::EqEq);
                    i += 1;
                }
            }
            '!' => {
                if chars.get(i + 1) == Some(&'=') {
                    toks.push(Tok::Ne);
                    i += 2;
                } else {
                    toks.push(Tok::Bang);
                    i += 1;
                }
            }
            '<' => {
                if chars.get(i + 1) == Some(&'=') {
                    toks.push(Tok::Le);
                    i += 2;
                } else {
                    toks.push(Tok::Lt);
                    i += 1;
                }
            }
            '>' => {
                if chars.get(i + 1) == Some(&'=') {
                    toks.push(Tok::Ge);
                    i += 2;
                } else {
                    toks.push(Tok::Gt);
                    i += 1;
                }
            }
            '&' => {
                if chars.get(i + 1) == Some(&'&') {
                    toks.push(Tok::AndAnd);
                    i += 2;
                } else {
                    return Err(format!("line {line}: single '&' (use &&)"));
                }
            }
            '|' => {
                if chars.get(i + 1) == Some(&'|') {
                    toks.push(Tok::OrOr);
                    i += 2;
                } else {
                    toks.push(Tok::Pipe);
                    i += 1;
                }
            }
            '.' => {
                toks.push(Tok::Dot);
                i += 1;
            }
            '+' => {
                toks.push(Tok::Plus);
                i += 1;
            }
            '*' => {
                toks.push(Tok::Star);
                i += 1;
            }
            '/' => {
                toks.push(Tok::Slash);
                i += 1;
            }
            '%' => {
                toks.push(Tok::Percent);
                i += 1;
            }
            '^' => {
                toks.push(Tok::Caret);
                i += 1;
            }
            other => return Err(format!("line {line}: unexpected character {other:?}")),
        }
    }
    Ok(toks)
}
