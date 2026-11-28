//! Recursive-descent parser producing the surface AST.
//!
//! Declarations and terms are parsed from the token stream; tactic blocks
//! are collected as indented lines after a theorem's `:=` and parsed line by
//! line (with `have ... by` and `calc` consuming deeper-indented blocks).

use crate::ast::*;
use crate::lexer::{describe, lex, Tok};

pub struct Parser {
    toks: Vec<Tok>,
    pos: usize,
    depth: usize, // parenthesis depth: newlines are skipped when > 0
}

type PResult<T> = Result<T, String>;

impl Parser {
    pub fn new(toks: Vec<Tok>) -> Self {
        Parser { toks, pos: 0, depth: 0 }
    }

    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn peek_at(&self, n: usize) -> Option<&Tok> {
        self.toks.get(self.pos + n)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn skip_newlines(&mut self) {
        while matches!(self.peek(), Some(Tok::Newline(_))) {
            self.pos += 1;
        }
    }
    fn skip_newlines_deep(&mut self) {
        if self.depth > 0 {
            self.skip_newlines();
        }
    }
    fn expect(&mut self, t: &Tok) -> PResult<()> {
        match self.bump() {
            Some(x) if &x == t => Ok(()),
            other => Err(format!("expected {t:?}, found {}", other.map(|o| describe(&o)).unwrap_or_else(|| "end of input".into()))),
        }
    }
    fn expect_ident(&mut self) -> PResult<String> {
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(s),
            other => Err(format!("expected identifier, found {}", other.map(|o| describe(&o)).unwrap_or_else(|| "end of input".into()))),
        }
    }
    fn at_ident(&self, kw: &str) -> bool {
        matches!(self.peek(), Some(Tok::Ident(s)) if s == kw)
    }

    // ---------------- program ----------------

    pub fn parse_program(&mut self) -> PResult<Vec<SDecl>> {
        let mut decls = Vec::new();
        loop {
            self.skip_newlines();
            match self.peek().cloned() {
                None => break,
                Some(Tok::Ident(kw)) => match kw.as_str() {
                    "module" => {
                        self.bump();
                        let name = self.expect_ident()?;
                        decls.push(SDecl::Module { name });
                    }
                    "profile" => {
                        self.bump();
                        let p = self.expect_ident()?;
                        let strict = match p.as_str() {
                            "strict" => true,
                            "liberal" => false,
                            _ => return Err(format!("unknown profile '{p}' (expected strict|liberal)")),
                        };
                        decls.push(SDecl::Profile { strict });
                    }
                    "import" => {
                        self.bump();
                        let mut modules = vec![self.expect_ident()?];
                        while matches!(self.peek(), Some(Tok::Comma)) {
                            self.bump();
                            modules.push(self.expect_ident()?);
                        }
                        decls.push(SDecl::Import { modules });
                    }
                    "theorem" => decls.push(self.parse_theorem_like(true)?),
                    "def" => decls.push(self.parse_theorem_like(false)?),
                    "axiom" => {
                        self.bump();
                        let name = self.expect_ident()?;
                        let levels = self.parse_levels()?;
                        let telescope = self.parse_telescope()?;
                        self.expect(&Tok::Colon)?;
                        let mut ty = self.parse_term()?;
                        for tele in telescope.iter().rev() {
                            for n in tele.names.iter().rev() {
                                ty = STerm::Pi(vec![(n.clone(), Some(tele.ty.clone()))], Box::new(ty));
                            }
                        }
                        decls.push(SDecl::Axiom { name, levels, ty });
                    }
                    "inductive" => decls.push(self.parse_inductive()?),
                    "challenge" => {
                        self.bump();
                        let name = self.expect_ident()?;
                        self.expect(&Tok::Assign)?;
                        let mut roots = vec![self.expect_ident()?];
                        while matches!(self.peek(), Some(Tok::Comma)) {
                            self.bump();
                            roots.push(self.expect_ident()?);
                        }
                        decls.push(SDecl::Challenge { name, roots });
                    }
                    other => return Err(format!("unexpected declaration keyword '{other}'")),
                },
                Some(t) => return Err(format!("expected a declaration, found {}", describe(&t))),
            }
        }
        Ok(decls)
    }

    fn parse_levels(&mut self) -> PResult<Vec<String>> {
        let mut levels = Vec::new();
        if matches!(self.peek(), Some(Tok::Dot)) && matches!(self.peek_at(1), Some(Tok::LBrace)) {
            self.bump();
            self.bump();
            loop {
                levels.push(self.expect_ident()?);
                if matches!(self.peek(), Some(Tok::Comma)) {
                    self.bump();
                } else {
                    break;
                }
            }
            self.expect(&Tok::RBrace)?;
        }
        Ok(levels)
    }

    /// `(given x y : T) (assuming h : P) (z : T) ...`
    fn parse_telescope(&mut self) -> PResult<Vec<Tele>> {
        let mut teles = Vec::new();
        loop {
            self.skip_newlines_deep();
            if !matches!(self.peek(), Some(Tok::LParen)) {
                break;
            }
            // A parenthesized binder group must contain a colon before the
            // matching close; otherwise it is not a telescope group.
            if !self.paren_group_is_binder() {
                break;
            }
            self.bump(); // (
            let assuming = if self.at_ident("assuming") {
                self.bump();
                true
            } else if self.at_ident("given") {
                self.bump();
                false
            } else {
                false
            };
            let mut names = Vec::new();
            loop {
                match self.bump() {
                    Some(Tok::Ident(s)) => names.push(s),
                    Some(Tok::Colon) => break,
                    other => return Err(format!("expected binder name or ':', found {}", other.map(|o| describe(&o)).unwrap_or_else(|| "end".into()))),
                }
            }
            if names.is_empty() {
                return Err("empty binder group".into());
            }
            self.depth += 1;
            let ty = self.parse_term()?;
            self.depth -= 1;
            self.expect(&Tok::RParen)?;
            teles.push(Tele { names, ty, assuming });
        }
        Ok(teles)
    }

    fn paren_group_is_binder(&self) -> bool {
        // scan to the matching RParen at this level; binder iff a Colon token
        // appears before it (and the group does not start with a keyword that
        // makes it a term, which cannot contain a bare colon anyway).
        let mut depth = 0i32;
        let mut i = self.pos;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Colon if depth == 1 => return true,
                Tok::Newline(_) if depth == 0 => return false,
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn parse_theorem_like(&mut self, is_theorem: bool) -> PResult<SDecl> {
        self.bump(); // keyword
        let name = self.expect_ident()?;
        let levels = self.parse_levels()?;
        let telescope = self.parse_telescope()?;
        // optional result type
        let mut ty: Option<STerm> = None;
        if matches!(self.peek(), Some(Tok::Colon)) {
            self.bump();
            self.depth += 1;
            let t = self.parse_term()?;
            self.depth -= 1;
            ty = Some(t);
        }
        self.expect(&Tok::Assign)?;
        let proof = self.parse_proof_body()?;
        if is_theorem {
            let target = ty.ok_or_else(|| format!("theorem '{name}' needs a statement type after ':'"))?;
            Ok(SDecl::Theorem { name, levels, telescope, target, proof })
        } else {
            Ok(SDecl::Def { name, levels, telescope, ty, value: proof })
        }
    }

    /// After `:=`: either a term on the same line, `by` + indented tactic
    /// lines, or indented tactic lines directly.
    fn parse_proof_body(&mut self) -> PResult<TheoremProof> {
        if self.at_ident("by") {
            self.bump();
            let lines = self.collect_tactic_lines()?;
            return Ok(TheoremProof::Tactics(parse_tactic_block(&lines, 0)?));
        }
        if matches!(self.peek(), Some(Tok::Newline(_))) {
            // tactics without `by`, or a term starting on the next line is not
            // supported: require tactics here.
            let save = self.pos;
            let lines = self.collect_tactic_lines()?;
            if !lines.is_empty() {
                return Ok(TheoremProof::Tactics(parse_tactic_block(&lines, 0)?));
            }
            self.pos = save;
        }
        let t = self.parse_term()?;
        Ok(TheoremProof::Term(t))
    }

    /// Collect consecutive indented lines (indent > 0) as (indent, tokens).
    /// The lexer records on each Newline the indentation of the following
    /// line, which makes this straightforward.
    fn collect_tactic_lines(&mut self) -> PResult<Vec<(usize, Vec<Tok>)>> {
        let mut lines = Vec::new();
        let mut cur_indent = match self.bump() {
            Some(Tok::Newline(i)) => i,
            Some(_) => {
                self.pos -= 1;
                return Ok(lines);
            }
            None => return Ok(lines),
        };
        loop {
            if cur_indent == 0 {
                // A declaration at column 0 follows; its tokens are unconsumed.
                break;
            }
            let mut toks = Vec::new();
            let mut next_indent = 0usize;
            let mut eof = false;
            loop {
                match self.bump() {
                    Some(Tok::Newline(i)) => {
                        next_indent = i;
                        break;
                    }
                    Some(tk) => toks.push(tk),
                    None => {
                        eof = true;
                        break;
                    }
                }
            }
            if !toks.is_empty() {
                lines.push((cur_indent, toks));
            }
            if eof {
                break;
            }
            cur_indent = next_indent;
        }
        Ok(lines)
    }

    fn parse_inductive(&mut self) -> PResult<SDecl> {
        self.bump(); // inductive
        let name = self.expect_ident()?;
        let levels = self.parse_levels()?;
        let params = self.parse_telescope()?;
        self.expect(&Tok::Colon)?;
        let ty = self.parse_term()?;
        self.expect(&Tok::Assign)?;
        let mut ctors = Vec::new();
        loop {
            self.skip_newlines();
            if !matches!(self.peek(), Some(Tok::Pipe)) {
                break;
            }
            self.bump();
            let cname = self.expect_ident()?;
            // ctor telescope: reuse parser over the remaining stream
            let binders = self.parse_telescope()?;
            let result = if matches!(self.peek(), Some(Tok::Colon)) {
                self.bump();
                Some(self.parse_term()?)
            } else {
                None
            };
            ctors.push(CtorDecl { name: cname, binders, result });
        }
        Ok(SDecl::Inductive { name, levels, params, ty, ctors })
    }

    // ---------------- terms ----------------

    /// Parse a term that does not consume top-level comparison operators
    /// (used for calc step sides, where `=` separates the two sides).
    pub fn parse_arith(&mut self) -> PResult<STerm> {
        self.parse_add()
    }

    pub fn parse_term(&mut self) -> PResult<STerm> {
        self.skip_newlines_deep();
        if self.at_ident("fun") {
            self.bump();
            let binders = self.parse_binders()?;
            self.expect(&Tok::FatArrow)?;
            let body = self.parse_term()?;
            return Ok(STerm::Lam(binders, Box::new(body)));
        }
        if self.at_ident("forall") {
            self.bump();
            let binders = self.parse_binders()?;
            self.expect(&Tok::Comma)?;
            let body = self.parse_term()?;
            return Ok(STerm::Pi(binders, Box::new(body)));
        }
        if self.at_ident("let") {
            self.bump();
            let name = self.expect_ident()?;
            let ty = if matches!(self.peek(), Some(Tok::Colon)) {
                self.bump();
                Some(Box::new(self.parse_term()?))
            } else {
                None
            };
            self.expect(&Tok::Assign)?;
            let val = self.parse_term()?;
            if !self.at_ident("in") {
                return Err("let expression needs 'in'".into());
            }
            self.bump();
            let body = self.parse_term()?;
            return Ok(STerm::Let(name, ty, Box::new(val), Box::new(body)));
        }
        self.parse_arrow()
    }

    fn parse_binders(&mut self) -> PResult<Vec<(String, Option<STerm>)>> {
        let mut out = Vec::new();
        loop {
            self.skip_newlines_deep();
            match self.peek().cloned() {
                Some(Tok::LParen) if self.paren_group_is_binder() => {
                    self.bump();
                    let mut names = Vec::new();
                    loop {
                        match self.bump() {
                            Some(Tok::Ident(s)) => names.push(s),
                            Some(Tok::Colon) => break,
                            other => return Err(format!("expected binder name, found {}", other.map(|o| describe(&o)).unwrap_or_else(|| "end".into()))),
                        }
                    }
                    self.depth += 1;
                    let ty = self.parse_term()?;
                    self.depth -= 1;
                    self.expect(&Tok::RParen)?;
                    for n in names {
                        out.push((n, Some(ty.clone())));
                    }
                }
                Some(Tok::Ident(s)) => {
                    self.bump();
                    out.push((s, None));
                }
                _ => break,
            }
        }
        if out.is_empty() {
            return Err("expected at least one binder".into());
        }
        Ok(out)
    }

    fn parse_arrow(&mut self) -> PResult<STerm> {
        let lhs = self.parse_or()?;
        if matches!(self.peek(), Some(Tok::Arrow)) {
            self.bump();
            let rhs = self.parse_term()?;
            return Ok(STerm::Arrow(Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn parse_or(&mut self) -> PResult<STerm> {
        let mut lhs = self.parse_and()?;
        while matches!(self.peek(), Some(Tok::OrOr)) {
            self.bump();
            let rhs = self.parse_and()?;
            lhs = STerm::Bin(BinOp::Or, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_and(&mut self) -> PResult<STerm> {
        let mut lhs = self.parse_cmp()?;
        while matches!(self.peek(), Some(Tok::AndAnd)) {
            self.bump();
            let rhs = self.parse_cmp()?;
            lhs = STerm::Bin(BinOp::And, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_cmp(&mut self) -> PResult<STerm> {
        let lhs = self.parse_add()?;
        let op = match self.peek() {
            Some(Tok::EqEq) => Some(BinOp::Eq),
            Some(Tok::Ne) => Some(BinOp::Ne),
            Some(Tok::Le) => Some(BinOp::Le),
            Some(Tok::Lt) => Some(BinOp::Lt),
            Some(Tok::Ge) => Some(BinOp::Ge),
            Some(Tok::Gt) => Some(BinOp::Gt),
            _ => None,
        };
        if let Some(op) = op {
            self.bump();
            let rhs = self.parse_add()?;
            return Ok(STerm::Bin(op, Box::new(lhs), Box::new(rhs)));
        }
        Ok(lhs)
    }

    fn parse_add(&mut self) -> PResult<STerm> {
        let mut lhs = self.parse_mul()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Plus) => BinOp::Add,
                Some(Tok::Minus) => BinOp::Sub,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_mul()?;
            lhs = STerm::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_mul(&mut self) -> PResult<STerm> {
        let mut lhs = self.parse_unary()?;
        loop {
            let op = match self.peek() {
                Some(Tok::Star) => BinOp::Mul,
                Some(Tok::Slash) => BinOp::Div,
                Some(Tok::Percent) => BinOp::Mod,
                Some(Tok::Caret) => BinOp::Pow,
                _ => break,
            };
            self.bump();
            let rhs = self.parse_unary()?;
            lhs = STerm::Bin(op, Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn parse_unary(&mut self) -> PResult<STerm> {
        match self.peek() {
            Some(Tok::Minus) => {
                self.bump();
                Ok(STerm::Neg(Box::new(self.parse_unary()?)))
            }
            Some(Tok::Bang) => {
                self.bump();
                Ok(STerm::Not(Box::new(self.parse_unary()?)))
            }
            _ => self.parse_app(),
        }
    }

    fn parse_app(&mut self) -> PResult<STerm> {
        let mut f = self.parse_postfix()?;
        loop {
            self.skip_newlines_deep();
            match self.peek() {
                Some(Tok::Ident(_)) | Some(Tok::Num(_)) | Some(Tok::Str(_)) | Some(Tok::LParen) | Some(Tok::Underscore) => {
                    let a = self.parse_postfix()?;
                    f = STerm::App(Box::new(f), Box::new(a));
                }
                _ => break,
            }
        }
        Ok(f)
    }

    fn parse_postfix(&mut self) -> PResult<STerm> {
        let mut e = self.parse_atom()?;
        loop {
            match self.peek().cloned() {
                Some(Tok::Dot) => {
                    // `.{u}` universe args or `.field`
                    if matches!(self.peek_at(1), Some(Tok::LBrace)) {
                        self.bump();
                        self.bump();
                        let mut levels = Vec::new();
                        loop {
                            levels.push(self.expect_ident()?);
                            if matches!(self.peek(), Some(Tok::Comma)) {
                                self.bump();
                            } else {
                                break;
                            }
                        }
                        self.expect(&Tok::RBrace)?;
                        e = STerm::ULevels(Box::new(e), levels);
                    } else if let Some(Tok::Ident(field)) = self.peek_at(1).cloned() {
                        self.bump();
                        self.bump();
                        e = STerm::Access(Box::new(e), field);
                    } else if let Some(Tok::Num(n)) = self.peek_at(1).cloned() {
                        self.bump();
                        self.bump();
                        e = STerm::Access(Box::new(e), n.decimal());
                    } else {
                        break;
                    }
                }
                _ => break,
            }
        }
        Ok(e)
    }

    fn parse_atom(&mut self) -> PResult<STerm> {
        self.skip_newlines_deep();
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(STerm::Ident(s)),
            Some(Tok::Num(n)) => Ok(STerm::Lit(n)),
            Some(Tok::Str(s)) => Ok(STerm::Str(s)),
            Some(Tok::Underscore) => Ok(STerm::Hole),
            Some(Tok::LParen) => {
                // binder group used as a Pi domain: `(x : T) -> ...`
                if self.paren_group_is_binder_at_current() {
                    // rewind: parse_binders expects to consume '('
                    self.pos -= 1;
                    let binders = self.parse_binders()?;
                    if matches!(self.peek(), Some(Tok::Arrow)) {
                        self.bump();
                        let body = self.parse_term()?;
                        return Ok(STerm::Pi(binders, Box::new(body)));
                    }
                    return Err("binder group must be followed by '->' in term position".into());
                }
                self.depth += 1;
                let first = self.parse_term()?;
                let out = if matches!(self.peek(), Some(Tok::Comma)) {
                    self.bump();
                    let second = self.parse_term()?;
                    // tuple sugar: (a, b) = Prod.mk a b
                    STerm::App(
                        Box::new(STerm::App(Box::new(STerm::Ident("Prod.mk".into())), Box::new(first))),
                        Box::new(second),
                    )
                } else {
                    first
                };
                self.depth -= 1;
                self.expect(&Tok::RParen)?;
                Ok(out)
            }
            other => Err(format!("expected a term, found {}", other.map(|o| describe(&o)).unwrap_or_else(|| "end of input".into()))),
        }
    }

    fn paren_group_is_binder_at_current(&self) -> bool {
        // current position is just after '('
        let mut depth = 1i32;
        let mut i = self.pos;
        while let Some(t) = self.toks.get(i) {
            match t {
                Tok::LParen | Tok::LBracket | Tok::LBrace => depth += 1,
                Tok::RParen => {
                    depth -= 1;
                    if depth == 0 {
                        return false;
                    }
                }
                Tok::RBracket | Tok::RBrace => depth -= 1,
                Tok::Colon if depth == 1 => return true,
                _ => {}
            }
            i += 1;
        }
        false
    }
}

// ---------------- tactic blocks ----------------

type Line = (usize, Vec<Tok>);

/// Parse a block of tactic lines. `lines` carry (indent, tokens); the block
/// base is the indent of the first line.
pub fn parse_tactic_block(lines: &[Line], _ignored: usize) -> PResult<Vec<Tactic>> {
    let mut rest: &[Line] = lines;
    let mut out = Vec::new();
    if lines.is_empty() {
        return Ok(out);
    }
    let base = lines[0].0;
    while !rest.is_empty() {
        let (indent, toks) = &rest[0];
        if *indent < base {
            break;
        }
        // Lines deeper than the block base (e.g. tactics under a `case`
        // header) are simply the next sequential tactics; only `have ... by`
        // and `calc` consume deeper lines as a nested block, which they do
        // relative to their own line's indentation.
        let line_indent = *indent;
        rest = &rest[1..];
        let tac = parse_tactic_line(toks, &mut rest, line_indent)?;
        out.push(tac);
    }
    Ok(out)
}

fn line_text(toks: &[Tok]) -> String {
    toks.iter().map(describe).collect::<Vec<_>>().join(" ")
}

/// Lines with indent > `base`, consumed as a sub-block.
fn take_subblock<'a>(rest: &mut &'a [Line], base: usize) -> &'a [Line] {
    let mut n = 0;
    while n < rest.len() && rest[n].0 > base {
        n += 1;
    }
    let (sub, rem) = rest.split_at(n);
    *rest = rem;
    sub
}

fn line_parser(toks: &[Tok]) -> Parser {
    Parser::new(toks.to_vec())
}

fn parse_tactic_line(toks: &[Tok], rest: &mut &[Line], base: usize) -> PResult<Tactic> {
    let head = match toks.first() {
        Some(Tok::Ident(s)) => s.clone(),
        _ => return Err(format!("expected a tactic, found: {}", line_text(toks))),
    };
    match head.as_str() {
        "exact" => {
            let mut p = line_parser(&toks[1..]);
            Ok(Tactic::Exact(p.parse_term()?))
        }
        "refine" => {
            let mut p = line_parser(&toks[1..]);
            Ok(Tactic::Refine(p.parse_term()?))
        }
        "apply" => {
            let mut p = line_parser(&toks[1..]);
            Ok(Tactic::Apply(p.parse_term()?))
        }
        "show" => {
            let mut p = line_parser(&toks[1..]);
            Ok(Tactic::Show(p.parse_term()?))
        }
        "rewrite" => {
            let mut idx = 1;
            let mut reverse = false;
            if matches!(toks.get(idx), Some(Tok::Lt)) {
                reverse = true;
                idx += 1;
            }
            let mut p = line_parser(&toks[idx..]);
            Ok(Tactic::Rewrite { term: p.parse_term()?, reverse })
        }
        "intro" | "intros" => {
            let mut names = Vec::new();
            for t in &toks[1..] {
                match t {
                    Tok::Ident(s) => names.push(s.clone()),
                    other => return Err(format!("intro expects names, found {}", describe(other))),
                }
            }
            if names.is_empty() {
                return Err("intro needs at least one name".into());
            }
            Ok(Tactic::Intro(names))
        }
        "induction" => Ok(Tactic::Induction(single_ident(&toks[1..], "induction")?)),
        "cases" => Ok(Tactic::Cases(single_ident(&toks[1..], "cases")?)),
        "branch" => Ok(Tactic::Branch(single_ident(&toks[1..], "branch")?)),
        "case" => Ok(Tactic::Case(single_ident(&toks[1..], "case")?)),
        "assumption" => Ok(Tactic::Assumption),
        "trivial" => Ok(Tactic::Trivial),
        "constructor" => Ok(Tactic::Constructor),
        "left" => Ok(Tactic::Left),
        "right" => Ok(Tactic::Right),
        "sorry" => Err("sorry is not part of Rigor: every goal must be closed by a checked proof".into()),
        "have" => {
            // have name : ty := term | have name : ty by <block>
            let toks = toks.to_vec();
            if toks.len() < 4 {
                return Err("have needs: have name : type := proof".into());
            }
            let name = match &toks[1] {
                Tok::Ident(s) => s.clone(),
                other => return Err(format!("have expects a name, found {}", describe(other))),
            };
            if !matches!(toks.get(2), Some(Tok::Colon)) {
                return Err("have expects ':' after the name".into());
            }
            // find := or trailing `by`
            let by_pos = toks.iter().rposition(|t| matches!(t, Tok::Ident(s) if s == "by"));
            let assign_pos = toks.iter().position(|t| matches!(t, Tok::Assign));
            if let Some(ap) = assign_pos {
                let mut tp = line_parser(&toks[3..ap]);
                let ty = tp.parse_term()?;
                let mut pp = line_parser(&toks[ap + 1..]);
                // `:= by` block form
                if pp.at_ident("by") && pp.pos + 1 >= pp.toks.len() {
                    let sub = take_subblock(rest, base);
                    let block = parse_tactic_block(sub, 0)?;
                    return Ok(Tactic::Have { name, ty, proof: HaveProof::Block(block) });
                }
                let term = pp.parse_term()?;
                Ok(Tactic::Have { name, ty, proof: HaveProof::Term(term) })
            } else if let Some(bp) = by_pos {
                let mut tp = line_parser(&toks[3..bp]);
                let ty = tp.parse_term()?;
                let sub = take_subblock(rest, base);
                let block = parse_tactic_block(sub, 0)?;
                Ok(Tactic::Have { name, ty, proof: HaveProof::Block(block) })
            } else {
                Err("have needs ':=' with a proof term or 'by' with an indented block".into())
            }
        }
        "calc" => {
            let sub = take_subblock(rest, base);
            let mut steps = Vec::new();
            for (_, ltoks) in sub {
                let mut p = line_parser(ltoks);
                let lhs = if matches!(p.peek(), Some(Tok::Underscore)) {
                    p.bump();
                    None
                } else {
                    Some(p.parse_arith()?)
                };
                p.expect(&Tok::EqEq)?;
                let rhs = p.parse_arith()?;
                p.expect(&Tok::Assign)?;
                let proof = p.parse_term()?;
                steps.push((lhs, rhs, proof));
            }
            if steps.is_empty() {
                return Err("calc needs at least one step".into());
            }
            Ok(Tactic::Calc(steps))
        }
        "solve" => {
            match toks.get(1) {
                Some(Tok::Ident(s)) if s == "poly" => Ok(Tactic::Solve(SolveKind::Poly)),
                Some(Tok::Ident(s)) if s == "sat" => Ok(Tactic::Solve(SolveKind::Sat)),
                Some(Tok::Ident(s)) if s == "farkas" => {
                    let mut mults = Vec::new();
                    for t in &toks[2..] {
                        match t {
                            Tok::Num(n) => mults.push(n.clone()),
                            other => return Err(format!("solve farkas expects natural multipliers, found {}", describe(other))),
                        }
                    }
                    Ok(Tactic::Solve(SolveKind::Farkas(mults)))
                }
                other => Err(format!("unknown solve plugin: {}", other.map(describe).unwrap_or_else(|| "<none>".into()))),
            }
        }
        other => Err(format!("unknown tactic '{other}'")),
    }
}

fn single_ident(toks: &[Tok], what: &str) -> PResult<String> {
    match toks {
        [Tok::Ident(s)] => Ok(s.clone()),
        _ => Err(format!("{what} expects a single identifier")),
    }
}

/// Parse a whole source file.
pub fn parse_source(src: &str) -> PResult<Vec<SDecl>> {
    let toks = lex(src)?;
    let mut p = Parser::new(toks);
    p.parse_program()
}

/// Parse one tactic block from source text (used by the machine protocol).
pub fn parse_tactics_text(src: &str) -> PResult<Vec<Tactic>> {
    let toks = lex(src)?;
    // Split into lines by Newline payloads.
    let mut lines: Vec<Line> = Vec::new();
    let mut cur: Vec<Tok> = Vec::new();
    let mut cur_indent = 0usize;
    let mut pending_indent = 0usize;
    let mut first = true;
    for t in toks {
        match t {
            Tok::Newline(ind) => {
                if !cur.is_empty() || !first {
                    lines.push((cur_indent, std::mem::take(&mut cur)));
                }
                first = false;
                pending_indent = ind;
                cur_indent = ind;
            }
            other => cur.push(other),
        }
    }
    let _ = pending_indent;
    if !cur.is_empty() {
        lines.push((cur_indent, cur));
    }
    let lines: Vec<Line> = lines.into_iter().filter(|(_, t)| !t.is_empty()).collect();
    if lines.is_empty() {
        return Ok(Vec::new());
    }
    let base = lines.iter().map(|(i, _)| *i).min().unwrap_or(0);
    let shifted: Vec<Line> = lines.iter().map(|(i, t)| (i - base, t.clone())).collect();
    parse_tactic_block(&shifted, 0)
}
