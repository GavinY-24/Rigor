//! Surface abstract syntax for `.rigor` sources.
//!
//! The surface language is an *authoring* notation only: every construct is
//! elaborated to a named core term (`rigor_kernel::NExpr`) and rechecked by
//! the kernel. Nothing in this AST is trusted.

use rigor_spec::BigUint;

#[derive(Debug, Clone, PartialEq)]
pub enum STerm {
    Ident(String),
    Lit(BigUint),
    Str(String),
    App(Box<STerm>, Box<STerm>),
    Bin(BinOp, Box<STerm>, Box<STerm>),
    Neg(Box<STerm>),
    Not(Box<STerm>),
    Lam(Vec<(String, Option<STerm>)>, Box<STerm>),
    Pi(Vec<(String, Option<STerm>)>, Box<STerm>),
    Arrow(Box<STerm>, Box<STerm>),
    Let(String, Option<Box<STerm>>, Box<STerm>, Box<STerm>),
    Access(Box<STerm>, String),
    /// `X.{u, v}` — explicit universe arguments (names of the enclosing
    /// declaration's level parameters).
    ULevels(Box<STerm>, Vec<String>),
    Hole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Eq,
    Ne,
    Le,
    Lt,
    Ge,
    Gt,
    And,
    Or,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Mod => "%",
            BinOp::Pow => "^",
            BinOp::Eq => "=",
            BinOp::Ne => "!=",
            BinOp::Le => "<=",
            BinOp::Lt => "<",
            BinOp::Ge => ">=",
            BinOp::Gt => ">",
            BinOp::And => "&&",
            BinOp::Or => "||",
        }
    }
}

/// One binder group of a declaration telescope. `given` and `assuming` are
/// both Pi binders; the distinction is documentary (data vs hypotheses) and
/// is preserved in diagnostics, never in semantics.
#[derive(Debug, Clone, PartialEq)]
pub struct Tele {
    pub names: Vec<String>,
    pub ty: STerm,
    pub assuming: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HaveProof {
    Term(STerm),
    Block(Vec<Tactic>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum SolveKind {
    Poly,
    Farkas(Vec<BigUint>),
    Sat,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Tactic {
    Exact(STerm),
    Refine(STerm),
    Have { name: String, ty: STerm, proof: HaveProof },
    Intro(Vec<String>),
    Apply(STerm),
    Rewrite { term: STerm, reverse: bool },
    Induction(String),
    Cases(String),
    Branch(String),
    Case(String),
    Show(STerm),
    /// Steps are (lhs, rhs, proof term); a step lhs of `None` means `_`
    /// (continue from the previous step's rhs).
    Calc(Vec<(Option<STerm>, STerm, STerm)>),
    Solve(SolveKind),
    Assumption,
    Trivial,
    Constructor,
    Left,
    Right,
}

#[derive(Debug, Clone, PartialEq)]
pub struct CtorDecl {
    pub name: String,
    pub binders: Vec<Tele>,
    pub result: Option<STerm>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum SDecl {
    Module { name: String },
    Profile { strict: bool },
    Import { modules: Vec<String> },
    Theorem { name: String, levels: Vec<String>, telescope: Vec<Tele>, target: STerm, proof: TheoremProof },
    Def { name: String, levels: Vec<String>, telescope: Vec<Tele>, ty: Option<STerm>, value: TheoremProof },
    Axiom { name: String, levels: Vec<String>, ty: STerm },
    Inductive { name: String, levels: Vec<String>, params: Vec<Tele>, ty: STerm, ctors: Vec<CtorDecl> },
    Challenge { name: String, roots: Vec<String> },
}

#[derive(Debug, Clone, PartialEq)]
pub enum TheoremProof {
    Term(STerm),
    Tactics(Vec<Tactic>),
}
