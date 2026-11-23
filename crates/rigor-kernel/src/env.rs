//! Ordered, well-formed environments of closed declarations.

use crate::expr::{ExprId, NameId};
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reducibility {
    Opaque,
    Abbrev,
    Regular,
}

impl Reducibility {
    pub fn to_tag(self) -> u8 {
        match self {
            Reducibility::Opaque => 0,
            Reducibility::Abbrev => 1,
            Reducibility::Regular => 2,
        }
    }
    pub fn from_tag(t: u8) -> Option<Self> {
        match t {
            0 => Some(Self::Opaque),
            1 => Some(Self::Abbrev),
            2 => Some(Self::Regular),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeclKind {
    Axiom,
    Definition,
    Theorem,
    Opaque,
    QuotPrimitive,
    Inductive,
    Constructor,
    Recursor,
    External,
}

impl DeclKind {
    pub fn unfolds(&self, hint: Reducibility) -> bool {
        matches!(self, DeclKind::Definition) && hint != Reducibility::Opaque
    }
    pub fn is_proof_like(&self) -> bool {
        matches!(self, DeclKind::Theorem | DeclKind::Opaque)
    }
}

#[derive(Debug, Clone)]
pub struct InductiveInfo {
    pub block_id: u32,
    pub ordinal_in_block: u32,
    pub num_params: u32,
    pub num_indices: u32,
    pub constructors: Vec<NameId>,
    /// Sort level of the inductive (with level params of the declaration).
    pub sort_level: crate::level::Level,
    pub is_prop: bool,
}

#[derive(Debug, Clone)]
pub struct CtorInfo {
    pub inductive: NameId,
    pub ordinal: u32,
    /// Number of fields (arguments after the parameters).
    pub num_fields: u32,
}

#[derive(Debug, Clone)]
pub struct RecursorInfo {
    pub inductive: NameId,
    pub block_id: u32,
}

#[derive(Debug, Clone)]
pub struct Decl {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
    pub value: Option<ExprId>,
    pub kind: DeclKind,
    pub hint: Reducibility,
    pub inductive: Option<InductiveInfo>,
    pub ctor: Option<CtorInfo>,
    pub recursor: Option<RecursorInfo>,
}

impl Decl {
    pub fn new(
        name: NameId,
        level_params: Vec<NameId>,
        ty: ExprId,
        value: Option<ExprId>,
        kind: DeclKind,
    ) -> Self {
        Self {
            name,
            level_params,
            ty,
            value,
            kind,
            hint: Reducibility::Regular,
            inductive: None,
            ctor: None,
            recursor: None,
        }
    }
}

/// An environment is an ordered graph: a declaration may only refer to
/// previously declared globals. Admission is append-only within a kernel.
#[derive(Debug, Default)]
pub struct Env {
    pub decls: Vec<Decl>,
    pub index: HashMap<NameId, usize>,
    pub num_blocks: u32,
}

impl Env {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn get(&self, name: NameId) -> Option<&Decl> {
        self.index.get(&name).map(|&i| &self.decls[i])
    }
    pub fn contains(&self, name: NameId) -> bool {
        self.index.contains_key(&name)
    }
    pub fn push(&mut self, decl: Decl) {
        let idx = self.decls.len();
        self.index.insert(decl.name, idx);
        self.decls.push(decl);
    }
    pub fn len(&self) -> usize {
        self.decls.len()
    }
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }
    /// Names of members of an inductive block, in declaration order.
    pub fn block_members(&self, block_id: u32) -> Vec<&Decl> {
        self.decls
            .iter()
            .filter(|d| d.inductive.as_ref().map(|i| i.block_id) == Some(block_id))
            .collect()
    }
}
