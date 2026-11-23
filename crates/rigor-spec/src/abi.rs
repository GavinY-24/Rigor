//! Frozen ABI constants, opcodes, domain prefixes, decoder limits, and status codes for Rigor 1.0 (L36).

use std::fmt;

/// Magic header for canonical `.rigorb` proof bundles.
pub const MAGIC_RIGB1: &[u8; 5] = b"RIGB1";

/// Magic header for canonical `.rigorc` sealed challenges.
pub const MAGIC_RIGC1: &[u8; 5] = b"RIGC1";

/// Pinned semantic profile targeting the mathematical core of Lean 4.36.0.
pub const PROFILE_L36_V1: &str = "L36-1.0";

/// Checker build identifier bound into `VerificationKey`.
pub const CHECKER_BUILD_ID: &str = "rigor-native-kernel-1.0.0-L36";

/// Pinned upstream reference commit / specification tag for Lean 4.36.0 core rules.
pub const UPSTREAM_L36_SPEC_PIN: &str = "lean4:v4.36.0-core-semantics-pin";

// --- Domain-separated SHA-256 prefixes (ASCII + NUL) ---

pub const DOMAIN_STATEMENT_ID: &[u8] = b"RIGOR_STMT_V1\0";
pub const DOMAIN_IND_BLOCK_ID: &[u8] = b"RIGOR_IND_BLK_V1\0";
pub const DOMAIN_IND_MEMBER_ID: &[u8] = b"RIGOR_IND_MEM_V1\0";
pub const DOMAIN_EVIDENCE_ID: &[u8] = b"RIGOR_EVID_V1\0";
pub const DOMAIN_VERIFICATION_KEY: &[u8] = b"RIGOR_VKEY_V1\0";
pub const DOMAIN_IFACE_CACHE_KEY: &[u8] = b"RIGOR_IFACE_V1\0";
pub const DOMAIN_CHALLENGE_ID: &[u8] = b"RIGOR_CHAL_V1\0";
pub const DOMAIN_POLICY_ID: &[u8] = b"RIGOR_POL_V1\0";
pub const DOMAIN_CONTEXT_ID: &[u8] = b"RIGOR_CTX_V1\0";
pub const DOMAIN_TICKET_ID: &[u8] = b"RIGOR_TKT_V1\0";

// --- Canonical RIGB1 chunk kind tags ---

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ChunkTag {
    Names = 0x01,
    Levels = 0x02,
    Terms = 0x03,
    Contexts = 0x04,
    Declarations = 0x05,
    Evidence = 0x06,
    Tickets = 0x07,
    Roots = 0x08,
    /// Optional commentary chunk: excluded from StatementId and cannot affect proof interpretation.
    Commentary = 0x80,
}

impl ChunkTag {
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0x01 => Some(Self::Names),
            0x02 => Some(Self::Levels),
            0x03 => Some(Self::Terms),
            0x04 => Some(Self::Contexts),
            0x05 => Some(Self::Declarations),
            0x06 => Some(Self::Evidence),
            0x07 => Some(Self::Tickets),
            0x08 => Some(Self::Roots),
            0x80 => Some(Self::Commentary),
            _ => None,
        }
    }

    pub fn is_mandatory_range(b: u8) -> bool {
        b < 0x80
    }
}

// --- Name entry tags ---

pub const NAME_ANON: u8 = 0x00;
pub const NAME_STR: u8 = 0x01;
pub const NAME_NUM: u8 = 0x02;

// --- Universe level tags ---

pub const LEVEL_ZERO: u8 = 0x00;
pub const LEVEL_SUCC: u8 = 0x01;
pub const LEVEL_MAX: u8 = 0x02;
pub const LEVEL_IMAX: u8 = 0x03;
pub const LEVEL_PARAM: u8 = 0x04;

// --- Core expression tags ---

pub const EXPR_BVAR: u8 = 0x01;
pub const EXPR_CONST: u8 = 0x02;
pub const EXPR_SORT: u8 = 0x03;
pub const EXPR_PI: u8 = 0x04;
pub const EXPR_LAM: u8 = 0x05;
pub const EXPR_APP: u8 = 0x06;
pub const EXPR_LET: u8 = 0x07;
pub const EXPR_PROJ: u8 = 0x08;
pub const EXPR_LIT_NAT: u8 = 0x09;
pub const EXPR_LIT_STR: u8 = 0x0A;

// --- Binder info tags ---

pub const BINDER_DEFAULT: u8 = 0x00;
pub const BINDER_IMPLICIT: u8 = 0x01;
pub const BINDER_STRICT_IMPLICIT: u8 = 0x02;
pub const BINDER_INST_IMPLICIT: u8 = 0x03;

// --- Context entry tags ---

pub const CTX_BINDER: u8 = 0x01;
pub const CTX_LET: u8 = 0x02;

// --- Declaration tags ---

pub const DECL_AXIOM: u8 = 0x01;
pub const DECL_DEF: u8 = 0x02;
pub const DECL_THEOREM: u8 = 0x03;
pub const DECL_OPAQUE: u8 = 0x04;
pub const DECL_QUOT: u8 = 0x05;
pub const DECL_INDUCTIVE: u8 = 0x06;
pub const DECL_EXTERNAL_REF: u8 = 0x07;

// --- Reducibility hint tags ---

pub const HINT_OPAQUE: u8 = 0x00;
pub const HINT_ABBREV: u8 = 0x01;
pub const HINT_REGULAR: u8 = 0x02;

// --- Conversion ticket & local proof arena opcodes (frozen ABI v1) ---

#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TicketOpcode {
    // Equivalence combinators
    Same = 0x10,
    Sym = 0x11,
    Join = 0x12,

    // Head computation rules
    Beta = 0x20,
    Let = 0x21,
    Delta = 0x22,
    Iota = 0x23,
    Proj = 0x24,
    Quot = 0x25,

    // Congruence frames (structurally identical binder domains in v1)
    FrameAppFun = 0x30,
    FrameAppArg = 0x31,
    FrameAppBoth = 0x32,
    FrameLamBody = 0x33,
    FramePiCod = 0x34,
    FramePiBoth = 0x35,
    FrameLetVal = 0x36,
    FrameLetBody = 0x37,
    FrameProj = 0x38,

    // Extensionality, irrelevance, and universe rules
    Irrel = 0x40,
    Eta = 0x41,
    Level = 0x42,

    // Local proof arena typing derivations (avoid re-running unrestricted inference)
    TyCheckCore = 0x50,
    TyBVar = 0x51,
    TyConst = 0x52,
    TySort = 0x53,
    TyApp = 0x54,
    TyLam = 0x55,
    TyPi = 0x56,
    TyConv = 0x57,

    // Fallback to pinned deterministic core conversion under context
    CheckCore = 0x7F,
}

impl TicketOpcode {
    pub fn from_byte(b: u8) -> Option<Self> {
        match b {
            0x10 => Some(Self::Same),
            0x11 => Some(Self::Sym),
            0x12 => Some(Self::Join),
            0x20 => Some(Self::Beta),
            0x21 => Some(Self::Let),
            0x22 => Some(Self::Delta),
            0x23 => Some(Self::Iota),
            0x24 => Some(Self::Proj),
            0x25 => Some(Self::Quot),
            0x30 => Some(Self::FrameAppFun),
            0x31 => Some(Self::FrameAppArg),
            0x32 => Some(Self::FrameAppBoth),
            0x33 => Some(Self::FrameLamBody),
            0x34 => Some(Self::FramePiCod),
            0x35 => Some(Self::FramePiBoth),
            0x36 => Some(Self::FrameLetVal),
            0x37 => Some(Self::FrameLetBody),
            0x38 => Some(Self::FrameProj),
            0x40 => Some(Self::Irrel),
            0x41 => Some(Self::Eta),
            0x42 => Some(Self::Level),
            0x50 => Some(Self::TyCheckCore),
            0x51 => Some(Self::TyBVar),
            0x52 => Some(Self::TyConst),
            0x53 => Some(Self::TySort),
            0x54 => Some(Self::TyApp),
            0x55 => Some(Self::TyLam),
            0x56 => Some(Self::TyPi),
            0x57 => Some(Self::TyConv),
            0x7F => Some(Self::CheckCore),
            _ => None,
        }
    }
}

/// Decoder safety limits enforced BEFORE memory allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DecoderLimits {
    pub max_bundle_bytes: usize,
    pub max_chunk_bytes: usize,
    pub max_names: usize,
    pub max_name_len: usize,
    pub max_levels: usize,
    pub max_terms: usize,
    pub max_contexts: usize,
    pub max_context_len: usize,
    pub max_declarations: usize,
    pub max_tickets: usize,
    pub max_ticket_steps: usize,
    pub max_roots: usize,
    pub max_literal_bytes: usize,
}

impl Default for DecoderLimits {
    fn default() -> Self {
        Self {
            max_bundle_bytes: 256 * 1024 * 1024, // 256 MiB
            max_chunk_bytes: 128 * 1024 * 1024,  // 128 MiB
            max_names: 2_000_000,
            max_name_len: 4096,
            max_levels: 1_000_000,
            max_terms: 16_000_000,
            max_contexts: 1_000_000,
            max_context_len: 8192,
            max_declarations: 1_000_000,
            max_tickets: 2_000_000,
            max_ticket_steps: 250_000,
            max_roots: 100_000,
            max_literal_bytes: 1024 * 1024, // 1 MiB literal ceiling
        }
    }
}

/// Public verification verdicts (§5.2).
/// Note: `Unsupported`, `UnknownResource`, and `InternalError` are never equated with
/// a mathematical counterexample, and none of the non-verified statuses may be labeled verified.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VerifyVerdict {
    VerifiedMatched,
    VerifiedSelfStated,
    Invalid,
    Unsupported,
    UnknownResource,
    InternalError,
}

impl VerifyVerdict {
    pub fn as_str(&self) -> &'static str {
        match self {
            Self::VerifiedMatched => "VERIFIED_MATCHED",
            Self::VerifiedSelfStated => "VERIFIED_SELF_STATED",
            Self::Invalid => "INVALID",
            Self::Unsupported => "UNSUPPORTED",
            Self::UnknownResource => "UNKNOWN_RESOURCE",
            Self::InternalError => "INTERNAL_ERROR",
        }
    }

    pub fn is_verified(&self) -> bool {
        matches!(self, Self::VerifiedMatched | Self::VerifiedSelfStated)
    }
}

impl fmt::Display for VerifyVerdict {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}
