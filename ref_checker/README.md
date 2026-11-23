# Independent Python checker for Rigor bundles

`rigor_check.py` is a **diverse reimplementation** of the L36 checker: it
decodes RIGB1 proof bundles and re-checks every declaration with its own
dependent-type kernel, written from the format and semantics
specification in pure Python (standard library only). It shares no code
with the Rust implementation and never consults Rust-produced receipts —
its verdict is independent evidence for differential testing (Track E/F
of the §7 experiment plan).

## Usage

```
python3 rigor_check.py <bundle.rigorb>
```

Per-root verdict lines are printed, then a summary verdict. Exit codes:

| verdict          | exit |
|------------------|------|
| VERIFIED         | 0    |
| INVALID          | 1    |
| UNSUPPORTED      | 2    |
| UNKNOWN_RESOURCE | 3    |
| (usage error)    | 4    |
| INTERNAL_ERROR   | 5    |

`UNSUPPORTED` means this checker does not implement a construct the
bundle uses (currently: nested inductive occurrences, external
references, non-`L36-1.0` profiles). It is never a counterexample and
never a verification. `UNKNOWN_RESOURCE` means the step/recursion budget
ran out — also not a counterexample.

## What it checks

- RIGB1 decoding with the same strictness rules as the reference codec
  (canonical LEB128, length-delimited chunks in tag order, no duplicate
  chunks, no trailing bytes, backward-only table references).
- The full L36 term language: de Bruijn terms, universe levels with
  **all-valuations equivalence** via normal forms (constant atoms,
  parameter atoms with offsets, guarded `imax` atoms — the same
  algorithm as `rigor-spec/src/reference.rs`), Pi/Lam/App/Let, structure
  projections, Nat/String literals.
- Conversion: beta, zeta (let and local definitions), delta for
  non-opaque definitions only, iota for recursors (including mutual
  blocks and Nat-literal majors), quotient computation for
  `Quot.lift` on `Quot.mk`, Nat literal acceleration, proof
  irrelevance restricted to definitionally equal propositions, eta.
- Declaration admission: types must be Sorts, values are checked
  against their stated types, axioms carry no values. Duplicate
  declarations are rejected.
- Inductive admission: constructor result types must return the
  parameters as the exact bound variables; **strict positivity** is
  enforced (block inductives in Pi domains are invalid; nested
  occurrences report UNSUPPORTED rather than being silently accepted).
  Recursor types are *reconstructed* here from the inductive
  declarations (motives, minors, induction hypotheses mirroring the
  reference kernel's generation scheme); producer-supplied recursor
  signatures are never trusted. Prop-elimination restrictions are
  enforced (non-singleton Prop inductives cannot eliminate into Type).
- The quotient package is admitted in its canonical form
  (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`); `Quot.sound` enters as
  an axiom through its bundle declaration.

Deliberate non-goals (produce UNSUPPORTED/INVALID, never silent
success): external references, certificates/tickets (this checker
always re-derives conversion and typing decisions from the core terms,
which is the point of the producer/checker contract), policy and
challenge matching (statement-ID sealing is the Rust runtime's job;
this checker's job is the core judgment).

## Differential testing

The conformance suite runs this checker on every corpus bundle and
requires verdict agreement with `rigor verify` (a VERIFIED from one and
INVALID from the other is a release-blocking divergence; UNSUPPORTED
from this checker is reported and counted, not silently waived).
