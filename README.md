# Rigor

Rigor is a proof language and native verifier for the mathematical core of
Lean 4.36.0 (profile `L36-1.0`). It is a producer/checker system: every
accepted artifact is a proof bundle (`.rigorb`) whose declarations the
kernel re-checks from scratch. Certificate plugins and the surface
language are untrusted producers. They may attach conversion tickets as
hints; the checker derives the same judgments either way, and a bad
ticket invalidates the bundle.

The implementation is a dependency-free Rust workspace (SHA-256 and
bignums included) plus an independent Python reimplementation of the
checker for differential testing. It builds and runs fully offline.

## Layout

| Path | Role |
| --- | --- |
| `crates/rigor-spec` | Frozen ABI: RIGB1/RIGC1 tags, domain-separated SHA-256, levels, policies, the three artifact ids |
| `crates/rigor-kernel` | Trusted L36 core: de Bruijn terms, universes (equivalence for all valuations), inductives with kernel-built recursors, quotients, conversion, tickets |
| `crates/rigor-codec` | RIGB1 encoder/decoder and statement/evidence ids |
| `crates/rigor-runtime` | Parallel bundle verifier, cache keyed by the full verification key, JSON receipts |
| `crates/rigor-certificates` | Standard library admitted by the kernel, and six proof-producing plugins (rewriting, polynomial identities, rational Farkas arithmetic, finite enumeration, SAT, interval bounds) |
| `crates/rigor-front` | `.rigor` parser, elaborator, tactics, machine protocol |
| `crates/rigor-bridges` | Pinned `.rigx` exchange, semantic diff, core-derived explanations |
| `crates/rigor-bench` | Tracks A–F. The pinned Lean toolchain is reported as not measured when it is not available; warm and cold runs are never compared as if they were the same thing |
| `crates/rigor-cli` | `rigor` binary, conformance fixtures, corpus |
| `ref_checker/` | Second L36 checker, in Python, sharing no code with the Rust kernel |

Three ids are kept distinct. `StatementId` names a declaration, `EvidenceId`
names one proof of it, and `VerificationKey` names a check: checker build,
profile, policy, evidence, covered roots, and ticket-rule version. The
cache is keyed by the verification key, so a different policy or a
different proof is a miss.

## Build and check

```
cargo test --workspace
cargo build -p rigor-cli --release
python3 ref_checker/rigor_check.py some.rigorb
```

`rigor` speaks `build`, `seal`, `verify`, `explain`, `import`, `export`,
`diff`, and `bench`. `verify` exits 0 on a verified bundle, 1 on
`INVALID`, 2 on `UNSUPPORTED`, 3 on `UNKNOWN_RESOURCE`, 4 on usage or IO
failure, and 5 on an internal error. `UNSUPPORTED` means a construct this
checker does not implement. `UNKNOWN_RESOURCE` means a step or size budget
ran out. Neither one is a counterexample, and neither one is a pass.

```
rigor build Module.rigor -o Module.rigorb --challenge main --challenge-out Module.rigorc
rigor verify Module.rigorb --challenge Module.rigorc --workers 4
rigor explain Module.rigorb
rigor bench
```

Surface files name their dependencies with `import`. `rigor build` orders
them and compiles them as one unit, because declaration names are global.

## What the kernel checks

Dependent type theory with `Prop = Sort 0` and `Type u = Sort (succ u)`.
There is no `Type : Type`. Universe levels are `0`, parameters, `succ`,
`max`, and `imax`, and two levels are convertible only when they agree
under every valuation. Conversion is a typing rule: beta, zeta, delta for
non-opaque definitions, iota (including mutual blocks and Nat literals),
quotient computation, proof irrelevance only for definitionally equal
propositions, and eta.

Inductive blocks are checked for strict positivity. A nested occurrence
is `UNSUPPORTED`, not a silent accept. Recursor types are rebuilt by the
kernel from the inductive declaration; a producer-supplied recursor
signature is never trusted. `Quot`, `Quot.mk`, `Quot.lift`, and `Quot.ind`
are the quotient package; `Quot.sound` is an axiom, so the constructive
policy rejects any root that reaches it and the classical policy accepts
it and reports the assumption.

## Conformance

`crates/rigor-cli/tests/conformance.rs` is the must-pass list: the
dependent transport round trip, indexed `Vec` append (and rejection of a
bad index), mutual `Tree`/`Forest` recursion, quotient computation plus
the `Quot.sound` policy split, a universe-polymorphic identity and the
rejection of `Type : Type`, same-name cache isolation, proof irrelevance
scoped to one proposition, the Farkas certificate `(1, 2)` accepted and
`(1, -2)` rejected, a sealed nonzero-denominator obligation, opaque proof
repair versus transparent invalidation, cache misses across policies,
mutual theorem cycles rejected with per-root coverage, a bad ticket and
an exhausted budget, and identical verdicts for packed and expanded
bundles and for one worker and many.

`crates/rigor-cli/tests/corpus.rs` compiles four families (algebra,
inequalities, structures, number theory), verifies each bundle, and
requires the Python checker to return the same verdict, including on a
truncated bundle.

## Trust

Imported `.rigx` text is re-admitted by the kernel. A mismatched upstream
pin (`lean4:v4.36.0-core-semantics-pin`) is refused unless the caller
passes an explicit override, which the feature matrix records. Receipts
from other tools are never consulted. `sorry` is rejected at parse time.
