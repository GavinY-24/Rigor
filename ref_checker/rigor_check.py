#!/usr/bin/env python3
"""Independent L36 checker for Rigor proof bundles (.rigorb), in Python.

This is a *diverse reimplementation* of the RIGB1 decoder and the L36
kernel semantics, written from the format/semantics specification for
differential testing against the Rust checker (`rigor-runtime`). It is
deliberately independent: no Rust code is shared.

Verdicts printed on the last line, one per root plus a summary:
  VERIFIED / INVALID / UNSUPPORTED / UNKNOWN_RESOURCE / INTERNAL_ERROR

Exit codes: 0 verified, 1 invalid, 2 unsupported, 3 resource, 4 usage,
5 internal error. UNSUPPORTED means "this checker does not implement a
construct the bundle uses" — it is never a counterexample and never a
successful verification.
"""

import sys
import threading
from functools import lru_cache

# --------------------------------------------------------------------------
# Errors and verdicts
# --------------------------------------------------------------------------


class KError(Exception):
    pass


class UnsupportedError(Exception):
    pass


class ResourceError(Exception):
    pass


# --------------------------------------------------------------------------
# RIGB1 decoding
# --------------------------------------------------------------------------


class Reader:
    def __init__(self, data: bytes):
        self.d = data
        self.i = 0

    def byte(self) -> int:
        if self.i >= len(self.d):
            raise KError("unexpected end of bundle")
        b = self.d[self.i]
        self.i += 1
        return b

    def u64(self) -> int:
        result = 0
        shift = 0
        start = self.i
        while True:
            if self.i >= len(self.d):
                raise KError("truncated LEB128")
            b = self.d[self.i]
            self.i += 1
            result |= (b & 0x7F) << shift
            if not (b & 0x80):
                break
            shift += 7
            if shift > 63:
                raise KError("LEB128 too long")
        # canonical (minimal) encoding required
        if self.i - start != max(1, (result.bit_length() + 6) // 7):
            raise KError("non-canonical LEB128")
        return result

    def bytes(self, n: int) -> bytes:
        if self.i + n > len(self.d):
            raise KError("truncated bundle")
        out = self.d[self.i : self.i + n]
        self.i += n
        return out

    def blob(self) -> bytes:
        return self.bytes(self.u64())

    def string(self) -> str:
        b = self.blob()
        try:
            return b.decode("utf-8")
        except UnicodeDecodeError:
            raise KError("invalid UTF-8 in bundle")


MAX_BUNDLE_BYTES = 256 * 1024 * 1024


def decode_bundle(data: bytes):
    if len(data) > MAX_BUNDLE_BYTES:
        raise KError("bundle exceeds size limit")
    r = Reader(data)
    if r.bytes(5) != b"RIGB1":
        raise KError("bad magic (expected RIGB1)")
    profile = r.string()
    nchunks = r.u64()
    chunks = {}
    last_tag = -1
    for _ in range(nchunks):
        tag = r.byte()
        payload = r.blob()
        if tag in chunks:
            raise KError(f"duplicate chunk tag {tag:#x}")
        if tag < 0x80 and tag < last_tag:
            raise KError("mandatory chunks out of order")
        if tag < 0x80:
            last_tag = tag
        chunks[tag] = payload
    if r.i != len(data):
        raise KError("trailing bytes after bundle")

    # Names
    names = []
    if 0x01 in chunks:
        rr = Reader(chunks[0x01])
        for _ in range(rr.u64()):
            parts = []
            for _ in range(rr.u64()):
                t = rr.byte()
                if t == 0x00:
                    parts.append("_")
                elif t == 0x01:
                    parts.append(rr.string())
                elif t == 0x02:
                    parts.append(str(rr.u64()))
                else:
                    raise KError("bad name part tag")
            names.append(".".join(parts))

    # Levels: nodes -> level tuples
    level_nodes = []
    if 0x02 in chunks:
        rr = Reader(chunks[0x02])
        for _ in range(rr.u64()):
            t = rr.byte()
            if t == 0x00:
                level_nodes.append(("zero",))
            elif t == 0x01:
                level_nodes.append(("succ", rr.u64()))
            elif t == 0x02:
                level_nodes.append(("max", rr.u64(), rr.u64()))
            elif t == 0x03:
                level_nodes.append(("imax", rr.u64(), rr.u64()))
            elif t == 0x04:
                level_nodes.append(("param", rr.u64()))
            else:
                raise KError("bad level node tag")

    def level_of(idx):
        if idx >= len(level_nodes):
            raise KError("level index out of bounds")
        n = level_nodes[idx]
        if n[0] == "zero":
            return ("zero",)
        if n[0] == "succ":
            return ("succ", level_of(n[1]))
        if n[0] in ("max", "imax"):
            return (n[0], level_of(n[1]), level_of(n[2]))
        return ("param", n[1])

    levels = [level_of(i) for i in range(len(level_nodes))]

    # Terms: nodes -> AST tuples (name indices resolved to strings)
    term_nodes = []
    if 0x03 in chunks:
        rr = Reader(chunks[0x03])
        for _ in range(rr.u64()):
            t = rr.byte()
            if t == 0x01:
                term_nodes.append(("bvar", rr.u64()))
            elif t == 0x02:
                name = rr.u64()
                lv = [rr.u64() for _ in range(rr.u64())]
                term_nodes.append(("const", name, lv))
            elif t == 0x03:
                term_nodes.append(("sort", rr.u64()))
            elif t == 0x04:
                term_nodes.append(("pi", rr.u64(), rr.byte(), rr.u64(), rr.u64()))
            elif t == 0x05:
                term_nodes.append(("lam", rr.u64(), rr.byte(), rr.u64(), rr.u64()))
            elif t == 0x06:
                term_nodes.append(("app", rr.u64(), rr.u64()))
            elif t == 0x07:
                term_nodes.append(("let", rr.u64(), rr.u64(), rr.u64(), rr.u64()))
            elif t == 0x08:
                term_nodes.append(("proj", rr.u64(), rr.u64(), rr.u64()))
            elif t == 0x09:
                raw = rr.blob()
                v = 0
                for k, b in enumerate(raw):
                    v |= (b & 0x7F) << (7 * k)
                term_nodes.append(("litnat", v))
            elif t == 0x0A:
                term_nodes.append(("litstr", rr.string()))
            else:
                raise KError(f"bad term node tag {t:#x}")

    def term_of(idx, depth=0):
        if idx >= len(term_nodes):
            raise KError("term index out of bounds")
        if depth > 100000:
            raise KError("term graph too deep")
        n = term_nodes[idx]
        if n[0] == "bvar":
            return ("bvar", n[1])
        if n[0] == "const":
            if n[1] >= len(names):
                raise KError("const name index out of bounds")
            return ("const", names[n[1]], tuple(levels[i] for i in n[2]))
        if n[0] == "sort":
            return ("sort", levels[n[1]])
        if n[0] == "pi":
            return ("pi", term_of(n[3], depth + 1), term_of(n[4], depth + 1))
        if n[0] == "lam":
            return ("lam", term_of(n[3], depth + 1), term_of(n[4], depth + 1))
        if n[0] == "app":
            return ("app", term_of(n[1], depth + 1), term_of(n[2], depth + 1))
        if n[0] == "let":
            return ("let", term_of(n[2], depth + 1), term_of(n[3], depth + 1), term_of(n[4], depth + 1))
        if n[0] == "proj":
            return ("proj", names[n[1]], n[2], term_of(n[3], depth + 1))
        if n[0] == "litnat":
            return ("litnat", n[1])
        return ("litstr", n[1])

    terms = [term_of(i) for i in range(len(term_nodes))]

    # Contexts (decoded for completeness; this checker re-derives contexts)
    contexts = []
    if 0x04 in chunks:
        rr = Reader(chunks[0x04])
        for _ in range(rr.u64()):
            ctx = []
            for _ in range(rr.u64()):
                is_let = rr.byte() == 0x02
                nm = rr.u64()
                ty = rr.u64()
                has_v = rr.byte()
                val = rr.u64() if has_v else None
                ctx.append((is_let, nm, ty, val))
            contexts.append(ctx)

    # Declarations
    decls = []
    if 0x05 in chunks:
        rr = Reader(chunks[0x05])
        for _ in range(rr.u64()):
            kind = rr.byte()
            name = rr.u64()
            lps = [rr.u64() for _ in range(rr.u64())]
            ty = rr.u64()
            has_v = rr.byte()
            value = rr.u64() if has_v else None
            hint = rr.byte()
            num_params = 0
            ctors = []
            block = None
            if kind == 0x06:
                num_params = rr.u64()
                for _ in range(rr.u64()):
                    cn = rr.u64()
                    ct = rr.u64()
                    ctors.append((cn, ct))
                if rr.byte():
                    block = rr.u64()
            if name >= len(names):
                raise KError("decl name index out of bounds")
            decls.append(
                {
                    "kind": kind,
                    "name": names[name],
                    "level_params": [names[i] for i in lps],
                    "ty": terms[ty],
                    "value": terms[value] if value is not None else None,
                    "ty_idx": ty,
                    "value_idx": value,
                    "hint": hint,
                    "num_params": num_params,
                    "ctors": [(names[c], terms[t], t) for (c, t) in ctors],
                    "block": block,
                }
            )

    roots = []
    if 0x08 in chunks:
        rr = Reader(chunks[0x08])
        roots = [names[rr.u64()] for _ in range(rr.u64())]

    return {"profile": profile, "names": names, "decls": decls, "roots": roots, "contexts": contexts}


# --------------------------------------------------------------------------
# Universe levels: reference normal forms (mirror of rigor-spec/reference.rs)
# Atoms: ('c', n) constant, ('p', idx, off) param+offset,
#        ('i', atoms_tuple, p) unresolved imax guarded by param p.
# A RefLevel is a sorted tuple of atoms.
# --------------------------------------------------------------------------


def _subsume(atoms):
    atoms = sorted(set(atoms))
    max_const = max([a[1] for a in atoms if a[0] == "c"], default=None)
    kept = []
    for a in atoms:
        if a[0] == "c":
            if any(b[0] == "p" and b[2] >= a[1] for b in atoms):
                continue
            if max_const is not None and a[1] == max_const:
                kept.append(a)
        elif a[0] == "p":
            if any(b[0] == "p" and b[1] == a[1] and b[2] > a[2] for b in atoms):
                continue
            kept.append(a)
        else:
            kept.append(a)
    return tuple(sorted(set(kept)))


@lru_cache(maxsize=None)
def ref_of_level(lv):
    if lv[0] == "zero":
        return (("c", 0),)
    if lv[0] == "succ":
        return ref_succ(ref_of_level(lv[1]))
    if lv[0] == "max":
        return ref_max(ref_of_level(lv[1]), ref_of_level(lv[2]))
    if lv[0] == "imax":
        return ref_imax(ref_of_level(lv[1]), ref_of_level(lv[2]))
    if lv[0] == "param":
        return (("p", lv[1], 0),)
    raise KError("bad level")


@lru_cache(maxsize=None)
def ref_succ(r):
    out = []
    for a in r:
        if a[0] == "c":
            out.append(("c", a[1] + 1))
        elif a[0] == "p":
            out.append(("p", a[1], a[2] + 1))
        else:
            out.append(("i", ref_succ(a[1]), a[2]))
    return _subsume(out)


@lru_cache(maxsize=None)
def ref_max(a, b):
    return _subsume(list(a) + list(b))


def _is_zero(r):
    return r == (("c", 0),)


def _positive_guaranteed(r):
    return any((a[0] == "c" and a[1] >= 1) or (a[0] == "p" and a[2] >= 1) for a in r)


@lru_cache(maxsize=None)
def ref_imax(u, v):
    if _is_zero(v):
        return (("c", 0),)
    if _positive_guaranteed(v):
        return ref_max(u, v)
    if len(v) > 1:
        result = (("c", 0),)
        first = True
        for atom in v:
            part = ref_imax(u, (atom,))
            result = part if first else ref_max(result, part)
            first = False
        return result
    a = v[0]
    if a[0] == "c":
        return ref_max(u, v)
    if a[0] == "p":
        if a[2] >= 1:
            return ref_max(u, v)
        return _subsume([("i", u, a[1])])
    # imax atom
    combined = ref_max(u, a[1])
    return _subsume([("i", combined, a[2])])


def levels_equiv(a, b):
    return ref_of_level(a) == ref_of_level(b)


# --------------------------------------------------------------------------
# De Bruijn operations
# --------------------------------------------------------------------------


def shift(e, by, cutoff=0):
    if by == 0:
        return e
    tag = e[0]
    if tag == "bvar":
        return ("bvar", e[1] + by) if e[1] >= cutoff else e
    if tag in ("const", "sort", "litnat", "litstr"):
        return e
    if tag == "pi":
        return ("pi", shift(e[1], by, cutoff), shift(e[2], by, cutoff + 1))
    if tag == "lam":
        return ("lam", shift(e[1], by, cutoff), shift(e[2], by, cutoff + 1))
    if tag == "app":
        return ("app", shift(e[1], by, cutoff), shift(e[2], by, cutoff))
    if tag == "let":
        return ("let", shift(e[1], by, cutoff), shift(e[2], by, cutoff), shift(e[3], by, cutoff + 1))
    if tag == "proj":
        return ("proj", e[1], e[2], shift(e[3], by, cutoff))
    raise KError("bad term in shift")


def subst_top(e, repl):
    """Replace BVar 0 by repl (shifted under binders), decrement the rest."""

    def go(t, depth):
        tag = t[0]
        if tag == "bvar":
            if t[1] == depth:
                return shift(repl, depth, 0)
            if t[1] > depth:
                return ("bvar", t[1] - 1)
            return t
        if tag in ("const", "sort", "litnat", "litstr"):
            return t
        if tag == "pi":
            return ("pi", go(t[1], depth), go(t[2], depth + 1))
        if tag == "lam":
            return ("lam", go(t[1], depth), go(t[2], depth + 1))
        if tag == "app":
            return ("app", go(t[1], depth), go(t[2], depth))
        if tag == "let":
            return ("let", go(t[1], depth), go(t[2], depth), go(t[3], depth + 1))
        if tag == "proj":
            return ("proj", t[1], t[2], go(t[3], depth))
        raise KError("bad term in subst")

    return go(e, 0)


def subst_telescope(e, args):
    """Instantiate a telescope (args[0] outermost) in one pass.

    Iterating subst_top is wrong: each subst_top decrements free
    variables inside ambient terms substituted earlier. A free BVar(i)
    at binder depth d names telescope position (i - d) from the
    innermost binder, i.e. args[len-1-(i-d)], shifted by d.
    """
    if not args:
        return e
    n = len(args)

    def go(t, depth):
        tag = t[0]
        if tag == "bvar":
            i = t[1]
            if i < depth:
                return t
            rel = i - depth
            if rel < n:
                return shift(args[n - 1 - rel], depth, 0)
            return ("bvar", i - n)
        if tag in ("const", "sort", "litnat", "litstr"):
            return t
        if tag == "pi":
            return ("pi", go(t[1], depth), go(t[2], depth + 1))
        if tag == "lam":
            return ("lam", go(t[1], depth), go(t[2], depth + 1))
        if tag == "app":
            return ("app", go(t[1], depth), go(t[2], depth))
        if tag == "let":
            return ("let", go(t[1], depth), go(t[2], depth), go(t[3], depth + 1))
        if tag == "proj":
            return ("proj", t[1], t[2], go(t[3], depth))
        raise KError("bad term in subst_telescope")

    return go(e, 0)


def subst_levels(e, subst):
    if not subst:
        return e

    def sl(lv):
        if lv[0] == "param":
            if lv[1] >= len(subst):
                raise KError("universe parameter out of scope")
            return subst[lv[1]]
        if lv[0] == "succ":
            return ("succ", sl(lv[1]))
        if lv[0] in ("max", "imax"):
            return (lv[0], sl(lv[1]), sl(lv[2]))
        return lv

    tag = e[0]
    if tag == "const":
        return ("const", e[1], tuple(sl(l) for l in e[2]))
    if tag == "sort":
        return ("sort", sl(e[1]))
    if tag == "pi":
        return ("pi", subst_levels(e[1], subst), subst_levels(e[2], subst))
    if tag == "lam":
        return ("lam", subst_levels(e[1], subst), subst_levels(e[2], subst))
    if tag == "app":
        return ("app", subst_levels(e[1], subst), subst_levels(e[2], subst))
    if tag == "let":
        return ("let", subst_levels(e[1], subst), subst_levels(e[2], subst), subst_levels(e[3], subst))
    if tag == "proj":
        return ("proj", e[1], e[2], subst_levels(e[3], subst))
    return e


def spine(e):
    args = []
    while e[0] == "app":
        args.append(e[2])
        e = e[1]
    args.reverse()
    return e, args


def pi_telescope(e):
    binders = []
    while e[0] == "pi":
        binders.append(e[1])
        e = e[2]
    return binders, e


# --------------------------------------------------------------------------
# Named terms (only for recursor generation, mirroring the kernel)
# ('nv', name) ('nc', name, levels) ('ns', level) ('npi', name, dom, cod)
# ('nlam', name, dom, body) ('napp', f, a)
# --------------------------------------------------------------------------


def named_to_db(e, scope):
    tag = e[0]
    if tag == "nv":
        for i, n in enumerate(reversed(scope)):
            if n == e[1]:
                return ("bvar", i)
        raise KError(f"recursor generation: unbound variable {e[1]}")
    if tag == "nc":
        return ("const", e[1], e[2])
    if tag == "ns":
        return ("sort", e[1])
    if tag == "napp":
        return ("app", named_to_db(e[1], scope), named_to_db(e[2], scope))
    if tag in ("npi", "nlam"):
        dom = named_to_db(e[2], scope)
        scope.append(e[1])
        body = named_to_db(e[3], scope)
        scope.pop()
        return ("pi" if tag == "npi" else "lam", dom, body)
    raise KError("named_to_db: unsupported")


def napp(f, *args):
    for a in args:
        f = ("napp", f, a)
    return f


def subst_named(e, frm, to):
    tag = e[0]
    if tag == "nv":
        return ("nv", to) if e[1] == frm else e
    if tag in ("nc", "ns"):
        return e
    if tag == "napp":
        return ("napp", subst_named(e[1], frm, to), subst_named(e[2], frm, to))
    if tag in ("npi", "nlam"):
        d = subst_named(e[2], frm, to)
        if e[1] == frm:
            return (tag, e[1], d, e[3])
        return (tag, e[1], d, subst_named(e[3], frm, to))
    return e


# --------------------------------------------------------------------------
# The kernel
# --------------------------------------------------------------------------

DECL_AXIOM, DECL_DEF, DECL_THEOREM, DECL_OPAQUE, DECL_QUOT, DECL_INDUCTIVE, DECL_EXTERNAL = 1, 2, 3, 4, 5, 6, 7
HINT_OPAQUE = 0


class Kernel:
    def __init__(self):
        self.env = {}  # name -> decl dict
        self.order = []
        self.steps = 0
        self.max_steps = 60_000_000
        self.level_scope = 0  # level params of the decl being admitted
        self.quot_used = False

    def tick(self):
        self.steps += 1
        if self.steps > self.max_steps:
            raise ResourceError("step budget exhausted")

    # ---- declaration helpers ----

    def add_decl(self, decl):
        name = decl["name"]
        if name in self.env:
            raise KError(f"duplicate declaration {name}")
        self.env[name] = decl
        self.order.append(name)

    # ---- whnf ----

    def whnf(self, ctx, e):
        while True:
            self.tick()
            nxt = self.whnf_step(ctx, e)
            if nxt == e:
                return e
            e = nxt

    def nat_literal_op(self, name, args):
        def lit(a):
            return a[1] if a[0] == "litnat" else None

        if len(args) < 2:
            return None
        a, b = lit(args[0]), lit(args[1])
        if a is None or b is None:
            return None
        if name == "Nat.add":
            return ("litnat", a + b)
        if name == "Nat.mul":
            return ("litnat", a * b)
        if name == "Nat.sub":
            return ("litnat", max(0, a - b))
        if name == "Nat.pow":
            if b > 10_000:
                return None
            return ("litnat", a**b)
        if name == "Nat.div":
            return ("litnat", 0 if b == 0 else a // b)
        if name == "Nat.mod":
            return ("litnat", a if b == 0 else a % b)
        return None

    def whnf_step(self, ctx, e):
        tag = e[0]
        if tag == "bvar":
            idx = len(ctx) - 1 - e[1]
            if 0 <= idx < len(ctx):
                v = ctx[idx][1]
                if v is not None:
                    return shift(v, e[1] + 1, 0)
            return e
        if tag == "let":
            return subst_top(e[3], e[2])
        if tag == "app":
            head, args = spine(e)
            if head[0] == "lam":
                result = subst_top(head[2], args[0])
                for a in args[1:]:
                    result = ("app", result, a)
                return result
            if head[0] == "const":
                name, levels = head[1], head[2]
                r = self.nat_literal_op(name, args)
                if r is not None:
                    return r
                decl = self.env.get(name)
                if decl is not None:
                    if decl.get("recursor"):
                        r = self.try_iota(ctx, name, levels, decl, args)
                        if r is not None:
                            return r
                        return e
                    if decl["kind"] == "quot":
                        r = self.try_quot(name, args)
                        if r is not None:
                            return r
                        return e
                    if decl["kind"] == DECL_DEF and decl["hint"] != HINT_OPAQUE and decl.get("value") is not None:
                        result = subst_levels(decl["value"], levels)
                        for a in args:
                            result = ("app", result, a)
                        return result
                return e
            if head[0] == "proj":
                p = self.whnf_step(ctx, head)
                if p != head:
                    result = p
                    for a in args:
                        result = ("app", result, a)
                    return result
                return e
            hw = self.whnf(ctx, head)
            if hw != head:
                result = hw
                for a in args:
                    result = ("app", result, a)
                return result
            return e
        if tag == "proj":
            tw = self.whnf(ctx, e[3])
            head, args = spine(tw)
            if head[0] == "const":
                ctor = self.env.get(head[1])
                if ctor is not None and ctor.get("ctor") and ctor["ctor"]["inductive"] == e[1]:
                    ind = self.env[e[1]]["inductive"]
                    pos = ind["num_params"] + e[2]
                    if pos < len(args):
                        return args[pos]
            if tw != e[3]:
                return ("proj", e[1], e[2], tw)
            return e
        if tag == "const":
            decl = self.env.get(e[1])
            if (
                decl is not None
                and decl["kind"] == DECL_DEF
                and decl["hint"] != HINT_OPAQUE
                and decl.get("value") is not None
            ):
                return subst_levels(decl["value"], e[2])
            return e
        return e

    def try_quot(self, name, args):
        if name == "Quot.lift" and len(args) >= 6:
            q = args[5]
            head, qargs = spine(q)
            if head[0] == "const" and head[1] == "Quot.mk" and len(qargs) >= 3:
                return ("app", args[3], qargs[2])
        return None

    # ---- iota ----

    def try_iota(self, ctx, rec_name, levels, rec_decl, args):
        info = self.env[rec_decl["recursor"]["inductive"]]["inductive"]
        block = info["block_members"]  # list of (name, info)
        total_ctors = sum(len(m[1]["constructors"]) for m in block)
        target_idx = next(i for i, m in enumerate(block) if m[0] == rec_decl["recursor"]["inductive"])
        tinfo = block[target_idx][1]
        num_params = tinfo["num_params"]
        num_motives = len(block)
        header = num_params + num_motives + total_ctors
        needed = header + tinfo["num_indices"] + 1
        if len(args) < needed:
            return None
        major = args[needed - 1]
        major_w = self.whnf(ctx, major)
        head, ctor_args = spine(major_w)
        if head[0] == "litnat":
            return self.iota_nat_literal(ctx, levels, rec_decl, args, head[1], needed)
        if head[0] != "const":
            return None
        ctor_decl = self.env.get(head[1])
        if ctor_decl is None or not ctor_decl.get("ctor"):
            return None
        cinfo = ctor_decl["ctor"]
        if len(ctor_args) < num_params + cinfo["num_fields"]:
            return None
        minor_offset = num_params + num_motives
        chosen_minor = None
        for _, minfo in block:
            for ci, cname in enumerate(minfo["constructors"]):
                if cname == head[1]:
                    chosen_minor = args[minor_offset + ci]
            minor_offset += len(minfo["constructors"])
        if chosen_minor is None:
            return None
        fields = ctor_args[num_params : num_params + cinfo["num_fields"]]
        ctor_binders, _ = pi_telescope(ctor_decl["ty"])
        result = chosen_minor
        applied = list(ctor_args[:num_params])
        # Minor telescope: all fields, then the IHs (field order).
        ihs = []
        for fi, field_val in enumerate(fields):
            result = ("app", result, field_val)
            applied.append(field_val)
            binder_pos = num_params + fi
            if binder_pos >= len(ctor_binders):
                continue
            field_ty = ctor_binders[binder_pos]
            # subst_telescope with applied-so-far excluding current field
            instantiated = subst_telescope(field_ty, applied[:-1])
            fb, tail = pi_telescope(instantiated)
            thead, targs = spine(tail)
            is_rec = thead[0] == "const" and any(thead[1] == bn for bn, _ in block)
            if not is_rec:
                continue
            rec_for = None
            for dname in self.order:
                d = self.env[dname]
                if d.get("recursor") and d["recursor"]["inductive"] == thead[1] and d["recursor"]["block_id"] == rec_decl["recursor"]["block_id"]:
                    rec_for = dname
                    break
            if rec_for is None:
                continue
            field_indices = targs[num_params:]
            ih = ("const", rec_for, levels)
            for a in args[:num_params]:
                ih = ("app", ih, a)
            for a in args[num_params : num_params + num_motives + total_ctors]:
                ih = ("app", ih, a)
            nb = len(fb)
            for idx_expr in field_indices:
                ih = ("app", ih, shift(idx_expr, nb, 0))
            major_expr = shift(field_val, nb, 0)
            for b in range(nb):
                major_expr = ("app", major_expr, ("bvar", nb - 1 - b))
            ih = ("app", ih, major_expr)
            for bdom in reversed(fb):
                ih = ("lam", bdom, ih)
            ihs.append(ih)
        for ih in ihs:
            result = ("app", result, ih)
        for a in args[needed:]:
            result = ("app", result, a)
        return result

    def iota_nat_literal(self, ctx, levels, rec_decl, args, v, needed):
        ind = self.env[rec_decl["recursor"]["inductive"]]["inductive"]
        if ind["num_params"] != 0 or len(args) < needed:
            return None
        # minors start after params(0) + motives(1)
        minor_start = ind["num_params"] + 1
        if minor_start + 1 >= len(args):
            return None
        if v == 0:
            result = args[minor_start]
            for a in args[needed:]:
                result = ("app", result, a)
            return result
        if v > 100_000:
            return None
        pred = v - 1
        succ_minor = args[minor_start + 1]
        rec_name = rec_decl["name"]
        rec_call = ("const", rec_name, levels)
        for a in args[: needed - 1]:
            rec_call = ("app", rec_call, a)
        rec_call = ("app", rec_call, ("litnat", pred))
        result = ("app", ("app", succ_minor, ("litnat", pred)), rec_call)
        for a in args[needed:]:
            result = ("app", result, a)
        return result

    # ---- nat values ----

    def nat_value(self, ctx, e):
        w = self.whnf(ctx, e)
        if w[0] == "litnat":
            return w[1]
        if w[0] == "const" and w[1] == "Nat.zero":
            return 0
        if w[0] == "app":
            head, args = spine(w)
            if len(args) == 1 and head[0] == "const" and head[1] == "Nat.succ":
                inner = self.nat_value(ctx, args[0])
                return None if inner is None else inner + 1
        return None

    # ---- defeq ----

    def is_prop_type(self, ctx, ty):
        try:
            s = self.infer(ctx, ty)
        except (KError, RecursionError):
            return False
        return s[0] == "sort" and _is_zero(ref_of_level(s[1]))

    def defeq(self, ctx, a, b):
        self.tick()
        if a == b:
            return True
        na, nb = self.nat_value(ctx, a), self.nat_value(ctx, b)
        if na is not None and nb is not None:
            return na == nb
        aw, bw = self.whnf(ctx, a), self.whnf(ctx, b)
        if aw == bw:
            return True
        # proof irrelevance: two proofs of the same proposition. The Prop
        # check comes first (as in the Rust kernel): it is the cheap gate
        # that keeps this probe from recursing into type-level defeq for
        # every pair of data terms.
        try:
            ta = self.infer(ctx, aw)
            tb = self.infer(ctx, bw)
            if self.is_prop_type(ctx, ta) and self.defeq(ctx, ta, tb):
                return True
        except (KError, RecursionError):
            pass
        if aw[0] == "sort" and bw[0] == "sort":
            return levels_equiv(aw[1], bw[1])
        if aw[0] == "pi" and bw[0] == "pi":
            return self.defeq(ctx, aw[1], bw[1]) and self.defeq(ctx + [(aw[1], None)], aw[2], bw[2])
        if aw[0] == "lam" and bw[0] == "lam":
            return self.defeq(ctx, aw[1], bw[1]) and self.defeq(ctx + [(aw[1], None)], aw[2], bw[2])
        if aw[0] == "lam":
            return self.defeq(ctx + [(aw[1], None)], aw[2], ("app", shift(bw, 1, 0), ("bvar", 0)))
        if bw[0] == "lam":
            return self.defeq(ctx + [(bw[1], None)], ("app", shift(aw, 1, 0), ("bvar", 0)), bw[2])
        if aw[0] == "app" and bw[0] == "app":
            ah, aa = spine(aw)
            bh, ba = spine(bw)
            if len(aa) != len(ba):
                return False
            if ah[0] == "const" and bh[0] == "const":
                if ah[1] != bh[1] or len(ah[2]) != len(bh[2]):
                    return False
                if not all(levels_equiv(x, y) for x, y in zip(ah[2], bh[2])):
                    return False
            elif not self.defeq(ctx, ah, bh):
                return False
            return all(self.defeq(ctx, x, y) for x, y in zip(aa, ba))
        if aw[0] == "const" and bw[0] == "const":
            return (
                aw[1] == bw[1]
                and len(aw[2]) == len(bw[2])
                and all(levels_equiv(x, y) for x, y in zip(aw[2], bw[2]))
            )
        if aw[0] == "proj" and bw[0] == "proj":
            return aw[1] == bw[1] and aw[2] == bw[2] and self.defeq(ctx, aw[3], bw[3])
        if aw[0] == "let":
            return self.defeq(ctx, subst_top(aw[3], aw[2]), bw)
        if bw[0] == "let":
            return self.defeq(ctx, aw, subst_top(bw[3], bw[2]))
        if aw[0] == "litstr" and bw[0] == "litstr":
            return aw[1] == bw[1]
        return False

    # ---- infer / check ----

    def check(self, ctx, e, expected):
        self.tick()
        if e[0] == "lam":
            ew = self.whnf(ctx, expected)
            if ew[0] == "pi":
                if not self.defeq(ctx, e[1], ew[1]):
                    raise KError("lambda domain does not match Pi domain")
                self.check(ctx + [(e[1], None)], e[2], ew[2])
                return
        if e[0] == "let":
            self.level_of_sort(ctx, e[1])
            self.check(ctx, e[2], e[1])
            self.check(ctx + [(e[1], e[2])], e[3], shift(expected, 1, 0))
            return
        inferred = self.infer(ctx, e)
        if not self.defeq(ctx, inferred, expected):
            raise KError("type mismatch")

    def level_of_sort(self, ctx, ty):
        s = self.infer(ctx, ty)
        if s[0] != "sort":
            raise KError("expected a type (a term whose type is a Sort)")
        return s[1]

    def infer(self, ctx, e):
        self.tick()
        tag = e[0]
        if tag == "bvar":
            idx = len(ctx) - 1 - e[1]
            if not (0 <= idx < len(ctx)):
                raise KError("unbound variable")
            return shift(ctx[idx][0], e[1] + 1, 0)
        if tag == "sort":
            self.validate_level(e[1])
            return ("sort", ("succ", e[1]))
        if tag == "pi":
            a = self.level_of_sort(ctx, e[1])
            b = self.level_of_sort(ctx + [(e[1], None)], e[2])
            return ("sort", ("imax", a, b))
        if tag == "lam":
            self.level_of_sort(ctx, e[1])
            body_ty = self.infer(ctx + [(e[1], None)], e[2])
            return ("pi", e[1], body_ty)
        if tag == "app":
            fty = self.infer(ctx, e[1])
            fw = self.whnf(ctx, fty)
            if fw[0] != "pi":
                raise KError("application of a non-function")
            self.check(ctx, e[2], fw[1])
            return subst_top(fw[2], e[2])
        if tag == "let":
            self.level_of_sort(ctx, e[1])
            self.check(ctx, e[2], e[1])
            return self.infer(ctx + [(e[1], e[2])], e[3])
        if tag == "const":
            name, levels = e[1], e[2]
            decl = self.env.get(name)
            if decl is None:
                raise KError(f"unknown constant {name}")
            # Recursor decls registered by admit_block already include the
            # trailing elimination universe (u_rec) in level_params.
            expected = len(decl["level_params"])
            if len(levels) != expected:
                raise KError(f"constant {name} expects {expected} universe arguments, got {len(levels)}")
            for lv in levels:
                self.validate_level(lv)
            if decl.get("recursor"):
                self.check_recursor_elim(decl, levels)
            return subst_levels(decl["ty"], levels)
        if tag == "proj":
            struct_name, idx, term = e[1], e[2], e[3]
            tty = self.infer(ctx, term)
            tw = self.whnf(ctx, tty)
            head, targs = spine(tw)
            if head[0] != "const" or head[1] != struct_name:
                raise KError("projection on a non-structure")
            ind = self.env[struct_name]["inductive"]
            if len(ind["constructors"]) != 1:
                raise KError("projection requires a single-constructor inductive")
            ctor = self.env[ind["constructors"][0]]
            binders, _ = pi_telescope(ctor["ty"])
            pos = ind["num_params"] + idx
            if pos >= len(binders):
                raise KError("projection index out of range")
            field_ty = binders[pos]
            subst_args = list(targs[: ind["num_params"]])
            for k in range(idx):
                subst_args.append(("proj", struct_name, k, term))
            return subst_telescope(field_ty, subst_args)
        if tag == "litnat":
            if "Nat" not in self.env:
                raise UnsupportedError("Nat literal used before Nat is declared")
            return ("const", "Nat", ())
        if tag == "litstr":
            if "String" not in self.env:
                raise UnsupportedError("String literal used before String is declared")
            return ("const", "String", ())
        raise KError(f"cannot infer type of {tag}")

    def validate_level(self, lv):
        if lv[0] == "param":
            if lv[1] >= self.level_scope:
                raise KError("universe parameter out of scope")
        elif lv[0] == "succ":
            self.validate_level(lv[1])
        elif lv[0] in ("max", "imax"):
            self.validate_level(lv[1])
            self.validate_level(lv[2])

    def check_recursor_elim(self, rec_decl, levels):
        ind_name = rec_decl["recursor"]["inductive"]
        ind_decl = self.env[ind_name]
        info = ind_decl["inductive"]
        if not info["is_prop"]:
            return
        if len(levels) != len(ind_decl["level_params"]) + 1:
            return
        motive_level = levels[-1]
        if _is_zero(ref_of_level(motive_level)):
            return
        if len(info["constructors"]) > 1:
            raise KError(f"Prop inductive {ind_name} with multiple constructors cannot eliminate into Type")
        if len(info["constructors"]) == 1:
            ctor = self.env[info["constructors"][0]]
            binders, _ = pi_telescope(ctor["ty"])
            ctx = []
            for j, dom in enumerate(binders):
                if j >= info["num_params"]:
                    s = self.level_of_sort(ctx, dom)
                    if not _is_zero(ref_of_level(s)):
                        raise KError(f"Prop inductive {ind_name} is not a singleton")
                ctx.append((dom, None))

    # ---- admission ----

    def admit_value_decl(self, d):
        self.level_scope = len(d["level_params"])
        # the type must be a type
        s = self.infer([], d["ty"])
        if s[0] != "sort":
            raise KError(f"{d['name']}: declaration type is not a Sort")
        decl = {
            "name": d["name"],
            "kind": d["kind"],
            "level_params": d["level_params"],
            "ty": d["ty"],
            "value": None,
            "hint": d["hint"],
        }
        if d["kind"] == DECL_AXIOM:
            if d["value"] is not None:
                raise KError("axiom with a value")
        else:
            if d["value"] is None:
                raise KError(f"{d['name']}: missing proof/value")
            self.check([], d["value"], d["ty"])
            decl["value"] = d["value"]
        self.add_decl(decl)

    def admit_quot(self):
        if "Quot" in self.env:
            return
        # Canonical quotient package (mirrors the kernel's add_quot).
        u = ("param", 0)
        v = ("param", 1)
        alpha = ("nv", "α")
        r = ("nv", "r")
        sort_u = ("ns", u)
        rel = ("npi", "_", alpha, ("npi", "_", alpha, ("ns", ("zero",))))
        quot_ty = ("npi", "α", sort_u, ("npi", "r", rel, ("ns", u)))
        mk_ty = ("npi", "α", sort_u, ("npi", "r", rel, ("npi", "a", alpha, napp(("nc", "Quot", (u,)), alpha, r))))
        eq_beta = napp(("nc", "Eq", (v,)), ("nv", "β"), ("napp", ("nv", "f"), ("nv", "a")), ("napp", ("nv", "f"), ("nv", "b")))
        h_ty = ("npi", "a", alpha, ("npi", "b", alpha, ("npi", "_", napp(r, ("nv", "a"), ("nv", "b")), eq_beta)))
        lift_ty = (
            "npi", "α", sort_u,
            ("npi", "r", rel,
             ("npi", "β", ("ns", v),
              ("npi", "f", ("npi", "_", alpha, ("nv", "β")),
               ("npi", "h", h_ty,
                ("npi", "q", napp(("nc", "Quot", (u,)), alpha, r), ("nv", "β")))))),
        )
        ind_ty = (
            "npi", "α", sort_u,
            ("npi", "r", rel,
             ("npi", "β", ("npi", "_", napp(("nc", "Quot", (u,)), alpha, r), ("ns", ("zero",))),
              ("npi", "h", ("npi", "a", alpha, napp(("nv", "β"), napp(("nc", "Quot.mk", (u,)), alpha, r, ("nv", "a")))),
               ("npi", "q", napp(("nc", "Quot", (u,)), alpha, r), napp(("nv", "β"), ("nv", "q")))))),
        )
        for name, lps, ty in [("Quot", ["u"], quot_ty), ("Quot.mk", ["u"], mk_ty), ("Quot.lift", ["u", "v"], lift_ty), ("Quot.ind", ["u"], ind_ty)]:
            self.level_scope = len(lps)
            db = named_to_db(ty, [])
            s = self.infer([], db)
            if s[0] != "sort":
                raise KError(f"{name}: quotient primitive type is not a Sort")
            self.add_decl({"name": name, "kind": "quot", "level_params": lps, "ty": db, "value": None, "hint": 0})

    # -- inductive blocks --

    def admit_block(self, specs):
        """specs: list of bundle decl dicts with kind == DECL_INDUCTIVE."""
        block_names = [s["name"] for s in specs]
        block_id = specs[0]["block"]
        members = []
        for s in specs:
            self.level_scope = len(s["level_params"])
            st = self.infer([], s["ty"])
            if st[0] != "sort":
                raise KError(f"{s['name']}: inductive type is not a Sort")
            binders, tail = pi_telescope(s["ty"])
            if tail[0] != "sort":
                raise KError(f"{s['name']}: inductive type does not end in a Sort")
            np = s["num_params"]
            if np > len(binders):
                raise KError(f"{s['name']}: num_params exceeds telescope")
            info = {
                "num_params": np,
                "num_indices": len(binders) - np,
                "constructors": [c[0] for c in s["ctors"]],
                "is_prop": _is_zero(ref_of_level(tail[1])),
                "sort_level": tail[1],
                "block_id": block_id,
                "block_members": None,  # filled below
                "level_params": s["level_params"],
            }
            members.append(info)
        for info in members:
            info["block_members"] = [(s["name"], i) for s, i in zip(specs, members)]
        # register inductives and constructors provisionally
        for s, info in zip(specs, members):
            self.add_decl(
                {
                    "name": s["name"],
                    "kind": DECL_INDUCTIVE,
                    "level_params": s["level_params"],
                    "ty": s["ty"],
                    "value": None,
                    "hint": s["hint"],
                    "inductive": info,
                }
            )
            for ci, (cname, cty, _) in enumerate(s["ctors"]):
                self.level_scope = len(s["level_params"])
                cbinders, _ = pi_telescope(cty)
                self.add_decl(
                    {
                        "name": cname,
                        "kind": "ctor",
                        "level_params": s["level_params"],
                        "ty": cty,
                        "value": None,
                        "hint": 0,
                        "ctor": {"inductive": s["name"], "ordinal": ci, "num_fields": len(cbinders) - info["num_params"]},
                    }
                )
        # validate constructors
        for s, info in zip(specs, members):
            self.level_scope = len(s["level_params"])
            for cname, cty, _ in s["ctors"]:
                s_ty = self.infer([], cty)
                if s_ty[0] != "sort":
                    raise KError(f"{cname}: constructor type is not a Sort")
                binders, result = pi_telescope(cty)
                head, rargs = spine(result)
                if head[0] != "const" or head[1] != s["name"]:
                    raise KError(f"{cname}: constructor does not construct {s['name']}")
                np = info["num_params"]
                nfields = len(binders) - np
                if len(rargs) < np:
                    raise KError(f"{cname}: constructor result missing parameters")
                for j in range(np):
                    expect = ("bvar", np + nfields - 1 - j)
                    if rargs[j] != expect:
                        raise KError(f"{cname}: constructor does not return its parameters as bound variables")
                # strict positivity over the whole block
                for dom in binders[np:]:
                    self.check_positive(dom, block_names)
        # generate recursors
        for si, (s, info) in enumerate(zip(specs, members)):
            rec_ty = self.generate_recursor(specs, members, si)
            rec_name = f"{s['name']}.rec"
            self.add_decl(
                {
                    "name": rec_name,
                    "kind": "recursor",
                    "level_params": list(s["level_params"]) + ["u_rec"],
                    "ty": rec_ty,
                    "value": None,
                    "hint": 0,
                    "recursor": {"inductive": s["name"], "block_id": block_id},
                }
            )

    def check_positive(self, e, block_names):
        """Strict positivity: block inductives may only occur as the head of
        the (Pi-stripped) field type, with no occurrence in any Pi domain or
        nested argument. Nested occurrences are UNSUPPORTED (matching the
        Rust kernel's classification)."""

        def occurs(t):
            tag = t[0]
            if tag == "const":
                return t[1] in block_names
            if tag in ("pi", "lam"):
                return occurs(t[1]) or occurs(t[2])
            if tag == "app":
                return occurs(t[1]) or occurs(t[2])
            if tag == "let":
                return occurs(t[1]) or occurs(t[2]) or occurs(t[3])
            if tag == "proj":
                return occurs(t[3])
            return False

        if e[0] == "pi":
            if occurs(e[1]):
                raise KError("inductive occurs in a Pi domain (strict positivity violated)")
            self.check_positive(e[2], block_names)
            return
        head, args = spine(e)
        if head[0] == "const" and head[1] in block_names:
            if any(occurs(a) for a in args):
                raise UnsupportedError("nested inductive occurrence")
            return
        if occurs(e):
            raise UnsupportedError("nested inductive occurrence")

    # -- recursor generation (named, mirroring the kernel) --

    def _db_named(self, e, _scope_from_root, full_scope):
        # Convert using full_scope (names outermost-first) with binder
        # positions from the term itself: we need the *local* scope at each
        # subterm; implement recursively with an explicit local scope.
        def go(t, scope):
            tag = t[0]
            if tag == "bvar":
                pos = len(scope) - 1 - t[1]
                return ("nv", scope[pos] if 0 <= pos < len(scope) else f"x{t[1]}")
            if tag == "const":
                return ("nc", t[1], t[2])
            if tag == "sort":
                return ("ns", t[1])
            if tag == "app":
                return ("napp", go(t[1], scope), go(t[2], scope))
            if tag in ("pi", "lam"):
                # binder name: position-based; callers rename as needed.
                name = f"_b{len(scope)}"
                dom = go(t[1], scope)
                body = go(t[2], scope + [name])
                return ("npi" if tag == "pi" else "nlam", name, dom, body)
            raise UnsupportedError(f"recursor generation over {tag} field shapes")

        return go(e, list(full_scope))

    def generate_recursor(self, specs, members, target):
        # Member data with canonical positional names.
        mem_data = []
        for si, s in enumerate(specs):
            np = members[si]["num_params"]
            binders, _ = pi_telescope(s["ty"])
            scope = [f"p{j}" if j < np else f"i{j - np}" for j in range(len(binders))]
            doms_named = []
            for i, dom in enumerate(binders):
                doms_named.append((scope[i], self._db_named(dom, None, scope[:i])))
            param_tys = doms_named[:np]
            index_tys = doms_named[np:]
            ctors = []
            for cname, cty, _ in s["ctors"]:
                cbinders, cresult = pi_telescope(cty)
                cscope = [f"p{j}" for j in range(np)] + [f"f{j}" for j in range(len(cbinders) - np)]
                fields = []
                for j in range(np, len(cbinders)):
                    fname = f"f{j - np}"
                    fields.append((fname, self._db_named(cbinders[j], None, cscope[:j])))
                _, rargs = spine(cresult)
                indices = [self._db_named(a, None, cscope) for a in rargs[np:]]
                ctors.append({"name": cname, "fields": fields, "indices": indices})
            mem_data.append(
                {
                    "name": s["name"],
                    "param_tys": param_tys,
                    "index_tys": index_tys,
                    "ctors": ctors,
                    "level_params": s["level_params"],
                    "num_params": np,
                }
            )

        tm = mem_data[target]
        param_names = [f"p{j}" for j in range(tm["num_params"])]
        index_names = [f"i{j}" for j in range(len(tm["index_tys"]))]

        def levels_of(mi):
            return tuple(("param", i) for i in range(len(mem_data[mi]["level_params"])))

        motive_level = ("param", len(tm["level_params"]))
        params_app = [("nv", n) for n in param_names]

        # result: motive{target} indices t
        result = napp(("nv", f"motive{target}"), *([("nv", n) for n in index_names] + [("nv", "t")]))
        ind_app = napp(("nc", tm["name"], levels_of(target)), *(params_app + [("nv", n) for n in index_names]))
        result = ("npi", "t", ind_app, result)
        for k in reversed(range(len(index_names))):
            result = ("npi", index_names[k], tm["index_tys"][k][1], result)

        # minors (names are minor_{member}_{ctor ordinal} in the kernel;
        # they vanish on lowering but are kept for fidelity)
        minor_specs = []
        for mi, member in enumerate(mem_data):
            for ci, ctor in enumerate(member["ctors"]):
                ctor_app = napp(("nc", ctor["name"], levels_of(mi)), *(params_app + [("nv", f) for f, _ in ctor["fields"]]))
                mty = napp(("nv", f"motive{mi}"), *(ctor["indices"] + [ctor_app]))
                for fname, fty in reversed(ctor["fields"]):
                    ih = self._ih_type(fty, mem_data)
                    if ih is not None:
                        ih = subst_named(ih, "__field__", fname)
                        mty = ("npi", f"ih_{fname}", ih, mty)
                for fname, fty in reversed(ctor["fields"]):
                    mty = ("npi", fname, fty, mty)
                minor_specs.append((f"minor_{mi}_{ci}", mty))
        for name, mty in reversed(minor_specs):
            result = ("npi", name, mty, result)

        # motives
        for mi in reversed(range(len(mem_data))):
            member = mem_data[mi]
            motive_ty = ("ns", motive_level)
            ind_app_m = napp(
                ("nc", member["name"], levels_of(mi)),
                *(params_app + [("nv", f"mi_i{k}") for k in range(len(member["index_tys"]))]),
            )
            motive_ty = ("npi", "mt", ind_app_m, motive_ty)
            for k in reversed(range(len(member["index_tys"]))):
                ity = member["index_tys"][k][1]
                for j in range(k):
                    ity = subst_named(ity, f"i{j}", f"mi_i{j}")
                motive_ty = ("npi", f"mi_i{k}", ity, motive_ty)
            result = ("npi", f"motive{mi}", motive_ty, result)

        # params
        for j in reversed(range(len(param_names))):
            result = ("npi", param_names[j], tm["param_tys"][j][1], result)

        self.level_scope = len(tm["level_params"]) + 1
        return named_to_db(result, [])

    def _ih_type(self, fty, mem_data):
        binders = []
        cur = fty
        while cur[0] == "npi":
            binders.append((cur[1], cur[2]))
            cur = cur[3]
        head, args = cur, []
        while head[0] == "napp":
            args.append(head[2])
            head = head[1]
        args.reverse()
        if head[0] != "nc":
            return None
        member_idx = next((i for i, m in enumerate(mem_data) if m["name"] == head[1]), None)
        if member_idx is None:
            return None
        np = mem_data[member_idx]["num_params"]
        if len(args) < np:
            return None
        indices = args[np:]
        applied = ("nv", "__field__")
        for bn, _ in binders:
            applied = ("napp", applied, ("nv", bn))
        ih = napp(("nv", f"motive{member_idx}"), *(indices + [applied]))
        for bn, bd in reversed(binders):
            ih = ("npi", bn, bd, ih)
        return ih


# --------------------------------------------------------------------------
# Bundle admission / verification driver
# --------------------------------------------------------------------------


def verify(data: bytes):
    """Returns (verdict, [root verdict lines])."""
    bundle = decode_bundle(data)
    if bundle["profile"] != "L36-1.0":
        return ("UNSUPPORTED", [f"profile {bundle['profile']} is not supported by this checker"])
    k = Kernel()
    decls = bundle["decls"]
    i = 0
    quot_done = False
    while i < len(decls):
        d = decls[i]
        kind = d["kind"]
        if kind == DECL_EXTERNAL:
            raise UnsupportedError(f"external reference {d['name']} cannot be checked by this checker")
        if kind == DECL_QUOT:
            if not quot_done:
                k.admit_quot()
                quot_done = True
            i += 1
            continue
        if kind == DECL_INDUCTIVE:
            # group consecutive members of one block
            block = d["block"]
            specs = [d]
            j = i + 1
            while j < len(decls) and decls[j]["kind"] == DECL_INDUCTIVE and decls[j]["block"] == block and block is not None:
                specs.append(decls[j])
                j += 1
            k.admit_block(specs)
            i = j
            continue
        k.admit_value_decl(d)
        i += 1
    lines = []
    for root in bundle["roots"]:
        if root not in k.env:
            raise KError(f"root {root} is not declared in the bundle")
        lines.append(f"{root}: VERIFIED")
    return ("VERIFIED", lines)


def main(argv):
    if len(argv) != 2:
        print("usage: rigor_check.py <bundle.rigorb>", file=sys.stderr)
        return 4
    with open(argv[1], "rb") as f:
        data = f.read()
    try:
        verdict, lines = verify(data)
        for line in lines:
            print(line)
        print(verdict)
        return {"VERIFIED": 0, "INVALID": 1, "UNSUPPORTED": 2, "UNKNOWN_RESOURCE": 3}.get(verdict, 5)
    except UnsupportedError as e:
        print(f"unsupported: {e}")
        print("UNSUPPORTED")
        return 2
    except ResourceError as e:
        print(f"resource: {e}")
        print("UNKNOWN_RESOURCE")
        return 3
    except KError as e:
        print(f"invalid: {e}")
        print("INVALID")
        return 1
    except RecursionError:
        print("resource: recursion limit")
        print("UNKNOWN_RESOURCE")
        return 3
    except Exception as e:  # never crash silently
        print(f"internal: {type(e).__name__}: {e}")
        print("INTERNAL_ERROR")
        return 5


if __name__ == "__main__":
    # Deep proof terms recurse through infer/defeq; the step budget in
    # Kernel.tick is the real termination guard, this just sizes the
    # Python stack to match (larger stacks via a worker thread).
    sys.setrecursionlimit(60_000)
    _result = {}

    def run():
        _result["code"] = main(sys.argv)

    try:
        threading.stack_size(512 * 1024 * 1024)
    except (ValueError, RuntimeError):
        pass
    t = threading.Thread(target=run)
    t.start()
    t.join()
    sys.exit(_result.get("code", 5))
