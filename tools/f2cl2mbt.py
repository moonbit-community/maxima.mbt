#!/usr/bin/env python3
"""Translate Maxima's f2cl-generated SLATEC/QUADPACK Lisp into MoonBit.

Usage:
    python3 tools/f2cl2mbt.py [SRC_DIR] [OUT_DIR]
    python3 tools/f2cl2mbt.py --reference-test [SRC_DIR] [OUT_DIR]

The second form regenerates slatec/sbcl_reference_wbtest.mbt by running the
original Lisp under SBCL (see gen_reference_test).

SRC_DIR defaults to .repos/maxima/src/numerical/slatec, OUT_DIR to slatec/.

The input files are the machine-generated output of f2cl (Fortran -> Common
Lisp).  Each file holds one DEFUN, optionally wrapped in a LET that holds the
Fortran SAVE/DATA variables.  The translation follows the f2cl runtime
(numerical/f2cl-lib.lisp) semantics:

* Types: double-float -> Double, single-float -> Float, integer4 -> Int,
  logical -> Bool, (simple-)array -> FixedArray[Double] / FixedArray[Int].
  Arithmetic follows CL float contagion pairwise and left to right, so the
  operation order (and hence every rounding) is the same as in the Lisp.
* Arrays keep Fortran's 1-based column-major indexing: (fref a (i j) bounds)
  becomes a[off + (i - lo1) + size1 * (j - lo2)].  When some caller passes an
  array section (f2cl's ARRAY-SLICE, or the offset of WITH-MULTI-ARRAY-DATA),
  the callee takes the array together with an Int offset parameter `<a>_off`.
* A Lisp function returns (values ...) with one slot per Fortran argument (plus
  the function value first for a FUNCTION subprogram); slots that are NIL are
  never used by callers.  The MoonBit function returns a tuple of the non-NIL
  slots, in order (a single slot is returned bare, none gives Unit).  Arrays are
  mutated in place.
* PROG/TAGBODY with GO become `while true` state machines over a `pc`
  variable; a GO to an enclosing TAGBODY uses a labelled `continue`.
  F2CL-LIB:FDO keeps f2cl's precomputed iteration count.
* SAVE variables become package-level `Ref`s (or plain constants when never
  assigned); local arrays are allocated per call like the Lisp does.
* Integrands passed to QUADPACK are closures `(Double) -> Double raise`; every
  routine that (transitively) calls one is declared `raise`.

XERMSG, XERPRN and XERSVE (string handling and formatted output) are written by
hand in slatec/xerror.mbt; the remaining routines are translated here.
"""

import math
import os
import re
import sys

sys.setrecursionlimit(100000)

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def _find_src():
    d = ROOT
    while True:
        cand = os.path.join(d, ".repos", "maxima", "src", "numerical", "slatec")
        if os.path.isdir(cand):
            return cand
        parent = os.path.dirname(d)
        if parent == d:
            return os.path.join(ROOT, ".repos", "maxima", "src", "numerical", "slatec")
        d = parent


DEFAULT_SRC = _find_src()
DEFAULT_OUT = os.path.join(ROOT, "slatec")

SKIP_FILES = {"quadpack.lisp", "xermsg.lisp", "xerprn.lisp", "xersve.lisp"}

# ---------------------------------------------------------------------------
# Reader


class Sym:
    __slots__ = ("name",)
    _tab = {}

    def __new__(cls, name):
        s = cls._tab.get(name)
        if s is None:
            s = object.__new__(cls)
            s.name = name
            cls._tab[name] = s
        return s

    def __repr__(self):
        return self.name


class Num:
    """A float literal; kind is 'd' (double) or 'f' (single)."""
    __slots__ = ("value", "kind", "text")

    def __init__(self, value, kind, text):
        self.value = value
        self.kind = kind
        self.text = text

    def __repr__(self):
        return self.text


class Str:
    __slots__ = ("text",)

    def __init__(self, text):
        self.text = text

    def __repr__(self):
        return '"%s"' % self.text


def S(name):
    return Sym(name)


_int_re = re.compile(r"^[+-]?\d+\.?$")
_flt_re = re.compile(r"^([+-]?(?:\d+\.\d*|\.\d+|\d+))(?:([eEdDfFsSlL])([+-]?\d+))?$")


def parse_atom(tok):
    if _int_re.match(tok):
        return int(tok.rstrip("."))
    m = _flt_re.match(tok)
    if m and ("." in tok or m.group(2)):
        mant, marker, ex = m.groups()
        kind = "d"
        if marker and marker in "fFsS":
            kind = "f"
        val = float(mant + ("e" + ex if ex else ""))
        return Num(val, kind, tok)
    name = tok.lower()
    if name.startswith("f2cl-lib::"):
        name = "f2cl-lib:" + name[len("f2cl-lib::"):]
    for pre in ("cl:", "common-lisp:", "slatec::", "slatec:"):
        if name.startswith(pre):
            name = name[len(pre):]
    return Sym(name)


def read_forms(text):
    toks = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c in " \t\r\n\f":
            i += 1
        elif c == ";":
            while i < n and text[i] != "\n":
                i += 1
        elif c == "#" and text[i + 1] == "|":
            i = text.index("|#", i) + 2
        elif c in "()":
            toks.append(c)
            i += 1
        elif c == "'":
            toks.append("'")
            i += 1
        elif c == "#" and text[i + 1] == "'":
            toks.append("#'")
            i += 2
        elif c == '"':
            j = i + 1
            buf = []
            while text[j] != '"':
                if text[j] == "\\":
                    j += 1
                buf.append(text[j])
                j += 1
            toks.append(Str("".join(buf)))
            i = j + 1
        elif c == "#" and text[i + 1] == "\\":
            toks.append(Str(text[i + 2]))
            i += 3
        else:
            j = i
            while j < n and text[j] not in " \t\r\n\f()\";":
                j += 1
            toks.append(parse_atom(text[i:j]))
            i = j
    pos = 0

    def rd():
        nonlocal pos
        t = toks[pos]
        pos += 1
        if t == "(":
            lst = []
            while toks[pos] != ")":
                lst.append(rd())
            pos += 1
            return lst
        if t == "'":
            return [S("quote"), rd()]
        if t == "#'":
            return [S("function"), rd()]
        return t

    out = []
    while pos < len(toks):
        out.append(rd())
    return out


def is_sym(x, name=None):
    return isinstance(x, Sym) and (name is None or x.name == name)


def head(x):
    if isinstance(x, list) and x and isinstance(x[0], Sym):
        return x[0].name
    return None


# ---------------------------------------------------------------------------
# Types
#
# 'I' Int, 'D' Double, 'F' Float, 'B' Bool, 'S' String,
# ('A', 'D') / ('A', 'I') arrays, ('FN', Sig) closures.


class Sig:
    def __init__(self, args, slots, raises):
        self.args = args          # list of types
        self.slots = slots        # list of (values-index, type) returned
        self.raises = raises

    def key(self):
        return (tuple(map(str, self.args)), tuple((i, str(t)) for i, t in self.slots), self.raises)

    def mbt(self):
        return "(%s) -> %s%s" % (", ".join(mbt_type(t) for t in self.args),
                                 ret_type([t for _, t in self.slots]),
                                 " raise" if self.raises else "")


USER_FN = Sig(["D"], [(0, "D")], True)


def mbt_type(t):
    if t == "I":
        return "Int"
    if t == "D":
        return "Double"
    if t == "F":
        return "Float"
    if t == "B":
        return "Bool"
    if t == "S":
        return "String"
    if isinstance(t, tuple) and t[0] == "A":
        return "FixedArray[%s]" % ("Double" if t[1] == "D" else "Int")
    if isinstance(t, tuple) and t[0] == "FN":
        return t[1].mbt()
    raise ValueError("type %r" % (t,))


def ret_type(ts):
    if not ts:
        return "Unit"
    if len(ts) == 1:
        return mbt_type(ts[0])
    return "(" + ", ".join(mbt_type(t) for t in ts) + ")"


def parse_type(spec):
    """Parse a type spec from a DECLARE (type <spec> vars...)."""
    s = spec
    if isinstance(s, list) and len(s) >= 1 and head(s) in ("array", "simple-array"):
        el = s[1]
        if is_sym(el, "double-float"):
            return ("A", "D")
        if is_sym(el, "f2cl-lib:integer4"):
            return ("A", "I")
        raise ValueError("array type %r" % (spec,))
    if isinstance(s, list):
        if head(s) == "simple-string" or head(s) == "string":
            return "S"
        s = s[0]
    if is_sym(s, "double-float"):
        return "D"
    if is_sym(s, "single-float"):
        return "F"
    if is_sym(s, "f2cl-lib:integer4"):
        return "I"
    if is_sym(s, "f2cl-lib:logical"):
        return "B"
    if is_sym(s, "simple-string"):
        return "S"
    raise ValueError("type %r" % (spec,))


def literal_type(v):
    if isinstance(v, bool):
        return "B"
    if isinstance(v, int):
        return "I"
    if isinstance(v, Num):
        return "F" if v.kind == "f" else "D"
    raise ValueError(v)


# ---------------------------------------------------------------------------
# Names

KEYWORDS = {
    "as", "else", "extern", "fn", "fnalias", "if", "let", "const", "match",
    "using", "mut", "type", "typealias", "struct", "enum", "trait",
    "traitalias", "derive", "while", "break", "continue", "import", "return",
    "throw", "raise", "try", "catch", "pub", "priv", "readonly", "true",
    "false", "_", "test", "loop", "for", "in", "impl", "with", "guard",
    "async", "is", "suberror", "and", "letrec", "enumview", "noraise",
    "defer", "init", "main", "where", "lexmatch", "module", "move", "ref",
    "static", "super", "unsafe", "use", "virtual", "yield", "object",
    "package", "declare", "recur", "sealed", "nobreak", "private", "protected",
    "override", "include", "self", "Self", "abstract", "do", "final", "macro",
    "method", "open", "trait", "union", "try", "not", "panic", "abort",
    "ignore", "fail", "println", "print", "min", "max", "debug", "inspect",
}


def mb_ident(name):
    s = name.replace("$", "_").replace("-", "_").replace("%", "")
    s = re.sub(r"[^A-Za-z0-9_]", "_", s)
    if s in KEYWORDS:
        s += "_"
    return s


# ---------------------------------------------------------------------------
# Function model


class TransError(Exception):
    pass


class FnDef:
    def __init__(self, name, fname):
        self.name = name
        self.file = fname
        self.params = []        # lisp names
        self.ptypes = {}        # lisp name -> type
        self.statics = []       # list of (lisp name, type, init form)
        self.static_inits = {}  # overrides from SETQ in the LET body
        self.locals = []        # (lisp name, init form)
        self.ltypes = {}
        self.body = []          # prog body items
        self.mad = []           # with-multi-array-data aliases
        self.values = []        # list of Sym or None (return form)
        self.is_function = False
        self.needs_off = {}     # param lisp name -> bool
        self.raises = False
        self.fnsigs = {}        # function param -> Sig
        self.hand = False       # hand-written in MoonBit
        self.result_type = None

    def slots(self):
        """Returned values-slots: list of (index, type)."""
        out = []
        for i, v in enumerate(self.values):
            if v is None:
                continue
            if self.is_function and i == 0:
                out.append((0, self.result_type))
            else:
                p = self.params[i - 1 if self.is_function else i]
                out.append((i, self.ptypes[p]))
        return out

    def param_index(self, i):
        """Map a values-index to a parameter name (None for result)."""
        if self.is_function:
            return None if i == 0 else self.params[i - 1]
        return self.params[i]


def collect_decls(forms, types):
    rest = []
    for f in forms:
        if head(f) == "declare":
            for d in f[1:]:
                if head(d) == "type":
                    t = parse_type(d[1])
                    for v in d[2:]:
                        types[v.name] = t
        else:
            rest.append(f)
    return rest


def parse_defun(form, fname, statics, static_inits):
    name = form[1].name
    fd = FnDef(name, fname)
    fd.params = [p.name for p in form[2]]
    body = collect_decls(form[3:], fd.ptypes)
    for p in fd.params:
        if p not in fd.ptypes:
            fd.ptypes[p] = ("FN", None)   # resolved later
    fd.statics = statics
    fd.static_inits = static_inits
    assert len(body) == 1, name
    b = body[0]
    if head(b) == "f2cl-lib:with-multi-array-data":
        fd.mad = b[1]
        assert len(b) == 3, name
        b = b[2]
    assert head(b) == "prog", (name, head(b))
    for binding in b[1]:
        if isinstance(binding, list):
            fd.locals.append((binding[0].name, binding[1]))
        else:
            fd.locals.append((binding.name, None))
    fd.body = collect_decls(b[2:], fd.ltypes)
    # return form
    rets = []

    def find_ret(x):
        if isinstance(x, list):
            if head(x) == "return":
                rets.append(x)
            for y in x:
                find_ret(y)
    find_ret(fd.body)
    assert len(rets) == 1, name
    vals = rets[0][1]
    assert head(vals) == "values", name
    fd.values = [None if is_sym(v, "nil") else v for v in vals[1:]]
    if len(fd.values) == len(fd.params) + 1:
        fd.is_function = True
        assert fd.values[0].name == name
        fd.result_type = fd.ltypes[name]
    else:
        assert len(fd.values) == len(fd.params), name
    for i, v in enumerate(fd.values):
        if v is not None:
            p = fd.param_index(i)
            assert p is None or v.name == p, (name, i, v)
    return fd


def parse_file(path):
    with open(path) as f:
        text = f.read()
    a = text.index("(in-package :slatec)")
    b = text.index("(in-package #:cl-user)")
    forms = read_forms(text[a:b])[1:]
    fname = os.path.basename(path)[:-5]
    out = []
    for form in forms:
        out.extend(parse_top(form, fname, [], {}))
    return out


def parse_top(form, fname, statics, static_inits):
    h = head(form)
    if h == "defun":
        return [parse_defun(form, fname, statics, static_inits)]
    if h in ("let", "let*"):
        types = {}
        body = collect_decls(form[2:], types)
        st = list(statics)
        for binding in form[1]:
            nm = binding[0].name
            st.append((nm, types.get(nm), binding[1]))
        inits = dict(static_inits)
        out = []
        for b in body:
            if head(b) == "setq":
                for k in range(1, len(b), 2):
                    inits[b[k].name] = b[k + 1]
            else:
                out.extend(parse_top(b, fname, st, inits))
        return out
    raise TransError("top form %r" % (h,))


# ---------------------------------------------------------------------------
# Hand-written routines (slatec/xerror.mbt)


def hand_fn(name, params, values, result_type=None):
    fd = FnDef(name, None)
    fd.hand = True
    fd.params = [p for p, _ in params]
    fd.ptypes = dict(params)
    fd.values = values
    fd.is_function = result_type is not None
    fd.result_type = result_type
    for p, t in params:
        if isinstance(t, tuple) and t[0] == "A":
            fd.needs_off[p] = False
    return fd


HAND = [
    hand_fn("xermsg", [("librar", "S"), ("subrou", "S"), ("messg", "S"),
                       ("nerr", "I"), ("level", "I")], [None] * 5),
    hand_fn("xerprn", [("prefix", "S"), ("npref", "I"), ("messg", "S"),
                       ("nwrap", "I")], [None] * 4),
    hand_fn("xersve", [("librar", "S"), ("subrou", "S"), ("messg", "S"),
                       ("kflag", "I"), ("nerr", "I"), ("level", "I"),
                       ("icount", "I")], [None] * 6 + [S("icount")]),
]


# ---------------------------------------------------------------------------
# Global analyses

def walk(x, fn):
    fn(x)
    if isinstance(x, list):
        for y in x:
            walk(y, fn)


def call_sites(fd):
    """Yield (callee-name, args) for direct calls in fd's body."""
    out = []

    def visit(x):
        if isinstance(x, list) and x and isinstance(x[0], Sym):
            if x[0].name in FNS:
                out.append((x[0].name, x[1:]))
    walk(fd.body, visit)
    return out


def base_array_name(fd, sym):
    """Return the parameter name an array symbol refers to (or None)."""
    nm = sym.name
    if nm.endswith("-%data%"):
        nm = nm[:-len("-%data%")]
    return nm if nm in fd.params else None


def compute_offsets():
    for fd in FNS.values():
        if fd.hand:
            continue
        for p in fd.params:
            t = fd.ptypes[p]
            if isinstance(t, tuple) and t[0] == "A":
                fd.needs_off[p] = False
    changed = True
    while changed:
        changed = False
        for fd in FNS.values():
            if fd.hand:
                continue
            for callee, args in call_sites(fd):
                cd = FNS[callee]
                for i, a in enumerate(args):
                    if i >= len(cd.params):
                        raise TransError("too many args to %s from %s" % (callee, fd.name))
                    p = cd.params[i]
                    t = cd.ptypes[p]
                    if not (isinstance(t, tuple) and t[0] == "A"):
                        continue
                    nz = False
                    if head(a) == "f2cl-lib:array-slice":
                        nz = True
                    elif isinstance(a, Sym):
                        bp = base_array_name(fd, a)
                        if bp is not None and fd.needs_off.get(bp):
                            nz = True
                    if nz and not cd.needs_off[p]:
                        if cd.hand:
                            raise TransError("offset into hand routine %s" % callee)
                        cd.needs_off[p] = True
                        changed = True


def compute_fnsigs():
    # Function-typed parameters: find what callers pass.
    for fd in FNS.values():
        for p in fd.params:
            if fd.ptypes[p] == ("FN", None):
                fd.fnsigs[p] = None
    changed = True
    while changed:
        changed = False
        for fd in FNS.values():
            if fd.hand:
                continue
            for callee, args in call_sites(fd):
                cd = FNS[callee]
                for i, a in enumerate(args):
                    p = cd.params[i]
                    if p not in cd.fnsigs:
                        continue
                    sig = None
                    if head(a) == "function":
                        g = FNS[a[1].name]
                        sig = Sig([g.ptypes[q] for q in g.params], g.slots(), g.raises)
                    elif isinstance(a, Sym) and a.name in fd.fnsigs:
                        sig = fd.fnsigs[a.name]
                    else:
                        raise TransError("bad function arg %r" % (a,))
                    if sig is None:
                        continue
                    old = cd.fnsigs[p]
                    if old is None:
                        cd.fnsigs[p] = sig
                        changed = True
                    elif old.key() != sig.key():
                        if old.args == sig.args:
                            if sig.raises and not old.raises:
                                old.raises = True
                                changed = True
                            merged = dict(old.slots)
                            for k, t in sig.slots:
                                merged[k] = t
                            if len(merged) != len(old.slots):
                                old.slots = sorted(merged.items())
                                changed = True
                        else:
                            raise TransError("conflicting fn sigs for %s.%s" % (callee, p))
        # raising
        for fd in FNS.values():
            if fd.hand or fd.raises:
                continue
            r = False
            for p, sig in fd.fnsigs.items():
                if (sig is None or sig.raises) and uses_funcall(fd, p):
                    r = True
            for callee, _ in call_sites(fd):
                if FNS[callee].raises:
                    r = True
            if r:
                fd.raises = True
                changed = True
    for fd in FNS.values():
        for p in list(fd.fnsigs):
            if fd.fnsigs[p] is None:
                fd.fnsigs[p] = USER_FN
            fd.ptypes[p] = ("FN", fd.fnsigs[p])


def uses_funcall(fd, p):
    found = []

    def visit(x):
        if head(x) == "funcall" and is_sym(x[1], p):
            found.append(x)
    walk(fd.body, visit)
    return bool(found)


# ---------------------------------------------------------------------------
# Code generation helpers

def fmt_double(v):
    if v != v or v in (float("inf"), float("-inf")):
        raise TransError("non-finite literal")
    s = repr(float(v))
    if "e" in s:
        mant, ex = s.split("e")
        if "." not in mant:
            mant += ".0"
        s = mant + "e" + ex
    elif "." not in s:
        s += ".0"
    return s


def paren(code):
    return "(" + code + ")"


def is_simple(code):
    return re.match(r"^[A-Za-z_][A-Za-z0-9_.]*(\[[^\[\]]*\])?$", code) is not None or re.match(r"^\d+(\.\d+)?$", code) is not None


def fully_parenthesized(code):
    if not (code.startswith("(") and code.endswith(")")):
        return False
    depth = 0
    for k, ch in enumerate(code):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
            if depth == 0 and k != len(code) - 1:
                return False
    return True


def wrap(code):
    return code if is_simple(code) or fully_parenthesized(code) else paren(code)


def conv(code, frm, to):
    if frm == to:
        return code
    if to == "D":
        if frm == "I":
            if re.match(r"^-?\d+$", code.strip("()")):
                return fmt_double(float(int(code.strip("()"))))
            return wrap(code) + ".to_double()"
        if frm == "F":
            return wrap(code) + ".to_double()"
    if to == "F":
        if frm == "I":
            return "Float::from_int(" + code + ")"
        if frm == "D":
            return "Float::from_double(" + code + ")"
    raise TransError("cannot convert %s -> %s (%s)" % (frm, to, code))


def contagion(a, b):
    if a == "D" or b == "D":
        return "D"
    if a == "F" or b == "F":
        return "F"
    if a == "I" and b == "I":
        return "I"
    raise TransError("contagion %s %s" % (a, b))


class Var:
    """Environment entry."""

    def __init__(self, kind, code, typ, off=None, assignable=True):
        self.kind = kind      # 'local', 'static', 'const', 'array', 'fn', 'off', 'nil', 'mv'
        self.code = code
        self.typ = typ
        self.off = off        # for arrays: offset code or None
        self.assignable = assignable


class Ctx:
    def __init__(self, fd):
        self.fd = fd
        self.env = {}
        self.lines = []
        self.ind = 1
        self.counter = 0
        self.tag_stack = []   # list of dicts: tag -> action

    def emit(self, s):
        self.lines.append("  " * self.ind + s)

    def fresh(self, base):
        self.counter += 1
        return "%s%d" % (base, self.counter)


# ---------------------------------------------------------------------------
# Expressions

ARITH = {"+": "+", "-": "-", "*": "*", "/": "/",
         "f2cl-lib:int-add": "+", "f2cl-lib:int-sub": "-", "f2cl-lib:int-mul": "*"}
CMP = {"<": "<", ">": ">", "<=": "<=", ">=": ">=", "=": "==", "/=": "!="}
MATH1 = {
    "exp": "f_exp", "sin": "f_sin", "cos": "f_cos", "tan": "f_tan",
    "f2cl-lib:flog": "f_log", "f2cl-lib:dlog": "f_log", "log": "f_log",
    "f2cl-lib:fsqrt": "f_sqrt", "sqrt": "f_sqrt", "f2cl-lib:datan": "f_atan",
    "cosh": "f_cosh", "sinh": "f_sinh", "tanh": "f_tanh",
}


def lookup(ctx, sym):
    v = ctx.env.get(sym.name)
    if v is None:
        raise TransError("unknown variable %s in %s" % (sym.name, ctx.fd.name))
    return v


def var_read(v):
    if v.kind == "static":
        return v.code + ".val"
    return v.code


def expr(ctx, x):
    """Translate expression -> (code, type)."""
    if isinstance(x, bool):
        return ("true" if x else "false", "B")
    if isinstance(x, int):
        return (str(x) if x >= 0 else "(%d)" % x, "I")
    if isinstance(x, Num):
        if x.kind == "f":
            return ("Float::from_double(%s)" % fmt_double(x.value), "F")
        c = fmt_double(x.value)
        return (c if x.value >= 0 and not c.startswith("-") else paren(c), "D")
    if isinstance(x, Str):
        return ('"%s"' % x.text.replace("\\", "\\\\").replace('"', '\\"'), "S")
    if isinstance(x, Sym):
        if x.name == "f2cl-lib:%true%" or x.name == "t":
            return ("true", "B")
        if x.name == "f2cl-lib:%false%" or x.name == "nil":
            return ("false", "B")
        v = lookup(ctx, x)
        if v.kind == "nil":
            raise TransError("use of NIL slot %s" % x.name)
        if v.kind == "array":
            raise TransError("array %s used as scalar" % x.name)
        return (var_read(v), v.typ)
    h = head(x)
    if h is None:
        raise TransError("bad expr %r" % (x,))
    args = x[1:]
    if h in ARITH:
        return arith(ctx, ARITH[h], args, int_only=h.startswith("f2cl-lib:"))
    if h in CMP:
        return compare(ctx, CMP[h], args)
    if h == "and" or h == "or":
        parts = [cond_code(ctx, a) for a in args]
        return (paren((" && " if h == "and" else " || ").join(parts)), "B")
    if h == "not":
        return ("!" + wrap(cond_code(ctx, args[0])), "B")
    if h == "the":
        return expr(ctx, args[1])
    if h == "coerce":
        c, t = expr(ctx, args[0])
        target = args[1][1]
        if is_sym(target, "double-float"):
            return (conv(c, t, "D"), "D")
        if is_sym(target, "f2cl-lib:integer4"):
            if t != "I":
                raise TransError("coerce to integer from %s" % t)
            return (c, "I")
        if is_sym(target, "single-float"):
            return (conv(c, t, "F"), "F")
        raise TransError("coerce %r" % (target,))
    if h == "realpart":
        return expr(ctx, args[0])
    if h in ("f2cl-lib:freal", "f2cl-lib:sngl"):
        c, t = expr(ctx, args[0])
        return (conv(c, t, "F"), "F")
    if h in ("f2cl-lib:dble", "f2cl-lib:dfloat"):
        c, t = expr(ctx, args[0])
        return (conv(c, t, "D"), "D")
    if h == "f2cl-lib:fref":
        return array_ref(ctx, x)
    if h in ("abs", "f2cl-lib:dabs", "f2cl-lib:iabs"):
        c, t = expr(ctx, args[0])
        if t == "I":
            return ("i_abs(%s)" % c, "I")
        if t == "D":
            return ("d_abs(%s)" % c, "D")
        if t == "F":
            return ("%s.abs()" % wrap(c), "F")
    if h in MATH1:
        c, t = expr(ctx, args[0])
        fn = MATH1[h]
        if t == "F":
            return ("Float::from_double(%s(%s))" % (fn, c + ".to_double()" if is_simple(c) else paren(c) + ".to_double()"), "F")
        return ("%s(%s)" % (fn, conv(c, t, "D")), "D")
    if h == "atan":
        if len(args) == 1:
            c, t = expr(ctx, args[0])
            return ("f_atan(%s)" % conv(c, t, "D"), "D")
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        return ("f_atan2(%s, %s)" % (conv(c1, t1, "D"), conv(c2, t2, "D")), "D")
    if h == "expt":
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 == "F" and t2 == "F":
            return ("Float::from_double(f_pow(%s, %s))" % (conv(c1, t1, "D"), conv(c2, t2, "D")), "F")
        if t1 == "I" and t2 == "I":
            raise TransError("integer expt")
        if t1 not in ("D", "F") or t2 not in ("D", "F", "I"):
            raise TransError("expt %s %s" % (t1, t2))
        return ("f_pow(%s, %s)" % (conv(c1, t1, "D"), conv(c2, t2, "D")), "D")
    if h in ("max", "min"):
        return minmax(ctx, h, args)
    if h == "mod":
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 != "I" or t2 != "I":
            raise TransError("float mod")
        return ("i_mod(%s, %s)" % (c1, c2), "I")
    if h == "truncate":
        if len(args) != 2:
            raise TransError("truncate/1")
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 != "I" or t2 != "I":
            raise TransError("float truncate")
        return (paren("%s / %s" % (wrap(c1), wrap(c2))), "I")
    if h == "f2cl-lib:int":
        c, t = expr(ctx, args[0])
        if t == "I":
            return (c, "I")
        if t == "F":
            c = wrap(c) + ".to_double()"
        return ("f_int(%s)" % c, "I")
    if h in ("f2cl-lib:aint", "f2cl-lib:dint"):
        c, t = expr(ctx, args[0])
        if t != "D":
            raise TransError("aint on %s" % t)
        return ("f_aint(%s)" % c, "D")
    if h in ("f2cl-lib:sign", "f2cl-lib:dsign", "f2cl-lib:isign"):
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 == "I":
            if t2 != "I":
                raise TransError("isign")
            return ("i_sign(%s, %s)" % (c1, c2), "I")
        if t1 == "D":
            return ("d_sign(%s, %s)" % (c1, conv(c2, t2, "D")), "D")
        raise TransError("sign on %s" % t1)
    if h == "f2cl-lib:d1mach":
        return ("d1mach(%s)" % expr(ctx, args[0])[0], "D")
    if h == "f2cl-lib:i1mach":
        if args[0] == 9:
            return ("i1mach9_as_double()", "D")
        return ("i1mach(%s)" % expr(ctx, args[0])[0], "I")
    if h == "if":
        c = cond_code(ctx, args[0])
        a, ta = expr(ctx, args[1])
        b, tb = expr(ctx, args[2])
        t = contagion(ta, tb) if ta != tb else ta
        return ("(if %s { %s } else { %s })" % (c, conv(a, ta, t), conv(b, tb, t)), t)
    if h == "multiple-value-bind":
        return mvb_expr(ctx, x)
    if h == "funcall":
        return call_expr(ctx, args[0], args[1:], funcall=True)
    if h in FNS:
        return call_expr(ctx, x[0], args)
    raise TransError("unknown expr head %s in %s" % (h, ctx.fd.name))


def cond_code(ctx, x):
    c, t = expr(ctx, x)
    if t != "B":
        raise TransError("non-boolean condition %r" % (x,))
    return c


def arith(ctx, op, args, int_only=False):
    if len(args) == 1:
        c, t = expr(ctx, args[0])
        if op == "-":
            return ("-" + wrap(c), t)
        if op == "/":
            if t == "I":
                raise TransError("integer reciprocal")
            one = "1.0" if t == "D" else "Float::from_double(1.0)"
            return (paren("%s / %s" % (one, wrap(c))), t)
        return (c, t)
    c, t = expr(ctx, args[0])
    for a in args[1:]:
        c2, t2 = expr(ctx, a)
        rt = contagion(t, t2)
        if op == "/" and rt == "I":
            raise TransError("integer division with / in %s" % ctx.fd.name)
        if rt == "I" and op in "+-*" and re.match(r"^\(?-?\d+\)?$", c) and re.match(r"^\(?-?\d+\)?$", c2):
            a1, a2 = int(c.strip("()")), int(c2.strip("()"))
            v = a1 + a2 if op == "+" else a1 - a2 if op == "-" else a1 * a2
            c = str(v) if v >= 0 else "(%d)" % v
        elif rt == "I" and op in "+-" and re.match(r"^\(?0\)?$", c2):
            pass
        else:
            c = paren("%s %s %s" % (wrap(conv(c, t, rt)), op, wrap(conv(c2, t2, rt))))
        t = rt
    if int_only and t != "I":
        raise TransError("int-op on %s" % t)
    return (c, t)


def compare(ctx, op, args):
    parts = []
    for k in range(len(args) - 1):
        c1, t1 = expr(ctx, args[k])
        c2, t2 = expr(ctx, args[k + 1])
        if t1 == "B" or t2 == "B":
            raise TransError("compare booleans")
        rt = contagion(t1, t2)
        parts.append("%s %s %s" % (wrap(conv(c1, t1, rt)), op, wrap(conv(c2, t2, rt))))
    return (paren(" && ".join(parts)), "B")


def minmax(ctx, h, args):
    cs = [expr(ctx, a) for a in args]
    t = cs[0][1]
    for _, t2 in cs[1:]:
        t = contagion(t, t2)
    pre = {"I": "i_", "D": "d_", "F": "s_"}[t]
    c = conv(cs[0][0], cs[0][1], t)
    for c2, t2 in cs[1:]:
        c = "%s%s(%s, %s)" % (pre, h, c, conv(c2, t2, t))
    return (c, t)


def colmajor(ctx, indices, bounds):
    """Return offset code (Int) of indices within bounds (0-based)."""
    terms = None
    # n1 + d1*(n2 + d2*(n3 ...)) built from the last index
    rev_i = list(reversed(indices))
    rev_b = list(reversed(bounds))

    def offset_of(n, b):
        lo = b[0]
        c, t = expr(ctx, n)
        if t != "I":
            raise TransError("non-int index")
        if isinstance(lo, int) and lo == 0:
            return c
        lc, lt = expr(ctx, lo)
        return paren("%s - %s" % (wrap(c), wrap(lc)))

    def size_of(b):
        lo, hi = b
        if isinstance(lo, int) and isinstance(hi, int):
            return str(hi - lo + 1)
        if isinstance(lo, int) and lo == 1:
            return expr(ctx, hi)[0]
        hc = expr(ctx, hi)[0]
        lc = expr(ctx, lo)[0]
        return paren("%s - %s + 1" % (wrap(hc), wrap(lc)))

    idx = offset_of(rev_i[0], rev_b[0])
    for n, b in zip(rev_i[1:], rev_b[1:]):
        idx = paren("%s + %s * %s" % (wrap(offset_of(n, b)), wrap(size_of(b)), wrap(idx)))
    return idx


def simplify_index(code):
    # turn "(i - 1)" forms into something a bit cleaner; keep semantics
    return code


def array_base(ctx, sym):
    v = lookup(ctx, sym)
    if v.kind != "array":
        raise TransError("%s is not an array" % sym.name)
    return v


def add_off(a, b):
    if a in (None, "0"):
        return b
    if b in (None, "0"):
        return a
    return "%s + %s" % (a, b)


def array_ref(ctx, x):
    # (fref arr (indices) (bounds) [offset])
    v = array_base(ctx, x[1])
    idx = colmajor(ctx, x[2], x[3])
    off = v.off
    if len(x) > 4:
        oc = expr(ctx, x[4])[0]
        # with-multi-array-data offset alias already is the array's offset
        if oc != (v.off or "0"):
            off = add_off(off, oc)
    full = add_off(off, idx)
    return ("%s[%s]" % (v.code, strip_paren(full)), v.typ[1])


def strip_paren(c):
    if c.startswith("(") and c.endswith(")"):
        depth = 0
        for k, ch in enumerate(c):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and k != len(c) - 1:
                    return c
        return c[1:-1]
    return c


def array_arg(ctx, a):
    """Return (base code, offset code) for an array argument."""
    if isinstance(a, Sym):
        v = array_base(ctx, a)
        return v.code, (v.off or "0"), v.typ
    if head(a) == "f2cl-lib:array-slice":
        v = array_base(ctx, a[1])
        idx = colmajor(ctx, a[3], a[4])
        off = v.off
        if len(a) > 5:
            oc = expr(ctx, a[5])[0]
            if oc != (v.off or "0"):
                off = add_off(off, oc)
        return v.code, strip_paren(add_off(off, idx)), v.typ
    raise TransError("bad array arg %r in %s" % (a, ctx.fd.name))


def callee_info(ctx, fsym, funcall):
    if funcall:
        v = lookup(ctx, fsym)
        if v.kind != "fn":
            raise TransError("funcall of non-fn %s" % fsym.name)
        sig = v.typ[1]
        return v.code, sig.args, [None] * len(sig.args), sig.slots, None
    cd = FNS[fsym.name]
    return mb_fn_name(cd.name), [cd.ptypes[p] for p in cd.params], cd.params, cd.slots(), cd


def call_code(ctx, fsym, args, funcall=False):
    name, ptypes, pnames, slots, cd = callee_info(ctx, fsym, funcall)
    if len(args) != len(ptypes):
        raise TransError("arg count mismatch calling %s from %s" % (fsym.name, ctx.fd.name))
    out = []
    for i, (a, pt) in enumerate(zip(args, ptypes)):
        if isinstance(pt, tuple) and pt[0] == "A":
            base, off, at = array_arg(ctx, a)
            if at != pt:
                raise TransError("array type mismatch")
            out.append(base)
            if cd is not None and cd.needs_off.get(pnames[i]):
                out.append(off)
            elif off != "0":
                raise TransError("offset passed to %s.%s without offset param" % (name, pnames[i]))
        elif isinstance(pt, tuple) and pt[0] == "FN":
            if head(a) == "function":
                out.append(fn_value(a[1].name, pt[1]))
            else:
                v = lookup(ctx, a)
                out.append(v.code)
        else:
            c, t = expr(ctx, a)
            out.append(conv(c, t, pt))
    return "%s(%s)" % (name, ", ".join(out)), slots


def fn_value(name, sig):
    """A function passed as an argument; adapt its returned slots to SIG."""
    g = FNS[name]
    gs = g.slots()
    if [k for k, _ in gs] == [k for k, _ in sig.slots]:
        return mb_fn_name(name)
    # The closure type returns more slots than G does: a slot G leaves NIL
    # is returned unchanged (the caller only stores it back where it came
    # from, which is what the Lisp's (when var-k ...) skip amounts to).
    ps = ["a%d" % k for k in range(len(g.params))]
    have = dict(gs)
    tmp = ["r%d" % k for k, _ in gs]
    res = []
    for k, _ in sig.slots:
        if k in have:
            res.append("r%d" % k)
        else:
            pi = k - 1 if g.is_function else k
            res.append(ps[pi])
    call = "%s(%s)" % (mb_fn_name(name), ", ".join(ps))
    if len(tmp) == 0:
        body = "%s; " % call
    elif len(tmp) == 1:
        body = "let %s = %s; " % (tmp[0], call)
    else:
        body = "let (%s) = %s; " % (", ".join(tmp), call)
    ret = res[0] if len(res) == 1 else "(" + ", ".join(res) + ")"
    params = ", ".join("%s : %s" % (pn, mbt_type(t)) for pn, t in zip(ps, sig.args))
    return "fn(%s) { %s%s }" % (params, body, ret)


def call_expr(ctx, fsym, args, funcall=False):
    code, slots = call_code(ctx, fsym, args, funcall)
    if not slots or slots[0][0] != 0:
        raise TransError("value of subroutine %s used" % fsym.name)
    if len(slots) == 1:
        return (code, slots[0][1])
    return (code + ".0", slots[0][1])


def mb_fn_name(name):
    return mb_ident(name)


def mvb_expr(ctx, x):
    # (multiple-value-bind (ret-val var-0 ...) (funcall f ...) (declare) (when ...)... ret-val)
    vars_ = x[1]
    call = x[2]
    body = [b for b in x[3:] if head(b) != "declare"]
    if head(call) == "funcall":
        code, slots = call_code(ctx, call[1], call[2:], funcall=True)
    else:
        code, slots = call_code(ctx, call[0], call[1:])
    returned = {i for i, _ in slots}
    if 0 not in returned:
        raise TransError("mvb expression without value")
    if returned != {0}:
        return mvb_block_expr(ctx, x, vars_, body, code, slots)
    last = body[-1]
    if not (is_sym(last) and last.name == vars_[0].name):
        raise TransError("mvb expression shape")
    for b in body[:-1]:
        if head(b) == "when" and is_sym(b[1]):
            k = [v.name for v in vars_].index(b[1].name)
            if k in returned:
                raise TransError("mvb when on returned slot")
            continue
        raise TransError("mvb expression body %r" % (b,))
    return (code, slots[0][1])


def mvb_block_expr(ctx, x, vars_, body, code, slots):
    """An MVB used for its value whose call also updates arguments: emit a
    block expression so the updates happen in Lisp evaluation order."""
    last = body[-1]
    if not (is_sym(last) and last.name == vars_[0].name):
        raise TransError("mvb expression shape")
    saved_lines, saved_ind = ctx.lines, ctx.ind
    ctx.lines, ctx.ind = [], 0
    names = mvb_bind(ctx, [v.name for v in vars_], body[:-1], code, slots, force_first=True)
    val = ctx.env[vars_[0].name].code
    mvb_body(ctx, [v.name for v in vars_], body[:-1])
    mvb_unbind(ctx, names)
    inner = "; ".join(l.strip() for l in ctx.lines)
    ctx.lines, ctx.ind = saved_lines, saved_ind
    return ("{ %s; %s }" % (inner, val), slots[0][1])


# ---------------------------------------------------------------------------
# Statements


def assign(ctx, target, value_code, value_type):
    if isinstance(target, Sym):
        v = lookup(ctx, target)
        if v.kind not in ("local", "static"):
            raise TransError("assignment to %s (%s)" % (target.name, v.kind))
        if value_type == "D" and v.typ == "I":
            raise TransError("implicit double->int assignment to %s" % target.name)
        c = conv(value_code, value_type, v.typ)
        ctx.emit("%s = %s" % (var_read(v), strip_paren(c)))
        return
    if head(target) == "f2cl-lib:fref":
        ref, et = array_ref(ctx, target)
        if value_type == "D" and et == "I":
            raise TransError("implicit double->int array store")
        ctx.emit("%s = %s" % (ref, strip_paren(conv(value_code, value_type, et))))
        return
    raise TransError("bad assignment target %r" % (target,))


def stmt(ctx, x):
    h = head(x)
    if h is None:
        raise TransError("bad statement %r" % (x,))
    args = x[1:]
    if h in ("setf", "setq"):
        for k in range(0, len(args), 2):
            c, t = expr(ctx, args[k + 1])
            assign(ctx, args[k], c, t)
        return
    if h == "f2cl-lib:fset":
        c, t = expr(ctx, args[1])
        assign(ctx, args[0], c, t)
        return
    if h == "declare":
        return
    if h == "go":
        go(ctx, args[0].name)
        return
    if h == "return":
        do_return(ctx, args[0])
        return
    if h == "if":
        c = cond_code(ctx, args[0])
        ctx.emit("if %s {" % strip_paren(c))
        block(ctx, [args[1]])
        if len(args) > 2:
            ctx.emit("} else {")
            block(ctx, [args[2]])
        ctx.emit("}")
        return
    if h in ("when", "unless"):
        c = cond_code(ctx, args[0])
        if h == "unless":
            c = "!" + wrap(c)
        ctx.emit("if %s {" % strip_paren(c))
        block(ctx, args[1:])
        ctx.emit("}")
        return
    if h == "cond":
        first = True
        for clause in args:
            test = clause[0]
            if is_sym(test, "t"):
                if first:
                    ctx.emit("{")
                else:
                    ctx.emit("} else {")
            else:
                c = cond_code(ctx, test)
                ctx.emit(("if %s {" if first else "} else if %s {") % strip_paren(c))
            block(ctx, clause[1:])
            first = False
        ctx.emit("}")
        return
    if h == "progn":
        for s in args:
            stmt(ctx, s)
        return
    if h == "tagbody":
        tagbody(ctx, args)
        return
    if h == "f2cl-lib:fdo":
        fdo(ctx, x)
        return
    if h == "f2cl-lib:arithmetic-if":
        c, t = expr(ctx, args[0])
        tmp = ctx.fresh("aif")
        ctx.emit("let %s = %s" % (tmp, strip_paren(c)))
        zero = {"I": "0", "D": "0.0", "F": "Float::from_double(0.0)"}[t]
        ctx.emit("if %s < %s {" % (tmp, zero))
        block(ctx, [args[1]])
        ctx.emit("} else if %s == %s {" % (tmp, zero))
        block(ctx, [args[2]])
        ctx.emit("} else {")
        block(ctx, [args[3]])
        ctx.emit("}")
        return
    if h == "f2cl-lib:computed-goto":
        c, t = expr(ctx, args[1])
        ctx.emit("match %s {" % strip_paren(c))
        for k, tag in enumerate(args[0]):
            ctx.emit("  %d => {" % (k + 1))
            ctx.ind += 2
            go(ctx, tag.name)
            ctx.ind -= 2
            ctx.emit("  }")
        ctx.emit("  _ => ()")
        ctx.emit("}")
        return
    if h == "multiple-value-bind":
        mvb_stmt(ctx, x)
        return
    if h == "f2cl-lib::stop" or h == "f2cl-lib:stop":
        return
    if h == "funcall":
        code, slots = call_code(ctx, args[0], args[1:], funcall=True)
        ctx.emit(code if not slots else "let _ = " + code)
        return
    if h in FNS:
        code, slots = call_code(ctx, x[0], args)
        ctx.emit(code if not slots else "let _ = " + code)
        return
    raise TransError("unknown statement %s in %s" % (h, ctx.fd.name))


def block(ctx, forms):
    ctx.ind += 1
    for f in forms:
        stmt(ctx, f)
    ctx.ind -= 1


def mvb_stmt(ctx, x):
    vars_ = [v.name for v in x[1]]
    call = x[2]
    body = [b for b in x[3:] if head(b) != "declare"]
    if head(call) == "funcall":
        code, slots = call_code(ctx, call[1], call[2:], funcall=True)
    else:
        code, slots = call_code(ctx, call[0], call[1:])
    saved = mvb_bind(ctx, vars_, body, code, slots)
    mvb_body(ctx, vars_, body)
    mvb_unbind(ctx, saved)


def mvb_bind(ctx, vars_, body, code, slots, force_first=False):
    returned = dict(slots)
    names = []
    saved = {}
    for i, vn in enumerate(vars_):
        saved[vn] = ctx.env.get(vn)
        if i in returned:
            used = mentions(body, vn) or (force_first and i == 0)
            nm = ctx.fresh("mv") if used else "_"
            names.append(nm)
            ctx.env[vn] = Var("mv", nm, returned[i], assignable=False)
        else:
            ctx.env[vn] = Var("nil", None, None)
    # slots beyond the bound vars
    for i, _ in slots:
        if i >= len(vars_):
            names.append("_")
    if not names:
        ctx.emit(code)
    elif len(names) == 1:
        ctx.emit("let %s = %s" % (names[0], code))
    else:
        ctx.emit("let (%s) = %s" % (", ".join(names), code))
    return saved


def mvb_unbind(ctx, saved):
    for vn, old in saved.items():
        if old is None:
            del ctx.env[vn]
        else:
            ctx.env[vn] = old


def mvb_body(ctx, vars_, body):
    for b in body:
        if head(b) == "when" and is_sym(b[1]) and b[1].name in vars_:
            v = ctx.env[b[1].name]
            if v.kind == "nil":
                continue
            for s in b[2:]:
                stmt(ctx, s)
            continue
        stmt(ctx, b)


def mentions(forms, name):
    found = []

    def visit(y):
        if is_sym(y, name):
            found.append(1)
    walk(forms, visit)
    return bool(found)


def do_return(ctx, vals):
    fd = ctx.fd
    codes = []
    for i, v in enumerate(vals[1:]):
        if is_sym(v, "nil"):
            continue
        var = lookup(ctx, v)
        codes.append(var_read(var))
    if not codes:
        ctx.emit("return")
    elif len(codes) == 1:
        ctx.emit("return " + codes[0])
    else:
        ctx.emit("return (%s)" % ", ".join(codes))


def go(ctx, tag):
    for frame in reversed(ctx.tag_stack):
        if tag in frame["tags"]:
            act = frame["tags"][tag]
            if act[0] == "pc":
                ctx.emit("%s = %d" % (frame["pc"], act[1]))
                ctx.emit("continue %s~" % frame["label"])
            elif act[0] == "exit":
                ctx.emit("break %s~" % frame["label"])
            elif act[0] == "ret":
                do_return(ctx, act[1][1])
            return
    raise TransError("go to unknown tag %s in %s" % (tag, ctx.fd.name))


def collect_gos(forms):
    out = set()

    def visit(y):
        if head(y) == "go":
            out.add(y[1].name)
        elif head(y) == "f2cl-lib:computed-goto":
            for t in y[1]:
                out.add(t.name)
    walk(forms, visit)
    return out


def tagbody(ctx, items):
    """Translate a TAGBODY (or PROG body) item list."""
    tags = [it.name for it in items if isinstance(it, Sym)]
    targeted = collect_gos(items) & set(tags)
    if not targeted:
        for it in items:
            if not isinstance(it, Sym):
                stmt(ctx, it)
        return
    # split into segments at targeted tags
    segs = [[None, []]]
    for it in items:
        if isinstance(it, Sym):
            if it.name in targeted:
                segs.append([it.name, []])
        else:
            segs[-1][1].append(it)
    label = ctx.fresh("tb")
    frame = {"label": label, "tags": {}, "pc": None}
    # Simple form: all targeted tags are at the very end with no code after.
    trailing = []
    k = len(segs) - 1
    while k > 0 and not segs[k][1]:
        trailing.append(segs[k][0])
        k -= 1
    if k == 0:
        for t in trailing:
            frame["tags"][t] = ("exit",)
        ctx.tag_stack.append(frame)
        ctx.emit("%s~: while true {" % label)
        block(ctx, segs[0][1])
        ctx.emit("  break %s~" % label)
        ctx.emit("}")
        ctx.tag_stack.pop()
        return
    # trailing empty segments (with no code) exit the machine
    nseg = k + 1
    for t in trailing:
        frame["tags"][t] = ("exit",)
    for i in range(1, nseg):
        seg = segs[i][1]
        if len(seg) == 1 and head(seg[0]) == "return":
            frame["tags"][segs[i][0]] = ("ret", seg[0])
        else:
            frame["tags"][segs[i][0]] = ("pc", i)
    if not trailing and all(a[0] == "ret" for a in frame["tags"].values()):
        # Every GO is a RETURN: the segments simply run in order.
        ctx.tag_stack.append(frame)
        for i in range(nseg):
            for st in segs[i][1]:
                stmt(ctx, st)
            if ends_with_jump(segs[i][1]):
                break
        ctx.tag_stack.pop()
        return
    pc = ctx.fresh("pc")
    frame["pc"] = pc
    ctx.tag_stack.append(frame)
    ctx.emit("let mut %s = 0" % pc)
    ctx.emit("%s~: while true {" % label)
    ctx.emit("  match %s {" % pc)
    for i in range(nseg):
        ctx.emit("    %d => {" % i)
        ctx.ind += 3
        for s in segs[i][1]:
            stmt(ctx, s)
        if i + 1 < nseg:
            if not ends_with_jump(segs[i][1]):
                ctx.emit("%s = %d" % (pc, i + 1))
                ctx.emit("continue %s~" % label)
        else:
            if not ends_with_jump(segs[i][1]):
                ctx.emit("break %s~" % label)
        ctx.ind -= 3
        ctx.emit("    }")
    ctx.emit("    _ => panic()")
    ctx.emit("  }")
    ctx.emit("}")
    ctx.tag_stack.pop()


def ends_with_jump(seg):
    if not seg:
        return False
    last = seg[-1]
    return head(last) in ("go", "return")


def fdo(ctx, x):
    clause = x[1]
    pred = x[2]
    body = x[3:]
    var = clause[0]
    start = clause[1]
    incr = clause[2]
    step = incr[2] if head(incr) == "f2cl-lib:int-add" else None
    if step is None or not is_sym(incr[1], var.name):
        raise TransError("fdo increment %r" % (incr,))
    test = pred[0]
    if not (head(test) == ">" and is_sym(test[1], var.name)):
        raise TransError("fdo predicate %r" % (pred,))
    end = test[2]
    v = lookup(ctx, var)
    sc, st = expr(ctx, step)
    ec, et = expr(ctx, end)
    bc, bt = expr(ctx, start)
    if st != "I" or et != "I" or bt != "I":
        raise TransError("non-integer fdo")
    cnt = ctx.fresh("cnt")
    if re.match(r"^\(?-?\d+\)?$", sc):
        stepc = sc
    else:
        stepc = ctx.fresh("step")
        ctx.emit("let %s = %s" % (stepc, strip_paren(sc)))
    ctx.emit("let mut %s = i_max(0, (%s - %s + %s) / %s)" % (cnt, wrap(ec), wrap(bc), stepc, stepc))
    ctx.emit("%s = %s" % (var_read(v), strip_paren(bc)))
    ctx.emit("while %s > 0 {" % cnt)
    block(ctx, body)
    ic, it = expr(ctx, incr)
    ctx.ind += 1
    ctx.emit("%s = %s" % (var_read(v), strip_paren(ic)))
    ctx.emit("%s = %s - 1" % (cnt, cnt))
    ctx.ind -= 1
    ctx.emit("}")


# ---------------------------------------------------------------------------
# Function emission


def assigned_vars(forms):
    out = set()

    def visit(y):
        h = head(y)
        if h in ("setf", "setq"):
            for k in range(1, len(y), 2):
                if isinstance(y[k], Sym):
                    out.add(y[k].name)
        elif h == "f2cl-lib:fdo":
            out.add(y[1][0].name)
    walk(forms, visit)
    return out


def static_name(fd, nm):
    return mb_ident(fd.file + "_" + nm)


def init_value(form, typ):
    """Code for a static/local initial value."""
    if head(form) == "make-array":
        n = form[1]
        if isinstance(n, list):
            n = n[0] if not head(n) else None
        kw = {form[k].name: form[k + 1] for k in range(2, len(form), 2)}
        et = kw.get(":element-type")
        et = et[1] if head(et) == "quote" else et
        if is_sym(et, "double-float"):
            elem = "D"
        elif is_sym(et, "f2cl-lib:integer4"):
            elem = "I"
        else:
            raise TransError("array element type %r" % (et,))
        if ":initial-contents" in kw:
            vals = kw[":initial-contents"][1]
            if len(vals) != n:
                raise TransError("initial-contents length")
            if elem == "D":
                items = [fmt_double(v.value if isinstance(v, Num) else float(v)) for v in vals]
            else:
                items = [str(v) for v in vals]
            return ("A", elem), "[%s]" % ", ".join(items)
        if not isinstance(n, int):
            return ("A", elem), None  # dynamic size
        return ("A", elem), "FixedArray::make(%d, %s)" % (n, "0.0" if elem == "D" else "0")
    if isinstance(form, bool) or is_sym(form, "nil") or is_sym(form, "f2cl-lib:%false%"):
        return "B", "false"
    if is_sym(form, "f2cl-lib:%true%") or is_sym(form, "t"):
        return "B", "true"
    if isinstance(form, int):
        return "I", str(form)
    if isinstance(form, Num):
        if form.kind == "f":
            return "F", "Float::from_double(%s)" % fmt_double(form.value)
        return "D", fmt_double(form.value)
    raise TransError("init %r" % (form,))


def literal_conv(code, frm, to):
    if frm == to:
        return code
    if frm == "I" and to == "D":
        return fmt_double(float(int(code)))
    if frm == "D" and to == "F":
        return "Float::from_double(%s)" % code
    if frm == "I" and to == "F":
        return "Float::from_double(%s)" % fmt_double(float(int(code)))
    if frm == "F" and to == "D":
        return code + ".to_double()"
    raise TransError("literal conv %s->%s" % (frm, to))


def emit_statics(fd, out):
    assigned = assigned_vars(fd.body)
    for nm, typ, init in fd.statics:
        form = fd.static_inits.get(nm, init)
        t0, code = init_value(form, typ)
        t = typ or t0
        mb = static_name(fd, nm)
        if isinstance(t, tuple):
            if code is None:
                raise TransError("dynamic static array")
            out.append("///|")
            out.append("let %s : %s = %s" % (mb, mbt_type(t), code))
            out.append("")
            continue
        code = literal_conv(code, t0, t)
        out.append("///|")
        if nm in assigned:
            out.append("let %s : Ref[%s] = { val: %s }" % (mb, mbt_type(t), code))
        else:
            out.append("let %s : %s = %s" % (mb, mbt_type(t), code))
        out.append("")


def gen_function(fd):
    ctx = Ctx(fd)
    assigned = assigned_vars(fd.body)
    # statics
    for nm, typ, init in fd.statics:
        form = fd.static_inits.get(nm, init)
        t0, _ = init_value(form, typ)
        t = typ or t0
        mb = static_name(fd, nm)
        if isinstance(t, tuple):
            ctx.env[nm] = Var("array", mb, t)
        elif nm in assigned:
            ctx.env[nm] = Var("static", mb, t)
        else:
            ctx.env[nm] = Var("const", mb, t, assignable=False)
    used_names = set(FNS_MB) | {"i_abs", "d_abs"}
    sig_parts = []
    pre = []
    for p in fd.params:
        t = fd.ptypes[p]
        mb = mb_ident(p)
        if mb in used_names:
            mb += "_v"
        if isinstance(t, tuple) and t[0] == "A":
            off = None
            sig_parts.append("%s : %s" % (mb, mbt_type(t)))
            if fd.needs_off.get(p):
                off = mb + "_off"
                sig_parts.append("%s : Int" % off)
            ctx.env[p] = Var("array", mb, t, off=off)
        elif isinstance(t, tuple) and t[0] == "FN":
            sig_parts.append("%s : %s" % (mb, mbt_type(t)))
            ctx.env[p] = Var("fn", mb, t)
        else:
            sig_parts.append("%s : %s" % (mb, mbt_type(t)))
            if p in assigned:
                pre.append("let mut %s = %s" % (mb, mb))
            ctx.env[p] = Var("local", mb, t)
    # with-multi-array-data aliases
    for entry in fd.mad:
        arr, _et, dvar, ovar = entry
        v = ctx.env[arr.name]
        ctx.env[dvar.name] = v
        ctx.env[ovar.name] = Var("off", v.off or "0", "I", assignable=False)
    # locals
    for nm, init in fd.locals:
        typ = fd.ltypes.get(nm)
        mb = mb_ident(nm)
        if mb in used_names or mb in [mb_ident(p) for p in fd.params]:
            mb += "_v"
        if isinstance(typ, tuple) or head(init) == "make-array":
            t0, code = init_value(init, typ)
            t = typ or t0
            if code is None:
                n = init[1]
                c, _ = expr(ctx, n)
                code = "FixedArray::make(%s, %s)" % (c, "0.0" if t[1] == "D" else "0")
            pre.append("let %s : %s = %s" % (mb, mbt_type(t), code))
            ctx.env[nm] = Var("array", mb, t)
            continue
        t0, code = init_value(init, typ)
        t = typ or t0
        code = literal_conv(code, t0, t)
        if nm in assigned:
            pre.append("let mut %s : %s = %s" % (mb, mbt_type(t), code))
        else:
            pre.append("let %s : %s = %s" % (mb, mbt_type(t), code))
        ctx.env[nm] = Var("local", mb, t)
    slots = fd.slots()
    rt = ret_type([t for _, t in slots])
    lines = []
    lines.append("///|")
    lines.append("/// Translated from SLATEC routine %s (numerical/slatec/%s.lisp)." % (fd.name.upper(), fd.file))
    sigline = "pub fn %s(%s) -> %s%s {" % (mb_fn_name(fd.name), ", ".join(sig_parts), rt,
                                           " raise" if fd.raises else "")
    lines.append(sigline)
    for p in pre:
        lines.append("  " + p)
    tagbody(ctx, fd.body)
    body = ctx.lines
    last = body[-1] if body else ""
    if last.startswith("  return") and not last.startswith("   "):
        # The function body ends with its RETURN at the top level.
        val = last.strip()[len("return"):].strip()
        body = body[:-1] + (["  " + val] if val else [])
        lines.extend(body)
    else:
        lines.extend(body)
        # Every path returns explicitly; this keeps the type checker happy.
        lines.append("  panic()")
    lines.append("}")
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Reference test generation (--reference-test)
#
# Runs the f2cl Lisp itself under SBCL on a fixed set of calls and writes
# slatec/sbcl_reference_wbtest.mbt, which checks that the MoonBit routines
# return the same IEEE bit patterns.  Needs `sbcl` on PATH.

def lf(x):
    s = repr(float(x))
    if "e" in s:
        m, e = s.split("e")
        if "." not in m:
            m += ".0"
        return m + "d" + e
    return s + "d0"


def mf(x):
    s = repr(float(x))
    if "e" in s:
        m, e = s.split("e")
        if "." not in m:
            m += ".0"
        s = m + "e" + e
    return "(" + s + ")" if s.startswith("-") else s


# integrands: name -> (lisp, moonbit)
REF_FUNS = {
    "sq": ("(lambda (x) (* x x))", "x => (x * x)"),
    "isqrt": ("(lambda (x) (/ 1d0 (sqrt x)))", "x => (1.0 / x.sqrt())"),
    "expm": ("(lambda (x) (exp (- x)))", "x => (f_exp(-x))"),
    "logx": ("(lambda (x) (log x))", "x => (f_log(x))"),
    "sinx": ("(lambda (x) (sin x))", "x => (f_sin(x))"),
    "gauss": ("(lambda (x) (exp (- (* x x))))", "x => (f_exp(-(x * x)))"),
    "lor": ("(lambda (x) (/ 1d0 (+ 1d0 (* x x))))", "x => (1.0 / (1.0 + x * x))"),
    "one": ("(lambda (x) (declare (ignore x)) 1d0)", "_x => 1.0"),
    "sinrecip": ("(lambda (x) (sin (/ 1d0 x)))", "x => (f_sin(1.0 / x))"),
    "recip": ("(lambda (x) (/ 1d0 x))", "x => (1.0 / x)"),
    "logabs": ("(lambda (x) (log (abs (- x 0.3d0))))", "x => (f_log((x - 0.3).abs()))"),
}

REF_CASES = []  # (fn, args) ; args: ('D',v) ('I',v) ('DA',n,[init]) ('IA',n) ('F',name) ('B', v)

XS = [-30.0, -7.5, -2.3, -1.0, -0.5, -1e-3, 0.0, 1e-5, 0.1, 0.5, 1.0, 1.5, 2.7, 4.5, 7.3, 12.0, 25.0, 40.0, 100.0]
for fn in ["dbesj0", "dbesj1", "dbesi0", "dbesi1", "dbsi0e", "dbsi1e", "derf", "dspenc", "dai", "daie", "dbi"]:
    for x in XS:
        if fn in ("dbesi0", "dbesi1") and abs(x) > 50:
            continue
        if fn == "dbi" and x > 20:
            continue
        REF_CASES.append((fn, [("D", x)]))
for fn in ["dbesy0", "dbesy1", "dbesk0", "dbesk1"]:
    for x in XS:
        if x > 0:
            REF_CASES.append((fn, [("D", x)]))
for x in XS:
    if x != 0:
        REF_CASES.append(("de1", [("D", x)]))
for x in [-7.5, -2.3, -0.5, 1e-3, 0.1, 0.5, 1.0, 1.5, 2.7, 4.5, 7.3, 12.0, 25.0, 40.0, 100.0, 170.5]:
    REF_CASES.append(("dgamma", [("D", x)]))
for x in [10.0, 12.5, 30.0, 1e3, 1e6]:
    REF_CASES.append(("d9lgmc", [("D", x)]))
for x in [-5.0, -1.2, 0.0, 0.7, 3.0, 9.0]:
    rx = math.sqrt(abs(x))
    c = 2.0 / 3.0 * abs(x) * rx
    REF_CASES.append(("djairy", [("D", x), ("D", rx), ("D", c), ("D", 0.0), ("D", 0.0)]))
    REF_CASES.append(("dyairy", [("D", x), ("D", rx), ("D", c), ("D", 0.0), ("D", 0.0)]))
for x in [0.5, 3.0, 10.0, 30.0]:
    for alpha in [0.0, 0.3, 2.5, 10.7, 40.2]:
        for n in [1, 3]:
            REF_CASES.append(("dbesj", [("D", x), ("D", alpha), ("I", n), ("DA", n), ("I", 0)]))
            REF_CASES.append(("dbesy", [("D", x), ("D", alpha), ("I", n), ("DA", n)]))
            for kode in [1, 2]:
                REF_CASES.append(("dbesi", [("D", x), ("D", alpha), ("I", kode), ("I", n), ("DA", n), ("I", 0)]))
                REF_CASES.append(("dbesk", [("D", x), ("D", alpha), ("I", kode), ("I", n), ("DA", n), ("I", 0)]))
ZS = [(0.5, 0.0), (1.5, 2.0), (-3.0, 0.7), (0.1, -0.2), (12.0, 5.0), (-20.0, -1.0), (0.0, 7.0), (40.0, 0.5)]
for zr, zi in ZS:
    for fnu in [0.0, 0.5, 2.25, 11.0]:
        for kode in [1, 2]:
            n = 3
            for fn in ["zbesj", "zbesi", "zbesk"]:
                if fn == "zbesk" and zr == 0 and zi == 0:
                    continue
                REF_CASES.append((fn, [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("I", 0)]))
            REF_CASES.append(("zbesy", [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("DA", n), ("DA", n), ("I", 0)]))
            for m in [1, 2]:
                REF_CASES.append(("zbesh", [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", m), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("I", 0)]))
    for idd in [0, 1]:
        for kode in [1, 2]:
            REF_CASES.append(("zairy", [("D", zr), ("D", zi), ("I", idd), ("I", kode), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0)]))
            REF_CASES.append(("zbiry", [("D", zr), ("D", zi), ("I", idd), ("I", kode), ("D", 0.0), ("D", 0.0), ("I", 0)]))

for x in XS:
    if x != 0:
        REF_CASES.append(("dei", [("D", x)]))
    REF_CASES.append(("derfc", [("D", x)]))
    if x > 0:
        REF_CASES.append(("dbie", [("D", x)]))
        REF_CASES.append(("dbsk0e", [("D", x)]))
        REF_CASES.append(("dbsk1e", [("D", x)]))
for x in [-20.5, -3.7, -0.3, 0.2, 1.7, 5.5, 33.3, 171.6, 1e5]:
    REF_CASES.append(("dlngam", [("D", x)]))
for x in [0.2, 1.0, 1.7, 5.5, 33.3, 171.6, 1e5, 2.5e7]:
    REF_CASES.append(("dgamln", [("D", x), ("I", 0)]))
REF_CASES.append(("dgamlm", [("D", 0.0), ("D", 0.0)]))
for x in [0.3, 2.0, 7.0, 35.0, 120.0]:
    for alpha in [12.5, 30.25, 75.5]:
        for n in [1, 4]:
            REF_CASES.append(("dbesj", [("D", x), ("D", alpha), ("I", n), ("DA", n), ("I", 0)]))
            REF_CASES.append(("dbesy", [("D", x), ("D", alpha), ("I", n), ("DA", n)]))
            for kode in [1, 2]:
                REF_CASES.append(("dbesi", [("D", x), ("D", alpha), ("I", kode), ("I", n), ("DA", n), ("I", 0)]))
                REF_CASES.append(("dbesk", [("D", x), ("D", alpha), ("I", kode), ("I", n), ("DA", n), ("I", 0)]))
for zr, zi in [(3.0, 2.0), (-50.0, 10.0), (100.0, -30.0), (0.5, 120.0), (-4.0, -0.001), (85.0, 85.0)]:
    for fnu in [33.5, 90.5, 160.25]:
        for kode in [1, 2]:
            n = 2
            for fn in ["zbesj", "zbesi", "zbesk"]:
                REF_CASES.append((fn, [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("I", 0)]))
            REF_CASES.append(("zbesy", [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("DA", n), ("DA", n), ("I", 0)]))
            for m in [1, 2]:
                REF_CASES.append(("zbesh", [("D", zr), ("D", zi), ("D", fnu), ("I", kode), ("I", m), ("I", n), ("DA", n), ("DA", n), ("I", 0), ("I", 0)]))
for zr, zi in [(25.0, 3.0), (-25.0, 3.0), (6.0, -9.0), (-1.0e-3, 2e-4), (150.0, 0.0), (-150.0, 1.0)]:
    for idd in [0, 1]:
        for kode in [1, 2]:
            REF_CASES.append(("zairy", [("D", zr), ("D", zi), ("I", idd), ("I", kode), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0)]))
            REF_CASES.append(("zbiry", [("D", zr), ("D", zi), ("I", idd), ("I", kode), ("D", 0.0), ("D", 0.0), ("I", 0)]))

LIM = 200


def q(fn, *args):
    REF_CASES.append((fn, list(args)))


for f, a, b in [("sq", 0.0, 1.0), ("isqrt", 0.0, 1.0), ("logx", 0.0, 1.0), ("sinrecip", 0.0, 1.0),
                ("gauss", -3.0, 2.0), ("recip", 0.0, 1.0), ("logabs", 0.0, 1.0)]:
    q("dqags", ("F", f), ("D", a), ("D", b), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", LIM), ("I", 4 * LIM), ("I", 0), ("IA", LIM), ("DA", 4 * LIM))
    for key in range(1, 7):
        q("dqag", ("F", f), ("D", a), ("D", b), ("D", 0.0), ("D", 1e-8), ("I", key), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
          ("I", LIM), ("I", 4 * LIM), ("I", 0), ("IA", LIM), ("DA", 4 * LIM))
    q("dqng", ("F", f), ("D", a), ("D", b), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0))
q("dqags", ("F", "sinrecip"), ("D", 0.0), ("D", 1.0), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
  ("I", 3), ("I", 12), ("I", 0), ("IA", 3), ("DA", 12))
for f, bnd, inf in [("expm", 0.0, 1), ("gauss", 0.0, 2), ("lor", 1.0, -1), ("lor", 0.0, 2)]:
    q("dqagi", ("F", f), ("D", bnd), ("I", inf), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", LIM), ("I", 4 * LIM), ("I", 0), ("IA", LIM), ("DA", 4 * LIM))
for f, a, b, c in [("one", -1.0, 1.0, 0.5), ("expm", 0.0, 5.0, 2.0), ("lor", -1.0, 5.0, 0.0)]:
    q("dqawc", ("F", f), ("D", a), ("D", b), ("D", c), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", LIM), ("I", 4 * LIM), ("I", 0), ("IA", LIM), ("DA", 4 * LIM))
for f, a, om, integr in [("expm", 0.0, 1.0, 1), ("expm", 0.0, 3.0, 2), ("lor", 0.0, 1.0, 1)]:
    limlst, leniw, maxp1 = 10, LIM, 100
    lenw = 2 * leniw + 25 * maxp1
    q("dqawf", ("F", f), ("D", a), ("D", om), ("I", integr), ("D", 1e-10), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", limlst), ("I", 0), ("I", leniw), ("I", maxp1), ("I", lenw), ("IA", leniw), ("DA", lenw))
for f, a, b, om, integr in [("expm", 0.0, 2.0, 10.0, 1), ("gauss", -1.0, 3.0, 25.0, 2), ("one", 0.0, 1.0, 0.5, 1)]:
    leniw, maxp1 = LIM, 100
    lenw = 2 * leniw + 25 * maxp1
    q("dqawo", ("F", f), ("D", a), ("D", b), ("D", om), ("I", integr), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", leniw), ("I", maxp1), ("I", lenw), ("I", 0), ("IA", leniw), ("DA", lenw))
for f, a, b, al, be, w in [("one", 0.0, 1.0, -0.5, -0.5, 1), ("expm", 0.0, 2.0, 0.5, 1.5, 2), ("sq", 0.0, 1.0, -0.3, 0.2, 3), ("lor", 0.0, 1.0, 0.0, 0.0, 4)]:
    q("dqaws", ("F", f), ("D", a), ("D", b), ("D", al), ("D", be), ("I", w), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", LIM), ("I", 4 * LIM), ("I", 0), ("IA", LIM), ("DA", 4 * LIM))
for f, a, b, pts in [("logabs", 0.0, 1.0, [0.3]), ("recip", -1.0, 2.0, [0.0, 1.0])]:
    npts2 = len(pts) + 2
    leniw = max(LIM, 3 * npts2 - 2)
    lenw = 2 * leniw - npts2
    q("dqagp", ("F", f), ("D", a), ("D", b), ("I", npts2), ("DA", npts2, pts), ("D", 0.0), ("D", 1e-8), ("D", 0.0), ("D", 0.0), ("I", 0), ("I", 0),
      ("I", leniw), ("I", lenw), ("I", 0), ("IA", leniw), ("DA", lenw))


def lisp_case(k, fn, args):
    binds = []
    call = []
    arrs = []
    for j, a in enumerate(args):
        if a[0] == "D":
            call.append(lf(a[1]))
        elif a[0] == "I":
            call.append(str(a[1]))
        elif a[0] == "F":
            call.append(REF_FUNS[a[1]][0])
        elif a[0] == "DA":
            nm = "a%d" % j
            init = a[2] if len(a) > 2 else []
            init = init + [0.0] * (a[1] - len(init))
            binds.append("(%s (make-array %d :element-type 'double-float :initial-contents (list %s)))" % (nm, a[1], " ".join(lf(v) for v in init)))
            call.append(nm)
            arrs.append((nm, "D", a[1]))
        elif a[0] == "IA":
            nm = "a%d" % j
            binds.append("(%s (make-array %d :element-type 'f2cl-lib:integer4 :initial-element 0))" % (nm, a[1]))
            call.append(nm)
            arrs.append((nm, "I", a[1]))
    pr_arrs = " ".join("(pa %s)" % nm for nm, _, n in arrs if n <= 8)
    return "(run %d (lambda () (let (%s) (prog1 (remove nil (multiple-value-list (slatec::%s %s))) %s))))" % (
        k, " ".join(binds), fn, " ".join(call), pr_arrs)


REF_LISP_HEAD = r"""
(setf *read-default-float-format* 'double-float)
(load "%(sl)s/f2cl-lib-package.lisp")
(load "%(sl)s/f2cl-lib.lisp")
(load "%(sl)s/slatec.lisp")
(dolist (f (directory "%(sl)s/slatec/*.lisp"))
  (unless (string= (pathname-name f) "quadpack")
    (let ((*error-output* (make-broadcast-stream)))
      (handler-bind ((warning #'muffle-warning))
        (load f)))))
(defvar *out* *standard-output*)
(defun pv (v)
  (etypecase v
    (double-float (format *out* " d~D" (sb-kernel:double-float-bits v)))
    (integer (format *out* " i~D" v))
    (function (format *out* " fn"))))
(defun pa (a) (format *out* " |") (loop for v across a do (pv v)))
(defun run (k thunk)
  (format *out* "~D:" k)
  (let ((r (handler-case
               (let ((*standard-output* (make-broadcast-stream)))
                 (funcall thunk))
             (error (e) (format *out* " ERROR ~A" (type-of e)) :err))))
    (unless (eq r :err)
      (format *out* " =")
      (dolist (v r) (pv v))))
  (terpri *out*))
"""


def gen_reference_test(src, out_dir):
    import subprocess
    import tempfile
    SL = os.path.dirname(os.path.abspath(src))
    OUT = os.path.join(out_dir, "sbcl_reference_wbtest.mbt")
    lines = [REF_LISP_HEAD % {"sl": SL}]
    for k, (fn, args) in enumerate(REF_CASES):
        lines.append(lisp_case(k, fn, args))
    tmpdir = tempfile.mkdtemp()
    lp = os.path.join(tmpdir, "ref_run.lisp")
    with open(lp, "w") as f:
        f.write("\n".join(lines) + "\n")
    out = subprocess.run(["sbcl", "--script", lp], capture_output=True, text=True).stdout
    res = {}
    for line in out.splitlines():
        if ":" in line and line.split(":")[0].isdigit():
            k, rest = line.split(":", 1)
            res[int(k)] = rest
    # The array printing happens inside the thunk before results; reorder:
    # output format is "k: |arr... = vals" -- keep as is.
    mb = ["// Generated by tools/f2cl2mbt.py --reference-test; do not edit.",
          "// Differential test against the f2cl Lisp run under SBCL 2.6.9 (the Lisp",
          "// Maxima 5.50.0 uses on this machine).  Each case calls a SLATEC/QUADPACK",
          "// routine and renders every returned value and output array as IEEE bit",
          "// patterns (doubles) or integers; the expected strings were produced by",
          "// loading numerical/f2cl-lib.lisp and numerical/slatec/*.lisp into SBCL",
          "// and running the identical calls.",
          ""]
    nerr = 0
    for k, (fn, args) in enumerate(REF_CASES):
        exp = res.get(k)
        if exp is None or "ERROR" in exp:
            nerr += 1
            continue
        call = []
        pre = []
        arrs = []
        for j, a in enumerate(args):
            if a[0] == "D":
                call.append(mf(a[1]))
            elif a[0] == "I":
                call.append(str(a[1]))
            elif a[0] == "F":
                call.append(REF_FUNS[a[1]][1])
            elif a[0] == "DA":
                nm = "a%d" % j
                init = a[2] if len(a) > 2 else []
                if init:
                    init = init + [0.0] * (a[1] - len(init))
                    pre.append("let %s : FixedArray[Double] = [%s]" % (nm, ", ".join(mf(v) for v in init)))
                else:
                    pre.append("let %s : FixedArray[Double] = FixedArray::make(%d, 0.0)" % (nm, a[1]))
                call.append(nm)
                arrs.append((nm, "D", a[1]))
            elif a[0] == "IA":
                nm = "a%d" % j
                pre.append("let %s : FixedArray[Int] = FixedArray::make(%d, 0)" % (nm, a[1]))
                call.append(nm)
                arrs.append((nm, "I", a[1]))
        mb.append("///|")
        mb.append('test "sbcl reference %d: %s" {' % (k, fn))
        for p in pre:
            mb.append("  " + p)
        mb.append("  let r = %s(%s)" % (fn, ", ".join(call)))
        mb.append("  let s = StringBuilder()")
        for nm, t, n in arrs:
            if n <= 8:
                mb.append("  render_array(s, %s)" % nm)
        mb.append('  s.write_string(" =")')
        mb.append("  render(s, r)")
        mb.append('  assert_eq(s.to_string(), "%s")' % exp)
        mb.append("}")
        mb.append("")
    with open(OUT, "w") as f:
        f.write("\n".join(mb))
    print("reference cases %d, skipped (Lisp signalled an error) %d" % (len(REF_CASES), nerr), file=sys.stderr)



# ---------------------------------------------------------------------------
# Driver

FNS = {}
FNS_MB = set()


HEADER = """// Generated by tools/f2cl2mbt.py from Maxima's
// src/numerical/slatec/%s.lisp (f2cl translation of SLATEC/QUADPACK).
// Do not edit by hand; regenerate instead.

"""


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    src = args[0] if len(args) > 0 else DEFAULT_SRC
    out = args[1] if len(args) > 1 else DEFAULT_OUT
    if "--reference-test" in sys.argv:
        gen_reference_test(src, out)
        return 0
    files = sorted(f for f in os.listdir(src) if f.endswith(".lisp") and f not in SKIP_FILES)
    defs = []
    for f in files:
        defs.extend(parse_file(os.path.join(src, f)))
    for h in HAND:
        FNS[h.name] = h
    for d in defs:
        FNS[d.name] = d
    for name in FNS:
        FNS_MB.add(mb_fn_name(name))
    compute_offsets()
    compute_fnsigs()
    errors = 0
    os.makedirs(out, exist_ok=True)
    byfile = {}
    for d in defs:
        byfile.setdefault(d.file, []).append(d)
    for fname, ds in sorted(byfile.items()):
        parts = [HEADER % fname]
        try:
            for d in ds:
                st = []
                emit_statics(d, st)
                parts.append("\n".join(st))
                parts.append(gen_function(d))
        except TransError as e:
            print("ERROR %s: %s" % (fname, e), file=sys.stderr)
            errors += 1
            continue
        with open(os.path.join(out, fname + ".mbt"), "w") as f:
            f.write("\n".join(p for p in parts if p))
    print("translated %d routines from %d files, %d errors" % (len(defs), len(byfile), errors),
          file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
