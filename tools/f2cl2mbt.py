#!/usr/bin/env python3
"""Translate Maxima's f2cl-generated Fortran libraries (Lisp) into MoonBit.

Usage:
    python3 tools/f2cl2mbt.py [SRC_DIR] [OUT_DIR]
    python3 tools/f2cl2mbt.py --reference-test [SRC_DIR] [OUT_DIR]
    python3 tools/f2cl2mbt.py --lib=lbfgs|odepack|lapack [--reference-test]

The first two forms translate SLATEC/QUADPACK (src/numerical/slatec) into
slatec/; the second regenerates slatec/sbcl_reference_wbtest.mbt by running
the original Lisp under SBCL (see gen_reference_test).  SRC_DIR defaults to
.repos/maxima/src/numerical/slatec, OUT_DIR to slatec/.

--lib=NAME translates the f2cl code of a share package into the package
NAME/ (lbfgs: share/lbfgs; odepack: the DLSODE subset of share/odepack/src;
lapack: share/lapack/blas and share/lapack/lapack), which uses the runtime
package f2cl/ (complex arithmetic as SBCL does it, Fortran strings, FFORMAT
output).  With --reference-test it writes NAME/sbcl_reference_wbtest.mbt
from the SHARE_REF cases (see gen_share_reference_test).  Beyond what
SLATEC needs, these libraries use COMMON blocks (DEFSTRUCT + SYMBOL-MACROLET,
displaced arrays), BLOCK DATA, statement functions (LABELS), CHARACTER
variables, COMPLEX*16 and formatted WRITEs.

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
REPOS_DIR = os.path.join(ROOT, ".repos") if os.path.isdir(os.path.join(ROOT, ".repos")) else "/Users/dii/git/maxima.mbt/.repos"


def _find_src():
    d = ROOT
    while True:
        cand = os.path.join(d, ".repos", "maxima", "src", "numerical", "slatec")
        if os.path.isdir(cand):
            return cand
        parent = os.path.dirname(d)
        if parent == d:
            return os.path.join(REPOS_DIR, "maxima", "src", "numerical", "slatec")
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


class CplxLit:
    """A #C(re im) literal (complex double-float in the f2cl code)."""
    __slots__ = ("re", "im")

    def __init__(self, re, im):
        self.re = re
        self.im = im

    def __repr__(self):
        return "#C(%r %r)" % (self.re, self.im)


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
    for pre in ("cl:", "common-lisp:", "slatec::", "slatec:", "odepack::", "odepack:",
                "lapack::", "lapack:", "blas::", "blas:", "common-lisp-user::"):
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
        elif c == "#" and text[i + 1] in "cC" and text[i + 2] == "(":
            toks.append("#C")
            i += 2
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
        if t == "#C":
            parts = rd()
            return CplxLit(parts[0], parts[1])
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
    if t == "C":
        return "Complex"
    if isinstance(t, tuple) and t[0] == "A":
        return "FixedArray[%s]" % ELEM_MBT[t[1]]
    if isinstance(t, tuple) and t[0] == "AO":
        # array section passed to a closure: the array and its offset
        return "FixedArray[%s], Int" % ELEM_MBT[t[1]]
    if isinstance(t, tuple) and t[0] == "FN":
        return t[1].mbt()
    if isinstance(t, tuple) and t[0] == "FNP":
        return mbt_type(resolve_t(t))
    raise ValueError("type %r" % (t,))


def resolve_t(t):
    """A closure argument that is itself a function parameter of the routine
    the closure was made from: its (by now resolved) type."""
    if isinstance(t, tuple) and t[0] == "FNP":
        return t[1].ptypes[t[2]]
    return t


ELEM_MBT = {"D": "Double", "I": "Int", "C": "Complex", "B": "Bool", "F": "Float"}
ELEM_ZERO = {"D": "0.0", "I": "0", "C": "c_zero", "B": "false", "F": "Float::from_double(0.0)"}


def is_array_type(t):
    return isinstance(t, tuple) and t[0] in ("A", "AO")


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
        if isinstance(el, list) and len(el) == 1:
            el = el[0]
        if is_sym(el, "double-float"):
            return ("A", "D")
        if is_sym(el, "f2cl-lib:integer4"):
            return ("A", "I")
        if is_sym(el, "f2cl-lib:complex16"):
            return ("A", "C")
        if is_sym(el, "f2cl-lib:logical"):
            return ("A", "B")
        raise ValueError("array type %r" % (spec,))
    if isinstance(s, list):
        if head(s) == "simple-string" or head(s) == "string":
            return "S"
        s = s[0]
    if is_sym(s, "f2cl-lib:complex16"):
        return "C"
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
    s = name.replace("$", "_").replace("-", "_").replace("%", "").strip("/")
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
        self.displaced = {}     # let-bound common-block array -> (part, offset, type)
        self.smacros = {}       # symbol-macrolet name -> form
        self.labels = []        # statement functions
        self.label_types = {}   # statement function -> (arg types, result type)
        self.blockdata = False  # BLOCK DATA: body is a statement list

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
    # Wrappers around the PROG: common-block bindings (LET of displaced
    # arrays, SYMBOL-MACROLET), statement functions (LABELS) and the
    # array-data aliases.
    while True:
        h = head(b)
        if h in ("let", "let*"):
            types = {}
            rest = collect_decls(b[2:], types)
            for binding in b[1]:
                nm = binding[0].name
                init = binding[1]
                if head(init) != "make-array":
                    raise TransError("let binding %s in %s" % (nm, name))
                kw = {init[k].name: init[k + 1] for k in range(2, len(init), 2)}
                tgt = kw[":displaced-to"]
                fd.displaced[nm] = (common_part_name(tgt), kw[":displaced-index-offset"],
                                    types.get(nm) or ("A", elem_type_of(kw[":element-type"])))
            assert len(rest) == 1, name
            b = rest[0]
        elif h == "symbol-macrolet":
            for nm, f in b[1]:
                fd.smacros[nm.name] = f
            rest = collect_decls(b[2:], {})
            if len(rest) != 1 or head(rest[0]) not in (
                    "f2cl-lib:with-multi-array-data", "prog", "labels", "let", "let*"):
                # BLOCK DATA: a plain sequence of statements
                fd.body = rest
                fd.blockdata = True
                fd.values = []
                return fd
            b = rest[0]
        elif h == "labels":
            fd.labels = b[1]
            for d in b[2:]:
                if head(d) != "declare":
                    continue
                for spec in d[1:]:
                    if head(spec) == "ftype":
                        fnt = spec[1]
                        argts = [parse_type(a) for a in fnt[1]]
                        rt = fnt[2][1] if head(fnt[2]) == "values" else fnt[2]
                        for nm in spec[2:]:
                            fd.label_types[nm.name] = (argts, parse_type(rt))
            rest = [x for x in b[2:] if head(x) != "declare"]
            assert len(rest) == 1, name
            b = rest[0]
        elif h == "f2cl-lib:with-multi-array-data":
            fd.mad = b[1]
            assert len(b) == 3, name
            b = b[2]
        else:
            break
    assert head(b) == "prog", (name, head(b))
    for binding in ([] if is_sym(b[1], "nil") else b[1]):
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


def common_part_name(form):
    """(dls001-part-0 *dls001-common-block*) -> 'dls001-part-0'."""
    if isinstance(form, list) and len(form) == 2 and is_sym(form[1]) and \
            form[1].name.endswith("-common-block*"):
        return form[0].name
    raise TransError("common block reference %r" % (form,))


def parse_defstruct(form):
    """A common block: (defstruct (name ...) (slot init :type type)...)."""
    name = form[1][0].name if isinstance(form[1], list) else form[1].name
    slots = []
    for s in form[2:]:
        kw = {s[k].name: s[k + 1] for k in range(2, len(s), 2)}
        t = parse_type(kw[":type"])
        init = s[1]
        if head(init) == "make-array":
            n = init[1]
            slots.append((s[0].name, t, n))
        else:
            slots.append((s[0].name, t, init))
    COMMONS[name] = slots


def parse_file(path):
    with open(path) as f:
        text = f.read()
    a = text.index("(in-package ")
    b = text.find("(in-package #:cl-user)")
    if b < 0:
        b = len(text)
    forms = read_forms(text[a:b])[1:]
    fname = os.path.basename(path).rsplit(".", 1)[0]
    out = []
    for form in forms:
        out.extend(parse_top(form, fname, [], {}))
    return out


def parse_top(form, fname, statics, static_inits):
    h = head(form)
    if h == "defun":
        return [parse_defun(form, fname, statics, static_inits)]
    if h == "defstruct":
        parse_defstruct(form)
        COMMON_FILES.append(fname)
        return []
    if h == "defparameter" and form[1].name.endswith("-common-block*"):
        return []
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


def fn_bindings():
    """(routine, function parameter) -> names of the routines passed for it
    (as #'g, directly or through other routines' function parameters)."""
    out = {}
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
                        continue
                    gs = set()
                    if head(a) == "function" and a[1].name in FNS:
                        gs = {a[1].name}
                    elif isinstance(a, Sym) and a.name in fd.params:
                        gs = out.get((fd.name, a.name), set())
                    key = (callee, cd.params[i])
                    old = out.setdefault(key, set())
                    if not gs <= old:
                        old |= gs
                        changed = True
    return out


def funcall_sites(fd, bindings):
    """(callee-name, args) for FUNCALLs of function parameters bound to known
    routines."""
    out = []

    def visit(x):
        if head(x) == "funcall" and isinstance(x[1], Sym):
            for g in sorted(bindings.get((fd.name, x[1].name), ())):
                out.append((g, x[2:]))
    walk(fd.body, visit)
    return out


def compute_offsets():
    bindings = fn_bindings()
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
            for callee, args in call_sites(fd) + funcall_sites(fd, bindings):
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
                        nm = a.name
                        if isinstance(fd.smacros.get(nm), Sym):
                            nm = fd.smacros[nm].name
                        if nm in fd.displaced and fd.displaced[nm][1]:
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
                fd.fnsigs[p] = LIB["user_sigs"].get(p)
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
                        sig = Sig([("FNP", g, q) if g.ptypes[q] == ("FN", None) else
                                   ("AO", g.ptypes[q][1]) if g.needs_off.get(q) else g.ptypes[q]
                                   for q in g.params], g.slots(), g.raises)
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
    if to == "C":
        if frm in ("I", "D"):
            # CL contagion of a real to (complex double-float): imaginary 0d0
            return "cplx(%s, 0.0)" % strip_paren(conv(code, frm, "D"))
    raise TransError("cannot convert %s -> %s (%s)" % (frm, to, code))


def contagion(a, b):
    if a == "C" or b == "C":
        if a in ("C", "D", "I") and b in ("C", "D", "I"):
            return "C"
        raise TransError("contagion %s %s" % (a, b))
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
        self.labels = {}      # statement function -> MoonBit function name

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
    "f2cl-lib:dsqrt": "f_sqrt",
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
    if h == "f2cl-lib:f2cl/":
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 == "I" and t2 == "I":
            return (paren("%s / %s" % (wrap(c1), wrap(c2))), "I")
        return arith(ctx, "/", args)
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
        if is_sym(target, "f2cl-lib:complex16"):
            return (conv(c, t, "C"), "C")
        if is_sym(target, "f2cl-lib:logical") and t == "B":
            return (c, "B")
        raise TransError("coerce %r" % (target,))
    if h in ("realpart", "imagpart", "f2cl-lib:dimag", "f2cl-lib:aimag"):
        c, t = expr(ctx, args[0])
        part = "re" if h == "realpart" else "im"
        if t == "C":
            return (wrap(c) + "." + part, "D")
        if h == "realpart":
            return (c, t)
        raise TransError("imagpart of %s" % t)
    if h in ("f2cl-lib:freal", "f2cl-lib:sngl"):
        c, t = expr(ctx, args[0])
        if t == "C":
            c, t = wrap(c) + ".re", "D"
        return (conv(c, t, "F"), "F")
    if h in ("f2cl-lib:dble", "f2cl-lib:dfloat"):
        c, t = expr(ctx, args[0])
        if t == "C":
            return (wrap(c) + ".re", "D")
        return (conv(c, t, "D"), "D")
    if h in ("f2cl-lib:dconjg", "f2cl-lib:conjg"):
        c, t = expr(ctx, args[0])
        if t != "C":
            raise TransError("conjugate of %s" % t)
        return ("c_conj(%s)" % strip_paren(c), "C")
    if h in ("f2cl-lib:dcmplx", "f2cl-lib:cmplx"):
        c1, t1 = expr(ctx, args[0])
        if t1 == "C" and len(args) == 1:
            return (c1, "C")
        if len(args) > 1:
            c2, t2 = expr(ctx, args[1])
            c2 = conv(c2, t2, "D")
        else:
            c2 = "0.0"
        return ("cplx(%s, %s)" % (strip_paren(conv(c1, t1, "D")), strip_paren(c2)), "C")
    if h == "f2cl-lib:fref":
        return array_ref(ctx, x)
    if h in ("abs", "f2cl-lib:dabs", "f2cl-lib:iabs", "f2cl-lib:cdabs"):
        c, t = expr(ctx, args[0])
        if t == "I":
            return ("i_abs(%s)" % c, "I")
        if t == "D":
            return ("d_abs(%s)" % c, "D")
        if t == "F":
            return ("%s.abs()" % wrap(c), "F")
        if t == "C":
            return ("c_abs(%s)" % strip_paren(c), "D")
    if h in ("sqrt", "f2cl-lib:fsqrt", "f2cl-lib:zsqrt", "f2cl-lib:csqrt"):
        c, t = expr(ctx, args[0])
        if t == "C":
            return ("c_sqrt(%s)" % strip_paren(c), "C")
    if h == "f2cl-lib:nint":
        c, t = expr(ctx, args[0])
        return ("f_nint(%s)" % strip_paren(conv(c, t, "D")), "I")
    if h == "f2cl-lib:log10":
        c, t = expr(ctx, args[0])
        return ("f_log10(%s)" % strip_paren(conv(c, t, "D")), "D")
    if h == "f2cl-lib:fref-string":
        c, t = expr(ctx, args[0])
        lo, _ = expr(ctx, args[1][0])
        hi, _ = expr(ctx, args[1][1])
        return ("fstr_sub(%s, %s, %s)" % (c, lo, hi), "S")
    if h == "f2cl-lib:f2cl-//":
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        return (paren("%s + %s" % (c1, c2)), "S")
    if h in ("f2cl-lib:fstring-=", "f2cl-lib:fstring-/="):
        c1, t1 = expr(ctx, args[0])
        c2, t2 = expr(ctx, args[1])
        if t1 != "S" or t2 != "S":
            raise TransError("string compare of %s %s" % (t1, t2))
        return (paren("%s %s %s" % (c1, "==" if h.endswith("-=") else "!=", c2)), "B")
    if h == "f2cl-lib:ichar":
        c, t = expr(ctx, args[0])
        return ("ichar(%s)" % c, "I")
    if h == "f2cl-lib:fchar":
        c, t = expr(ctx, args[0])
        return ("fchar(%s)" % c, "S")
    if h in ctx.labels:
        argts, rt = ctx.fd.label_types[h]
        cs = []
        for a, at in zip(args, argts):
            c, t = expr(ctx, a)
            cs.append(strip_paren(conv(c, t, at)))
        return ("%s(%s)" % (ctx.labels[h], ", ".join(cs)), rt)
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
            return ("i_pow(%s, %s)" % (c1, c2), "I")
        if t1 == "C" and args[1] == 2:
            # SBCL compiles (expt z 2) as (* z z)
            return ("c_mul(%s, %s)" % (strip_paren(c1), strip_paren(c1)), "C")
        if t1 not in ("D", "F") or t2 not in ("D", "F", "I"):
            raise TransError("expt %s %s" % (t1, t2))
        if t1 == "D" and args[1] == 2:
            # SBCL compiles (expt x 2) as (* x x) (not libm pow, which
            # differs in the last bit for some x)
            if is_simple(c1):
                return (paren("%s * %s" % (c1, c1)), "D")
            return ("d_sq(%s)" % strip_paren(c1), "D")
        if t1 == "D" and args[1] == -1:
            return (paren("1.0 / %s" % wrap(c1)), "D")
        return ("f_pow(%s, %s)" % (conv(c1, t1, "D"), conv(c2, t2, "D")), "D")
    if h in ("max", "min", "f2cl-lib:dmax1", "f2cl-lib:dmin1", "f2cl-lib:max0", "f2cl-lib:min0"):
        return minmax(ctx, "max" if "max" in h else "min", args)
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
        if t == "C":
            c = wrap(c) + ".re"
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


C_OPS = {"+": "c_add", "-": "c_sub", "*": "c_mul", "/": "c_div"}


def complex_op(op, c, t, c2, t2):
    """SBCL's arithmetic on (complex double-float): a real operand of + - /
    is converted to a complex with imaginary part 0d0, while * by a real
    scales both parts."""
    if op == "*" and t != "C":
        return "d_mul_c(%s, %s)" % (strip_paren(conv(c, t, "D")), strip_paren(c2))
    if op == "*" and t2 != "C":
        return "c_mul_d(%s, %s)" % (strip_paren(c), strip_paren(conv(c2, t2, "D")))
    return "%s(%s, %s)" % (C_OPS[op], strip_paren(conv(c, t, "C")), strip_paren(conv(c2, t2, "C")))


def arith(ctx, op, args, int_only=False):
    if len(args) == 1:
        c, t = expr(ctx, args[0])
        if op == "-":
            if t == "C":
                return ("c_neg(%s)" % strip_paren(c), t)
            return ("-" + wrap(c), t)
        if op == "/":
            if t == "I":
                raise TransError("integer reciprocal")
            if t == "C":
                return ("c_div(cplx(1.0, 0.0), %s)" % strip_paren(c), t)
            one = "1.0" if t == "D" else "Float::from_double(1.0)"
            return (paren("%s / %s" % (one, wrap(c))), t)
        return (c, t)
    c, t = expr(ctx, args[0])
    for a in args[1:]:
        c2, t2 = expr(ctx, a)
        rt = contagion(t, t2)
        if rt == "C":
            c = complex_op(op, c, t, c2, t2)
            t = rt
            continue
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
        if rt == "C":
            if op not in ("==", "!="):
                raise TransError("complex ordering")
            parts.append("%sc_eq(%s, %s)" % ("" if op == "==" else "!",
                                            strip_paren(conv(c1, t1, rt)), strip_paren(conv(c2, t2, rt))))
            continue
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
        return v.code, [resolve_t(t) for t in sig.args], [None] * len(sig.args), sig.slots, None
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
        elif isinstance(pt, tuple) and pt[0] == "AO":
            base, off, at = array_arg(ctx, a)
            if at != ("A", pt[1]):
                raise TransError("array type mismatch")
            out.append(base)
            out.append(off)
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
    cargs = [pn + ", " + pn + "_off" if isinstance(t, tuple) and t[0] == "AO" else pn
             for pn, t in zip(ps, sig.args)]
    call = "%s(%s)" % (mb_fn_name(name), ", ".join(cargs))
    if len(tmp) == 0:
        body = "%s; " % call
    elif len(tmp) == 1:
        body = "let %s = %s; " % (tmp[0], call)
    else:
        body = "let (%s) = %s; " % (", ".join(tmp), call)
    ret = res[0] if len(res) == 1 else "(" + ", ".join(res) + ")"
    params = ", ".join("%s : FixedArray[%s], %s_off : Int" % (pn, ELEM_MBT[t[1]], pn)
                       if isinstance(t, tuple) and t[0] == "AO" else "%s : %s" % (pn, mbt_type(t))
                       for pn, t in zip(ps, sig.args))
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
        if v.kind not in ("local", "static", "cell"):
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
            val = args[k + 1]
            if isinstance(val, Sym) and val.name in ctx.env and ctx.env[val.name].kind == "nil":
                # (setf x var-k) where the callee returned NIL for that slot
                # (zungtr's LDA after zungqr, i.e. zheev with UPLO = "L"):
                # a TYPE-ERROR in the Lisp, as X is declared an integer.
                ctx.emit('abort("f2cl: NIL assigned to %s (a TYPE-ERROR in the Lisp)")' % args[k].name)
                continue
            c, t = expr(ctx, val)
            assign(ctx, args[k], c, t)
        return
    if h == "f2cl-lib:f2cl-set-string":
        c, t = expr(ctx, args[1])
        n = args[2][1]
        if t != "S" or not isinstance(n, int):
            raise TransError("f2cl-set-string %r" % (x,))
        assign(ctx, args[0], "f2cl_string(%s, %d)" % (c, n), "S")
        return
    if h == "f2cl-lib:fset-string":
        tgt = args[0]
        if head(tgt) != "f2cl-lib:fref-string" or not isinstance(tgt[1], Sym):
            raise TransError("fset-string %r" % (x,))
        sc, st = expr(ctx, tgt[1])
        lo, _ = expr(ctx, tgt[2][0])
        hi, _ = expr(ctx, tgt[2][1])
        c, t = expr(ctx, args[1])
        assign(ctx, tgt[1], "fstr_set(%s, %s, %s, %s)" % (sc, lo, hi, c), "S")
        return
    if h == "f2cl-lib:fformat":
        fformat_stmt(ctx, x)
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


def fmt_items(items):
    """MoonBit FmtItem array for an f2cl format list (see EXECUTE-FORMAT)."""
    out = []
    k = 0
    while k < len(items):
        it = items[k]
        if isinstance(it, Str):
            out.append("Lit(%s)" % mb_string_lit(it.text))
        elif isinstance(it, int):
            out.append("Rep(%d, %s)" % (it, fmt_items(items[k + 1])))
            k += 1
        elif is_sym(it, "t"):
            out.append("Forever(%s)" % fmt_items(items[k + 1]))
            k += 1
        elif isinstance(it, list) and len(it) == 1 and isinstance(it[0], Str):
            out.append("Dir(%s)" % mb_string_lit(it[0].text))
        else:
            raise TransError("format item %r" % (it,))
        k += 1
    return "[" + ", ".join(out) + "]"


FARG = {"I": "AI", "D": "AD", "S": "AS", "B": "AB", "C": "AC"}


def fformat_stmt(ctx, x):
    """(f2cl-lib:fformat unit (format...) args...): the arguments are
    flattened (implied DO loops give lists) into an Array[FArg]."""
    unit = x[1]
    if is_sym(unit, "t"):
        uc = "-1"
    else:
        uc, ut = expr(ctx, unit)
        if ut != "I":
            raise TransError("format unit %r" % (unit,))
    items = fmt_items(x[2])
    fa = ctx.fresh("fa")
    ctx.emit("let %s : Array[FArg] = []" % fa)
    for a in x[3:]:
        if head(a) == "do":
            implied_do(ctx, a, fa)
            continue
        c, t = expr(ctx, a)
        ctx.emit("%s.push(%s(%s))" % (fa, FARG[t], strip_paren(c)))
    ctx.emit("fformat(%s, %s, %s)" % (uc, items, fa))


def implied_do(ctx, a, fa):
    # (do ((i 1 (int-add i 1)) (%ret nil)) ((> i n) (nreverse %ret))
    #   (declare ...) (push x %ret))
    var, start, step = a[1][0]
    test = a[2][0]
    body = [b for b in a[3:] if head(b) != "declare"]
    if len(body) != 1 or head(body[0]) != "push" or head(test) != ">" or \
            not is_sym(test[1], var.name):
        raise TransError("implied do %r" % (a,))
    iv = ctx.fresh("di")
    saved = ctx.env.get(var.name)
    ctx.env[var.name] = Var("local", iv, "I")
    sc, _ = expr(ctx, start)
    ctx.emit("let mut %s = %s" % (iv, strip_paren(sc)))
    ec, _ = expr(ctx, test[2])
    ctx.emit("while %s <= %s {" % (iv, wrap(ec)))
    c, t = expr(ctx, body[0][1])
    ctx.emit("  %s.push(%s(%s))" % (fa, FARG[t], strip_paren(c)))
    nc, _ = expr(ctx, step)
    ctx.emit("  %s = %s" % (iv, strip_paren(nc)))
    ctx.emit("}")
    if saved is None:
        del ctx.env[var.name]
    else:
        ctx.env[var.name] = saved


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
    # (go f2cl-lib::exit) leaves the loop (FDO's PROG* has an EXIT tag)
    exits = "f2cl-lib:exit" in collect_gos(body)
    if exits:
        label = ctx.fresh("fdo")
        ctx.tag_stack.append({"label": label, "tags": {"f2cl-lib:exit": ("exit",)}, "pc": None})
        ctx.emit("%s~: while %s > 0 {" % (label, cnt))
    else:
        ctx.emit("while %s > 0 {" % cnt)
    block(ctx, body)
    if exits:
        ctx.tag_stack.pop()
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
        elif h == "f2cl-lib:f2cl-set-string" and isinstance(y[1], Sym):
            out.add(y[1].name)
        elif h == "f2cl-lib:fset-string" and head(y[1]) == "f2cl-lib:fref-string":
            out.add(y[1][1].name)
    walk(forms, visit)
    return out


def static_name(fd, nm):
    return mb_ident(fd.file + "_" + nm)


def const_eval(form, consts):
    """Value of a constant initialiser expression (Python int/float), or None."""
    if isinstance(form, bool):
        return None
    if isinstance(form, int):
        return form
    if isinstance(form, Num):
        return form.value
    if isinstance(form, Sym):
        return consts.get(form.name)
    h = head(form)
    if h == "the":
        return const_eval(form[2], consts)
    if h in ("+", "*", "-", "/", "f2cl-lib:f2cl/", "f2cl-lib:int-add", "f2cl-lib:int-mul",
             "f2cl-lib:int-sub"):
        vals = [const_eval(a, consts) for a in form[1:]]
        if any(v is None for v in vals):
            return None
        if any(isinstance(v, float) for v in vals):
            # CL contagion, pairwise and left to right (IEEE, like Python)
            vals = [float(v) for v in vals]
        elif h.endswith("/"):
            return None
        acc = vals[0]
        if len(vals) == 1 and h in ("-", "f2cl-lib:int-sub"):
            return -acc
        for v in vals[1:]:
            acc = acc + v if h.endswith("+") or h.endswith("add") else \
                acc * v if h.endswith("*") or h.endswith("mul") else \
                acc / v if h.endswith("/") else acc - v
        return acc
    if h == "reduce" and head(form[1]) == "function" and is_sym(form[1][1], "*") \
            and head(form[2]) == "list":
        acc = 1
        for a in form[2][1:]:
            v = const_eval(a, consts)
            if v is None:
                return None
            acc *= v
        return acc
    return None


def elem_type_of(et):
    et = et[1] if head(et) == "quote" else et
    if isinstance(et, list) and len(et) == 1:
        et = et[0]
    if is_sym(et, "double-float"):
        return "D"
    if is_sym(et, "f2cl-lib:integer4"):
        return "I"
    if is_sym(et, "f2cl-lib:complex16"):
        return "C"
    if is_sym(et, "f2cl-lib:logical"):
        return "B"
    if is_sym(et, "character"):
        return "CH"
    if is_sym(et, "t"):
        return None   # the declared type says
    raise TransError("array element type %r" % (et,))


def mb_string_lit(s):
    return '"%s"' % s.replace("\\", "\\\\").replace('"', '\\"')


def init_value(form, typ, consts=None):
    """(type, code) for a static/local initial value; code is None for an
    array whose size is only known at run time."""
    consts = consts or {}
    if head(form) == "make-array":
        n = form[1]
        if head(n) == "quote":
            n = n[1]
        if isinstance(n, list) and not head(n):
            n = n[0]
        kw = {form[k].name: form[k + 1] for k in range(2, len(form), 2)}
        elem = elem_type_of(kw.get(":element-type"))
        if elem is None:
            if not is_array_type(typ):
                raise TransError("untyped array")
            elem = typ[1]
        nv = const_eval(n, consts)
        if elem == "CH":
            init = kw.get(":initial-element")
            ch = init.text if isinstance(init, Str) else " "
            if nv is None:
                raise TransError("dynamic string length")
            return "S", mb_string_lit(ch * nv)
        if ":initial-contents" in kw:
            vals = kw[":initial-contents"][1]
            if len(vals) != nv:
                raise TransError("initial-contents length")
            if elem == "D":
                items = [fmt_double(v.value if isinstance(v, Num) else float(v)) for v in vals]
            elif elem == "I":
                items = [str(v) for v in vals]
            elif elem == "B":
                items = ["true" if is_sym(v, "t") else "false" for v in vals]
            else:
                raise TransError("initial-contents of %s" % elem)
            return ("A", elem), "[%s]" % ", ".join(items)
        if nv is None:
            return ("A", elem), None  # dynamic size
        return ("A", elem), "FixedArray::make(%d, %s)" % (nv, ELEM_ZERO[elem])
    if isinstance(form, bool) or is_sym(form, "nil") or is_sym(form, "f2cl-lib:%false%"):
        return "B", "false"
    if is_sym(form, "f2cl-lib:%true%") or is_sym(form, "t"):
        return "B", "true"
    if isinstance(form, CplxLit):
        return "C", "cplx(%s, %s)" % (fmt_double(float(form.re.value if isinstance(form.re, Num) else form.re)),
                                      fmt_double(float(form.im.value if isinstance(form.im, Num) else form.im)))
    if head(form) in ("f2cl-lib:cmplx", "f2cl-lib:dcmplx"):
        re_ = const_eval(form[1], consts)
        im_ = const_eval(form[2], consts) if len(form) > 2 else 0
        return "C", "cplx(%s, %s)" % (fmt_double(float(re_)), fmt_double(float(im_)))
    if isinstance(form, Str):
        return "S", mb_string_lit(form.text)
    if isinstance(form, int):
        return "I", str(form)
    if isinstance(form, Num):
        if form.kind == "f":
            return "F", "Float::from_double(%s)" % fmt_double(form.value)
        return "D", fmt_double(form.value)
    v = const_eval(form, consts)
    if isinstance(v, int):
        return "I", str(v)
    if isinstance(v, float):
        return "D", fmt_double(v)
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
    if frm == "D" and to == "C":
        return "cplx(%s, 0.0)" % code
    raise TransError("literal conv %s->%s" % (frm, to))


def static_consts(fd):
    """Python values of the integer/double constants among FD's statics."""
    consts = {}
    for nm, typ, init in fd.statics:
        form = fd.static_inits.get(nm, init)
        v = const_eval(form, consts)
        if v is not None:
            if typ == "D" and isinstance(v, int):
                v = float(v)
            consts[nm] = v
    return consts


def emit_statics(fd, out):
    assigned = assigned_vars(fd.body)
    consts = {}
    for nm, typ, init in fd.statics:
        form = fd.static_inits.get(nm, init)
        t0, code = init_value(form, typ, consts)
        v = const_eval(form, consts)
        if v is not None:
            consts[nm] = v
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


def common_var(form):
    """Environment entry for a SYMBOL-MACROLET expansion into a common block."""
    if isinstance(form, list) and len(form) == 2 and is_sym(form[1]) and \
            form[1].name.endswith("-common-block*"):
        acc = form[0].name
        for sname, slots in COMMONS.items():
            if acc.startswith(sname + "-"):
                field = acc[len(sname) + 1:]
                for fnm, t, _ in slots:
                    if fnm == field:
                        mb = mb_ident(sname + "_" + fnm)
                        if is_array_type(t):
                            return Var("array", mb, t)
                        return Var("static", mb, t)
        raise TransError("unknown common field %s" % acc)
    if head(form) == "aref":
        part = common_part_name(form[1])
        sname, fnm = split_common_part(part)
        t = common_slot_type(sname, fnm)
        return Var("cell", "%s[%d]" % (mb_ident(part), form[2]), t[1])
    raise TransError("symbol-macrolet form %r" % (form,))


def split_common_part(part):
    for sname in COMMONS:
        if part.startswith(sname + "-"):
            return sname, part[len(sname) + 1:]
    raise TransError("unknown common part %s" % part)


def common_slot_type(sname, fnm):
    for f, t, _ in COMMONS[sname]:
        if f == fnm:
            return t
    raise TransError("unknown common slot %s-%s" % (sname, fnm))


def emit_commons(fname, out):
    for sname, slots in COMMONS.items():
        if COMMON_SRC.get(sname) != fname:
            continue
        out.append("// Fortran COMMON /%s/" % sname.upper())
        out.append("")
        for fnm, t, init in slots:
            mb = mb_ident(sname + "_" + fnm)
            out.append("///|")
            if is_array_type(t):
                out.append("let %s : %s = FixedArray::make(%d, %s)" % (
                    mb, mbt_type(t), init, ELEM_ZERO[t[1]]))
            else:
                t0, code = init_value(init, t)
                out.append("let %s : Ref[%s] = { val: %s }" % (mb, mbt_type(t), literal_conv(code, t0, t)))
            out.append("")


def label_fn_name(fd, lname):
    return mb_ident(fd.name + "_" + lname)


def gen_labels(fd, base_env):
    """Statement functions (LABELS) as private top-level functions."""
    out = []
    for lab in fd.labels:
        lname = lab[0].name
        params = [p.name for p in lab[1]]
        argts, rt = fd.label_types[lname]
        ctx = Ctx(fd)
        ctx.env = dict(base_env)
        ctx.labels = {}
        parts = []
        for p, t in zip(params, argts):
            mb = mb_ident(p)
            ctx.env[p] = Var("local", mb, t, assignable=False)
            parts.append("%s : %s" % (mb, mbt_type(t)))
        body = [b for b in lab[2:] if head(b) != "declare"]
        assert len(body) == 1
        c, t = expr(ctx, body[0])
        out.append("///|")
        out.append("fn %s(%s) -> %s {" % (label_fn_name(fd, lname), ", ".join(parts), mbt_type(rt)))
        out.append("  " + strip_paren(conv(c, t, rt)))
        out.append("}")
        out.append("")
    return "\n".join(out)


def gen_function(fd):
    ctx = Ctx(fd)
    assigned = assigned_vars(fd.body)
    consts = static_consts(fd)
    # statics
    for nm, typ, init in fd.statics:
        form = fd.static_inits.get(nm, init)
        t0, _ = init_value(form, typ, consts)
        t = typ or t0
        mb = static_name(fd, nm)
        if isinstance(t, tuple):
            ctx.env[nm] = Var("array", mb, t)
        elif nm in assigned:
            ctx.env[nm] = Var("static", mb, t)
        else:
            ctx.env[nm] = Var("const", mb, t, assignable=False)
    label_code = ""
    if fd.labels:
        label_code = gen_labels(fd, ctx.env)
        ctx.labels = {lab[0].name: label_fn_name(fd, lab[0].name) for lab in fd.labels}
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
    # common blocks
    for nm, (part, off, t) in fd.displaced.items():
        ctx.env[nm] = Var("array", mb_ident(part), t, off=(str(off) if off else None))
    for nm, form in fd.smacros.items():
        if isinstance(form, Sym):
            ctx.env[nm] = ctx.env[form.name]
        else:
            ctx.env[nm] = common_var(form)
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
        if isinstance(typ, tuple) or (head(init) == "make-array" and typ != "S"):
            t0, code = init_value(init, typ, consts)
            t = typ or t0
            if code is None:
                n = init[1]
                c, _ = expr(ctx, n)
                code = "FixedArray::make(%s, %s)" % (c, ELEM_ZERO[t[1]])
            pre.append("let %s : %s = %s" % (mb, mbt_type(t), code))
            ctx.env[nm] = Var("array", mb, t)
            continue
        t0, code = init_value(init, typ, consts)
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
    if label_code:
        lines.append(label_code)
    lines.append("///|")
    lines.append("/// Translated from %s %s (%s/%s.lisp)." % (LIB["what"], fd.name.upper(), LIB["srcrel"], fd.file))
    sigline = "pub fn %s(%s) -> %s%s {" % (mb_fn_name(fd.name), ", ".join(sig_parts), rt,
                                           " raise" if fd.raises else "")
    lines.append(sigline)
    for p in pre:
        lines.append("  " + p)
    if fd.blockdata:
        ctx.ind = 0
        block(ctx, fd.body)
        lines.extend(ctx.lines)
        lines.append("}")
        return "\n".join(lines) + "\n"
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
# Reference tests of the share packages (--lib=NAME --reference-test)
#
# Each case is a pair of programs, one in Lisp (run under SBCL on the f2cl
# code itself) and one in MoonBit, that call the routines and render every
# result with the same primitives: (rd x) " d<IEEE bits>", (ri n) " i<n>",
# (rb b) " bT"/" bF", (rc z) " c<re bits>,<im bits>", (ra array) " |" and
# the elements.  The text the routines print (Fortran unit 6) is appended as
# " s\"...\"".  <lib>/sbcl_reference_wbtest.mbt asserts that the MoonBit
# rendering equals the Lisp one.

SHARE_REF_LISP_HEAD = r"""
(setf *read-default-float-format* 'double-float)
(load "%(num)s/f2cl-lib-package.lisp")
(load "%(num)s/f2cl-lib.lisp")
(defvar *out* *standard-output*)
(defun bits (x) (sb-kernel:double-float-bits x))
(defun rd (x) (format *out* " d~D" (bits x)))
(defun ri (n) (format *out* " i~D" n))
(defun rb (b) (format *out* " b~A" (if b "T" "F")))
(defun rc (z) (format *out* " c~D,~D" (bits (realpart z)) (bits (imagpart z))))
(defun rv (v)
  (etypecase v
    (double-float (rd v))
    (integer (ri v))
    (complex (rc v))
    (symbol (rb v))))
(defun mix (h w)
  (logand (* (logxor h (logand w #xFFFFFFFFFFFFFFFF)) 1099511628211) #xFFFFFFFFFFFFFFFF))
;; arrays of more than 64 elements are rendered as an FNV-1a hash of their
;; bit patterns
(defun ra (a)
  (if (<= (length a) 64)
      (progn (format *out* " |") (loop for v across a do (rv v)))
      (let ((h 14695981039346656037))
        (loop for v across a do
          (etypecase v
            (double-float (setf h (mix h (bits v))))
            (integer (setf h (mix h v)))
            (complex (setf h (mix (mix h (bits (realpart v))) (bits (imagpart v)))))))
        (format *out* " |h~D:~D" (length a) h))))
(defun quote-text (s)
  (with-output-to-string (o)
    (loop for c across s do
      (case c
        (#\Newline (write-string "\\n" o))
        (#\" (write-string "\\\"" o))
        (#\\ (write-string "\\\\" o))
        (t (write-char c o))))))
(defun run (k thunk)
  (format *out* "~D:" k)
  (clrhash f2cl-lib::*lun-hash*)
  (let* ((text (make-string-output-stream))
         (ok (handler-case (let ((*standard-output* text)) (funcall thunk) t)
               (error (e) (format *out* " ERROR ~A" (type-of e)) nil))))
    (when ok
      (format *out* " s\"~A\"" (quote-text (get-output-stream-string text)))))
  (terpri *out*))
(defun dvec (&rest xs) (make-array (length xs) :element-type 'double-float :initial-contents (mapcar (lambda (x) (float x 1d0)) xs)))
(defun ivec (n) (make-array n :element-type 'f2cl-lib:integer4 :initial-element 0))
(defun dzeros (n) (make-array n :element-type 'double-float :initial-element 0d0))
(defun zvec (&rest xs) (make-array (length xs) :element-type '(complex double-float) :initial-contents (mapcar (lambda (x) (coerce x '(complex double-float))) xs)))
(defun zzeros (n) (make-array n :element-type '(complex double-float) :initial-element #c(0d0 0d0)))
"""

SHARE_REF_MBT_HEAD = """// Generated by tools/f2cl2mbt.py --lib=%(lib)s --reference-test; do not edit.
// Differential test against the f2cl Lisp of Maxima's %(src)s run under
// SBCL 2.6.9: each case runs the same calls in Lisp and in MoonBit and
// renders every result as IEEE bit patterns, plus the text printed on
// Fortran unit 6.

///|
fn rd(s : StringBuilder, x : Double) -> Unit {
  s.write_string(" d" + x.reinterpret_as_int64().to_string())
}

///|
fn ri(s : StringBuilder, n : Int) -> Unit {
  s.write_string(" i" + n.to_string())
}

///|
fn rb(s : StringBuilder, b : Bool) -> Unit {
  s.write_string(if b { " bT" } else { " bF" })
}

///|
fn rc(s : StringBuilder, z : Complex) -> Unit {
  s.write_string(
    " c" + z.re.reinterpret_as_int64().to_string() + "," +
    z.im.reinterpret_as_int64().to_string(),
  )
}

///|
fn mix(h : UInt64, w : Int64) -> UInt64 {
  (h ^ w.reinterpret_as_uint64()) * 1099511628211UL
}

///|
/// Arrays of more than 64 elements are rendered as an FNV-1a hash of their
/// bit patterns.
fn rhash(s : StringBuilder, n : Int, h : UInt64) -> Unit {
  s.write_string(" |h" + n.to_string() + ":" + h.to_string())
}

///|
fn rad(s : StringBuilder, a : FixedArray[Double]) -> Unit {
  if a.length() > 64 {
    let mut h = 14695981039346656037UL
    for x in a {
      h = mix(h, x.reinterpret_as_int64())
    }
    rhash(s, a.length(), h)
    return
  }
  s.write_string(" |")
  for x in a {
    rd(s, x)
  }
}

///|
fn rai(s : StringBuilder, a : FixedArray[Int]) -> Unit {
  if a.length() > 64 {
    let mut h = 14695981039346656037UL
    for x in a {
      h = mix(h, x.to_int64())
    }
    rhash(s, a.length(), h)
    return
  }
  s.write_string(" |")
  for x in a {
    ri(s, x)
  }
}

///|
fn rac(s : StringBuilder, a : FixedArray[Complex]) -> Unit {
  if a.length() > 64 {
    let mut h = 14695981039346656037UL
    for x in a {
      h = mix(mix(h, x.re.reinterpret_as_int64()), x.im.reinterpret_as_int64())
    }
    rhash(s, a.length(), h)
    return
  }
  s.write_string(" |")
  for x in a {
    rc(s, x)
  }
}

///|
fn quote_text(t : String) -> String {
  let sb = StringBuilder()
  for c in t {
    match c {
      '\\n' => sb.write_string("\\\\n")
      '"' => sb.write_string("\\\\\\"")
      '\\\\' => sb.write_string("\\\\\\\\")
      _ => sb.write_char(c)
    }
  }
  sb.to_string()
}

///|
/// Run `body`, capturing what the routines print.
fn ref_case(body : (StringBuilder) -> Unit raise) -> String raise {
  let s = StringBuilder()
  let text = StringBuilder()
  let saved = @f2cl.output_hook.val
  @f2cl.output_hook.val = t => text.write_string(t)
  body(s) catch {
    e => {
      @f2cl.output_hook.val = saved
      raise e
    }
  }
  @f2cl.output_hook.val = saved
  s.write_string(" s\\"" + quote_text(text.to_string()) + "\\"")
  s.to_string()
}

///|
fn dvec(xs : Array[Double]) -> FixedArray[Double] {
  FixedArray::from_array(xs)
}

///|
fn cvec(xs : Array[(Double, Double)]) -> FixedArray[Complex] {
  FixedArray::from_array(xs.map(p => cplx(p.0, p.1)))
}
"""


def mbt_lit(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lisp_d(x):
    return lf(x)


# --- lbfgs ------------------------------------------------------------------

LBFGS_REF_LISP = r"""
(defun rosen (n x g)
  (let ((f 0d0))
    (loop for j from 0 below n by 2 do
      (let* ((t1 (- 1d0 (aref x j)))
             (t2 (* 10d0 (- (aref x (1+ j)) (* (aref x j) (aref x j))))))
        (setf (aref g (1+ j)) (* 20d0 t2))
        (setf (aref g j) (* -2d0 (+ (* (aref x j) (aref g (1+ j))) t1)))
        (setf f (+ f (* t1 t1) (* t2 t2)))))
    f))
(defun quartic (n x g)
  (let ((f 0d0))
    (loop for j from 0 below n do
      (let ((d (- (aref x j) (float (1+ j) 1d0))))
        (setf (aref g j) (* 4d0 d d d))
        (setf f (+ f (* d d d d)))))
    f))
(defun badgrad (n x g)
  (let ((f (rosen n x g)))
    (loop for j from 0 below n do (setf (aref g j) (- (aref g j))))
    f))
(defun lb-run (fun n m ip1 ip2 eps maxcall)
  (let ((x (dzeros n)) (g (dzeros n)) (diag (dzeros n)) (scache (dzeros n))
        (w (dzeros (+ (* n (+ (* 2 m) 1)) (* 2 m))))
        (iprint (make-array 2 :element-type 'f2cl-lib:integer4 :initial-contents (list ip1 ip2)))
        (iflag 0) (f 0d0) (calls 0))
    (/blockdata-lb2/)
    (loop for j from 0 below n by 2 do (setf (aref x j) -1.2d0 (aref x (1+ j)) 1d0))
    (loop
      (setf f (funcall fun n x g))
      (multiple-value-bind (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12)
          (lbfgs n m x f g nil diag iprint eps (sb-kernel:make-double-float #x3CA00000 1) w iflag scache)
        (declare (ignore v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v12))
        (setf iflag v11))
      (incf calls)
      (when (or (<= iflag 0) (>= calls maxcall)) (return)))
    (ri iflag) (ri calls) (rd f) (ra x) (ra scache) (ra diag)))
"""

LBFGS_REF_MBT = """
///|
fn rosen(n : Int, x : FixedArray[Double], g : FixedArray[Double]) -> Double {
  let mut f = 0.0
  let mut j = 0
  while j < n {
    let t1 = 1.0 - x[j]
    let t2 = 10.0 * (x[j + 1] - x[j] * x[j])
    g[j + 1] = 20.0 * t2
    g[j] = -2.0 * (x[j] * g[j + 1] + t1)
    f = f + t1 * t1 + t2 * t2
    j = j + 2
  }
  f
}

///|
fn quartic(n : Int, x : FixedArray[Double], g : FixedArray[Double]) -> Double {
  let mut f = 0.0
  for j in 0..<n {
    let d = x[j] - (j + 1).to_double()
    g[j] = 4.0 * d * d * d
    f = f + d * d * d * d
  }
  f
}

///|
fn badgrad(n : Int, x : FixedArray[Double], g : FixedArray[Double]) -> Double {
  let f = rosen(n, x, g)
  for j in 0..<n {
    g[j] = -g[j]
  }
  f
}

///|
fn lb_run(
  s : StringBuilder,
  fun : (Int, FixedArray[Double], FixedArray[Double]) -> Double,
  n : Int,
  m : Int,
  ip1 : Int,
  ip2 : Int,
  eps : Double,
  maxcall : Int,
) -> Unit {
  let x = FixedArray::make(n, 0.0)
  let g = FixedArray::make(n, 0.0)
  let diag = FixedArray::make(n, 0.0)
  let scache = FixedArray::make(n, 0.0)
  let w = FixedArray::make(n * (2 * m + 1) + 2 * m, 0.0)
  let iprint : FixedArray[Int] = [ip1, ip2]
  let mut iflag = 0
  let mut f = 0.0
  let mut calls = 0
  blockdata_lb2()
  let mut j = 0
  while j < n {
    x[j] = -1.2
    x[j + 1] = 1.0
    j = j + 2
  }
  while true {
    f = fun(n, x, g)
    let (_, fl) = lbfgs(
      n, m, x, f, g, false, diag, iprint, eps,
      0x3CA0000000000001L.reinterpret_as_double(), w, iflag, scache,
    )
    iflag = fl
    calls = calls + 1
    if iflag <= 0 || calls >= maxcall {
      break
    }
  }
  ri(s, iflag)
  ri(s, calls)
  rd(s, f)
  rad(s, x)
  rad(s, scache)
  rad(s, diag)
}
"""

LBFGS_CASES = []
for fun, n, m, ip, eps, mx in [
        ("rosen", 8, 5, (1, 0), 1e-5, 200), ("rosen", 8, 25, (1, 0), 1e-3, 100),
        ("rosen", 4, 3, (1, 3), 1e-4, 200), ("rosen", 2, 7, (2, 2), 1e-8, 300),
        ("quartic", 4, 25, (1, 0), 1e-4, 100), ("quartic", 6, 4, (-1, 0), 1e-12, 10),
        ("badgrad", 4, 5, (1, 0), 1e-5, 50), ("rosen", 100, 5, (5, 1), 1e-5, 500),
        ("quartic", 2, 25, (1, 1), 1e-10, 100)]:
    LBFGS_CASES.append(("lbfgs %s n=%d m=%d" % (fun, n, m),
                        "(lb-run #'%s %d %d %d %d %s %d)" % (fun, n, m, ip[0], ip[1], lf(eps), mx),
                        "lb_run(s, %s, %d, %d, %d, %d, %s, %d)" % (fun, n, m, ip[0], ip[1], mf(eps), mx)))


def share_ref_config(lib):
    num = os.path.dirname(DEFAULT_SRC)
    if lib == "lbfgs":
        return dict(src="share/lbfgs", pre=[], lisp=LBFGS_REF_LISP, mbt=LBFGS_REF_MBT,
                    cases=LBFGS_CASES, files=LIB["files"])
    if lib == "odepack":
        d = os.path.join(SHARE_DIR, "odepack")
        return dict(src="share/odepack", pre=[os.path.join(d, "package.lisp")],
                    lisp=ODEPACK_REF_LISP, mbt=ODEPACK_REF_MBT, cases=ODEPACK_CASES,
                    files=LIB["files"])
    if lib == "lapack":
        d = os.path.join(SHARE_DIR, "lapack")
        return dict(src="share/lapack", pre=[os.path.join(d, "lapack-package.lisp")],
                    lisp=LAPACK_REF_LISP, mbt=LAPACK_REF_MBT, cases=LAPACK_CASES,
                    files=LIB["files"])
    raise SystemExit("no reference test for %s" % lib)


def gen_share_reference_test(lib, out_dir):
    import subprocess
    import tempfile
    cfg = share_ref_config(lib)
    num = os.path.dirname(DEFAULT_SRC)
    lines = [SHARE_REF_LISP_HEAD % {"num": num}]
    for p in cfg["pre"]:
        lines.append('(load "%s")' % p)
    for p in cfg["files"]:
        # SBCL 2.6.9's arm64 back end fails on zlaqr5 (an assembler
        # TYPE-ERROR, which also makes the reference Maxima's load(lapack)
        # fail); it is only reached for matrices of order > 75, so it is
        # loaded with the interpreter here.
        mode = ":interpret" if os.path.basename(p) == "zlaqr5.lisp" else ":compile"
        lines.append('(let ((*error-output* (make-broadcast-stream)) (sb-ext:*evaluator-mode* %s)) '
                     '(handler-bind ((warning #\'muffle-warning)) (load "%s")))' % (mode, p))
    lines.append(cfg["lisp"])
    for k, (name, lcode, _) in enumerate(cfg["cases"]):
        lines.append("(cl-user::run %d (lambda () %s))" % (k, lcode))
    tmpdir = tempfile.mkdtemp()
    lp = os.path.join(tmpdir, "ref_run.lisp")
    with open(lp, "w") as f:
        f.write("\n".join(lines) + "\n")
    proc = subprocess.run(["sbcl", "--script", lp], capture_output=True, text=True)
    res = {}
    for line in proc.stdout.splitlines():
        if ":" in line and line.split(":")[0].isdigit():
            k, rest = line.split(":", 1)
            res[int(k)] = rest
    if not res:
        print(lp, proc.stdout[-3000:], proc.stderr[-3000:], file=sys.stderr)
    mb = [SHARE_REF_MBT_HEAD % {"lib": lib, "src": cfg["src"]}, cfg["mbt"]]
    nerr = 0
    for k, (name, _, mcode) in enumerate(cfg["cases"]):
        exp = res.get(k)
        if exp is None or not exp.endswith("\"") or " s\"" not in exp:
            nerr += 1
            print("case %d (%s): %s" % (k, name, exp), file=sys.stderr)
            continue
        mb.append("///|")
        mb.append('test "sbcl reference %d: %s" {' % (k, name))
        mb.append("  let r = ref_case(s => {")
        for l in mcode.split("\n"):
            mb.append("    " + l)
        mb.append("  })")
        mb.append("  assert_eq(r, %s)" % mbt_lit(exp))
        mb.append("}")
        mb.append("")
    with open(os.path.join(out_dir, "sbcl_reference_wbtest.mbt"), "w") as f:
        f.write("\n".join(mb))
    print("reference cases %d, skipped (Lisp signalled an error) %d" % (len(cfg["cases"]), nerr),
          file=sys.stderr)


ODEPACK_REF_LISP = r"""
(defun rob-f (neq tt y ydot)
  (declare (ignore neq tt))
  (setf (aref ydot 0) (+ (* -0.04d0 (aref y 0)) (* 1d4 (aref y 1) (aref y 2))))
  (setf (aref ydot 2) (* 3d7 (aref y 1) (aref y 1)))
  (setf (aref ydot 1) (- (- (aref ydot 0)) (aref ydot 2)))
  nil)
(defun rob-jac (neq tt y ml mu pd nrpd)
  (declare (ignore neq tt ml mu))
  (setf (aref pd 0) -0.04d0
        (aref pd 1) 0.04d0
        (aref pd 2) 0d0
        (aref pd nrpd) (* 1d4 (aref y 2))
        (aref pd (+ nrpd 1)) (- (* -1d4 (aref y 2)) (* 6d7 (aref y 1)))
        (aref pd (+ nrpd 2)) (* 6d7 (aref y 1))
        (aref pd (* 2 nrpd)) (* 1d4 (aref y 1))
        (aref pd (+ (* 2 nrpd) 1)) (* -1d4 (aref y 1))
        (aref pd (+ (* 2 nrpd) 2)) 0d0)
  nil)
(defun osc-f (neq tt y ydot)
  (declare (ignore neq))
  (setf (aref ydot 0) (aref y 1))
  (setf (aref ydot 1) (- (* -1d0 (aref y 0)) (* 0.1d0 (aref y 1)) (sin tt)))
  nil)
(defun osc-jac (neq tt y ml mu pd nrpd)
  (declare (ignore neq tt y ml mu))
  (setf (aref pd 0) 0d0
        (aref pd 1) -1d0
        (aref pd nrpd) 1d0
        (aref pd (+ nrpd 1)) -0.1d0)
  nil)
(defun ode-run (f jac mf itol rtol atols y0 t0 tout0 nout factor maxima-style)
  (let* ((neq (length y0))
         (lrw (if (= mf 10) (+ 20 (* 16 neq)) (+ 22 (* 9 neq) (* neq neq))))
         (liw (if (= mf 10) 20 (+ 20 neq)))
         (rwork (dzeros lrw)) (iwork (ivec liw))
         (y (apply #'dvec y0))
         (tt (float t0 1d0)) (tout (float tout0 1d0)) (istate 1))
    (dotimes (k nout)
      (when maxima-style
        (setf y (apply #'dvec y0) tt (float t0 1d0)))
      (multiple-value-bind (i0 i1 i2 rt i4 i5 i6 i7 i8 ri)
          (odepack:dlsode f (make-array 1 :element-type 'f2cl-lib:integer4 :initial-element neq)
                          y tt tout itol (dvec rtol) (apply #'dvec atols) 1 istate 0
                          rwork lrw iwork liw jac mf)
        (declare (ignore i0 i1 i2 i4 i5 i6 i7 i8))
        (setf tt rt istate ri))
      (rd tt) (ri istate) (ra y)
      (when (< istate 0) (return))
      (if (= factor 0) (setf tout (+ tout tout0)) (setf tout (* tout factor))))
    (ra iwork) (ra rwork)))
"""

ODEPACK_REF_MBT = """
///|
fn rob_f(
  _neq : FixedArray[Int],
  _t : Double,
  y : FixedArray[Double],
  yo : Int,
  ydot : FixedArray[Double],
  dofs : Int,
) -> Unit raise {
  ydot[dofs + 0] = -0.04 * y[yo + 0] + 1.0e4 * y[yo + 1] * y[yo + 2]
  ydot[dofs + 2] = 3.0e7 * y[yo + 1] * y[yo + 1]
  ydot[dofs + 1] = -ydot[dofs + 0] - ydot[dofs + 2]
}

///|
fn rob_jac(
  _neq : FixedArray[Int],
  _t : Double,
  y : FixedArray[Double],
  _ml : Int,
  _mu : Int,
  pd : FixedArray[Double],
  po : Int,
  nrpd : Int,
) -> Unit raise {
  pd[po + 0] = -0.04
  pd[po + 1] = 0.04
  pd[po + 2] = 0.0
  pd[po + nrpd] = 1.0e4 * y[2]
  pd[po + nrpd + 1] = -1.0e4 * y[2] - 6.0e7 * y[1]
  pd[po + nrpd + 2] = 6.0e7 * y[1]
  pd[po + 2 * nrpd] = 1.0e4 * y[1]
  pd[po + 2 * nrpd + 1] = -1.0e4 * y[1]
  pd[po + 2 * nrpd + 2] = 0.0
}

///|
fn osc_f(
  _neq : FixedArray[Int],
  t : Double,
  y : FixedArray[Double],
  yo : Int,
  ydot : FixedArray[Double],
  dofs : Int,
) -> Unit raise {
  ydot[dofs + 0] = y[yo + 1]
  ydot[dofs + 1] = -1.0 * y[yo + 0] - 0.1 * y[yo + 1] - @f2cl.f_sin(t)
}

///|
fn osc_jac(
  _neq : FixedArray[Int],
  _t : Double,
  _y : FixedArray[Double],
  _ml : Int,
  _mu : Int,
  pd : FixedArray[Double],
  po : Int,
  nrpd : Int,
) -> Unit raise {
  pd[po + 0] = 0.0
  pd[po + 1] = -1.0
  pd[po + nrpd] = 1.0
  pd[po + nrpd + 1] = -0.1
}

///|
fn ode_run(
  s : StringBuilder,
  f : (FixedArray[Int], Double, FixedArray[Double], Int, FixedArray[Double], Int) -> Unit raise,
  jac : (FixedArray[Int], Double, FixedArray[Double], Int, Int, FixedArray[Double], Int, Int) -> Unit raise,
  mf : Int,
  itol : Int,
  rtol : Double,
  atols : Array[Double],
  y0 : Array[Double],
  t0 : Double,
  tout0 : Double,
  nout : Int,
  factor : Double,
  maxima_style : Bool,
) -> Unit raise {
  let neq = y0.length()
  let lrw = if mf == 10 { 20 + 16 * neq } else { 22 + 9 * neq + neq * neq }
  let liw = if mf == 10 { 20 } else { 20 + neq }
  let rwork = FixedArray::make(lrw, 0.0)
  let iwork = FixedArray::make(liw, 0)
  let mut y = dvec(y0)
  let mut tt = t0
  let mut tout = tout0
  let mut istate = 1
  for _k in 0..<nout {
    if maxima_style {
      y = dvec(y0)
      tt = t0
    }
    let (rt, ri_) = dlsode(
      f, [neq], y, tt, tout, itol, [rtol], dvec(atols), 1, istate, 0, rwork, lrw,
      iwork, liw, jac, mf,
    )
    tt = rt
    istate = ri_
    rd(s, tt)
    ri(s, istate)
    rad(s, y)
    if istate < 0 {
      break
    }
    if factor == 0.0 {
      tout = tout + tout0
    } else {
      tout = tout * factor
    }
  }
  rai(s, iwork)
  rad(s, rwork)
}
"""

ODEPACK_CASES = []


def _ode_case(name, f, jac, mf, itol, rtol, atols, y0, t0, tout0, nout, factor, mstyle):
    ODEPACK_CASES.append((
        name,
        "(ode-run #'%s #'%s %d %d %s (list %s) (list %s) %s %s %d %s %s)" % (
            f.replace("_", "-"), jac.replace("_", "-"), mf, itol, lf(rtol),
            " ".join(lf(a) for a in atols), " ".join(lf(v) for v in y0), lf(t0), lf(tout0),
            nout, lf(factor) if factor else "0", "t" if mstyle else "nil"),
        "ode_run(s, %s, %s, %d, %d, %s, [%s], [%s], %s, %s, %d, %s, %s)" % (
            f, jac, mf, itol, mf_(rtol), ", ".join(mf_(a) for a in atols),
            ", ".join(mf_(v) for v in y0), mf_(t0), mf_(tout0), nout, mf_(factor),
            "true" if mstyle else "false")))


def mf_(x):
    return mf(float(x))


_ode_case("robertson mf=21 (rtest_dlsode)", "rob_f", "rob_jac", 21, 2, 1e-4, [1e-6, 1e-10, 1e-6],
          [1.0, 0.0, 0.0], 0.0, 0.4, 12, 10.0, True)
_ode_case("robertson mf=22", "rob_f", "rob_jac", 22, 2, 1e-4, [1e-6, 1e-10, 1e-6],
          [1.0, 0.0, 0.0], 0.0, 0.4, 12, 10.0, False)
_ode_case("robertson mf=21 itol=1", "rob_f", "rob_jac", 21, 1, 1e-6, [1e-8],
          [1.0, 0.0, 0.0], 0.0, 0.4, 8, 10.0, False)
_ode_case("robertson mf=10 (excess work)", "rob_f", "rob_jac", 10, 2, 1e-4, [1e-6, 1e-10, 1e-6],
          [1.0, 0.0, 0.0], 0.0, 0.4, 6, 10.0, True)
_ode_case("oscillator mf=10", "osc_f", "osc_jac", 10, 1, 1e-8, [1e-10],
          [1.0, 0.0], 0.0, 0.5, 20, 0, True)
_ode_case("oscillator mf=21", "osc_f", "osc_jac", 21, 1, 1e-6, [1e-8],
          [1.0, 0.0], 0.0, 0.5, 20, 0, False)
_ode_case("oscillator mf=22", "osc_f", "osc_jac", 22, 1, 1e-6, [1e-8],
          [1.0, 0.0], 0.0, 0.5, 20, 0, True)
_ode_case("illegal input (negative rtol)", "osc_f", "osc_jac", 22, 1, -1e-6, [1e-8],
          [1.0, 0.0], 0.0, 0.5, 2, 0, True)
_ode_case("tout = t", "osc_f", "osc_jac", 10, 1, 1e-6, [1e-8],
          [1.0, 0.0], 0.0, 0.0, 1, 0, True)
LAPACK_REF_LISP = r"""
(defun cm (rows)
  (let* ((m (length rows)) (n (length (first rows))) (a (dzeros (* m n))))
    (loop for i from 0 for r in rows do
      (loop for j from 0 for v in r do (setf (aref a (+ i (* j m))) (float v 1d0))))
    a))
(defun zcm (rows)
  (let* ((m (length rows)) (n (length (first rows))) (a (zzeros (* m n))))
    (loop for i from 0 for r in rows do
      (loop for j from 0 for v in r do
        (setf (aref a (+ i (* j m))) (coerce v '(complex double-float)))))
    a))
(defun gen (m n seed)
  ;; deterministic test matrix: small integers / 64, column-major
  (let ((a (dzeros (* m n))))
    (dotimes (j n)
      (dotimes (i m)
        (setf (aref a (+ i (* j m)))
              (/ (float (- (mod (+ (* (+ i 1) 37) (* (+ j 1) 17) (* seed 101) (* i j 7)) 199) 99) 1d0) 64d0))))
    a))
(defun zgen (m n seed herm)
  (let ((a (zzeros (* m n))))
    (dotimes (j n)
      (dotimes (i m)
        (let ((re (/ (float (- (mod (+ (* (+ i 1) 37) (* (+ j 1) 17) (* seed 101) (* i j 7)) 199) 99) 1d0) 64d0))
              (im (/ (float (- (mod (+ (* (+ i 1) 13) (* (+ j 1) 29) (* seed 53) (* i j 3)) 151) 75) 1d0) 64d0)))
          (setf (aref a (+ i (* j m))) (complex re im)))))
    (when herm
      (dotimes (j n)
        (dotimes (i m)
          (cond ((= i j) (setf (aref a (+ i (* j m))) (complex (realpart (aref a (+ i (* j m)))) 0d0)))
                ((> i j) (setf (aref a (+ i (* j m))) (conjugate (aref a (+ j (* i m))))))))))
    a))
(defmacro rvals (call) `(dolist (v (remove nil (multiple-value-list ,call))) (rv v)))
(defun t-dgemm (ta tb m n k alpha a lda b ldb beta c ldc)
  (rvals (blas::dgemm ta tb m n k alpha a lda b ldb beta c ldc))
  (ra c))
(defun t-dgesv (n nrhs a b)
  (let ((ipiv (ivec n)))
    (rvals (lapack::dgesv n nrhs a n ipiv b n 0))
    (ra a) (ra ipiv) (ra b)))
(defun t-dgeqrf (m n a)
  (let ((tau (dzeros (min m n))) (work (dzeros 1)))
    (rvals (lapack::dgeqrf m n a m tau work -1 0))
    (ra work)
    (let ((work (dzeros (floor (aref work 0)))))
      (rvals (lapack::dgeqrf m n a m tau work (length work) 0))
      (ra a) (ra tau))))
(defun t-dgeev (n a jl jr)
  (let ((wr (dzeros n)) (wi (dzeros n)) (vl (dzeros (* n n))) (vr (dzeros (* n n)))
        (work (dzeros 1)))
    (rvals (lapack::dgeev jl jr n a n wr wi vl n vr n work -1 0))
    (ra work)
    (let ((work (dzeros (floor (aref work 0)))))
      (rvals (lapack::dgeev jl jr n a n wr wi vl n vr n work (length work) 0))
      (ra a) (ra wr) (ra wi) (ra vl) (ra vr))))
(defun t-dgesvd (m n a ju jv)
  (let ((s (dzeros (min m n))) (u (dzeros (* m m))) (vt (dzeros (* n n))) (work (dzeros 1)))
    (rvals (lapack::dgesvd ju jv m n a m s u m vt n work -1 0))
    (ra work)
    (let ((work (dzeros (floor (aref work 0)))))
      (rvals (lapack::dgesvd ju jv m n a m s u m vt n work (length work) 0))
      (ra s) (ra u) (ra vt))))
(defun t-dlange (norm m n a)
  (rvals (lapack::dlange norm m n a m (dzeros m))))
(defun t-zlange (norm m n a)
  (rvals (lapack::zlange norm m n a m (dzeros m))))
(defun t-zgeev (n a jl jr)
  (let ((w (zzeros n)) (vl (zzeros (* n n))) (vr (zzeros (* n n))) (work (zzeros 1))
        (rwork (dzeros (* 2 n))))
    (rvals (lapack::zgeev jl jr n a n w vl n vr n work -1 rwork 0))
    (ra work)
    (let ((work (zzeros (floor (realpart (aref work 0))))))
      (rvals (lapack::zgeev jl jr n a n w vl n vr n work (length work) rwork 0))
      (ra a) (ra w) (ra vl) (ra vr))))
(defun t-zheev (n a jz up)
  (let ((w (dzeros n)) (work (zzeros 1)) (rwork (dzeros (max 1 (- (* 3 n) 2)))))
    (rvals (lapack::zheev jz up n a n w work -1 rwork 0))
    (ra work)
    (let ((work (zzeros (floor (realpart (aref work 0))))))
      (rvals (lapack::zheev jz up n a n w work (length work) rwork 0))
      (ra a) (ra w))))
"""

LAPACK_REF_MBT = """
///|
fn cm(rows : Array[Array[Double]]) -> FixedArray[Double] {
  let m = rows.length()
  let n = rows[0].length()
  let a = FixedArray::make(m * n, 0.0)
  for i, r in rows {
    for j, v in r {
      a[i + j * m] = v
    }
  }
  a
}

///|
fn zcm(rows : Array[Array[(Double, Double)]]) -> FixedArray[Complex] {
  let m = rows.length()
  let n = rows[0].length()
  let a = FixedArray::make(m * n, cplx(0.0, 0.0))
  for i, r in rows {
    for j, v in r {
      a[i + j * m] = cplx(v.0, v.1)
    }
  }
  a
}

///|
fn gen(m : Int, n : Int, seed : Int) -> FixedArray[Double] {
  let a = FixedArray::make(m * n, 0.0)
  for j in 0..<n {
    for i in 0..<m {
      let v = ((i + 1) * 37 + (j + 1) * 17 + seed * 101 + i * j * 7) % 199 - 99
      a[i + j * m] = v.to_double() / 64.0
    }
  }
  a
}

///|
fn zgen(m : Int, n : Int, seed : Int, herm : Bool) -> FixedArray[Complex] {
  let a = FixedArray::make(m * n, cplx(0.0, 0.0))
  for j in 0..<n {
    for i in 0..<m {
      let re = ((i + 1) * 37 + (j + 1) * 17 + seed * 101 + i * j * 7) % 199 - 99
      let im = ((i + 1) * 13 + (j + 1) * 29 + seed * 53 + i * j * 3) % 151 - 75
      a[i + j * m] = cplx(re.to_double() / 64.0, im.to_double() / 64.0)
    }
  }
  if herm {
    for j in 0..<n {
      for i in 0..<m {
        if i == j {
          a[i + j * m] = cplx(a[i + j * m].re, 0.0)
        } else if i > j {
          a[i + j * m] = c_conj(a[j + i * m])
        }
      }
    }
  }
  a
}

///|
fn imin(a : Int, b : Int) -> Int {
  if a < b {
    a
  } else {
    b
  }
}

///|
fn t_dgemm(
  s : StringBuilder,
  ta : String,
  tb : String,
  m : Int,
  n : Int,
  k : Int,
  alpha : Double,
  a : FixedArray[Double],
  lda : Int,
  b : FixedArray[Double],
  ldb : Int,
  beta : Double,
  c : FixedArray[Double],
  ldc : Int,
) -> Unit {
  dgemm(ta, tb, m, n, k, alpha, a, 0, lda, b, 0, ldb, beta, c, 0, ldc)
  rad(s, c)
}

///|
fn t_dgesv(
  s : StringBuilder,
  n : Int,
  nrhs : Int,
  a : FixedArray[Double],
  b : FixedArray[Double],
) -> Unit {
  let ipiv = FixedArray::make(n, 0)
  ri(s, dgesv(n, nrhs, a, n, ipiv, b, n, 0))
  rad(s, a)
  rai(s, ipiv)
  rad(s, b)
}

///|
fn t_dgeqrf(s : StringBuilder, m : Int, n : Int, a : FixedArray[Double]) -> Unit {
  let tau = FixedArray::make(imin(m, n), 0.0)
  let work0 = FixedArray::make(1, 0.0)
  ri(s, dgeqrf(m, n, a, m, tau, 0, work0, 0, -1, 0))
  rad(s, work0)
  let work = FixedArray::make(work0[0].to_int(), 0.0)
  ri(s, dgeqrf(m, n, a, m, tau, 0, work, 0, work.length(), 0))
  rad(s, a)
  rad(s, tau)
}

///|
fn t_dgeev(
  s : StringBuilder,
  n : Int,
  a : FixedArray[Double],
  jl : String,
  jr : String,
) -> Unit {
  let wr = FixedArray::make(n, 0.0)
  let wi = FixedArray::make(n, 0.0)
  let vl = FixedArray::make(n * n, 0.0)
  let vr = FixedArray::make(n * n, 0.0)
  let work0 = FixedArray::make(1, 0.0)
  ri(s, dgeev(jl, jr, n, a, n, wr, wi, vl, n, vr, n, work0, -1, 0))
  rad(s, work0)
  let work = FixedArray::make(work0[0].to_int(), 0.0)
  ri(s, dgeev(jl, jr, n, a, n, wr, wi, vl, n, vr, n, work, work.length(), 0))
  rad(s, a)
  rad(s, wr)
  rad(s, wi)
  rad(s, vl)
  rad(s, vr)
}

///|
fn t_dgesvd(
  s : StringBuilder,
  m : Int,
  n : Int,
  a : FixedArray[Double],
  ju : String,
  jv : String,
) -> Unit {
  let sv = FixedArray::make(imin(m, n), 0.0)
  let u = FixedArray::make(m * m, 0.0)
  let vt = FixedArray::make(n * n, 0.0)
  let work0 = FixedArray::make(1, 0.0)
  ri(s, dgesvd(ju, jv, m, n, a, m, sv, u, m, vt, n, work0, -1, 0))
  rad(s, work0)
  let work = FixedArray::make(work0[0].to_int(), 0.0)
  ri(s, dgesvd(ju, jv, m, n, a, m, sv, u, m, vt, n, work, work.length(), 0))
  rad(s, sv)
  rad(s, u)
  rad(s, vt)
}

///|
fn t_dlange(s : StringBuilder, norm : String, m : Int, n : Int, a : FixedArray[Double]) -> Unit {
  rd(s, dlange(norm, m, n, a, 0, m, FixedArray::make(m, 0.0), 0))
}

///|
fn t_zlange(s : StringBuilder, norm : String, m : Int, n : Int, a : FixedArray[Complex]) -> Unit {
  rd(s, zlange(norm, m, n, a, m, FixedArray::make(m, 0.0)))
}

///|
fn t_zgeev(
  s : StringBuilder,
  n : Int,
  a : FixedArray[Complex],
  jl : String,
  jr : String,
) -> Unit {
  let w = FixedArray::make(n, cplx(0.0, 0.0))
  let vl = FixedArray::make(n * n, cplx(0.0, 0.0))
  let vr = FixedArray::make(n * n, cplx(0.0, 0.0))
  let work0 = FixedArray::make(1, cplx(0.0, 0.0))
  let rwork = FixedArray::make(2 * n, 0.0)
  ri(s, zgeev(jl, jr, n, a, n, w, vl, n, vr, n, work0, -1, rwork, 0))
  rac(s, work0)
  let work = FixedArray::make(work0[0].re.to_int(), cplx(0.0, 0.0))
  ri(s, zgeev(jl, jr, n, a, n, w, vl, n, vr, n, work, work.length(), rwork, 0))
  rac(s, a)
  rac(s, w)
  rac(s, vl)
  rac(s, vr)
}

///|
fn t_zheev(
  s : StringBuilder,
  n : Int,
  a : FixedArray[Complex],
  jz : String,
  up : String,
) -> Unit {
  let w = FixedArray::make(n, 0.0)
  let work0 = FixedArray::make(1, cplx(0.0, 0.0))
  let rwork = FixedArray::make(if 3 * n - 2 > 1 { 3 * n - 2 } else { 1 }, 0.0)
  let (r1, r2) = zheev(jz, up, n, a, n, w, work0, -1, rwork, 0)
  ri(s, r1)
  ri(s, r2)
  rac(s, work0)
  let work = FixedArray::make(work0[0].re.to_int(), cplx(0.0, 0.0))
  let (q1, q2) = zheev(jz, up, n, a, n, w, work, work.length(), rwork, 0)
  ri(s, q1)
  ri(s, q2)
  rac(s, a)
  rad(s, w)
}
"""

LAPACK_CASES = []


def _lmat(rows):
    return "(cm '(%s))" % " ".join("(" + " ".join(lf(v) for v in r) + ")" for r in rows)


def _mmat(rows):
    return "cm([%s])" % ", ".join("[" + ", ".join(mf(float(v)) for v in r) + "]" for r in rows)


def _lzmat(rows):
    return "(zcm '(%s))" % " ".join(
        "(" + " ".join("#C(%s %s)" % (lf(re_), lf(im_)) for re_, im_ in r) + ")" for r in rows)


def _mzmat(rows):
    return "zcm([%s])" % ", ".join(
        "[" + ", ".join("(%s, %s)" % (mf(float(re_)), mf(float(im_))) for re_, im_ in r) + "]"
        for r in rows)


A4 = [[.35, .45, -.14, -.17], [.09, .07, -.54, .35], [-.44, -.33, -.03, .17], [.25, -.32, -.13, .11]]
B42 = [[1, 2], [3, 4], [5, 6], [7, 8]]
A43 = [[1, 2, 3], [4, 5, 6], [7, 8, 10], [-1, 0.5, 2]]
A34 = [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]
SYM = [[4, 1, -2, 2], [1, 2, 0, 1], [-2, 0, 3, -2], [2, 1, -2, -1]]
ROT = [[0, -1, 0], [1, 0, 0], [0, 0, 2]]
Z3 = [[(1, 2), (3, -1), (0, 0.5)], [(-2, 1), (0, 0), (4, 4)], [(1, 1), (2, -3), (-1, 0)]]
H3 = [[(2, 0), (1, -1), (0, 2)], [(1, 1), (3, 0), (-1, 0.5)], [(0, -2), (-1, -0.5), (1, 0)]]
ZI2 = [[(1, 0), (0, 0)], [(0, 0), (1, 0)]]


def _case(name, lisp, mbt):
    LAPACK_CASES.append((name, lisp, mbt))


for ta, tb, m, n, k, A, B in [("N", "N", 3, 2, 4, A34, B42), ("T", "N", 4, 2, 3, A34, [[1, 0], [2, 1], [0, 3]]),
                              ("N", "T", 4, 4, 2, B42, B42), ("T", "T", 2, 3, 4, B42, A34)]:
    lda = len(A)
    ldb = len(B)
    _case("dgemm %s%s" % (ta, tb),
          '(t-dgemm "%s" "%s" %d %d %d 1.5d0 %s %d %s %d -0.5d0 (dzeros %d) %d)' % (
              ta, tb, m, n, k, _lmat(A), lda, _lmat(B), ldb, m * n, m),
          't_dgemm(s, "%s", "%s", %d, %d, %d, 1.5, %s, %d, %s, %d, -0.5, FixedArray::make(%d, 0.0), %d)' % (
              ta, tb, m, n, k, _mmat(A), lda, _mmat(B), ldb, m * n, m))
_case("dgesv 4x4", "(t-dgesv 4 2 %s %s)" % (_lmat(A4), _lmat(B42)),
      "t_dgesv(s, 4, 2, %s, %s)" % (_mmat(A4), _mmat(B42)))
_case("dgesv singular", "(t-dgesv 3 1 %s %s)" % (_lmat([[1, 2, 3], [2, 4, 6], [1, 0, 1]]), _lmat([[1], [2], [3]])),
      "t_dgesv(s, 3, 1, %s, %s)" % (_mmat([[1, 2, 3], [2, 4, 6], [1, 0, 1]]), _mmat([[1], [2], [3]])))
for name, m, n, A in [("4x3", 4, 3, A43), ("3x4", 3, 4, A34), ("4x4", 4, 4, A4)]:
    _case("dgeqrf %s" % name, "(t-dgeqrf %d %d %s)" % (m, n, _lmat(A)),
          "t_dgeqrf(s, %d, %d, %s)" % (m, n, _mmat(A)))
for name, A, jl, jr in [("rtest_lapack", A4, "V", "V"), ("symmetric", SYM, "N", "V"),
                        ("rotation", ROT, "V", "N"), ("values only", A4, "N", "N")]:
    n = len(A)
    _case("dgeev %s" % name, '(t-dgeev %d %s "%s" "%s")' % (n, _lmat(A), jl, jr),
          't_dgeev(s, %d, %s, "%s", "%s")' % (n, _mmat(A), jl, jr))
for name, A, ju, jv in [("4x3 AA", A43, "A", "A"), ("3x4 AA", A34, "A", "A"), ("4x4 NN", A4, "N", "N"),
                        ("4x3 SS", A43, "S", "S")]:
    m, n = len(A), len(A[0])
    _case("dgesvd %s" % name, '(t-dgesvd %d %d %s "%s" "%s")' % (m, n, _lmat(A), ju, jv),
          't_dgesvd(s, %d, %d, %s, "%s", "%s")' % (m, n, _mmat(A), ju, jv))
for norm in ["M", "O", "I", "F", "1", "E"]:
    _case("dlange %s" % norm, '(t-dlange "%s" 4 4 %s)' % (norm, _lmat(A4)),
          't_dlange(s, "%s", 4, 4, %s)' % (norm, _mmat(A4)))
    _case("zlange %s" % norm, '(t-zlange "%s" 3 3 %s)' % (norm, _lzmat(Z3)),
          't_zlange(s, "%s", 3, 3, %s)' % (norm, _mzmat(Z3)))
for name, A, jl, jr in [("3x3 VV", Z3, "V", "V"), ("identity", ZI2, "V", "N"), ("hermitian", H3, "N", "V")]:
    n = len(A)
    _case("zgeev %s" % name, '(t-zgeev %d %s "%s" "%s")' % (n, _lzmat(A), jl, jr),
          't_zgeev(s, %d, %s, "%s", "%s")' % (n, _mzmat(A), jl, jr))
A4z = [[(v, 0) for v in r] for r in A4]
_case("zgeev real", '(t-zgeev 4 %s "N" "V")' % _lzmat(A4z), 't_zgeev(s, 4, %s, "N", "V")' % _mzmat(A4z))
_case("dgemm TN 50x60x70", '(t-dgemm "T" "N" 50 60 70 0.75d0 (gen 70 50 1) 70 (gen 70 60 2) 70 1.25d0 (gen 50 60 3) 50)',
      't_dgemm(s, "T", "N", 50, 60, 70, 0.75, gen(70, 50, 1), 70, gen(70, 60, 2), 70, 1.25, gen(50, 60, 3), 50)')
_case("dgesv 50x50", "(t-dgesv 50 3 (gen 50 50 4) (gen 50 3 5))", "t_dgesv(s, 50, 3, gen(50, 50, 4), gen(50, 3, 5))")
_case("dgeqrf 60x40", "(t-dgeqrf 60 40 (gen 60 40 6))", "t_dgeqrf(s, 60, 40, gen(60, 40, 6))")
_case("dgeqrf 70x90", "(t-dgeqrf 70 90 (gen 70 90 7))", "t_dgeqrf(s, 70, 90, gen(70, 90, 7))")
_case("dgeev 40x40", '(t-dgeev 40 (gen 40 40 8) "V" "V")', 't_dgeev(s, 40, gen(40, 40, 8), "V", "V")')
_case("dgeev 90x90", '(t-dgeev 90 (gen 90 90 9) "N" "V")', 't_dgeev(s, 90, gen(90, 90, 9), "N", "V")')
_case("dgesvd 45x30", '(t-dgesvd 45 30 (gen 45 30 10) "A" "A")', 't_dgesvd(s, 45, 30, gen(45, 30, 10), "A", "A")')
_case("dgesvd 30x45", '(t-dgesvd 30 45 (gen 30 45 11) "A" "A")', 't_dgesvd(s, 30, 45, gen(30, 45, 11), "A", "A")')
_case("dgesvd 80x20", '(t-dgesvd 80 20 (gen 80 20 12) "S" "N")', 't_dgesvd(s, 80, 20, gen(80, 20, 12), "S", "N")')
_case("dlange F 40x30", '(t-dlange "F" 40 30 (gen 40 30 13))', 't_dlange(s, "F", 40, 30, gen(40, 30, 13))')
_case("zgeev 30x30", '(t-zgeev 30 (zgen 30 30 14 nil) "V" "V")', 't_zgeev(s, 30, zgen(30, 30, 14, false), "V", "V")')
_case("zgeev 90x90", '(t-zgeev 90 (zgen 90 90 15 nil) "N" "V")', 't_zgeev(s, 90, zgen(90, 90, 15, false), "N", "V")')
_case("zheev 40x40", '(t-zheev 40 (zgen 40 40 16 t) "V" "U")', 't_zheev(s, 40, zgen(40, 40, 16, true), "V", "U")')
_case("zlange 1 25x35", '(t-zlange "1" 25 35 (zgen 25 35 17 nil))', 't_zlange(s, "1", 25, 35, zgen(25, 35, 17, false))')
for name, A, jz, up in [("3x3 V U", H3, "V", "U"), ("3x3 N U", H3, "N", "U"), ("3x3 V L", H3, "V", "L"),
                        ("identity", ZI2, "V", "U")]:
    n = len(A)
    _case("zheev %s" % name, '(t-zheev %d %s "%s" "%s")' % (n, _lzmat(A), jz, up),
          't_zheev(s, %d, %s, "%s", "%s")' % (n, _mzmat(A), jz, up))


# ---------------------------------------------------------------------------
# Driver

FNS = {}
FNS_MB = set()
COMMONS = {}        # common block name -> [(slot, type, init)]
COMMON_FILES = []   # files holding a common-block DEFSTRUCT
COMMON_SRC = {}     # common block name -> file stem


HEADER = """// Generated by tools/f2cl2mbt.py from Maxima's
// src/numerical/slatec/%s.lisp (f2cl translation of SLATEC/QUADPACK).
// Do not edit by hand; regenerate instead.

"""

MAXIMA_DIR = os.path.dirname(os.path.dirname(os.path.dirname(DEFAULT_SRC)))
SHARE_DIR = os.path.join(MAXIMA_DIR, "share")


def lisp_files(d, exclude=()):
    return sorted(os.path.join(d, f) for f in os.listdir(d)
                  if f.endswith(".lisp") and f[:-5] not in exclude)


# Signatures of the user-supplied functions of the share packages: DLSODE's
# right-hand side F(NEQ, T, Y, YDOT) and Jacobian JAC(NEQ, T, Y, ML, MU, PD,
# NROWPD).  Array arguments that DLSODE passes as sections of its work array
# come with their offsets.
ODEPACK_SIGS = {
    "f": Sig([("A", "I"), "D", ("AO", "D"), ("AO", "D")], [], True),
    "jac": Sig([("A", "I"), "D", ("A", "D"), "I", "I", ("AO", "D"), "I"], [], True),
}


def lib_config(name):
    if name == "slatec":
        return dict(name="slatec", out=DEFAULT_OUT, what="SLATEC routine",
                    srcrel="numerical/slatec", header=HEADER, hand=HAND, user_sigs={},
                    files=[os.path.join(DEFAULT_SRC, f) for f in sorted(os.listdir(DEFAULT_SRC))
                           if f.endswith(".lisp") and f not in SKIP_FILES])
    if name == "lbfgs":
        d = os.path.join(SHARE_DIR, "lbfgs")
        files = [os.path.join(d, f + ".lisp") for f in
                 ["lbfgs-daxpy", "lbfgs-ddot", "lb2", "lb1", "mcstep", "mcsrch", "lbfgs"]]
        return dict(name="lbfgs", out=os.path.join(ROOT, "lbfgs"), what="L-BFGS routine",
                    srcrel="share/lbfgs", hand=[], user_sigs={}, files=files,
                    header=share_header("share/lbfgs", "L-BFGS (Nocedal's LBFGS.F and MCSRCH.F)"))
    if name == "odepack":
        d = os.path.join(SHARE_DIR, "odepack", "src")
        files = [os.path.join(d, "dls001.cmn")] + [os.path.join(d, f + ".lisp") for f in [
            "dlsode", "dintdy", "dstode", "dgbfa", "dcfode", "dprepj", "dsolsy", "dewset",
            "dvnorm", "dsrcom", "dgefa", "dgesl", "dgbsl", "dscal", "ddot", "idamax", "dumach",
            "xerrwd", "xsetun", "xsetf", "ixsav", "iumach", "daxpy", "dumsum"]]
        return dict(name="odepack", out=os.path.join(ROOT, "odepack"), what="ODEPACK routine",
                    srcrel="share/odepack/src", hand=[], user_sigs=ODEPACK_SIGS, files=files,
                    header=share_header("share/odepack/src", "ODEPACK's DLSODE"))
    if name == "lapack":
        d = os.path.join(SHARE_DIR, "lapack")
        files = lisp_files(os.path.join(d, "blas"), ("blas-package", "icamax", "isamax")) + \
            lisp_files(os.path.join(d, "lapack"), ("lapack-package",))
        return dict(name="lapack", out=os.path.join(ROOT, "lapack"), what="BLAS/LAPACK routine",
                    srcrel="share/lapack/{blas,lapack}", hand=[], user_sigs={}, files=files,
                    header=share_header("share/lapack/{blas,lapack}", "BLAS and LAPACK"))
    raise SystemExit("unknown library %s" % name)


def share_header(srcrel, what):
    return ("// Generated by tools/f2cl2mbt.py from Maxima's\n"
            "// " + srcrel + "/%s.lisp (f2cl translation of " + what + ").\n"
            "// Do not edit by hand; regenerate instead.\n\n")


LIB = None


def main():
    global LIB
    args = [a for a in sys.argv[1:] if not a.startswith("--")]
    libname = "slatec"
    for a in sys.argv[1:]:
        if a.startswith("--lib="):
            libname = a[len("--lib="):]
    LIB = lib_config(libname)
    if libname == "slatec":
        src = args[0] if len(args) > 0 else DEFAULT_SRC
        out = args[1] if len(args) > 1 else DEFAULT_OUT
        if src != DEFAULT_SRC:
            LIB["files"] = [os.path.join(src, f) for f in sorted(os.listdir(src))
                            if f.endswith(".lisp") and f not in SKIP_FILES]
    else:
        out = LIB["out"]
    if "--reference-test" in sys.argv:
        if libname == "slatec":
            gen_reference_test(src, out)
        else:
            gen_share_reference_test(libname, out)
        return 0
    defs = []
    for path in LIB["files"]:
        n0 = len(COMMON_FILES)
        defs.extend(parse_file(path))
        if len(COMMON_FILES) > n0:
            stem = os.path.basename(path).rsplit(".", 1)[0]
            for sname in COMMONS:
                COMMON_SRC.setdefault(sname, stem)
    for h in LIB["hand"]:
        FNS[h.name] = h
    for d in defs:
        if d.name in FNS:
            raise SystemExit("duplicate routine %s" % d.name)
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
    for stem in COMMON_SRC.values():
        byfile.setdefault(stem, [])
    for fname, ds in sorted(byfile.items()):
        parts = [LIB["header"] % fname]
        try:
            st = []
            emit_commons(fname, st)
            parts.append("\n".join(st))
            for d in ds:
                st = []
                emit_statics(d, st)
                parts.append("\n".join(st))
                parts.append(gen_function(d))
        except TransError as e:
            print("ERROR %s: %s" % (fname, e), file=sys.stderr)
            errors += 1
            continue
        with open(os.path.join(out, fname.replace("-", "_") + ".mbt"), "w") as f:
            f.write("\n".join(p for p in parts if p))
    print("translated %d routines from %d files, %d errors" % (len(defs), len(byfile), errors),
          file=sys.stderr)
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
