"""Analyze Maxima's Lisp sources: definitions, lambda lists, specials, macros.

Writes tools/db.json used by gen.py.
"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(__file__))
from lispread import *  # noqa

SRC = os.path.join(os.path.dirname(__file__), "..", ".repos", "maxima", "src")


def system_files():
    """Files in maxima.system build order (those that exist)."""
    text = open(os.path.join(SRC, "maxima.system")).read()
    r = Reader(text, "maxima.system")
    forms = [f for f, _ in r.read_all()]
    order = []

    def walk(x, module):
        if isinstance(x, list):
            if len(x) >= 2 and isinstance(x[0], Sym) and x[0].name in (":file", ":private-file") and isinstance(x[1], Str):
                order.append((module, x[1].text))
            elif len(x) >= 2 and isinstance(x[0], Sym) and x[0].name == ":module":
                m = x[1].name if isinstance(x[1], Sym) else str(x[1])
                for y in x[2:]:
                    walk(y, m)
                return
            for y in x:
                walk(y, module)
    for f in forms:
        walk(f, "")
    out = []
    for module, name in order:
        for d in ("", "numerical/", "numerical/slatec/"):
            p = os.path.join(SRC, d + name + ".lisp")
            if os.path.exists(p):
                out.append((module, d + name))
                break
    return out


def sym(x):
    return x.name if isinstance(x, Sym) else None


LAMBDA_KEYS = {"&optional", "&rest", "&key", "&aux", "&body", "&allow-other-keys",
               "&whole", "&environment"}


def parse_lambda_list(ll):
    """Return dict with req, opt [(name, default, svar)], rest, key [(name, default)]."""
    res = {"req": [], "opt": [], "rest": None, "key": [], "aux": [], "dotted": False}
    if isinstance(ll, DottedList):
        items = list(ll.items)
        res["rest"] = sym(ll.tail)
        res["dotted"] = True
    elif isinstance(ll, list):
        items = list(ll)
    elif ll is None or (isinstance(ll, Sym) and ll.name == "nil"):
        items = []
    elif isinstance(ll, Sym):
        # Maclisp lexpr: (defun f n ...) -- all args, accessed with (arg i)
        res["rest"] = ll.name
        res["lexpr"] = True
        items = []
    else:
        items = []
    mode = "req"
    for it in items:
        s = sym(it)
        if s in LAMBDA_KEYS:
            mode = {"&optional": "opt", "&rest": "rest", "&body": "rest", "&key": "key",
                    "&aux": "aux", "&allow-other-keys": mode, "&whole": "whole",
                    "&environment": "env"}[s]
            continue
        if mode == "req":
            res["req"].append(s if s else repr(it))
        elif mode == "opt":
            if isinstance(it, list):
                res["opt"].append((sym(it[0]), lit_repr(it[1]) if len(it) > 1 else None,
                                   sym(it[2]) if len(it) > 2 else None))
            else:
                res["opt"].append((s, None, None))
        elif mode == "rest":
            res["rest"] = s
        elif mode == "key":
            if isinstance(it, list):
                nm = it[0]
                if isinstance(nm, list):
                    nm = nm[1]
                res["key"].append((sym(nm), lit_repr(it[1]) if len(it) > 1 else None))
            else:
                res["key"].append((s, None))
        elif mode == "aux":
            pass
    return res


def lit_repr(x):
    """A JSON-able description of a default/init form for literal emission."""
    if x is None:
        return None
    if isinstance(x, bool):
        return {"k": "bool", "v": x}
    if isinstance(x, int):
        return {"k": "int", "v": str(x)}
    if isinstance(x, float):
        return {"k": "float", "v": repr(x)}
    if isinstance(x, Fraction):
        return {"k": "ratio", "v": "%d/%d" % (x.numerator, x.denominator)}
    if isinstance(x, Str):
        return {"k": "str", "v": x.text}
    if isinstance(x, Char):
        return {"k": "char", "v": x.c}
    if isinstance(x, Sym):
        if x.name == "nil":
            return {"k": "nil"}
        if x.name == "t":
            return {"k": "t"}
        if x.name.startswith(":"):
            return {"k": "kw", "v": x.name}
        return {"k": "expr", "v": x.name}
    if isinstance(x, Quote) and x.kind == "quote":
        return {"k": "quote", "v": to_text(x.form)}
    return {"k": "expr", "v": to_text(x)}


def to_text(x):
    """Re-serialize a form as Lisp text in the port's naming convention."""
    if isinstance(x, Sym):
        n = x.name
        if needs_bars(n):
            return "|" + n.replace("\\", "\\\\").replace("|", "\\|") + "|"
        return n
    if isinstance(x, bool):
        return "t" if x else "nil"
    if isinstance(x, int):
        return str(x)
    if isinstance(x, float):
        return repr(x)
    if isinstance(x, Fraction):
        return "%d/%d" % (x.numerator, x.denominator)
    if isinstance(x, Str):
        return '"' + x.text.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(x, Char):
        return "#\\" + {" ": "Space", "\n": "Newline", "\t": "Tab"}.get(x.c, x.c)
    if isinstance(x, DottedList):
        return "(" + " ".join(to_text(i) for i in x.items) + " . " + to_text(x.tail) + ")"
    if isinstance(x, list):
        return "(" + " ".join(to_text(i) for i in x) + ")"
    if isinstance(x, Quote):
        p = {"quote": "'", "function": "#'", "backquote": "`", "comma": ",",
             "comma-at": ",@"}[x.kind]
        return p + to_text(x.form)
    if isinstance(x, MaximaExpr):
        return "#$" + x.text + "$"
    if isinstance(x, Vector):
        return "#(" + " ".join(to_text(i) for i in x.items) + ")"
    if isinstance(x, tuple):
        return "#<%s %s>" % (x[0], to_text(x[1]) if not isinstance(x[1], str) else x[1])
    return repr(x)


def needs_bars(n):
    if n == "":
        return True
    for c in n:
        if c in " ()\"';`,|\\\n\t" or (c.isalpha() and c.isupper()):
            return True
    return False


def count_values(body):
    """Max arg count of (values ...) forms in body (outside nested lambdas)."""
    best = [0]

    def walk(x):
        if isinstance(x, list) and x:
            h = sym(x[0])
            if h in ("lambda", "function", "flet", "labels", "defun"):
                return
            if h == "values":
                best[0] = max(best[0], len(x) - 1)
            if h == "values-list":
                best[0] = max(best[0], 2)
            for y in x[1:]:
                walk(y)
        elif isinstance(x, Quote) and x.kind in ("backquote",):
            return
    for b in body:
        walk(b)
    return best[0]


def collect_specials_in(x, acc):
    """(declare (special ...)) forms anywhere."""
    if isinstance(x, list) and x:
        if sym(x[0]) == "declare":
            for d in x[1:]:
                if isinstance(d, list) and d and sym(d[0]) == "special":
                    for v in d[1:]:
                        if sym(v):
                            acc.add(sym(v))
        for y in x:
            collect_specials_in(y, acc)


def collect_symbols(x, acc, quoted=False):
    """All symbols in quoted/backquoted data, plus all $/% symbols anywhere."""
    if isinstance(x, Sym):
        n = x.name
        if quoted or n.startswith("$") or n.startswith("%"):
            acc.add(n)
    elif isinstance(x, (list,)):
        for y in x:
            collect_symbols(y, acc, quoted)
    elif isinstance(x, DottedList):
        for y in x.items:
            collect_symbols(y, acc, quoted)
        collect_symbols(x.tail, acc, quoted)
    elif isinstance(x, Quote):
        if x.kind in ("quote", "backquote"):
            collect_symbols(x.form, acc, True)
        elif x.kind == "function":
            collect_symbols(x.form, acc, True)
        else:
            collect_symbols(x.form, acc, False)
    elif isinstance(x, Vector):
        for y in x.items:
            collect_symbols(y, acc, quoted)


def collect_calls(x, acc):
    """Heads of forms (potential function/macro calls)."""
    if isinstance(x, list) and x:
        h = sym(x[0])
        if h:
            acc[h] = acc.get(h, 0) + 1
        for y in x[1:]:
            collect_calls(y, acc)
    elif isinstance(x, Quote):
        if x.kind == "function":
            s = sym(x.form)
            if s:
                acc[s] = acc.get(s, 0) + 1
        elif x.kind in ("comma", "comma-at"):
            collect_calls(x.form, acc)
        elif x.kind == "backquote":
            collect_calls_bq(x.form, acc)
    elif isinstance(x, DottedList):
        for y in x.items:
            collect_calls(y, acc)


def collect_calls_bq(x, acc):
    if isinstance(x, Quote) and x.kind in ("comma", "comma-at"):
        collect_calls(x.form, acc)
    elif isinstance(x, list):
        for y in x:
            collect_calls_bq(y, acc)


def analyze_file(module, rel):
    path = os.path.join(SRC, rel + ".lisp")
    forms = read_file(path)
    info = {"file": rel, "module": module, "functions": [], "macros": [], "vars": [],
            "specials": set(), "symbols": set(), "calls": {}, "toplevel": [],
            "lines": sum(1 for _ in open(path, encoding="utf-8", errors="replace"))}

    pkg = ["maxima"]

    def add_fn(kind, name, ll, body, line, extra=None):
        if pkg[0] != "maxima" and name:
            name = pkg[0] + "::" + name
        d = {"kind": kind, "name": name, "pkg": pkg[0], "ll": parse_lambda_list(ll), "line": line,
             "nvalues": count_values(body)}
        if extra:
            d.update(extra)
        info["functions"].append(d)

    def handle(f, line):
        collect_symbols(f, info["symbols"])
        collect_specials_in(f, info["specials"])
        collect_calls(f, info["calls"])
        if not isinstance(f, list) or not f:
            return
        h = sym(f[0])
        if h in ("progn", "eval-when"):
            for g in f[(2 if h == "eval-when" else 1):]:
                handle(g, line)
            return
        if h == "defun" or h == "defun-maclisp":
            name = sym(f[1])
            if name is None and isinstance(f[1], list):
                # (defun (foo prop) ...) Maclisp style
                name = sym(f[1][0]) + "-" + sym(f[1][1])
            add_fn("defun", name, f[2], f[3:], line)
        elif h == "defmfun":
            nm = f[1]
            opts = {}
            if isinstance(nm, list):
                opts["opts"] = to_text(LList(nm[1:]))
                nm = nm[0]
            add_fn("defmfun", sym(nm), f[2], f[3:], line, opts)
        elif h == "defmspec":
            add_fn("defmspec", sym(f[1]), f[2], f[3:], line)
        elif h == "def-simplifier":
            bn = f[1]
            opts = {}
            if isinstance(bn, list):
                opts["opts"] = to_text(LList(bn[1:]))
                bn = bn[0]
            b = sym(bn)
            add_fn("simplifier", "simp-%" + b, LList([Sym("form"), Sym("y"), Sym("%%simpflag")]),
                   f[3:], line, dict(opts, base=b, args=[sym(a) for a in f[2]]))
        elif h == "defmacro":
            info["macros"].append({"name": (sym(f[1]) if pkg[0] == "maxima" else pkg[0] + "::" + sym(f[1])), "ll": to_text(f[2]), "line": line})
        elif h == "define-compiler-macro":
            pass
        elif h in ("defvar", "defparameter", "defconstant", "defmvar"):
            name = sym(f[1])
            init = lit_repr(f[2]) if len(f) > 2 else None
            d = {"kind": h, "name": name, "init": init, "line": line}
            if h == "defmvar":
                rest = f[3:]
                if rest and isinstance(rest[0], Str):
                    rest = rest[1:]
                if rest:
                    d["opts"] = to_text(LList(rest))
            info["vars"].append(d)
            info["specials"].add(name)
        elif h == "declare-top":
            for d in f[1:]:
                if isinstance(d, list) and d and sym(d[0]) == "special":
                    for v in d[1:]:
                        if sym(v):
                            info["specials"].add(sym(v))
        elif h == "defmethod":
            nm = f[1]
            info["toplevel"].append({"head": h, "name": to_text(nm), "line": line})
        elif h == "in-package":
            p = f[1]
            pn = (p.name if isinstance(p, Sym) else p.text if isinstance(p, Str) else "maxima").lower().lstrip(":").lstrip("#:")
            if pn in ("common-lisp-user", "cl-user"):
                pn = "maxima"
            pkg[0] = pn
        elif h in ("macsyma-module", "declaim", "load-macsyma-macros",
                   "defpackage"):
            pass
        else:
            info["toplevel"].append({"head": h, "line": line,
                                     "text": to_text(f)[:200]})

    for f, line in forms:
        handle(f, line)
    info["specials"] = sorted(info["specials"])
    info["symbols"] = sorted(info["symbols"])
    return info


def main():
    files = system_files()
    db = []
    for module, rel in files:
        try:
            db.append(analyze_file(module, rel))
        except Exception as e:
            print("ERROR", rel, e, file=sys.stderr)
    out = os.path.join(os.path.dirname(__file__), "db.json")
    json.dump(db, open(out, "w"), indent=0)
    nf = sum(len(d["functions"]) for d in db)
    print("files", len(db), "functions", nf, "macros", sum(len(d["macros"]) for d in db),
          "vars", sum(len(d["vars"]) for d in db))


if __name__ == "__main__":
    main()
