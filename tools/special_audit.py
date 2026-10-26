"""List variables that a file binds lexically-looking (let/let*/do/lambda
params/prog vars) whose names were proclaimed special by an EARLIER file in
build order (CL global proclamation), but which the file itself does not
declare special. These are bindings a porter may have treated as lexical."""
import json, os, sys
sys.path.insert(0, os.path.dirname(__file__))
from lispread import *
from analyze import SRC, system_files, sym
db = json.load(open(os.path.join(os.path.dirname(__file__), "db.json")))
excluded = set(open(os.path.join(os.path.dirname(__file__), "excluded.txt")).read().split())
global_specials = set()
own = {d["file"]: set(d["specials"]) for d in db}

def bound_names(x, acc):
    if isinstance(x, list) and x:
        h = sym(x[0])
        if h in ("let", "let*", "prog", "do", "do*") and len(x) > 1 and isinstance(x[1], list):
            for b in x[1]:
                n = sym(b) if isinstance(b, Sym) else (sym(b[0]) if isinstance(b, list) and b else None)
                if n: acc.add(n)
        if h in ("defun", "lambda", "defmfun") and len(x) > 2:
            ll = x[2] if h != "lambda" else x[1]
            if isinstance(ll, list):
                for p in ll:
                    n = sym(p) if isinstance(p, Sym) else (sym(p[0]) if isinstance(p, list) and p else None)
                    if n and not n.startswith("&"): acc.add(n)
        if h in ("multiple-value-bind", "destructuring-bind", "dolist", "dotimes") and len(x) > 1:
            v = x[1]
            if isinstance(v, list):
                for p in v:
                    if sym(p): acc.add(sym(p))
        for y in x:
            bound_names(y, acc)

out = []
for d in db:
    f = d["file"]
    if f in excluded or f.startswith("numerical"):
        global_specials |= own[f]; continue
    forms = read_file(os.path.join(SRC, f + ".lisp"))
    acc = set()
    for form, _ in forms:
        bound_names(form, acc)
    risky = sorted(n for n in acc if n in global_specials and n not in own[f]
                   and not n.startswith("$") and not n.startswith("*"))
    if risky:
        out.append("%s\t%s" % (f, " ".join(risky)))
    global_specials |= own[f]
open(os.path.join(os.path.dirname(__file__), "..", "docs", "index", "inherited_specials.tsv"), "w").write("\n".join(out) + "\n")
print("\n".join(out))
