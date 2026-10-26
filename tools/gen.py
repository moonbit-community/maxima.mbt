"""Generate the MoonBit contract for the Maxima port from tools/db.json.

Outputs (all in core/):
  gen_symbols.mbt   -- q_* symbol constants
  gen_decls.mbt     -- `declare fn` for every Lisp function
  gen_registry.mbt  -- function-cell / plist registration of every function
  gen_vars.mbt      -- literal initial values of special variables
  gen_init.mbt      -- master init in build order
Also docs/index/*.txt listings for translators.
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
CORE = os.path.join(ROOT, "core")

KEYWORDS = {
    "var",
    "as", "else", "extern", "fn", "fnalias", "if", "let", "const", "match", "using",
    "mut", "type", "typealias", "struct", "enum", "trait", "traitalias", "derive",
    "while", "break", "continue", "import", "return", "throw", "raise", "try", "catch",
    "pub", "priv", "readonly", "true", "false", "_", "test", "loop", "for", "in", "impl",
    "with", "guard", "async", "is", "suberror", "and", "letrec", "enumview", "noraise",
    "defer", "lexmatch", "declare", "init", "main", "where", "proof", "module", "open",
    "package", "extend", "virtual", "sizeof", "lazy", "recur", "do", "object", "include",
    "method", "macro", "static", "unsafe", "yield", "super", "self", "Self", "new",
    "abort", "panic", "fail", "ignore", "not", "inspect", "println", "print",
    "assert", "debug", "error", "todo", "nil", "t", "list", "cons", "car", "cdr",
    "eq", "eql", "equal", "set", "get", "sym", "int", "flo", "length", "append",
    "reverse", "member", "assoc", "apply", "funcall", "format", "char", "string",
    "vector", "every", "some", "find", "remove", "delete", "position", "max", "min",
    "abs", "floor", "round", "sqrt", "exp", "log", "sin", "cos", "tan", "atan",
    "sort", "copy", "push", "pop", "nth", "last", "rest", "first", "second", "third",
    "atom", "null", "intern", "gensym", "putprop", "remprop", "symval", "bind",
    "unbind", "lstr", "lbool", "lnot", "kw", "physical_equal", "elt", "subseq",
    "union_", "intersection", "subst", "sublis", "reduce", "mapcar", "mapc",
    "mapcan", "maplist", "numberp", "integerp", "floatp", "symbolp", "consp",
    "listp", "stringp", "zerop", "plusp", "minusp", "oddp", "evenp", "expt",
    "ash", "gcd", "lcm", "isqrt", "signum", "realpart", "imagpart", "complex",
    "conjugate", "phase", "cis", "numerator", "denominator", "rational",
    "rationalize", "truncate", "ceiling", "mod", "rem", "logand", "logior",
    "logxor", "lognot", "logbitp", "logcount", "boundp", "fboundp", "defun",
    "makunbound", "fmakunbound", "princ", "prin1", "terpri", "aref", "aset",
    "gethash", "sethash", "remhash", "maphash", "clrhash", "Value", "Symbol",
    "Cons", "Nil", "Fix", "Big", "Ratio", "Flo", "Cplx", "Str", "Char", "Vec",
    "Hash", "Func", "Struct", "Stream", "Box", "lfloat", "make_array", "vector_push_extend",
}


OVERRIDES = {}


def mangle(n):
    if n in OVERRIDES:
        return OVERRIDES[n]
    return mangle0(n)


def mangle0(n, alt=False):
    s = n
    pre = ""
    if re.match(r"^[a-z][a-z0-9-]*::.", s):
        pk, s = s.split("::", 1)
        pre = {"bigfloat": "bf_", "pregexp": "rx_", "getopt": "getopt_",
               "cl-info": "info_", "command-line": "cmdline_", "intl": "intl_",
               "mt19937": "mt_", "f2cl-lib": "f2cl_"}.get(pk, pk.replace("-", "_") + "_")
    if s.startswith("$"):
        pre += "d_"
        s = s[1:]
    elif s.startswith("%"):
        pre += "p_"
        s = s[1:]
    elif s.startswith(":"):
        pre += "kw_"
        s = s[1:]
    if len(s) > 2 and s[0] == "*" and s[-1] == "*":
        pre += "ear_"
        s = s[1:-1]
    rep = {"-": "_", "*": "_star", "%": "_pct", "$": "_dol", "+": "_plus", "/": "_sl",
           "=": "_eq", "<": "_lt", ">": "_gt", "?": "_q", "!": "_bang", "&": "_amp",
           ".": "_dot", "^": "_hat", "@": "_at", "~": "_tl", ":": "_col", "#": "_hash",
           "|": "_bar", " ": "_sp", "'": "_quo", ",": "_cm", "\\": "_bs", "[": "_lb",
           "]": "_rb", "{": "_lc", "}": "_rc", '"': "_dq", "`": "_bq", ";": "_sc"}
    if not pre and re.match(r"^(d|p|kw|ear|bf|q|n)-", s):
        s = s.replace("-", "--", 1)
    elif not pre and re.match(r"^(d|p|kw|ear|bf|q|n)_", s):
        s = s.replace("_", "-_", 1)
    if alt == "h":
        rep = dict(rep)
        rep["-"] = "_h_"
    out = []
    for c in s:
        if c == "_" and alt is True:
            out.append("_u_")
        elif c.isascii() and (c.isalnum() or c == "_"):
            if c.isupper():
                out.append("_c" + c.lower() + "_")
            else:
                out.append(c)
        elif c in rep:
            out.append(rep[c])
        else:
            out.append("_u%04x" % ord(c))
    if s and not any(c.isalnum() for c in s):
        pre += "op"
    name = pre + "".join(out)
    if name == "":
        name = "empty_symbol_name"
    if name[0].isdigit() or name[0] == "_":
        name = "n" + name
    return name


RUNTIME = set(open(os.path.join(HERE, "runtime_names.txt")).read().split()) if os.path.exists(os.path.join(HERE, "runtime_names.txt")) else set()
GLUE = {"arg", "rest_args", "key_arg", "check_arity_range", "check_arity", "arity_error",
        "register_mspec", "register_simplifier", "defvar_init", "gettext", "take",
        "take_star", "ftake", "ftake_star", "fapply", "fapply_star", "addn_", "addn_star",
        "muln_", "muln_star", "inv", "inv_star", "ncmul_", "eq0", "eq1", "mk", "mk_simp",
        "op_of", "is_op", "merr", "save_specials", "catch_tag", "throw_tag",
        "is_maxima_error", "errset", "defmfun_check_keywords", "set_init"}


def fn_name(n):
    m = mangle(n)
    if m in KEYWORDS or m in RUNTIME or m in GLUE:
        m = m + "_"
    return m


def sym_const(n):
    return "q_" + mangle(n)


def param_name(n):
    if n is None:
        return "arg"
    m = mangle(n)
    if m in KEYWORDS or m.startswith("q_"):
        m = m + "_"
    return m


def moon_str(s):
    out = []
    for c in s:
        if c == "\\":
            out.append("\\\\")
        elif c == '"':
            out.append('\\"')
        elif c == "\n":
            out.append("\\n")
        elif c == "\t":
            out.append("\\t")
        elif c == "\r":
            out.append("\\r")
        elif ord(c) < 32 or ord(c) == 127:
            out.append("\\u{%x}" % ord(c))
        else:
            out.append(c)
    return '"' + "".join(out) + '"'


def lit_expr(lit, symbols):
    """MoonBit expression for a literal default/init, or None if not literal."""
    if lit is None:
        return "Nil"
    k = lit["k"]
    if k == "nil":
        return "Nil"
    if k == "t":
        return "t"
    if k == "int":
        v = int(lit["v"])
        if -(2 ** 63) <= v < 2 ** 63:
            return "Fix(%dL)" % v
        return 'from_big(@bigint.BigInt::from_string("%d"))' % v
    if k == "float":
        v = lit["v"]
        if v in ("inf", "-inf", "nan"):
            return None
        if "e" not in v and "." not in v:
            v += ".0"
        if "e" in v:
            m, e = v.split("e")
            if "." not in m:
                m += ".0"
            v = m + "e" + e
        return "Flo(%s)" % v
    if k == "str":
        return "Str(%s)" % moon_str(lit["v"])
    if k == "char":
        return "Char(%s)" % moon_char(lit["v"])
    if k == "kw":
        symbols.add(lit["v"])
        return sym_const(lit["v"])
    if k == "quote":
        v = lit["v"]
        if re.match(r"^[^\s()'\"|#;`,]+$", v) and not re.match(r"^[-+]?\d", v):
            symbols.add(v)
            return sym_const(v)
        return None
    return None


def moon_char(c):
    if c == "'":
        return "'\\''"
    if c == "\\":
        return "'\\\\'"
    if c == "\n":
        return "'\\n'"
    if c == "\t":
        return "'\\t'"
    if c == "\r":
        return "'\\r'"
    if ord(c) < 32 or ord(c) == 127:
        return "'\\u{%x}'" % ord(c)
    return "'%s'" % c


def signature(f, symbols):
    """Return (params text, call info) for a function definition."""
    ll = f["ll"]
    params = []
    used = set()

    def pn(n):
        p = param_name(n)
        while p in used:
            p = p + "_"
        used.add(p)
        return p
    req = [pn(r) for r in ll["req"]]
    for r in req:
        params.append("%s : Value" % r)
    opts = []
    for (n, d, svar) in ll["opt"]:
        p = pn(n)
        e = lit_expr(d, symbols) if svar is None else None
        if d is None and svar is None:
            e = "Nil"
        if e is None:
            params.append("%s? : Value" % p)
            opts.append((p, "opt"))
        else:
            params.append("%s? : Value = %s" % (p, e))
            opts.append((p, "def"))
    rest = None
    if ll["rest"]:
        rest = pn(ll["rest"])
        params.append("%s : Value" % rest)
    keys = []
    keyspecs = []
    for (n, d) in ll["key"]:
        p = pn(n)
        e = lit_expr(d, symbols)
        if d is None:
            e = "Nil"
        if e is None:
            params.append("%s? : Value" % p)
        else:
            params.append("%s? : Value = %s" % (p, e))
        keys.append((n, p))
        symbols.add("$" + n)
        keyspecs.append((n, p, e))
    # keyword params are always plain options so absent keys keep defaults
    return params, {"req": req, "opts": opts, "rest": rest, "keys": keys, "keyspecs": keyspecs}


def ret_type(f):
    nv = f.get("nvalues", 0)
    if nv >= 2:
        return "(" + ", ".join(["Value"] * nv) + ")"
    return "Value"


_SHARE_STEM_COUNT = {}


def share_base(fname, db=None):
    """Identifier base for a share file's init/register/load functions: the
    mangled file stem, or dir-stem when several share files share a stem."""
    if db is not None and not _SHARE_STEM_COUNT:
        for d in db:
            if d.get("module") == "share":
                st = d["file"].split("/")[-1]
                _SHARE_STEM_COUNT[st] = _SHARE_STEM_COUNT.get(st, 0) + 1
    parts = fname.split("/")
    if _SHARE_STEM_COUNT.get(parts[-1], 1) > 1:
        # full path below share/, e.g. lapack-lapack-lapack-package
        i = parts.index("share") + 1 if "share" in parts else 0
        return mangle("-".join(parts[i:]))
    return mangle(parts[-1])


def compute_overrides(db):
    """Resolve names that mangle identically. The underscore spelling (the
    Maxima-level name, e.g. %gamma_incomplete) keeps the natural identifier;
    the hyphenated Lisp spelling gets "-" mangled as "_h_"."""
    names = set()
    for d in db:
        names |= set(d["symbols"])
        names |= set(f["name"] for f in d["functions"] if f["name"])
        names |= set(v["name"] for v in d["vars"])
        names |= set(d["specials"])
        for f in d["functions"]:
            for k in f["ll"].get("key", []):
                if k[0]:
                    names.add("$" + k[0])
    by = {}
    for n in sorted(names):
        by.setdefault(mangle0(n), []).append(n)
    for m, ns in by.items():
        if len(ns) > 1:
            for n in ns:
                if "-" in n:
                    OVERRIDES[n] = mangle0(n, alt="h")
            rest = [n for n in ns if n not in OVERRIDES]
            if len(rest) > 1:
                print("UNRESOLVED CLASH", m, rest, file=sys.stderr)


def main():
    db = json.load(open(os.path.join(HERE, "db.json")))
    compute_overrides(db)
    excluded = set(open(os.path.join(HERE, "excluded.txt")).read().split()) \
        if os.path.exists(os.path.join(HERE, "excluded.txt")) else set()
    symbols = set()
    decl_lines = ["// GENERATED by tools/gen.py -- do not edit.", "// Declarations of every Lisp function in Maxima's sources.", ""]
    reg_lines = ["// GENERATED by tools/gen.py -- do not edit.", "",
                 "///|", "fn register_generated_functions() -> Unit {"]
    seen = {}
    index_lines = []
    simp_verbs = []
    share_regs = {}
    for d in db:
        if d["file"] in excluded:
            continue
        target = reg_lines if d.get("module") != "share" else share_regs.setdefault(d["file"], [])
        for f in d["functions"]:
            name = f["name"]
            if not name:
                continue
            mn = fn_name(name)
            if mn in seen:
                prev = seen[mn]
                if prev[0] != name:
                    print("NAME CLASH", mn, name, prev, file=sys.stderr)
                continue
            seen[mn] = (name, d["file"])
            symbols.add(name)
            params, info = signature(f, symbols)
            rt = ret_type(f)
            kind = f["kind"]
            src = "%s.lisp:%d" % (d["file"], f["line"])
            decl_lines.append("///|")
            decl_lines.append("/// %s %s -- %s" % (kind, name, src))
            if rt != "Value":
                decl_lines.append("/// Returns %d values (CL multiple values) as a tuple." % f["nvalues"])
            decl_lines.append("declare fn %s(%s) -> %s raise" % (mn, ", ".join(params), rt))
            decl_lines.append("")
            index_lines.append("%s\t%s\t%s\t%s(%s) -> %s" % (name, kind, src, mn, ", ".join(params), rt))
            # registration
            q = sym_const(name)
            if kind == "defmspec":
                target.append("  register_mspec(%s, %s)" % (q, mn))
                continue
            call = gen_call(mn, info, rt, check=(name if kind == "defmfun" else None))
            if kind == "simplifier":
                target.append("  register_simplifier(%s, args => %s)" % (q, call))
                base = f["base"]
                opts = f.get("opts", "")
                simp_verbs.append((base, f["args"], opts, target))
                continue
            target.append("  defun(%s, args => %s)" % (q, call))
            if kind == "defmfun":
                symbols.add("translated")
                target.append("  putprop(%s, t, q_translated) |> ignore" % q)
                m = re.search(r":properties \(((?:\([a-z-]+ t\) ?)+)\)", f.get("opts", ""))
                if m:
                    for pname in re.findall(r"\(([a-z-]+) t\)", m.group(1)):
                        symbols.add(pname)
                        target.append("  putprop(%s, t, %s) |> ignore" % (q, sym_const(pname)))
    reg_lines.append("}")
    reg_lines.append("")
    # function-like macros: declared so their port can be shared
    decl_lines.append("// ---- Function-like macros (implemented as functions by the porter of the defining file)")
    decl_lines.append("")
    for d in db:
        if d["file"] in excluded:
            continue
        for m in d["macros"]:
            name = m["name"]
            if not m.get("simple") or not name:
                continue
            mn = fn_name(name)
            if mn in seen:
                continue
            seen[mn] = (name, d["file"])
            f = {"ll": m["pll"], "nvalues": 0}
            params, info = signature(f, symbols)
            src = "%s.lisp:%d" % (d["file"], m["line"])
            decl_lines.append("///|")
            decl_lines.append("/// macro %s %s -- %s" % (name, m["ll"], src))
            decl_lines.append("declare fn %s(%s) -> Value raise" % (mn, ", ".join(params)))
            decl_lines.append("")
            index_lines.append("%s\tmacro\t%s\t%s(%s) -> Value" % (name, src, mn, ", ".join(params)))
    # per-file init functions
    decl_lines.append("// ---- Per-file initialization (top-level forms of each Lisp file)")
    decl_lines.append("")
    for d in db:
        if d["file"] in excluded:
            continue
        nm = ("init_share_" + share_base(d["file"], db)) if d.get("module") == "share" else ("init_" + mangle(d["file"].split("/")[-1]))
        decl_lines.append("///|")
        decl_lines.append("/// top-level forms of %s.lisp" % d["file"])
        decl_lines.append("declare fn %s() -> Unit raise" % nm)
        decl_lines.append("")
    # def-simplifier verb functions and properties
    reg_lines.append("///|")
    reg_lines.append("fn register_generated_simplifiers() -> Unit {")
    for base, args, opts, vtarget in simp_verbs:
        out = reg_lines if vtarget is reg_lines else vtarget
        noun = "%" + base
        verb = "$" + base
        simp = "simp-%" + base
        for s in (noun, verb, simp):
            symbols.add(s)
        for p in ("alias", "reversealias", "operators", "noun", "verb"):
            symbols.add(p)
        custom = ":custom-defmfun t" in opts
        skip = re.search(r":skip-properties \(([^)]*)\)", opts)
        skips = skip.group(1).split() if skip else []
        subfun = ":subfun-arglist" in opts
        if subfun:
            out.append("  putprop(%s, %s, q_specsimp) |> ignore" % (sym_const(verb), sym_const(simp)))
            symbols.add("specsimp")
            continue
        if not custom:
            n = len(args)
            out.append("  defun(%s, args => { check_arity(%s, args, %d); ftake(%s, args) })"
                             % (sym_const(verb), moon_str(verb), n, sym_const(noun)))
        if "alias" not in skips:
            out.append("  putprop(%s, %s, q_alias) |> ignore" % (sym_const(verb), sym_const(noun)))
        if "reversealias" not in skips:
            out.append("  putprop(%s, %s, q_reversealias) |> ignore" % (sym_const(noun), sym_const(verb)))
        out.append("  putprop(%s, %s, q_operators) |> ignore" % (sym_const(noun), sym_const(simp)))
        out.append("  putprop(%s, %s, q_noun) |> ignore" % (sym_const(noun), sym_const(verb)))
        out.append("  putprop(%s, %s, q_verb) |> ignore" % (sym_const(verb), sym_const(noun)))
    reg_lines.append("}")

    for fname, lines in share_regs.items():
        reg_lines.append("")
        reg_lines.append("///|")
        reg_lines.append("fn register_share_%s() -> Unit {" % share_base(fname, db))
        reg_lines.extend(lines)
        reg_lines.append("}")
    # variables
    var_lines = ["// GENERATED by tools/gen.py -- do not edit.", ""]
    init_lines = ["// GENERATED by tools/gen.py -- do not edit.", "",
                  "///|", "/// Initialize literal special-variable values, file by file in build order.",
                  "fn init_generated_vars() -> Unit raise {"]
    complex_vars = []
    specials_all = set()
    for d in db:
        if d["file"] in excluded:
            continue
        for s in d["specials"]:
            specials_all.add(s)
            symbols.add(s)
        body = []
        for v in d["vars"]:
            nm = v["name"]
            symbols.add(nm)
            e = lit_expr(v["init"], symbols) if v["init"] is not None else None
            if v["init"] is None:
                # (defvar x) -- unbound declaration
                continue
            if e is None:
                complex_vars.append("%s\t%s.lisp:%d\t%s" % (nm, d["file"], v["line"], v["init"].get("v")))
                vt = v["init"].get("v") or ""
                if v["init"]["k"] == "quote" and not any(x in vt for x in ("#<", "##", "`", ",", "#$")):
                    init_fn = "set_init" if v["kind"] in ("defparameter", "defconstant") else "defvar_init"
                    body.append("  %s(%s, lread(%s))" % (init_fn, sym_const(nm), moon_str(v["init"]["v"])))
                continue
            # defparameter (and defconstant) always assign; defvar/defmvar
            # only when unbound
            init_fn = "set_init" if v["kind"] in ("defparameter", "defconstant") else "defvar_init"
            body.append("  %s(%s, %s)" % (init_fn, sym_const(nm), e))
        if body:
            fnm = "init_vars_" + mangle(d["file"].replace("/", "-"))
            var_lines.append("///|")
            var_lines.append("fn %s() -> Unit raise {" % fnm)
            var_lines.extend(body)
            var_lines.append("}")
            var_lines.append("")
            if d.get("module") != "share":
                init_lines.append("  %s()" % fnm)
    init_lines.append("}")
    var_lines.extend(init_lines)

    # symbols
    for d in db:
        if d["file"] in excluded:
            continue
        for s in d["symbols"]:
            symbols.add(s)
    sym_lines = ["// GENERATED by tools/gen.py -- do not edit.", "// Symbol constants: q_<mangled name>.", ""]
    seen_q = {}
    for s in sorted(symbols):
        if s is None or s in ("nil",):
            continue
        q = sym_const(s)
        if q in seen_q:
            if seen_q[q] != s:
                print("SYMBOL CLASH", q, s, seen_q[q], file=sys.stderr)
            continue
        seen_q[q] = s
        if s == "t":
            sym_lines.append("///|\nlet q_t : Value = t\n")
            continue
        sym_lines.append("///|\nlet %s : Value = sym(%s)\n" % (q, moon_str(s)))

    os.makedirs(CORE, exist_ok=True)
    open(os.path.join(CORE, "gen_symbols.mbt"), "w").write("\n".join(sym_lines) + "\n")
    open(os.path.join(CORE, "gen_decls.mbt"), "w").write("\n".join(decl_lines) + "\n")
    open(os.path.join(CORE, "gen_registry.mbt"), "w").write("\n".join(reg_lines) + "\n")
    open(os.path.join(CORE, "gen_vars.mbt"), "w").write("\n".join(var_lines) + "\n")
    idx = os.path.join(ROOT, "docs", "index")
    os.makedirs(idx, exist_ok=True)
    open(os.path.join(idx, "functions.tsv"), "w").write("\n".join(index_lines) + "\n")
    open(os.path.join(idx, "specials.txt"), "w").write("\n".join(sorted(specials_all)) + "\n")
    open(os.path.join(idx, "complex_var_inits.tsv"), "w").write("\n".join(complex_vars) + "\n")
    mac = []
    for d in db:
        for m in d["macros"]:
            mac.append("%s\t%s.lisp:%d\t%s" % (m["name"], d["file"], m["line"], m["ll"]))
    open(os.path.join(idx, "macros.tsv"), "w").write("\n".join(mac) + "\n")
    print("functions", len(seen), "symbols", len(seen_q), "specials", len(specials_all))


def gen_call(mn, info, rt, check=None):
    req = info["req"]
    opts = info["opts"]
    rest = info["rest"]
    keys = info["keys"]
    nreq = len(req)
    post = "" if rt == "Value" else ".0"
    args = ["arg(args, %d)" % i for i in range(nreq)]
    for j, (p, _) in enumerate(opts):
        args.append("%s?=args.get(%d)" % (p, nreq + j))
    if rest is not None:
        args.append("rest_args(args, %d)" % (nreq + len(opts)))
    for (kname, p) in keys:
        args.append("%s?=key_arg(args, %d, %s)" % (p, nreq + len(opts), moon_str(":" + kname)))
    call = "%s(%s)%s" % (mn, ", ".join(args), post)
    if check is not None and keys:
        # defmfun-keywords: every option must be `name = value` with a
        # recognized name, else Maxima's "Unrecognized keyword" error
        specs = ", ".join("(%s, %s)" % (sym_const("$" + kname), kdefault or "Nil")
                          for (kname, p, kdefault) in info.get("keyspecs", []))
        call = "{ defmfun_check_keywords(%s, args, %d, [%s]); %s }" % (
            sym_const(check), nreq + len(opts), specs, call)
    if check is not None:
        mx = -1 if (rest is not None or keys) else nreq + len(opts)
        return "{ check_arity_range(%s, args, %d, %d); %s }" % (moon_str(check), nreq, mx, call)
    return call


if __name__ == "__main__":
    main()
