#!/usr/bin/env python3
"""Generate core/lisp_eval_maxima_macros.mbt: the source text of the
DEFMACROs of Maxima's Lisp code (src/*.lisp in maxima.system order), by
name. The Lisp evaluator defines one of these macros when Lisp code it
compiles uses the name and the name has no definition (macros are not in
the port's function cells: their uses were expanded by hand when the code
was ported). Macros whose names the evaluator defines itself (CL macros,
its prelude) are skipped. Rerun when the Maxima sources change."""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
import analyze  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def top_forms(text):
    """Yield (start, end) of each top-level form, skipping comments and
    strings."""
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            while i < n and text[i] != '\n':
                i += 1
        elif text.startswith('#|', i):
            depth = 0
            while i < n:
                if text.startswith('#|', i):
                    depth += 1
                    i += 2
                elif text.startswith('|#', i):
                    depth -= 1
                    i += 2
                    if depth == 0:
                        break
                else:
                    i += 1
        elif c == '(':
            start = i
            depth = 0
            while i < n:
                c = text[i]
                if c == ';':
                    while i < n and text[i] != '\n':
                        i += 1
                    continue
                if c == '"':
                    i += 1
                    while i < n and text[i] != '"':
                        if text[i] == '\\':
                            i += 1
                        i += 1
                elif c == '|':
                    i += 1
                    while i < n and text[i] != '|':
                        if text[i] == '\\':
                            i += 1
                        i += 1
                elif c == '#' and i + 1 < n and text[i + 1] == '\\':
                    i += 2
                elif c == '(':
                    depth += 1
                elif c == ')':
                    depth -= 1
                    if depth == 0:
                        i += 1
                        break
                i += 1
            yield start, i
        else:
            i += 1


def defmacros(form_text):
    """defmacro forms inside a top-level form text (also within progn or
    an eval-when that includes :load-toplevel, i.e. that exist in the
    compiled Maxima image)."""
    m = re.match(r'\(\s*(defmacro|progn|eval-when)\b', form_text, re.I)
    if not m:
        return []
    head = m.group(1).lower()
    if head == 'defmacro':
        nm = re.match(r'\(\s*defmacro\s+([^\s()]+)', form_text, re.I)
        return [(nm.group(1).lower(), form_text)] if nm else []
    inner = form_text[m.end():-1]
    if head == 'eval-when':
        sit = re.match(r'\s*\(([^()]*)\)', inner)
        if not sit or not re.search(r'(:load-toplevel|\bload\b)', sit.group(1), re.I):
            return []
        inner = inner[sit.end():]
    out = []
    for s, e in top_forms(inner):
        out += defmacros(inner[s:e])
    return out


# The features of the reference (SBCL) Maxima, for #+/#- before a form.
FEATURES = {"sbcl", "common-lisp", "cl", "ansi-cl", "ieee-floating-point", "64-bit",
            "unix", "darwin", "lisp-unicode-capable", "has-distinct-double-float",
            "mk-defsystem", "cltl2", "sb-unicode"}


def feature_true(expr):
    expr = expr.strip().lower()
    if expr.startswith('('):
        parts = expr[1:-1].split()
        op, args = parts[0], parts[1:]
        # only flat feature expressions
        if op == 'or':
            return any(a.lstrip(':') in FEATURES for a in args)
        if op == 'and':
            return all(a.lstrip(':') in FEATURES for a in args)
        if op == 'not':
            return not any(a.lstrip(':') in FEATURES for a in args)
        return False
    return expr.lstrip(':') in FEATURES


def conditional_ok(text, start):
    """Is the form at `start` enabled by a preceding #+/#- (if any)?"""
    before = text[max(0, start - 200):start]
    m = re.search(r'#([+-])(\([^()]*\)|[^\s()]+)\s*$', before)
    if not m:
        return True
    ok = feature_true(m.group(2))
    return ok if m.group(1) == '+' else not ok


def main():
    skip = set(sys.argv[1:])
    files = analyze.system_files()
    macros = {}
    order = []
    for _module, rel in files:
        path = os.path.join(analyze.SRC, rel + ".lisp")
        if not os.path.exists(path):
            continue
        text = open(path, encoding="utf-8", errors="replace").read()
        if re.search(r'\(in-package\s+[:#]*(bigfloat|f2cl-lib|cl-info|intl|getopt|command-line)', text, re.I):
            continue
        for s, e in top_forms(text):
            if not conditional_ok(text, s):
                continue
            for name, src in defmacros(text[s:e]):
                if name.startswith("|") or name in skip:
                    continue
                if name not in macros:
                    order.append(name)
                macros[name] = (rel, src)
    out = [
        "// GENERATED by tools/gen_lisp_macros.py from the Maxima sources.",
        "// The DEFMACROs of Maxima's Lisp code, by name, defined on demand",
        "// by the Lisp evaluator (see le__maxima_macro_source).",
        "",
        "///|",
        "let le__maxima_macro_sources : Map[String, String] = {",
    ]
    for name in order:
        rel, src = macros[name]
        out.append("  %s: %s," % (moon_str(name), moon_str(src)))
    out += ["}", ""]
    open(os.path.join(ROOT, "core/lisp_eval_maxima_macros.mbt"), "w").write("\n".join(out))
    print("macros", len(order), "bytes", sum(len(macros[n][1]) for n in order))


def moon_str(s):
    r = ['"']
    for c in s:
        if c == '\\':
            r.append('\\\\')
        elif c == '"':
            r.append('\\"')
        elif c == '\n':
            r.append('\\n')
        elif c == '\t':
            r.append('\\t')
        elif c == '\r':
            continue
        elif ord(c) < 32:
            r.append('\\u{%x}' % ord(c))
        else:
            r.append(c)
    r.append('"')
    return "".join(r)


if __name__ == "__main__":
    main()
