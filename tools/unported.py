#!/usr/bin/env python3
"""List declared contract functions with no implementation, grouped by Lisp file.
Usage: tools/unported.py [--names] [file-prefix...]"""
import re, sys, glob, collections, os
root = os.path.join(os.path.dirname(__file__), "..")
defined = set()
for f in glob.glob(os.path.join(root, "core", "*.mbt")):
    if os.path.basename(f).startswith("gen_"):
        continue
    for m in re.finditer(r"^(?:pub )?fn ([a-z_][A-Za-z0-9_]*)", open(f).read(), re.M):
        defined.add(m.group(1))
by = collections.defaultdict(list)
lines = collections.Counter()
for l in open(os.path.join(root, "docs/index/functions.tsv")):
    p = l.rstrip("\n").split("\t")
    if len(p) < 4:
        continue
    name = p[3].split("(")[0]
    if name in defined:
        continue
    by[p[2].rsplit(":", 1)[0]].append(name)
args = [a for a in sys.argv[1:] if not a.startswith("--")]
for f, ns in sorted(by.items(), key=lambda kv: -len(kv[1])):
    if args and not any(f.startswith(a) for a in args):
        continue
    print(f"{len(ns):5d} {f}")
    if "--names" in sys.argv:
        print("      " + " ".join(ns))
print("total", sum(len(v) for v in by.values()), "in", len(by), "files", file=sys.stderr)
