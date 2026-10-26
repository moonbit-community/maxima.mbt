"""Find calls to &rest functions whose rest argument is clearly not a list
(a q_ symbol constant, a number, a string, Nil is fine)."""
import re, os, glob, json, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
decls = open(os.path.join(ROOT, "core", "gen_decls.mbt")).read()
restpos = {}
db = json.load(open(os.path.join(ROOT, "tools", "db.json")))
sys.path.insert(0, os.path.join(ROOT, "tools"))
import gen
gen.compute_overrides(db)
for d in db:
    for f in d["functions"]:
        ll = f["ll"]
        if ll.get("rest") and f["name"]:
            # positional index of rest param = number of required params
            restpos[gen.fn_name(f["name"])] = len(ll["req"])
def split_args(s, i):
    # s[i] == '(' ; return list of top-level arg strings and end index
    depth, j, start, args = 0, i, i + 1, []
    while j < len(s):
        c = s[j]
        if c in "([{": depth += 1
        elif c in ")]}":
            depth -= 1
            if depth == 0:
                args.append(s[start:j]); return args, j
        elif c == "," and depth == 1:
            args.append(s[start:j]); start = j + 1
        elif c == '"':
            j += 1
            while j < len(s) and s[j] != '"':
                j += 2 if s[j] == "\\" else 1
        j += 1
    return args, j
bad = 0
for path in sorted(glob.glob(os.path.join(ROOT, "core", "*.mbt"))):
    if os.path.basename(path).startswith("gen_"): continue
    src = open(path).read()
    for m in re.finditer(r"\b([a-z_][a-z0-9_]*)\(", src):
        name = m.group(1)
        if name not in restpos: continue
        if src[max(0, m.start()-3):m.start()] == "fn ": continue
        args, _ = split_args(src, m.end() - 1)
        positional = [a.strip() for a in args if not re.match(r"^\s*[a-z_0-9]+\??=", a)]
        k = restpos[name]
        if k < len(positional):
            a = positional[k]
            if re.match(r"^(q_[a-z0-9_]+|Fix\(|Str\(|int\(|Flo\(|t)$", a) or re.match(r"^(q_[a-z0-9_]+|Fix\(.*\)|Str\(.*\)|int\(.*\))$", a):
                line = src[:m.start()].count("\n") + 1
                print("%s:%d: %s(... rest=%s)" % (os.path.basename(path), line, name, a[:60]))
                bad += 1
print("--", bad, "suspicious calls")
