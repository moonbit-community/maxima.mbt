"""Print problem N (input and expected) of a Maxima rtest file.
usage: python3 tools/rtest_problem.py rtest7 46 [47 ...]"""
import sys, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPOS_DIR = os.environ.get("MAXIMA_REPOS", os.path.join(ROOT, ".repos"))

def statements(text):
    out, buf, i, n = [], [], 0, len(text)
    depth = 0
    while i < n:
        c = text[i]
        if text.startswith("/*", i):
            j = text.find("*/", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            buf.append(text[i:j + 1]); i = j + 1; continue
        if c == "\\" and i + 1 < n:
            buf.append(text[i:i + 2]); i += 2; continue
        if c in ";$":
            s = "".join(buf).strip()
            if s:
                out.append(s + c)
            buf = []; i += 1; continue
        buf.append(c); i += 1
    return out

def find(name):
    for d in ("tests", "share"):
        for root, _, files in os.walk(os.path.join(REPOS_DIR, "maxima", d)):
            if name + ".mac" in files:
                return os.path.join(root, name + ".mac")

if __name__ == "__main__":
    path = find(sys.argv[1])
    st = statements(open(path, encoding="utf-8", errors="replace").read())
    for a in sys.argv[2:]:
        k = int(a)
        print("Problem %d:\n  %s\n  => %s" % (k, st[2 * (k - 1)], st[2 * (k - 1) + 1]))
