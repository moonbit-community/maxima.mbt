import sys, json
n = 0
lim = int(sys.argv[1]) if len(sys.argv) > 1 else 60
seen = set()
for line in sys.stdin:
    line = line.strip()
    if not line.startswith("{"):
        continue
    try:
        d = json.loads(line)
    except Exception:
        continue
    if d.get("level") != "error":
        continue
    p = d.get("path", "?").split("/")[-1]
    key = (p, d.get("loc"), d.get("message"))
    if key in seen:
        continue
    seen.add(key)
    msg = d.get("message", "").replace("\n", " ")[:240]
    if n < lim:
        print("%s:%s: %s" % (p, d.get("loc", "").split("-")[0], msg))
    n += 1
print("-- %d errors" % n)
