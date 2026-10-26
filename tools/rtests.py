"""Run Maxima's core test files one per process; print a pass/fail table.

usage: python3 tools/rtests.py [-j N] [-t TIMEOUT] [names...]
Writes logs to _build/rtests/<name>.log and a summary to docs/TESTS.md (with
--save).
"""
import subprocess, sys, os, re, concurrent.futures, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
EXE = os.environ.get("MAXIMA_PORT") or os.path.join(ROOT, "_build", "native", "release", "build", "cmd", "main", "main.exe")
LOGDIR = os.path.join(ROOT, "_build", "rtests")

def testsuite_files():
    src = open(os.path.join(ROOT, ".repos", "maxima", "src", "testsuite.lisp")).read()
    i = src.index("$testsuite_files")
    j = src.index("$share_testsuite_files")
    names = re.findall(r'"(rtest[^"]*)"', src[i:j])
    return names

def run_one(name, timeout):
    os.makedirs(LOGDIR, exist_ok=True)
    log = os.path.join(LOGDIR, name + ".log")
    t0 = time.time()
    try:
        p = subprocess.run([EXE, "--batch-string=run_testsuite(tests=[\"%s\"]);" % name],
                           capture_output=True, text=True, timeout=timeout)
        out = p.stdout + p.stderr
        status = "ok" if p.returncode == 0 else "exit %d" % p.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode(errors="replace") if isinstance(e.stdout, bytes) else (e.stdout or "")
        status = "timeout"
    open(log, "w").write(out)
    m = re.search(r"(\d+)/(\d+) tests passed", out)
    passed, total = (int(m.group(1)), int(m.group(2))) if m else (None, None)
    nprob = len(set(re.findall(r"Problem (\d+) \(line", out)))
    if m is None and "No unexpected errors" in out:
        status = status
    return name, status, passed, total, nprob, time.time() - t0

def main():
    args = sys.argv[1:]
    j, timeout, save = 6, 600, False
    names = []
    while args:
        a = args.pop(0)
        if a == "-j": j = int(args.pop(0))
        elif a == "-t": timeout = int(args.pop(0))
        elif a == "--save": save = True
        else: names.append(a)
    if not names:
        names = testsuite_files()
    rows = []
    with concurrent.futures.ThreadPoolExecutor(j) as ex:
        for r in ex.map(lambda n: run_one(n, timeout), names):
            rows.append(r)
            name, status, passed, total, nprob, dt = r
            res = "%s/%s" % (passed, total) if passed is not None else "CRASH(%d failing seen)" % nprob
            print("%-28s %-10s %-22s %5.0fs" % (name, status, res, dt), flush=True)
    tp = sum(r[2] or 0 for r in rows); tt = sum(r[3] or 0 for r in rows)
    print("TOTAL passed %d of %d in completed files; %d files incomplete" %
          (tp, tt, sum(1 for r in rows if r[2] is None)))
    if save:
        with open(os.path.join(ROOT, "docs", "TESTS.md"), "w") as f:
            f.write("# Core test suite status\n\n| file | status | passed |\n|---|---|---|\n")
            for name, status, passed, total, nprob, dt in rows:
                res = "%s/%s" % (passed, total) if passed is not None else "incomplete"
                f.write("| %s | %s | %s |\n" % (name, status, res))
            f.write("\nTotal: %d of %d in completed files.\n" % (tp, tt))

if __name__ == "__main__":
    main()
