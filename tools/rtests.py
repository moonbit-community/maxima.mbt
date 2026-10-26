"""Run Maxima's core test files one per process; print a pass/fail table.

usage: python3 tools/rtests.py [--share] [-j N] [-t TIMEOUT] [--save|--check] [names...]
Writes logs to _build/rtests/<name>.log and a summary to docs/TESTS.md
(docs/TESTS_SHARE.md with --share) with --save. --check instead compares with
that summary and exits with status 1 if any file passes fewer tests than
recorded there (used by CI).
"""
import subprocess, sys, os, re, concurrent.futures, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPOS_DIR = os.environ.get("MAXIMA_REPOS", os.path.join(ROOT, ".repos"))
EXE = os.environ.get("MAXIMA_PORT") or os.path.join(ROOT, "_build", "native", "release", "build", "cmd", "main", "main.exe")
LOGDIR = os.path.join(ROOT, "_build", "rtests")

def testsuite_files(share=False):
    src = open(os.path.join(REPOS_DIR, "maxima", "src", "testsuite.lisp")).read()
    i = src.index("$testsuite_files")
    j = src.index("$share_testsuite_files")
    names = re.findall(r'"(rtest[^"]*)"', src[j:] if share else src[i:j])
    return names

SHARE = False

def run_one(name, timeout):
    os.makedirs(LOGDIR, exist_ok=True)
    log = os.path.join(LOGDIR, name + ".log")
    t0 = time.time()
    try:
        opt = ", share_tests=true" if SHARE else ""
        p = subprocess.run([EXE, "--batch-string=run_testsuite(tests=[\"%s\"]%s);" % (name, opt)],
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
    j, timeout, save, check = 6, 600, False, False
    names = []
    while args:
        a = args.pop(0)
        if a == "-j": j = int(args.pop(0))
        elif a == "-t": timeout = int(args.pop(0))
        elif a == "--save": save = True
        elif a == "--check": check = True
        elif a == "--share":
            global SHARE
            SHARE = True
        else: names.append(a)
    if not names:
        names = testsuite_files(SHARE)
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
    out = "TESTS_SHARE.md" if SHARE else "TESTS.md"
    if check:
        recorded = {}
        for line in open(os.path.join(ROOT, "docs", out)):
            m = re.match(r"\| (\S+) \| [^|]* \| (\d+)/(\d+) \|", line)
            if m:
                recorded[m.group(1)] = int(m.group(2))
        worse = [(r[0], r[2], recorded[r[0]]) for r in rows
                 if r[0] in recorded and (r[2] or 0) < recorded[r[0]]]
        for name, passed, want in worse:
            print("REGRESSION %s: %s passed, docs/%s records %d" % (name, passed, out, want))
        if worse:
            sys.exit(1)
        print("no regressions against docs/%s" % out)
    if save:
        title = "Share" if SHARE else "Core"
        with open(os.path.join(ROOT, "docs", out), "w") as f:
            f.write("# %s test suite status\n\n| file | status | passed |\n|---|---|---|\n" % title)
            for name, status, passed, total, nprob, dt in rows:
                res = "%s/%s" % (passed, total) if passed is not None else "incomplete"
                f.write("| %s | %s | %s |\n" % (name, status, res))
            f.write("\nTotal: %d of %d in completed files.\n" % (tp, tt))

if __name__ == "__main__":
    main()
