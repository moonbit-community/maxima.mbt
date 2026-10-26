"""Differential test: run Maxima statements through the reference `maxima`
and through the port, compare 1-D outputs.

usage: python3 tools/difftest.py 'expr1;' 'expr2;' ...
       python3 tools/difftest.py -f file_with_one_statement_per_line
"""
import subprocess, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PORT = os.environ.get("MAXIMA_PORT") or os.path.join(ROOT, "_build", "native", "debug", "build", "cmd", "main", "main.exe")


def run(cmd, stmt, timeout=60):
    try:
        p = subprocess.run(cmd + ["--batch-string=display2d:false$ " + stmt],
                           capture_output=True, text=True, timeout=timeout)
        out = p.stdout
    except subprocess.TimeoutExpired:
        return "<timeout>"
    lines = [l.rstrip() for l in out.splitlines() if l.strip()]
    return "\n".join(l for l in lines if not l.startswith("display2d"))


def main():
    args = sys.argv[1:]
    if args and args[0] == "-f":
        stmts = [l.strip() for l in open(args[1]) if l.strip() and not l.startswith("//")]
    else:
        stmts = args
    ref_cmd = [os.path.join(ROOT, "tools", "maxima-ref"), "--very-quiet", "--no-init"]
    port_cmd = [PORT, "--very-quiet"]
    bad = 0
    for s in stmts:
        a = run(ref_cmd, s)
        b = run(port_cmd, s)
        if a != b:
            bad += 1
            print("MISMATCH:", s)
            print("  ref : " + a.replace("\n", "\n        "))
            print("  port: " + b.replace("\n", "\n        "))
        else:
            print("ok   :", s, "=>", a[:100].replace("\n", " | "))
    print("%d/%d mismatches" % (bad, len(stmts)))


if __name__ == "__main__":
    main()
