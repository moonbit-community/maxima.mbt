# Fixing test failures in the MoonBit port

The port (core/*.mbt) is a function-by-function translation of Maxima's Lisp
(`.repos/maxima/src/*.lisp`); see docs/PORTING.md for conventions. Bugs are
translation mistakes: the fix is almost always to make the MoonBit match the
Lisp exactly. Do not "improve" algorithms or rewrite working code.

## Tools

- Build: `moon build` (debug, prints panics with MoonBit backtraces) or
  `moon build --release` (fast). Binaries:
  `_build/native/debug/build/cmd/main/main.exe`,
  `_build/native/release/build/cmd/main/main.exe`.
- Run a test file: `python3 tools/rtests.py rtest_sign` (uses the release
  build; log in `_build/rtests/rtest_sign.log`; set
  `MAXIMA_PORT=_build/native/debug/build/cmd/main/main.exe` to use debug).
  Or directly: `main.exe --batch-string='run_testsuite(tests=["rtest_sign"]);'`
  (add `display_all=true` to see every problem; share tests need
  `share_tests=true`).
- Show problem N of a test file: `python3 tools/rtest_problem.py rtest_sign 12`.
- Reference Maxima built from the same source:
  `tools/maxima-ref --very-quiet --batch-string='display2d:false$ expr;'`.
  Compare both: `python3 tools/difftest.py 'expr1;' 'expr2;'`.
- Call Lisp-level functions from Maxima: `?fname(args)` (e.g. `?sign1(x)`);
  in the reference, `:lisp (print (foo ...))` also works.
- `exit -6` = abort: a MoonBit panic (often an unported/undeclared function:
  the debug build prints the backtrace). `exit -11` = segfault, usually stack
  overflow from infinite recursion: sample the running debug process with
  `sample <pid> 1 -file out.txt` to see the cycle. A log ending without the
  "N/M tests passed" line means the run aborted (an error escaped the test
  harness, or a crash).
- Instrument with `write_stdout(...)` + `flush_stdout()` (MoonBit `println`
  is buffered and lost on crashes). Remove instrumentation before committing.
- Common bug classes found so far: `&rest` parameters passed a single value
  instead of a list (`op_equalp(e, list1(q_x))`); runtime `string_trim(bag, s)`
  argument order; specials bound lexically instead of with `bind`/
  `with_special` (see docs/index/specials.txt and
  docs/index/inherited_specials.tsv); CL `delete` being destructive;
  multiple values dropped.

## Rules

- Work in your worktree; commit small, focused commits with messages naming
  the Lisp function(s) fixed. Never run `moon fmt` on the project. Don't edit
  `core/gen_*.mbt` (report generator issues instead).
- Before each commit, check you didn't break green files:
  `python3 tools/rtests.py rtest4 rtest7 rtest9 rtest10 rtest12 rtest_gcd`
  must stay fully passing.
- Some tests need the `stringproc` share package (being ported by another
  agent); skip problems that fail only for that reason.
- Final report: before/after pass counts for your files, list of bugs fixed
  (file + function), remaining failures with a one-line diagnosis each.
