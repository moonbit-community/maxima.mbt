# Finishing the port: porting the remaining files

Every remaining Lisp file of Maxima (the core subsystems that were left out
at first, and all share-package Lisp files) is now in the generated contract:
each function has a `declare fn` in `core/gen_decls.mbt` that nobody has
implemented yet. You are porting one area. Read `docs/PORTING.md` (all of
it) and `docs/FIXING.md` first; this file adds what is specific to this
phase.

## Your work

- `python3 tools/unported.py --names <file-prefix>...` lists the declared but
  unimplemented functions per Lisp file (e.g.
  `tools/unported.py --names ../share/logic plot.lisp`). Implement every one
  of them for your files, with exactly the declared signatures
  (`tools/sig.sh <lisp-name>`), translating the Lisp faithfully.
- File names: `core/<lispfile>.mbt` for `src/<lispfile>.lisp`;
  `core/share_<base>.mbt` for share files (split big files as `_1`, `_2`,
  ...), where `<base>` is what `core/gen_init.mbt` uses in
  `init_share_<base>` / `share_load_<base>`.
- Initialization: implement the `init_<file>` / `init_share_<base>`
  function for each of your files (`grep -n "init_share_<base>\|init_<file>" core/gen_*.mbt`):
  non-literal `defvar` initial values (`docs/index/complex_var_inits.tsv`),
  property-list setup (`defprop`, `(setf (get ...))`), top-level forms the
  file runs at load time. Look at an existing share port (e.g.
  `core/share_stringproc*.mbt`, `core/share_draw_*.mbt`) for the pattern.
- Share packages are loaded through `core/share_loader.mbt`: `load("foo")`
  finds `share/.../foo.lisp` (or the `.mac` that loads it) and runs the
  ported file's init. Groups of files loaded by one loader file are in
  `tools/share_groups.json`.
- Code that was hand-written earlier to stand in for your area ("not
  supported in this port", "X is not ported" comments/messages — `grep -rn
  "this port\|not ported" core/`) is yours to replace with the real thing
  when it falls in your area (your brief lists them).

## Checking

- Compare with the reference Maxima, built from the same sources:
  `python3 tools/difftest.py 'load(foo)$' 'expr;' ...` runs both and shows a
  diff. Exercise every user-level function of your files, using the
  package's `rtest_*.mac`, `*.dem`, `*_test.mac` files, and the examples in
  `.repos/maxima/doc/info/*.texi` (and the package's own docs/comments).
- Share test files run with `python3 tools/rtests.py --share <name>` (see
  `share/share_testsuite_files` / `tools/rtests.py`). Core test files with
  `python3 tools/rtests.py <name>`.
- Before each commit: `tools/errs.sh` must show 0 errors, and
  `python3 tools/rtests.py rtest1 rtest4 rtest7 rtest9 rtest10 rtest12 rtest_gcd`
  must not regress (rtest1 is 206/208 before this phase).

## Rules

- You work in your own git worktree (it has no `.repos`; the tools fall back
  to `/Users/dii/git/maxima.mbt/.repos`). Commit your own files only, in
  small focused commits. **Never commit `core/gen_*.mbt`, `tools/db.json` or
  `docs/index/*`** (other agents' contract changes would conflict; the
  integrator regenerates them). If you need a generator change (a missing
  declaration, a wrong signature), make it in `tools/*.py`, regenerate
  locally to keep working (`python3 tools/analyze.py && python3 tools/gen.py
  && python3 tools/gen_init.py && python3 tools/gen_using.py`), commit only
  the `tools/*.py` change, and say so in your report.
- Edits to already-ported files outside your area: keep them minimal and
  mention each in your report (other agents work in parallel).
- Never run `moon fmt` on the project. No `todo` placeholders or
  `abort("unimplemented")`: port everything. If something truly cannot work
  (it needs a facility the runtime lacks), implement the function as
  faithfully as possible, make the missing piece raise a clear Maxima error,
  and list it in your report.
- Final report (short): files ported, pass counts / what you compared
  against the reference, runtime or generator changes, edits outside your
  area, and anything left with a one-line reason each.
