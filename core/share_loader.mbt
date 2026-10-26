// Loading of share-package Lisp files. The port has no Lisp loader; share
// Lisp files that have been ported to MoonBit are found by file name and
// their initialization (function registration, variables, top-level forms)
// runs when Maxima loads the file, as CL Maxima runs the file's forms.

///|
/// If `path` names a ported share Lisp file, run it and return true.
fn share_try_load(path : String) -> Bool raise {
  let base = match path.rev_find("/") {
    Some(i) => path.substring(start=i + 1)
    None => path
  }
  let stem = match base.rev_find(".") {
    Some(i) => base.substring(end=i)
    None => base
  }
  // Lisp loader files that only compile/load a defsystem of other files.
  let group = match stem {
    "load-linearalgebra-lisp-files" =>
      [
        "mring", "lu", "linalgcholesky", "eigens-by-jacobi", "linalg-extra", "matrixexp",
        "linalg-utilities",
      ]
    "load-numericalio" => ["encode-decode-float", "numericalio"]
    _ => []
  }
  if group.length() > 0 {
    for g in group {
      match share_module_loader(g) {
        Some(f) => f()
        None => ()
      }
    }
    return true
  }
  match share_module_loader(stem) {
    Some(f) => {
      f()
      true
    }
    None => share_loader__core_source_p(path)
  }
}

///|
/// True when `path` is one of Maxima's own src/*.lisp files (as found by
/// e.g. load("hypergeometric")). Those are all compiled into the port and
/// were initialized at startup; reloading the source in CL Maxima only
/// re-runs idempotent top-level forms, so it is a no-op here.
fn share_loader__core_source_p(path : String) -> Bool raise {
  let srcdir = match symval(q_ear_maxima_srcdir) {
    Str(s) => s
    _ => return false
  }
  let dir = if srcdir.has_suffix("/") { srcdir } else { srcdir + "/" }
  path.has_prefix(dir) &&
  path.has_suffix(".lisp") &&
  !path.substring(start=dir.length()).contains("/")
}
