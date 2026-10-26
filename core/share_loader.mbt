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
  match share_module_loader(stem) {
    Some(f) => {
      f()
      true
    }
    None => false
  }
}
