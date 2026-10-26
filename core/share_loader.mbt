// Loading of share-package Lisp files. The port has no Lisp loader; share
// Lisp files that have been ported to MoonBit are found by their directory
// and file name (e.g. "stringproc/printf"), and their initialization
// (function registration, variables, top-level forms) runs when Maxima
// loads the file, as CL Maxima runs the file's forms.

///|
/// "dir/stem" of a path: the parent directory name and the file name
/// without extension.
fn share_loader__key(path : String) -> String {
  let parts = path.split("/").to_array().map(v => v.to_string())
  let n = parts.length()
  let base = parts[n - 1]
  let stem = match base.rev_find(".") {
    Some(i) => base.substring(end=i)
    None => base
  }
  if n >= 2 {
    parts[n - 2] + "/" + stem
  } else {
    stem
  }
}

///|
/// If `path` names a ported share Lisp file (or a loader file for a group
/// of them), run it and return true.
fn share_try_load(path : String) -> Bool raise {
  let key = share_loader__key(path)
  if share_module_group(key) is Some(group) {
    for g in group {
      match share_module_loader(g) {
        Some(f) => f()
        None => ()
      }
    }
    return true
  }
  match share_module_loader(key) {
    Some(f) => {
      f()
      true
    }
    None => false
  }
}
