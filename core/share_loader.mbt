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
        None => share_loader__load_maxima_member(path, g)
      }
      share_loader__group_forms(key, g)
    }
    lisp_eval_after_share_load()
    return true
  }
  match share_module_loader(key) {
    Some(f) => {
      f()
      lisp_eval_after_share_load()
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

///|
/// A member of a loader group that is a Maxima file rather than a Lisp file
/// (the loader does `($load "stem")` and Maxima finds `stem.mac` next to
/// it): load it with $load. Members that are Lisp files without a port are
/// skipped.
fn share_loader__load_maxima_member(path : String, member : String) -> Unit raise {
  let dir = match path.rev_find("/") {
    Some(i) => path.substring(end=i)
    None => "."
  }
  let stem = match member.rev_find("/") {
    Some(i) => member.substring(start=i + 1)
    None => member
  }
  if probe_file(dir + "/" + stem + ".lisp") {
    return
  }
  let mac = dir + "/" + stem + ".mac"
  if probe_file(mac) {
    d_load(Str(mac)) |> ignore
  }
}

///|
/// Top-level forms of a loader file between its loads of group members,
/// run after loading MEMBER.
fn share_loader__group_forms(key : String, member : String) -> Unit raise {
  match (key, member) {
    // load-sym-lisp-files.lisp: ($operation) after ($load "ecrivain")
    ("sym/load-sym-lisp-files", "sym/ecrivain") => d_operation() |> ignore
    _ => ()
  }
}
