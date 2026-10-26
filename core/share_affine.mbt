// Port of share/affine/affine.lisp, the loader of the affine package:
// `load(affine)` compiles and loads the files of affine.system. The files
// are compiled into the port; the share loader runs their initializations
// in the order of affine.system (the "affine/affine" group of
// tools/share_groups.json), so this file has nothing left to do.

///|
fn init_share_affine() -> Unit raise {
  ()
}
