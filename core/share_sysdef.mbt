// Port of share/affine/sysdef.lisp, an alternative loader of the affine
// package through the MAKE system of make.lisp.

///|
fn init_share_sysdef() -> Unit raise {
  // (pushnew :cl *features*)
  let cl = kw("cl")
  if memq(cl, symval(q_ear_features)) is Nil {
    set(q_ear_features, cons(cl, symval(q_ear_features))) |> ignore
  }
  let affine = kw("affine")
  setf_get(affine, kw("source-path"), Str("foo.lisp")) |> ignore
  setf_get(affine, kw("object-path"), Str("foo.o")) |> ignore
  // (require "MAKE" "make.lisp"): the MAKE system (share/affine/make.lisp)
  // is not part of the port; load(affine) loads the package instead.
  merr(
    "load: share/affine/sysdef.lisp needs make.lisp, which is not supported in this port; use load(affine)",
    [],
  )
  |> ignore
}
