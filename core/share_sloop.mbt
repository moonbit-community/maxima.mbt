// Port of share/utils/sloop.lisp: the deprecated cl-sloop:sloop macro,
// which warns and expands into CL loop.

///|
/// Macro expander: returns the expansion `(loop ,@body)`.
fn cl_sloop_sloop(body : Value) -> Value raise {
  format(error_output, "~&WARNING: ~A~%", [
    Str("Using deprecated macro 'sloop'. Use 'loop' instead."),
  ])
  |> ignore
  cons(q_loop, body)
}
