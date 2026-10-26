// Port of share/affine/compat.lisp.

///|
/// FORMAT directive function: (format t "~/maxima::tilde-q-fsh/" x)
/// prints X with FSH.
fn tilde_q_fsh(stream : Value, arg : Value, colonp : Value, at_p : Value) -> Value raise {
  ignore(colonp)
  ignore(at_p)
  fsh(arg, stream~)
}

///|
fn init_share_compat() -> Unit raise {
  ()
}
