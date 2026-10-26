// Port of share/contrib/diffequations/sqfr.lisp (Barton Willis, 2004):
// square-free factorization with provisos, for odelin. The algorithms are
// shared with the port of odelin.lisp (core/share_odelin.mbt).

///|
/// If x is a symbol or a subvarp, return its general representation.
/// Otherwise signal an error---the argument f is the string name of a
/// function that requires the symbol.
fn require_symbol(x : Value, f : Value, a? : Value = Nil) -> Value raise {
  ignore(a)
  share_odelin__require_symbol(x, f)
}

///|
fn d_strictmysqfr(p : Value, x : Value) -> (Value, Value) raise {
  share_odelin__strictmysqfr(p, x)
}

///|
fn d_mysqfr(p : Value, x : Value) -> Value raise {
  share_odelin__mysqfr(p, x)
}

///|
fn init_share_sqfr() -> Unit raise {
  d_put(q_d_sqfr, int(1), q_d_version) |> ignore
  d_load(Str("odeutils")) |> ignore
}
