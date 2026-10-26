// Port of share/gamma_simp/isequal.lisp: isequal and isunequal, the
// three-valued equality tests meqp/mnqp reduced to true/false.

///|
fn d_isequal(a : Value, b : Value) -> Value raise {
  lbool(eq(t, meqp(a, b)))
}

///|
fn d_isunequal(a : Value, b : Value) -> Value raise {
  lbool(eq(t, mnqp(a, b)))
}
