// Elementary functions for the non-native backends (wasm, js), which have no
// C libm.  @math's implementations may differ from the platform libm used by
// SBCL in the last bit for some arguments.

///|
fn f_exp(x : Double) -> Double {
  @math.exp(x)
}

///|
fn f_log(x : Double) -> Double {
  @math.ln(x)
}

///|
fn f_pow(x : Double, y : Double) -> Double {
  @math.pow(x, y)
}

///|
fn f_sin(x : Double) -> Double {
  @math.sin(x)
}

///|
fn f_cos(x : Double) -> Double {
  @math.cos(x)
}

///|
fn f_tan(x : Double) -> Double {
  @math.tan(x)
}

///|
fn f_atan(x : Double) -> Double {
  @math.atan(x)
}

///|
fn f_atan2(y : Double, x : Double) -> Double {
  @math.atan2(y, x)
}

///|
fn f_sinh(x : Double) -> Double {
  @math.sinh(x)
}

///|
fn f_cosh(x : Double) -> Double {
  @math.cosh(x)
}

///|
fn f_tanh(x : Double) -> Double {
  @math.tanh(x)
}
