// Elementary functions for the non-native backends (wasm, js), which have no
// C libm.  @math's implementations may differ from the platform libm used by
// SBCL in the last bit for some arguments.

///|
pub fn f_exp(x : Double) -> Double {
  @math.exp(x)
}

///|
pub fn f_log(x : Double) -> Double {
  @math.ln(x)
}

///|
pub fn f_pow(x : Double, y : Double) -> Double {
  @math.pow(x, y)
}

///|
pub fn f_sin(x : Double) -> Double {
  @math.sin(x)
}

///|
pub fn f_cos(x : Double) -> Double {
  @math.cos(x)
}

///|
pub fn f_tan(x : Double) -> Double {
  @math.tan(x)
}

///|
pub fn f_atan(x : Double) -> Double {
  @math.atan(x)
}

///|
pub fn f_atan2(y : Double, x : Double) -> Double {
  @math.atan2(y, x)
}

///|
pub fn f_sinh(x : Double) -> Double {
  @math.sinh(x)
}

///|
pub fn f_cosh(x : Double) -> Double {
  @math.cosh(x)
}

///|
pub fn f_tanh(x : Double) -> Double {
  @math.tanh(x)
}

///|
pub fn f_hypot(x : Double, y : Double) -> Double {
  @math.hypot(x, y)
}
