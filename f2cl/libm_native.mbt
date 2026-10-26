// Elementary functions for the native backend.
//
// SBCL (which runs Maxima's f2cl code) calls the C library's libm for EXP,
// LOG, EXPT, SIN, ... on double-floats, so the native backend binds the very
// same libm entry points to reproduce its results bit for bit.

///|
extern "C" fn c_exp(x : Double) -> Double = "exp"

///|
extern "C" fn c_log(x : Double) -> Double = "log"

///|
extern "C" fn c_pow(x : Double, y : Double) -> Double = "pow"

///|
extern "C" fn c_sin(x : Double) -> Double = "sin"

///|
extern "C" fn c_cos(x : Double) -> Double = "cos"

///|
extern "C" fn c_tan(x : Double) -> Double = "tan"

///|
extern "C" fn c_atan(x : Double) -> Double = "atan"

///|
extern "C" fn c_atan2(y : Double, x : Double) -> Double = "atan2"

///|
extern "C" fn c_sinh(x : Double) -> Double = "sinh"

///|
extern "C" fn c_cosh(x : Double) -> Double = "cosh"

///|
extern "C" fn c_tanh(x : Double) -> Double = "tanh"

///|
pub fn f_exp(x : Double) -> Double {
  c_exp(x)
}

///|
pub fn f_log(x : Double) -> Double {
  c_log(x)
}

///|
pub fn f_pow(x : Double, y : Double) -> Double {
  c_pow(x, y)
}

///|
pub fn f_sin(x : Double) -> Double {
  c_sin(x)
}

///|
pub fn f_cos(x : Double) -> Double {
  c_cos(x)
}

///|
pub fn f_tan(x : Double) -> Double {
  c_tan(x)
}

///|
pub fn f_atan(x : Double) -> Double {
  c_atan(x)
}

///|
pub fn f_atan2(y : Double, x : Double) -> Double {
  c_atan2(y, x)
}

///|
pub fn f_sinh(x : Double) -> Double {
  c_sinh(x)
}

///|
pub fn f_cosh(x : Double) -> Double {
  c_cosh(x)
}

///|
pub fn f_tanh(x : Double) -> Double {
  c_tanh(x)
}

///|
extern "C" fn c_hypot(x : Double, y : Double) -> Double = "hypot"

///|
/// SBCL computes ABS of a (complex double-float) with the C library hypot.
pub fn f_hypot(x : Double, y : Double) -> Double {
  c_hypot(x, y)
}

///|
extern "C" fn c_acos(x : Double) -> Double = "acos"

///|
/// ACOS of a double-float in [-1, 1] (SBCL calls libm acos).
pub fn f_acos(x : Double) -> Double {
  c_acos(x)
}
