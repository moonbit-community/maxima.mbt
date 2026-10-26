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
fn f_exp(x : Double) -> Double {
  c_exp(x)
}

///|
fn f_log(x : Double) -> Double {
  c_log(x)
}

///|
fn f_pow(x : Double, y : Double) -> Double {
  c_pow(x, y)
}

///|
fn f_sin(x : Double) -> Double {
  c_sin(x)
}

///|
fn f_cos(x : Double) -> Double {
  c_cos(x)
}

///|
fn f_tan(x : Double) -> Double {
  c_tan(x)
}

///|
fn f_atan(x : Double) -> Double {
  c_atan(x)
}

///|
fn f_atan2(y : Double, x : Double) -> Double {
  c_atan2(y, x)
}

///|
fn f_sinh(x : Double) -> Double {
  c_sinh(x)
}

///|
fn f_cosh(x : Double) -> Double {
  c_cosh(x)
}

///|
fn f_tanh(x : Double) -> Double {
  c_tanh(x)
}
