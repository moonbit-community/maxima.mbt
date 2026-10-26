// SBCL computes double-float elementary functions with the C library's libm;
// binding the same entry points reproduces its results bit for bit.

///|
extern "C" fn libm_exp(x : Double) -> Double = "exp"

///|
extern "C" fn libm_log(x : Double) -> Double = "log"

///|
extern "C" fn libm_pow(x : Double, y : Double) -> Double = "pow"

///|
extern "C" fn libm_sin(x : Double) -> Double = "sin"

///|
extern "C" fn libm_cos(x : Double) -> Double = "cos"

///|
extern "C" fn libm_tan(x : Double) -> Double = "tan"

///|
extern "C" fn libm_atan(x : Double) -> Double = "atan"

///|
extern "C" fn libm_atan2(y : Double, x : Double) -> Double = "atan2"

///|
extern "C" fn libm_asin(x : Double) -> Double = "asin"

///|
extern "C" fn libm_acos(x : Double) -> Double = "acos"

///|
extern "C" fn libm_sinh(x : Double) -> Double = "sinh"

///|
extern "C" fn libm_cosh(x : Double) -> Double = "cosh"

///|
extern "C" fn libm_tanh(x : Double) -> Double = "tanh"

///|
extern "C" fn libm_asinh(x : Double) -> Double = "asinh"

///|
extern "C" fn libm_acosh(x : Double) -> Double = "acosh"

///|
extern "C" fn libm_atanh(x : Double) -> Double = "atanh"

///|
extern "C" fn libm_hypot(x : Double, y : Double) -> Double = "hypot"

///|
extern "C" fn libm_log1p(x : Double) -> Double = "log1p"

///|
extern "C" fn libm_expm1(x : Double) -> Double = "expm1"

///|
/// Public access to libm (for ported code that calls CL math directly on
/// doubles).
pub fn dexp(x : Double) -> Double {
  libm_exp(x)
}

///|
pub fn dlog(x : Double) -> Double {
  libm_log(x)
}

///|
pub fn dpow(x : Double, y : Double) -> Double {
  libm_pow(x, y)
}

///|
pub fn dsin(x : Double) -> Double {
  libm_sin(x)
}

///|
pub fn dcos(x : Double) -> Double {
  libm_cos(x)
}

///|
pub fn dtan(x : Double) -> Double {
  libm_tan(x)
}

///|
pub fn datan(x : Double) -> Double {
  libm_atan(x)
}

///|
pub fn datan2(y : Double, x : Double) -> Double {
  libm_atan2(y, x)
}

///|
pub fn dasin(x : Double) -> Double {
  libm_asin(x)
}

///|
pub fn dacos(x : Double) -> Double {
  libm_acos(x)
}

///|
pub fn dsinh(x : Double) -> Double {
  libm_sinh(x)
}

///|
pub fn dcosh(x : Double) -> Double {
  libm_cosh(x)
}

///|
pub fn dtanh(x : Double) -> Double {
  libm_tanh(x)
}

///|
pub fn dasinh(x : Double) -> Double {
  libm_asinh(x)
}

///|
pub fn dacosh(x : Double) -> Double {
  libm_acosh(x)
}

///|
pub fn datanh(x : Double) -> Double {
  libm_atanh(x)
}

///|
pub fn dhypot(x : Double, y : Double) -> Double {
  libm_hypot(x, y)
}

///|
pub fn dlog1p(x : Double) -> Double {
  libm_log1p(x)
}

///|
pub fn dexpm1(x : Double) -> Double {
  libm_expm1(x)
}
