// Runtime support mirroring numerical/f2cl-lib.lisp (as run by SBCL) for the
// f2cl-translated share packages (lbfgs, odepack, lapack).  The same helpers
// as slatec/f2cl_runtime.mbt, public so that those packages can share them.

///|
/// D1MACH: double-precision machine constants exactly as f2cl-lib's D1MACH
/// returns them under SBCL.  Note that (3) and (4) are derived from SBCL's
/// DOUBLE-FLOAT-EPSILON, which is 2^-53 + 2^-105 (one ulp above 2^-53).
pub fn d1mach(i : Int) -> Double {
  match i {
    1 => 4503599627370496L.reinterpret_as_double() // 2.2250738585072014e-308
    2 => 9218868437227405311L.reinterpret_as_double() // 1.7976931348623157e308
    3 => 4368491638549381121L.reinterpret_as_double() // 1.1102230246251568e-16
    4 => 4372995238176751617L.reinterpret_as_double() // 2.2204460492503136e-16
    5 => 4599094494223104510L.reinterpret_as_double() // 0.30102999566398114
    _ => abort("d1mach: invalid argument")
  }
}

///|
/// I1MACH: integer machine constants as f2cl-lib's I1MACH returns them under
/// 64-bit SBCL (I1MACH(9), MOST-POSITIVE-FIXNUM, is `i1mach9_as_double`).
pub fn i1mach(i : Int) -> Int {
  match i {
    1 => 5
    2 => 6
    3 => 6
    4 => 6
    5 => 62
    6 => 4
    7 => 2
    8 => 62
    10 => 2
    11 => 24
    12 => -124
    13 => 127
    14 => 53
    15 => -1020
    16 => 1023
    _ => abort("i1mach: invalid argument")
  }
}

///|
pub fn i1mach9_as_double() -> Double {
  4611686018427387903L.to_double()
}

///|
pub fn i_abs(x : Int) -> Int {
  if x < 0 {
    -x
  } else {
    x
  }
}

///|
pub fn d_abs(x : Double) -> Double {
  x.abs()
}

///|
/// CL MOD on integers (result has the sign of the divisor).
pub fn i_mod(a : Int, b : Int) -> Int {
  let r = a % b
  if r != 0 && (r < 0) != (b < 0) {
    r + b
  } else {
    r
  }
}

///|
pub fn i_max(a : Int, b : Int) -> Int {
  if a >= b {
    a
  } else {
    b
  }
}

///|
pub fn i_min(a : Int, b : Int) -> Int {
  if a <= b {
    a
  } else {
    b
  }
}

///|
/// SBCL's two-argument MAX on doubles: returns the first argument on ties.
pub fn d_max(a : Double, b : Double) -> Double {
  if a >= b {
    a
  } else {
    b
  }
}

///|
pub fn d_min(a : Double, b : Double) -> Double {
  if a <= b {
    a
  } else {
    b
  }
}

///|
pub fn s_max(a : Float, b : Float) -> Float {
  if a >= b {
    a
  } else {
    b
  }
}

///|
pub fn s_min(a : Float, b : Float) -> Float {
  if a <= b {
    a
  } else {
    b
  }
}

///|
/// f2cl-lib ISIGN.
pub fn i_sign(x : Int, y : Int) -> Int {
  if y >= 0 {
    i_abs(x)
  } else {
    -i_abs(x)
  }
}

///|
/// f2cl-lib SIGN/DSIGN on doubles: (float-sign y x).
pub fn d_sign(x : Double, y : Double) -> Double {
  let mag = x.reinterpret_as_int64() & 0x7FFFFFFFFFFFFFFFL
  let sgn = y.reinterpret_as_int64() & (-0x7FFFFFFFFFFFFFFFL - 1L)
  (mag | sgn).reinterpret_as_double()
}

///|
/// f2cl-lib INT on a double: truncation toward zero.
pub fn f_int(x : Double) -> Int {
  x.to_int()
}

///|
/// f2cl-lib AINT/DINT: FTRUNCATE.
pub fn f_aint(x : Double) -> Double {
  x.trunc()
}

///|
/// f2cl-lib NINT: CL ROUND, which rounds halfway cases to even.
pub fn f_nint(x : Double) -> Int {
  let t = x.trunc()
  let r = x - t
  if r.abs() == 0.5 {
    let ti = t.to_int()
    if ti % 2 == 0 {
      ti
    } else if x > 0.0 {
      ti + 1
    } else {
      ti - 1
    }
  } else {
    x.round().to_int()
  }
}

///|
pub fn f_sqrt(x : Double) -> Double {
  x.sqrt()
}

///|
/// f2cl-lib LOG10 on a double: (log x 10d0) = (/ (log x) (log 10d0)).
pub fn f_log10(x : Double) -> Double {
  f_log(x) / f_log(10.0)
}

///|
/// CL EXPT on integers (non-negative exponent).
pub fn i_pow(b : Int, e : Int) -> Int {
  let mut r = 1
  let mut k = 0
  while k < e {
    r = r * b
    k = k + 1
  }
  r
}

///|
/// (expt x 2), which SBCL compiles as (* x x).
pub fn d_sq(x : Double) -> Double {
  x * x
}
