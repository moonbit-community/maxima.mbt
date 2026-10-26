// Runtime support mirroring numerical/f2cl-lib.lisp (as run by SBCL) for the
// translated SLATEC/QUADPACK routines.

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
/// I1MACH: integer machine constants exactly as f2cl-lib's I1MACH returns them
/// under 64-bit SBCL.  I1MACH(9) is MOST-POSITIVE-FIXNUM (2^62 - 1), which does
/// not fit in an Int; it is only ever used in floating-point arithmetic, see
/// `i1mach9_as_double`.
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
/// I1MACH(9) = MOST-POSITIVE-FIXNUM converted to double (as CL contagion does
/// when it is multiplied by a double).
fn i1mach9_as_double() -> Double {
  4611686018427387903L.to_double()
}

///|
fn i_abs(x : Int) -> Int {
  if x < 0 {
    -x
  } else {
    x
  }
}

///|
fn d_abs(x : Double) -> Double {
  x.abs()
}

///|
/// CL MOD on integers (result has the sign of the divisor).
fn i_mod(a : Int, b : Int) -> Int {
  let r = a % b
  if r != 0 && (r < 0) != (b < 0) {
    r + b
  } else {
    r
  }
}

///|
fn i_max(a : Int, b : Int) -> Int {
  if a >= b {
    a
  } else {
    b
  }
}

///|
fn i_min(a : Int, b : Int) -> Int {
  if a <= b {
    a
  } else {
    b
  }
}

///|
/// SBCL's two-argument MAX on doubles: returns the first argument on ties
/// (so (max 0d0 -0d0) is 0d0 and (max -0d0 0d0) is -0d0).
fn d_max(a : Double, b : Double) -> Double {
  if a >= b {
    a
  } else {
    b
  }
}

///|
fn d_min(a : Double, b : Double) -> Double {
  if a <= b {
    a
  } else {
    b
  }
}

///|
fn s_max(a : Float, b : Float) -> Float {
  if a >= b {
    a
  } else {
    b
  }
}

///|
fn s_min(a : Float, b : Float) -> Float {
  if a <= b {
    a
  } else {
    b
  }
}

///|
/// f2cl-lib ISIGN.
fn i_sign(x : Int, y : Int) -> Int {
  if y >= 0 {
    i_abs(x)
  } else {
    -i_abs(x)
  }
}

///|
/// f2cl-lib SIGN/DSIGN on doubles: (float-sign y x), i.e. |x| with the sign
/// bit of y.
fn d_sign(x : Double, y : Double) -> Double {
  let mag = x.reinterpret_as_int64() & 0x7FFFFFFFFFFFFFFFL
  let sgn = y.reinterpret_as_int64() & (-0x7FFFFFFFFFFFFFFFL - 1L)
  (mag | sgn).reinterpret_as_double()
}

///|
/// f2cl-lib INT on a double: truncation toward zero.
fn f_int(x : Double) -> Int {
  x.to_int()
}

///|
/// f2cl-lib AINT/DINT: FTRUNCATE.
fn f_aint(x : Double) -> Double {
  x.trunc()
}

///|
fn f_sqrt(x : Double) -> Double {
  x.sqrt()
}
