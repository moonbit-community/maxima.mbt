// (complex double-float) arithmetic as SBCL performs it in the compiled f2cl
// code (f2cl's COMPLEX*16 is CL's (complex double-float)).  Checked against
// SBCL 2.6.9 bit for bit:
//
// * + - and / with a real operand convert it to a complex with imaginary
//   part 0d0 first ((+ #c(1d0 -0d0) 2d0) is #c(3d0 0d0)); * by a real
//   scales both parts ((* #c(1d0 -0d0) 2) is #c(2d0 -0d0)).
// * Complex division is Smith's algorithm with the denominator
//   ry + r*iy (SBCL's deftransform for (complex double-float)).
// * ABS is the C library's hypot; SQRT is SBCL's COMPLEX-SQRT (Kahan).

///|
pub(all) struct Complex {
  re : Double
  im : Double
}

///|
pub fn cplx(re : Double, im : Double) -> Complex {
  { re, im }
}

///|
pub let c_zero : Complex = { re: 0.0, im: 0.0 }

///|
pub fn c_add(a : Complex, b : Complex) -> Complex {
  { re: a.re + b.re, im: a.im + b.im }
}

///|
pub fn c_sub(a : Complex, b : Complex) -> Complex {
  { re: a.re - b.re, im: a.im - b.im }
}

///|
pub fn c_mul(a : Complex, b : Complex) -> Complex {
  { re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re }
}

///|
pub fn d_mul_c(x : Double, b : Complex) -> Complex {
  { re: x * b.re, im: x * b.im }
}

///|
pub fn c_mul_d(a : Complex, x : Double) -> Complex {
  { re: a.re * x, im: a.im * x }
}

///|
pub fn c_div(x : Complex, y : Complex) -> Complex {
  let rx = x.re
  let ix = x.im
  let ry = y.re
  let iy = y.im
  if ry.abs() > iy.abs() {
    let r = iy / ry
    let dn = ry + r * iy
    { re: (rx + ix * r) / dn, im: (ix - rx * r) / dn }
  } else {
    let r = ry / iy
    let dn = iy + r * ry
    { re: (rx * r + ix) / dn, im: (ix * r - rx) / dn }
  }
}

///|
pub fn c_neg(a : Complex) -> Complex {
  { re: -a.re, im: -a.im }
}

///|
pub fn c_conj(a : Complex) -> Complex {
  { re: a.re, im: -a.im }
}

///|
/// CL = on complex numbers (both parts numerically equal).
pub fn c_eq(a : Complex, b : Complex) -> Bool {
  a.re == b.re && a.im == b.im
}

///|
pub fn c_abs(a : Complex) -> Double {
  f_hypot(a.re, a.im)
}

///|
fn pow2(k : Int) -> Double {
  // 2^k for -1022 <= k <= 1023
  ((k + 1023).to_int64() << 52).reinterpret_as_double()
}

///|
fn scalb(x : Double, k : Int) -> Double {
  // x * 2^k, exact unless it over/underflows
  let mut r = x
  let mut n = k
  while n > 1023 {
    r = r * pow2(1023)
    n = n - 1023
  }
  while n < -1022 {
    r = r * pow2(-1022)
    n = n + 1022
  }
  r * pow2(n)
}

///|
/// SBCL's LOGB-FINITE: the unbiased exponent of a finite nonzero x.
fn logb_finite(x : Double) -> Int {
  let bits = x.reinterpret_as_int64()
  let e = ((bits >> 52) & 0x7FFL).to_int()
  if e == 0 {
    // denormal
    let mut m = bits & 0xFFFFFFFFFFFFFL
    let mut k = -1022
    while (m & 0x10000000000000L) == 0L {
      m = m << 1
      k = k - 1
    }
    k
  } else {
    e - 1023
  }
}

///|
/// SBCL's CSSQS: |z|^2 scaled to avoid overflow/underflow, as (rho, k) with
/// |z|^2 = rho * 4^k.
fn cssqs(x : Double, y : Double) -> (Double, Int) {
  let rho = x * x + y * y
  if (rho.is_nan() || rho.is_inf()) && (x.is_inf() || y.is_inf()) {
    return (@double.infinity, 0)
  }
  // least-positive-double-float / double-float-epsilon
  let threshold = 0x001FFFFFFFFFFFFEL.reinterpret_as_double()
  if rho.is_inf() || (rho < threshold && (x != 0.0 || y != 0.0)) {
    let k = -logb_finite(if x.abs() >= y.abs() { x.abs() } else { y.abs() })
    let sx = scalb(x, k)
    let sy = scalb(y, k)
    return (sx * sx + sy * sy, -k)
  }
  (rho, 0)
}

///|
/// SBCL's COMPLEX-SQRT (Kahan's algorithm).
pub fn c_sqrt(z : Complex) -> Complex {
  let x = z.re
  let y = z.im
  let (rho0, k0) = cssqs(x, y)
  let mut rho = rho0
  let mut k = k0
  if !x.is_nan() {
    rho = scalb(x.abs(), -k) + rho.sqrt()
  }
  if k % 2 != 0 {
    k = k >> 1
  } else {
    k = (k >> 1) - 1
    rho = rho + rho
  }
  rho = scalb(rho.sqrt(), k)
  let mut eta = rho
  let mut nu = y
  if rho != 0.0 {
    if !nu.abs().is_inf() {
      nu = nu / rho / 2.0
    }
    if x < 0.0 {
      eta = nu.abs()
      nu = d_sign(rho, y)
    }
  }
  { re: eta, im: nu }
}
