// Common Lisp numeric tower: fixnum (Int64), bignum, ratio, double-float and
// complex. Generic operations follow CL contagion rules.

///|
using @bigint { type BigInt }

///|
pub fn dsignbit(x : Double) -> Bool {
  x.reinterpret_as_int64() < 0L
}

///|
let big_int64_min : BigInt = BigInt::from_int64(-9223372036854775807L - 1L)

///|
let big_int64_max : BigInt = BigInt::from_int64(9223372036854775807L)

///|
/// Normalize a BigInt into Fix when it fits.
pub fn from_big(b : BigInt) -> Value {
  if b >= big_int64_min && b <= big_int64_max {
    Fix(b.to_int64())
  } else {
    Big(b)
  }
}

///|
pub fn int(n : Int) -> Value {
  Fix(n.to_int64())
}

///|
pub fn int64(n : Int64) -> Value {
  Fix(n)
}

///|
pub fn flo(d : Double) -> Value {
  Flo(d)
}

///|
/// Integer to BigInt.
pub fn to_big(x : Value) -> BigInt raise LispError {
  match x {
    Fix(n) => BigInt::from_int64(n)
    Big(b) => b
    _ => raise type_error(x, "integer")
  }
}

///|
pub fn type_error(x : Value, expected : String) -> LispError {
  Condition(
    intern("type-error"),
    "The value \{x} is not of type \{expected}",
    x,
  )
}

///|
/// Extract a fixnum as Int; raises if not a small integer.
pub fn to_int(x : Value) -> Int raise LispError {
  match x {
    Fix(n) =>
      if n >= -2147483648L && n <= 2147483647L {
        n.to_int()
      } else {
        raise type_error(x, "fixnum")
      }
    _ => raise type_error(x, "fixnum")
  }
}

///|
/// Extract an Int64; raises if not a fixnum.
pub fn to_int64(x : Value) -> Int64 raise LispError {
  match x {
    Fix(n) => n
    _ => raise type_error(x, "fixnum")
  }
}

///|
/// Make a normalized ratio n/d (d != 0).
pub fn make_ratio(n : BigInt, d : BigInt) -> Value raise LispError {
  if d.is_zero() {
    raise Condition(intern("division-by-zero"), "Division by zero", Nil)
  }
  let mut n = n
  let mut d = d
  if d < 0N {
    n = -n
    d = -d
  }
  let g = big_gcd(n, d)
  if !(g == 1N) {
    n = n / g
    d = d / g
  }
  if d == 1N {
    from_big(n)
  } else {
    Ratio(n, d)
  }
}

///|
pub fn big_gcd(a : BigInt, b : BigInt) -> BigInt {
  let mut x = if a < 0N { -a } else { a }
  let mut y = if b < 0N { -b } else { b }
  while !y.is_zero() {
    let r = x % y
    x = y
    y = r
  }
  x
}

///|
fn i64_gcd(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let r = x % y
    x = y
    y = r
  }
  x
}

// ---------------------------------------------------------------------------
// Predicates

///|
pub fn numberp(x : Value) -> Bool {
  x is (Fix(_) | Big(_) | Ratio(_, _) | Flo(_) | Cplx(_, _))
}

///|
pub fn integerp(x : Value) -> Bool {
  x is (Fix(_) | Big(_))
}

///|
/// SBCL's fixnum range is 62 bits plus sign: [-2^62, 2^62 - 1].
pub fn fixnump(x : Value) -> Bool {
  x is Fix(n) && n >= -4611686018427387904L && n <= 4611686018427387903L
}

///|
pub fn bignump(x : Value) -> Bool {
  x is Big(_) || (x is Fix(_) && !fixnump(x))
}

///|
pub fn rationalp(x : Value) -> Bool {
  x is (Fix(_) | Big(_) | Ratio(_, _))
}

///|
pub fn floatp(x : Value) -> Bool {
  x is Flo(_)
}

///|
pub fn realp(x : Value) -> Bool {
  x is (Fix(_) | Big(_) | Ratio(_, _) | Flo(_))
}

///|
pub fn complexp(x : Value) -> Bool {
  x is Cplx(_, _)
}

///|
pub fn ratiop(x : Value) -> Bool {
  x is Ratio(_, _)
}

///|
/// `(zerop x)`
pub fn zerop(x : Value) -> Bool raise LispError {
  match x {
    Fix(n) => n == 0L
    Big(_) | Ratio(_, _) => false
    Flo(d) => d == 0.0
    Cplx(r, i) => zerop(r) && zerop(i)
    _ => raise type_error(x, "number")
  }
}

///|
/// `(plusp x)`
pub fn plusp(x : Value) -> Bool raise LispError {
  match x {
    Fix(n) => n > 0L
    Big(b) => b > 0N
    Ratio(n, _) => n > 0N
    Flo(d) => d > 0.0
    _ => raise type_error(x, "real")
  }
}

///|
/// `(minusp x)`
pub fn minusp(x : Value) -> Bool raise LispError {
  match x {
    Fix(n) => n < 0L
    Big(b) => b < 0N
    Ratio(n, _) => n < 0N
    Flo(d) => d < 0.0
    _ => raise type_error(x, "real")
  }
}

///|
/// `(oddp x)`
pub fn oddp(x : Value) -> Bool raise LispError {
  match x {
    Fix(n) => (n & 1L) == 1L
    Big(b) => !(b % 2N).is_zero()
    _ => raise type_error(x, "integer")
  }
}

///|
/// `(evenp x)`
pub fn evenp(x : Value) -> Bool raise LispError {
  !oddp(x)
}

// ---------------------------------------------------------------------------
// Conversion to double

///|
/// Correctly rounded BigInt -> Double.
pub fn big_to_double(b : BigInt) -> Double {
  if b.is_zero() {
    return 0.0
  }
  let neg = b < 0N
  let a = if neg { -b } else { b }
  let len = a.bit_length()
  let r = if len <= 63 {
    a.to_int64().to_double()
  } else {
    let shift = len - 64
    let top = a.shr(shift)
    let mut u = top.to_uint64()
    // sticky bit for correct rounding
    if !(top.shl(shift) == a) {
      u = u | 1UL
    }
    @math.scalbn(u.to_double(), shift)
  }
  if neg {
    -r
  } else {
    r
  }
}

///|
/// Correctly rounded n/d -> Double (d > 0).
pub fn ratio_to_double(n : BigInt, d : BigInt) -> Double {
  if n.is_zero() {
    return 0.0
  }
  let neg = n < 0N
  let a = if neg { -n } else { n }
  // scale so that the quotient has ~65 bits
  let k = 65 - (a.bit_length() - d.bit_length())
  let (num, den) = if k >= 0 { (a.shl(k), d) } else { (a, d.shl(-k)) }
  let q = num / den
  let rem = num - q * den
  let mut qq = q
  if !rem.is_zero() {
    qq = qq.lor(1N)
  }
  let r = @math.scalbn(big_to_double(qq), -k)
  if neg {
    -r
  } else {
    r
  }
}

///|
/// SBCL traps floating-point overflow and invalid operations: a non-finite
/// result from finite operands signals an arithmetic error.
pub fn ftrap(r : Double, x : Double, y : Double) -> Value raise LispError {
  if (r.is_inf() || r.is_nan()) && !(x.is_inf() || x.is_nan()) &&
    !(y.is_inf() || y.is_nan()) {
    if r.is_nan() {
      raise Condition(
        intern("floating-point-invalid-operation"),
        "arithmetic error FLOATING-POINT-INVALID-OPERATION signalled",
        Nil,
      )
    }
    raise Condition(
      intern("floating-point-overflow"),
      "arithmetic error FLOATING-POINT-OVERFLOW signalled",
      Nil,
    )
  }
  Flo(r)
}

///|
/// `(float x)` / `(coerce x 'double-float)` for reals.
pub fn to_double(x : Value) -> Double raise LispError {
  match x {
    Fix(n) => n.to_double()
    Big(b) => {
      let d = big_to_double(b)
      if d.is_inf() {
        raise Condition(
          intern("floating-point-overflow"),
          "Too large to be represented as a DOUBLE-FLOAT: \{b}",
          x,
        )
      }
      d
    }
    Ratio(n, d) => {
      let r = ratio_to_double(n, d)
      if r.is_inf() {
        raise Condition(
          intern("floating-point-overflow"),
          "Too large to be represented as a DOUBLE-FLOAT",
          x,
        )
      }
      r
    }
    Flo(d) => d
    _ => raise type_error(x, "real")
  }
}

///|
/// `(float x)` as a Value. Complex numbers get float parts.
pub fn lfloat(x : Value) -> Value raise LispError {
  match x {
    Cplx(r, i) => Cplx(Flo(to_double(r)), Flo(to_double(i)))
    _ => Flo(to_double(x))
  }
}

///|
/// Decompose a double into (mantissa integer, exponent, sign), as
/// `integer-decode-float`.
pub fn integer_decode_float(d : Double) -> (BigInt, Int, Int) {
  let bits = d.reinterpret_as_uint64()
  let sign = if (bits >> 63) == 1UL { -1 } else { 1 }
  let expo = ((bits >> 52) & 0x7ffUL).to_int()
  let frac = bits & 0xfffffffffffffUL
  if expo == 0 {
    if frac == 0UL {
      (0N, 0, sign)
    } else {
      (BigInt::from_uint64(frac), -1074, sign)
    }
  } else {
    (BigInt::from_uint64(frac | 0x10000000000000UL), expo - 1075, sign)
  }
}

///|
/// `(rational d)`: exact rational value of a double.
pub fn double_to_rational(d : Double) -> Value raise LispError {
  let (m, e, s) = integer_decode_float(d)
  let mm = if s < 0 { -m } else { m }
  if e >= 0 {
    from_big(mm.shl(e))
  } else {
    make_ratio(mm, 1N.shl(-e))
  }
}

///|
/// `(rational x)`
pub fn rational(x : Value) -> Value raise LispError {
  match x {
    Flo(d) => double_to_rational(d)
    Fix(_) | Big(_) | Ratio(_, _) => x
    _ => raise type_error(x, "real")
  }
}

///|
/// `(rationalize x)`: simplest rational within float precision.
pub fn rationalize(x : Value) -> Value raise LispError {
  match x {
    Flo(d) => {
      if d == 0.0 {
        return Fix(0L)
      }
      // Stern-Brocot / continued fraction search for the simplest rational
      // that rounds to d.
      let neg = d < 0.0
      let a = d.abs()
      let mut p0 = 0N
      let mut q0 = 1N
      let mut p1 = 1N
      let mut q1 = 0N
      let mut v = a
      for _ in 0..<64 {
        let ai = v.floor()
        let aib = from_double_integer(ai)
        let p2 = aib * p1 + p0
        let q2 = aib * q1 + q0
        p0 = p1
        q0 = q1
        p1 = p2
        q1 = q2
        if ratio_to_double(p1, q1) == a {
          break
        }
        let frac = v - ai
        if frac == 0.0 {
          break
        }
        v = 1.0 / frac
      }
      make_ratio(if neg { -p1 } else { p1 }, q1)
    }
    _ => rational(x)
  }
}

///|
/// Integer-valued double to BigInt.
pub fn from_double_integer(d : Double) -> BigInt {
  if d.abs() < 9.0e18 {
    BigInt::from_int64(d.to_int64())
  } else {
    let (m, e, s) = integer_decode_float(d)
    let r = if e >= 0 { m.shl(e) } else { m.shr(-e) }
    if s < 0 {
      -r
    } else {
      r
    }
  }
}

// ---------------------------------------------------------------------------
// Arithmetic

///|
fn level(x : Value) -> Int raise LispError {
  match x {
    Fix(_) | Big(_) => 0
    Ratio(_, _) => 1
    Flo(_) => 2
    Cplx(_, _) => 3
    _ => raise type_error(x, "number")
  }
}

///|
fn ratio_parts(x : Value) -> (BigInt, BigInt) raise LispError {
  match x {
    Fix(n) => (BigInt::from_int64(n), 1N)
    Big(b) => (b, 1N)
    Ratio(n, d) => (n, d)
    _ => raise type_error(x, "rational")
  }
}

///|
fn cparts(x : Value) -> (Value, Value) {
  match x {
    Cplx(r, i) => (r, i)
    _ => (x, Fix(0L))
  }
}

///|
/// Make a complex number following CL canonicalization: a rational complex
/// with zero imaginary part is just the real part.
pub fn make_complex(r : Value, i : Value) -> Value raise LispError {
  match (r, i) {
    (Flo(_), _) | (_, Flo(_)) => Cplx(Flo(to_double(r)), Flo(to_double(i)))
    _ => if i is Fix(0L) { r } else { Cplx(r, i) }
  }
}

///|
/// `(+ a b)`
pub fn num_add(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => {
      let r = x + y
      if ((x ^ r) & (y ^ r)) < 0L {
        Big(BigInt::from_int64(x) + BigInt::from_int64(y))
      } else {
        Fix(r)
      }
    }
    (Flo(x), Flo(y)) => ftrap(x + y, x, y)
    _ => {
      let l = level(a).max(level(b))
      match l {
        0 => from_big(to_big(a) + to_big(b))
        1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          make_ratio(n1 * d2 + n2 * d1, d1 * d2)
        }
        2 => {
          let x = to_double(a)
          let y = to_double(b)
          ftrap(x + y, x, y)
        }
        _ =>
          // As SBCL: the real operand is treated as complex with zero
          // imaginary part (so -0.0 + 0 gives 0.0).
          {
            let (r1, i1) = cparts(a)
            let (r2, i2) = cparts(b)
            make_complex(num_add(r1, r2), num_add(i1, i2))
          }
      }
    }
  }
}

///|
/// `(- a b)`
pub fn num_sub(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => {
      let r = x - y
      if ((x ^ y) & (x ^ r)) < 0L {
        Big(BigInt::from_int64(x) - BigInt::from_int64(y))
      } else {
        Fix(r)
      }
    }
    (Flo(x), Flo(y)) => ftrap(x - y, x, y)
    (Cplx(_, _), _) | (_, Cplx(_, _)) => {
      // As SBCL: componentwise, a real operand having a zero imaginary
      // part (so #c(2.0 -0.0) - 1 keeps -0.0, 1 - #c(2.0 -0.0) gives 0.0).
      let (r1, i1) = cparts(a)
      let (r2, i2) = cparts(b)
      make_complex(num_sub(r1, r2), num_sub(i1, i2))
    }
    (Flo(_), _) | (_, Flo(_)) => {
      let x = to_double(a)
      let y = to_double(b)
      ftrap(x - y, x, y)
    }
    _ => num_add(a, num_neg(b))
  }
}

///|
/// `(- a)`
pub fn num_neg(a : Value) -> Value raise LispError {
  match a {
    Fix(x) =>
      if x == -9223372036854775807L - 1L {
        Big(-BigInt::from_int64(x))
      } else {
        Fix(-x)
      }
    Big(b) => from_big(-b)
    Ratio(n, d) => Ratio(-n, d)
    Flo(d) => Flo(-d)
    Cplx(r, i) => Cplx(num_neg(r), num_neg(i))
    _ => raise type_error(a, "number")
  }
}

///|
/// `(* a b)`
pub fn num_mul(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) =>
      if x > -2147483648L && x < 2147483648L && y > -2147483648L && y < 2147483648L {
        Fix(x * y)
      } else {
        from_big(BigInt::from_int64(x) * BigInt::from_int64(y))
      }
    (Flo(x), Flo(y)) => ftrap(x * y, x, y)
    _ => {
      let l = level(a).max(level(b))
      match l {
        0 => from_big(to_big(a) * to_big(b))
        1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          make_ratio(n1 * n2, d1 * d2)
        }
        2 => {
          let x = to_double(a)
          let y = to_double(b)
          ftrap(x * y, x, y)
        }
        _ =>
          match (a, b) {
            (Cplx(r1, i1), Cplx(r2, i2)) =>
              make_complex(
                num_sub(num_mul(r1, r2), num_mul(i1, i2)),
                num_add(num_mul(r1, i2), num_mul(i1, r2)),
              )
            (Cplx(r1, i1), _) => make_complex(num_mul(r1, b), num_mul(i1, b))
            (_, Cplx(r2, i2)) => make_complex(num_mul(a, r2), num_mul(a, i2))
            _ => raise type_error(a, "number")
          }
      }
    }
  }
}

///|
pub fn division_by_zero() -> LispError {
  Condition(intern("division-by-zero"), "arithmetic error DIVISION-BY-ZERO signalled", Nil)
}

///|
/// `(/ a b)`
pub fn num_div(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Flo(x), Flo(y)) =>
      if y == 0.0 {
        raise division_by_zero()
      } else {
        ftrap(x / y, x, y)
      }
    _ => {
      let l = level(a).max(level(b))
      match l {
        0 | 1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          if n2.is_zero() {
            raise division_by_zero()
          }
          make_ratio(n1 * d2, d1 * n2)
        }
        2 => {
          let y = to_double(b)
          if y == 0.0 {
            raise division_by_zero()
          }
          let x = to_double(a)
          ftrap(x / y, x, y)
        }
        _ =>
          // SBCL's algorithms (Smith-style scaling for complex divisors).
          match (a, b) {
            (Cplx(rx, ix), Cplx(ry, iy)) =>
              if num_gt(num_abs(ry), num_abs(iy)) {
                let r = num_div(iy, ry)
                let dn = num_mul(ry, num_add(Fix(1L), num_mul(r, r)))
                make_complex(
                  num_div(num_add(rx, num_mul(ix, r)), dn),
                  num_div(num_sub(ix, num_mul(rx, r)), dn),
                )
              } else {
                let r = num_div(ry, iy)
                let dn = num_mul(iy, num_add(Fix(1L), num_mul(r, r)))
                make_complex(
                  num_div(num_add(num_mul(rx, r), ix), dn),
                  num_div(num_sub(num_mul(ix, r), rx), dn),
                )
              }
            (Cplx(rx, ix), _) => make_complex(num_div(rx, b), num_div(ix, b))
            (_, Cplx(ry, iy)) =>
              if num_gt(num_abs(ry), num_abs(iy)) {
                let r = num_div(iy, ry)
                let dn = num_mul(ry, num_add(Fix(1L), num_mul(r, r)))
                make_complex(num_div(a, dn), num_div(num_neg(num_mul(a, r)), dn))
              } else {
                let r = num_div(ry, iy)
                let dn = num_mul(iy, num_add(Fix(1L), num_mul(r, r)))
                make_complex(num_div(num_mul(a, r), dn), num_div(num_neg(a), dn))
              }
            _ => raise type_error(a, "number")
          }
      }
    }
  }
}

///|
/// `(/ a)`
pub fn num_inv(a : Value) -> Value raise LispError {
  num_div(Fix(1L), a)
}

///|
/// `(1+ x)`
pub fn one_plus(x : Value) -> Value raise LispError {
  num_add(x, Fix(1L))
}

///|
/// `(1- x)`
pub fn one_minus(x : Value) -> Value raise LispError {
  num_sub(x, Fix(1L))
}

///|
/// Sum of many numbers.
pub fn num_sum(xs : Array[Value]) -> Value raise LispError {
  let mut r = Fix(0L)
  for x in xs {
    r = num_add(r, x)
  }
  r
}

///|
/// Product of many numbers.
pub fn num_prod(xs : Array[Value]) -> Value raise LispError {
  let mut r = Fix(1L)
  for x in xs {
    r = num_mul(r, x)
  }
  r
}

// ---------------------------------------------------------------------------
// Comparison

///|
/// Compare two reals: -1, 0, 1.
pub fn num_compare(a : Value, b : Value) -> Int raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x.compare(y)
    (Flo(x), Flo(y)) => x.compare(y)
    (Flo(x), _) =>
      if x.is_nan() {
        1
      } else if x.is_inf() {
        if x > 0.0 {
          1
        } else {
          -1
        }
      } else {
        num_compare(double_to_rational(x), b)
      }
    (_, Flo(y)) =>
      if y.is_nan() {
        -1
      } else if y.is_inf() {
        if y > 0.0 {
          -1
        } else {
          1
        }
      } else {
        num_compare(a, double_to_rational(y))
      }
    _ => {
      let l = level(a).max(level(b))
      match l {
        0 => to_big(a).compare(to_big(b))
        1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          (n1 * d2).compare(n2 * d1)
        }
        _ => raise type_error(if complexp(a) { a } else { b }, "real")
      }
    }
  }
}

///|
/// `(= a b)`
pub fn num_eq(a : Value, b : Value) -> Bool raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x == y
    (Flo(x), Flo(y)) => x == y
    (Cplx(_, _), _) | (_, Cplx(_, _)) => {
      let (r1, i1) = cparts(a)
      let (r2, i2) = cparts(b)
      num_eq(r1, r2) && num_eq(i1, i2)
    }
    _ => {
      if a is Flo(x) && x.is_nan() {
        return false
      }
      if b is Flo(y) && y.is_nan() {
        return false
      }
      num_compare(a, b) == 0
    }
  }
}

///|
pub fn num_lt(a : Value, b : Value) -> Bool raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x < y
    (Flo(x), Flo(y)) => x < y
    _ => num_compare(a, b) < 0
  }
}

///|
pub fn num_gt(a : Value, b : Value) -> Bool raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x > y
    (Flo(x), Flo(y)) => x > y
    _ => num_compare(a, b) > 0
  }
}

///|
pub fn num_le(a : Value, b : Value) -> Bool raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x <= y
    (Flo(x), Flo(y)) => x <= y
    _ => num_compare(a, b) <= 0
  }
}

///|
pub fn num_ge(a : Value, b : Value) -> Bool raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => x >= y
    (Flo(x), Flo(y)) => x >= y
    _ => num_compare(a, b) >= 0
  }
}

///|
/// `(max a b)` (CL contagion is implementation dependent; keep the winner).
pub fn num_max(a : Value, b : Value) -> Value raise LispError {
  if num_lt(a, b) {
    b
  } else {
    a
  }
}

///|
pub fn num_min(a : Value, b : Value) -> Value raise LispError {
  if num_gt(a, b) {
    b
  } else {
    a
  }
}

///|
/// `(abs x)`
pub fn num_abs(x : Value) -> Value raise LispError {
  match x {
    Fix(n) => if n < 0L { num_neg(x) } else { x }
    Big(b) => if b < 0N { Big(-b) } else { x }
    Ratio(n, d) => if n < 0N { Ratio(-n, d) } else { x }
    Flo(d) => Flo(d.abs())
    Cplx(r, i) => {
      let rd = to_double(r)
      let id = to_double(i)
      Flo(libm_hypot(rd, id))
    }
    _ => raise type_error(x, "number")
  }
}

///|
/// `(signum x)`
pub fn signum(x : Value) -> Value raise LispError {
  match x {
    Flo(d) => Flo(if d > 0.0 { 1.0 } else if d < 0.0 { -1.0 } else { d })
    Cplx(_, _) => if zerop(x) { x } else { num_div(x, num_abs(x)) }
    _ => if zerop(x) { Fix(0L) } else if plusp(x) { Fix(1L) } else { Fix(-1L) }
  }
}

// ---------------------------------------------------------------------------
// Integer division

///|
/// Floor division of BigInts: (q, r) with r having the sign of d.
pub fn big_floor(n : BigInt, d : BigInt) -> (BigInt, BigInt) {
  let q = n / d
  let r = n - q * d
  if !r.is_zero() && (r < 0N) != (d < 0N) {
    (q - 1N, r + d)
  } else {
    (q, r)
  }
}

///|
/// `(floor a b)` -> (quotient, remainder).
pub fn num_floor(a : Value, b? : Value = Fix(1L)) -> (Value, Value) raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) if y != 0L && !(x == -9223372036854775807L - 1L && y == -1L) => {
      let q = x / y
      let r = x - q * y
      if r != 0L && (r < 0L) != (y < 0L) {
        (Fix(q - 1L), Fix(r + y))
      } else {
        (Fix(q), Fix(r))
      }
    }
    _ => {
      if zerop(b) {
        raise division_by_zero()
      }
      let l = level(a).max(level(b))
      match l {
        0 => {
          let (q, r) = big_floor(to_big(a), to_big(b))
          (from_big(q), from_big(r))
        }
        1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          let (q, _) = big_floor(n1 * d2, d1 * n2)
          let qv = from_big(q)
          (qv, num_sub(a, num_mul(qv, b)))
        }
        2 => {
          let x = to_double(a)
          let y = to_double(b)
          let q = (x / y).floor()
          (from_big(from_double_integer(q)), Flo(x - q * y))
        }
        _ => raise type_error(a, "real")
      }
    }
  }
}

///|
/// `(ceiling a b)`
pub fn num_ceiling(a : Value, b? : Value = Fix(1L)) -> (Value, Value) raise LispError {
  let (q, r) = num_floor(a, b~)
  if zerop(r) {
    (q, r)
  } else {
    let q1 = one_plus(q)
    (q1, num_sub(a, num_mul(q1, b)))
  }
}

///|
/// `(truncate a b)`
pub fn num_truncate(a : Value, b? : Value = Fix(1L)) -> (Value, Value) raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) if y != 0L && !(x == -9223372036854775807L - 1L && y == -1L) =>
      (Fix(x / y), Fix(x % y))
    _ => {
      if zerop(b) {
        raise division_by_zero()
      }
      let l = level(a).max(level(b))
      match l {
        0 => {
          let n = to_big(a)
          let d = to_big(b)
          let q = n / d
          (from_big(q), from_big(n - q * d))
        }
        1 => {
          let (n1, d1) = ratio_parts(a)
          let (n2, d2) = ratio_parts(b)
          let q = n1 * d2 / (d1 * n2)
          let qv = from_big(q)
          (qv, num_sub(a, num_mul(qv, b)))
        }
        2 => {
          let x = to_double(a)
          let y = to_double(b)
          let q = (x / y).trunc()
          (from_big(from_double_integer(q)), Flo(x - q * y))
        }
        _ => raise type_error(a, "real")
      }
    }
  }
}

///|
/// `(round a b)`: round half to even.
pub fn num_round(a : Value, b? : Value = Fix(1L)) -> (Value, Value) raise LispError {
  let (q, r) = num_floor(a, b~)
  // compare 2r with b
  let twice = num_mul(Fix(2L), r)
  let c = num_compare(num_abs(twice), num_abs(b))
  let q2 = if c > 0 || (c == 0 && oddp(q)) { one_plus(q) } else { q }
  (q2, num_sub(a, num_mul(q2, b)))
}

///|
/// `(mod a b)`
pub fn num_mod(a : Value, b : Value) -> Value raise LispError {
  num_floor(a, b~).1
}

///|
/// `(rem a b)`
pub fn num_rem(a : Value, b : Value) -> Value raise LispError {
  num_truncate(a, b~).1
}

///|
/// `(floor x)` quotient only.
pub fn floor1(a : Value) -> Value raise LispError {
  num_floor(a).0
}

///|
pub fn ceiling1(a : Value) -> Value raise LispError {
  num_ceiling(a).0
}

///|
pub fn truncate1(a : Value) -> Value raise LispError {
  num_truncate(a).0
}

///|
pub fn round1(a : Value) -> Value raise LispError {
  num_round(a).0
}

///|
/// `(gcd a b)`
pub fn num_gcd(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) if x != -9223372036854775807L - 1L && y != -9223372036854775807L - 1L =>
      Fix(i64_gcd(x, y))
    _ => from_big(big_gcd(to_big(a), to_big(b)))
  }
}

///|
/// `(lcm a b)`
pub fn num_lcm(a : Value, b : Value) -> Value raise LispError {
  if zerop(a) || zerop(b) {
    return Fix(0L)
  }
  num_abs(num_mul(num_truncate(a, b=num_gcd(a, b)).0, b))
}

///|
/// `(numerator x)`
pub fn numerator(x : Value) -> Value raise LispError {
  match x {
    Ratio(n, _) => from_big(n)
    Fix(_) | Big(_) => x
    _ => raise type_error(x, "rational")
  }
}

///|
/// `(denominator x)`
pub fn denominator(x : Value) -> Value raise LispError {
  match x {
    Ratio(_, d) => from_big(d)
    Fix(_) | Big(_) => Fix(1L)
    _ => raise type_error(x, "rational")
  }
}

///|
/// `(isqrt n)`
pub fn isqrt(n : Value) -> Value raise LispError {
  let b = to_big(n)
  if b < 0N {
    raise type_error(n, "unsigned-byte")
  }
  from_big(big_isqrt(b))
}

///|
pub fn big_isqrt(n : BigInt) -> BigInt {
  if n.is_zero() {
    return 0N
  }
  // Newton iteration starting above the root
  let mut x = 1N.shl((n.bit_length() + 1) / 2)
  while true {
    let y = (x + n / x).shr(1)
    if y >= x {
      return x
    }
    x = y
  }
  x
}

// ---------------------------------------------------------------------------
// Bit operations

///|
/// `(ash n count)`
pub fn ash(n : Value, count : Int) -> Value raise LispError {
  match n {
    Fix(x) if count <= 0 =>
      if count <= -64 {
        Fix(if x < 0L { -1L } else { 0L })
      } else {
        Fix(x >> -count)
      }
    _ => {
      let b = to_big(n)
      if count >= 0 {
        from_big(b.shl(count))
      } else {
        // arithmetic shift (floor)
        from_big(big_floor(b, 1N.shl(-count)).0)
      }
    }
  }
}

///|
pub fn logand(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => Fix(x & y)
    _ => from_big(to_big(a).land(to_big(b)))
  }
}

///|
pub fn logior(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => Fix(x | y)
    _ => from_big(to_big(a).lor(to_big(b)))
  }
}

///|
pub fn logxor(a : Value, b : Value) -> Value raise LispError {
  match (a, b) {
    (Fix(x), Fix(y)) => Fix(x ^ y)
    _ => from_big(to_big(a).lxor(to_big(b)))
  }
}

///|
pub fn lognot(a : Value) -> Value raise LispError {
  num_sub(Fix(-1L), a)
}

///|
/// `(logbitp index n)`
pub fn logbitp(index : Int, n : Value) -> Bool raise LispError {
  oddp(ash(n, -index))
}

///|
/// `(integer-length n)`
pub fn integer_length(n : Value) -> Int raise LispError {
  let b = to_big(n)
  if b < 0N {
    (-b - 1N).bit_length()
  } else {
    b.bit_length()
  }
}

///|
/// `(logcount n)`
pub fn logcount(n : Value) -> Int raise LispError {
  let mut b = to_big(n)
  if b < 0N {
    b = -b - 1N
  }
  let mut c = 0
  while !b.is_zero() {
    if !b.land(1N).is_zero() {
      c += 1
    }
    b = b.shr(1)
  }
  c
}

// ---------------------------------------------------------------------------
// Exponentiation

///|
/// `(expt base power)`, dispatching as SBCL's EXPT (src/code/irrat.lisp).
pub fn expt(base : Value, power : Value) -> Value raise LispError {
  match power {
    Fix(_) | Big(_) =>
      if complex_float_p(base) {
        if zerop(power) {
          one_plus(num_mul(base, Fix(0L)))
        } else {
          num_mul(
            expt(num_abs(base), power),
            cis(num_mul(power, phase(base))),
          )
        }
      } else {
        expt_int(base, power)
      }
    Ratio(_, _) =>
      match base {
        Cplx(_, _) =>
          num_mul(
            expt(num_abs(base), power),
            cis(num_mul(power, phase(base))),
          )
        _ => real_expt(base, power)
      }
    Flo(_) =>
      match base {
        Cplx(_, _) => complex_expt(complex_to_double(base), power)
        _ => real_expt(base, power)
      }
    Cplx(_, _) =>
      if complex_float_p(power) {
        match base {
          Cplx(_, _) => complex_expt(complex_to_double(base), power)
          _ => complex_expt(Flo(to_double(base)), power)
        }
      } else {
        complex_expt(base, power)
      }
    _ => raise type_error(power, "number")
  }
}

///|
fn complex_float_p(x : Value) -> Bool {
  x is Cplx(Flo(_), _) || x is Cplx(_, Flo(_))
}

///|
fn complex_to_double(x : Value) -> Value raise LispError {
  match x {
    Cplx(r, i) => Cplx(Flo(to_double(r)), Flo(to_double(i)))
    _ => x
  }
}

///|
/// EXPT's REAL-EXPT: real base and non-integer real power, in doubles.
fn real_expt(base : Value, power : Value) -> Value raise LispError {
  let x = to_double(base)
  let y = to_double(power)
  if x >= 0.0 || x == @double.neg_infinity || y.trunc() == y {
    let r = libm_pow(x, y)
    if x == 0.0 && r.is_inf() {
      raise division_by_zero()
    }
    ftrap(r, x, y)
  } else {
    let y_pi = y * @math.PI
    let pow = libm_pow(-x, y)
    Cplx(Flo(pow * libm_cos(y_pi)), Flo(pow * libm_sin(y_pi)))
  }
}

///|
/// EXPT's COMPLEX-EXPT.
fn complex_expt(base : Value, power : Value) -> Value raise LispError {
  if zerop(power) {
    one_plus(num_mul(base, power))
  } else if zerop(base) && plusp(realpart(power)) {
    num_mul(base, power)
  } else {
    lexp(num_mul(power, llog(base)))
  }
}

///|
fn expt_int(base : Value, power : Value) -> Value raise LispError {
  if minusp(power) {
    return num_div(Fix(1L), expt_int(base, num_neg(power)))
  }
  match base {
    Flo(d) => Flo(libm_pow(d, to_double(power)))
    Fix(1L) => base
    Fix(0L) => if zerop(power) { Fix(1L) } else { base }
    Fix(-1L) => if oddp(power) { base } else { Fix(1L) }
    Fix(_) | Big(_) => {
      let e = to_big(power)
      from_big(to_big(base).pow(e))
    }
    Ratio(n, d) => {
      let e = to_big(power)
      Ratio(n.pow(e), d.pow(e))
    }
    _ => {
      // complex: repeated squaring
      let mut result = Fix(1L)
      let mut b = base
      let mut e = to_big(power)
      while !e.is_zero() {
        if !e.land(1N).is_zero() {
          result = num_mul(result, b)
        }
        b = num_mul(b, b)
        e = e.shr(1)
      }
      result
    }
  }
}

// ---------------------------------------------------------------------------
// Complex parts

///|
pub fn realpart(x : Value) -> Value {
  match x {
    Cplx(r, _) => r
    _ => x
  }
}

///|
pub fn imagpart(x : Value) -> Value {
  match x {
    Cplx(_, i) => i
    Flo(_) => Flo(0.0)
    _ => Fix(0L)
  }
}

///|
/// `(complex r i)`
pub fn complex(r : Value, i? : Value = Fix(0L)) -> Value raise LispError {
  make_complex(r, i)
}

///|
/// `(conjugate x)`
pub fn conjugate(x : Value) -> Value raise LispError {
  match x {
    Cplx(r, i) => Cplx(r, num_neg(i))
    _ => x
  }
}

///|
/// `(phase x)`
pub fn phase(x : Value) -> Value raise LispError {
  match x {
    Cplx(r, i) => Flo(libm_atan2(to_double(i), to_double(r)))
    _ => {
      let d = to_double(x)
      Flo(if d < 0.0 || (d == 0.0 && dsignbit(d)) { libm_atan2(0.0, d) } else { 0.0 })
    }
  }
}

///|
fn cparts_d(x : Value) -> (Double, Double) raise LispError {
  match x {
    Cplx(r, i) => (to_double(r), to_double(i))
    _ => (to_double(x), 0.0)
  }
}

///|
/// Complex exponential: SBCL's `(* (exp (realpart z)) (cis (imagpart z)))`.
pub fn cexp(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (a, b) = cparts_d(x)
      let m = libm_exp(a)
      Cplx(Flo(m * libm_cos(b)), Flo(m * libm_sin(b)))
    }
    _ => Flo(libm_exp(to_double(x)))
  }
}

// ---------------------------------------------------------------------------
// SBCL's complex elementary functions (src/code/irrat.lisp, after Kahan,
// "Branch Cuts for Complex Elementary Functions"). The results are always
// complex double-floats (the port has no single-floats).

///|
fn dsquare(x : Double) -> Double {
  x * x
}

///|
/// `(float-sign x y)`: |y| with the sign of x.
fn dfloat_sign(x : Double, y : Double) -> Double {
  if dsignbit(x) {
    -y.abs()
  } else {
    y.abs()
  }
}

///|
/// LOGB-FINITE: the exponent of x as by DECODE-FLOAT, minus one.
fn logb_finite(x : Double) -> Int {
  let (_, e, _) = decode_float(x)
  e - 1
}

///|
/// The underflow flag that x*x raises: the exact square is nonzero and
/// below the smallest normalized double.
fn square_underflows(x : Double) -> Bool {
  x != 0.0 && !x.is_nan() && !x.is_inf() &&
  (x * x).abs() < least_positive_normalized_double_float
}

///|
/// CSSQS: |(x+i*y)/2^k|^2 scaled to avoid over/underflow, as (rho, k).
fn cssqs(x : Double, y : Double) -> (Double, Int) {
  let rho = dsquare(x) + dsquare(y)
  if (rho.is_inf() || rho.is_nan()) && (x.is_inf() || y.is_inf()) {
    return (@double.infinity, 0)
  }
  // (/ least-positive-double-float double-float-epsilon)
  let threshold = 4.450147717014402e-308
  let overflow = rho.is_inf() && !x.is_nan() && !y.is_nan()
  let underflow = square_underflows(x) ||
    square_underflows(y) ||
    (rho != 0.0 && rho.abs() < least_positive_normalized_double_float)
  if overflow || (underflow && rho < threshold) {
    let k = -logb_finite(x.abs().max(y.abs()))
    (dsquare(@math.scalbn(x, k)) + dsquare(@math.scalbn(y, k)), -k)
  } else {
    (rho, 0)
  }
}

///|
/// COMPLEX-SQRT: principal square root (Kahan's algorithm).
fn complex_sqrt(z : Value) -> Value raise LispError {
  let (x, y) = cparts_d(z)
  let (rho0, k0) = cssqs(x, y)
  let mut rho = rho0
  let mut k = k0
  if !x.is_nan() {
    rho = @math.scalbn(x.abs(), -k) + rho.sqrt()
  }
  if (k & 1) != 0 {
    k = k >> 1
  } else {
    k = (k >> 1) - 1
    rho = rho + rho
  }
  rho = @math.scalbn(rho.sqrt(), k)
  let mut eta = rho
  let mut nu = y
  if rho != 0.0 {
    if !nu.is_inf() {
      nu = nu / rho / 2.0
    }
    if x < 0.0 {
      eta = nu.abs()
      nu = dfloat_sign(y, rho)
    }
  }
  Cplx(Flo(eta), Flo(nu))
}

///|
/// COMPLEX-LOG: log |z| + i arg z.
fn complex_log(z : Value) -> Value raise LispError {
  let t0 = 0x3fe6a09e667f3bcdL.reinterpret_as_double()
  let t1 = 1.2
  let t2 = 3.0
  let ln2 = 0x3fe62e42fefa39efL.reinterpret_as_double()
  let (x, y) = cparts_d(z)
  let (rho, k) = cssqs(x, y)
  let beta = x.abs().max(y.abs())
  let theta = x.abs().min(y.abs())
  let re = if k == 0 && t0 < beta && (beta <= t1 || rho < t2) {
    libm_log1p((beta - 1.0) * (beta + 1.0) + theta * theta) / 2.0
  } else {
    libm_log(rho) / 2.0 + k.to_double() * ln2
  }
  Cplx(Flo(re), Flo(libm_atan2(y, x)))
}

///|
/// Complex logarithm (principal branch): CL `log` of a complex.
pub fn clog(x : Value) -> Value raise LispError {
  complex_log(x)
}

///|
/// COMPLEX-ATANH: (log(1+z) - log(1-z))/2.
fn complex_atanh(z : Value) -> Value raise LispError {
  let theta = most_positive_double_float.sqrt() / 4.0
  let rho = 4.0 / most_positive_double_float.sqrt()
  let half_pi = @math.PI / 2.0
  let (rp, ip) = cparts_d(z)
  let beta = dfloat_sign(rp, 1.0)
  let x = beta * rp
  let y = beta * -ip
  let mut eta = 0.0
  let mut nu = 0.0
  if x > theta || y.abs() > theta {
    nu = dfloat_sign(y, half_pi)
    let x_bigger = x > y.abs()
    let r = if x_bigger { y / x } else { x / y }
    let d = 1.0 + r * r
    eta = if x_bigger { 1.0 / x / d } else { r / y / d }
  } else if x == 1.0 {
    let t1 = 4.0 + dsquare(y)
    let t2 = y.abs() + rho
    eta = libm_log(t1.sqrt().sqrt() / t2.sqrt())
    nu = 0.5 * dfloat_sign(y, half_pi + libm_atan(0.5 * t2))
  } else {
    let t1 = y.abs() + rho
    eta = 0.25 * libm_log1p(4.0 * x / (dsquare(1.0 - x) + dsquare(t1)))
    nu = 0.5 * libm_atan2(2.0 * y, (1.0 - x) * (1.0 + x) - dsquare(t1))
  }
  Cplx(Flo(beta * eta), Flo(-(beta * nu)))
}

///|
/// COMPLEX-TANH: sinh z / cosh z.
fn complex_tanh(z : Value) -> Value raise LispError {
  let (x, y) = cparts_d(z)
  if x.abs() > 0x406633ce8fb9f87dL.reinterpret_as_double() {
    Cplx(Flo(dfloat_sign(x, 1.0)), Flo(dfloat_sign(y, 1.0)))
  } else {
    let tv = libm_tan(y)
    let beta = 1.0 + tv * tv
    let s = libm_sinh(x)
    let rho = (1.0 + s * s).sqrt()
    if tv.is_inf() {
      Cplx(Flo(rho / s), Flo(1.0 / tv))
    } else {
      let den = 1.0 + beta * s * s
      Cplx(Flo(beta * rho * s / den), Flo(tv / den))
    }
  }
}

///|
/// COMPLEX-ACOS: pi/2 - asin z.
fn complex_acos(z : Value) -> Value raise LispError {
  let (ap, ai) = cparts_d(complex_sqrt(num_add(Fix(1L), z)))
  let (bm, bi) = cparts_d(complex_sqrt(num_sub(Fix(1L), z)))
  // (* (conjugate sqrt-1+z) sqrt-1-z)
  let im = ap * bi + -ai * bm
  Cplx(Flo(2.0 * libm_atan(bm / ap)), Flo(libm_asinh(im)))
}

///|
/// COMPLEX-ACOSH: 2 log(sqrt((z+1)/2) + sqrt((z-1)/2)).
fn complex_acosh(z : Value) -> Value raise LispError {
  let (ar, ai) = cparts_d(complex_sqrt(num_sub(z, Fix(1L))))
  let (br, bi) = cparts_d(complex_sqrt(num_add(z, Fix(1L))))
  // (* (conjugate sqrt-z-1) sqrt-z+1)
  let re = ar * br - -ai * bi
  Cplx(Flo(libm_asinh(re)), Flo(2.0 * libm_atan(ai / br)))
}

///|
/// COMPLEX-ASIN: asinh(i z)/i.
fn complex_asin(z : Value) -> Value raise LispError {
  let (ar, ai) = cparts_d(complex_sqrt(num_sub(Fix(1L), z)))
  let (br, bi) = cparts_d(complex_sqrt(num_add(Fix(1L), z)))
  // (realpart (* sqrt-1-z sqrt-1+z))
  let re = ar * br - ai * bi
  // (imagpart (* (conjugate sqrt-1-z) sqrt-1+z))
  let im = ar * bi + -ai * br
  Cplx(Flo(libm_atan(to_double(realpart(z)) / re)), Flo(libm_asinh(im)))
}

///|
/// (complex (- (imagpart z)) (realpart z)), i.e. i*z.
fn complex_times_i(z : Value) -> Value raise LispError {
  make_complex(num_neg(imagpart(z)), realpart(z))
}

///|
/// COMPLEX-ASINH: -i asin(i z).
fn complex_asinh(z : Value) -> Value raise LispError {
  let (r, i) = cparts_d(complex_asin(complex_times_i(z)))
  Cplx(Flo(i), Flo(-r))
}

///|
/// COMPLEX-ATAN: -i atanh(i z).
fn complex_atan(z : Value) -> Value raise LispError {
  let (r, i) = cparts_d(complex_atanh(complex_times_i(z)))
  Cplx(Flo(i), Flo(-r))
}

///|
/// `(exp x)`
pub fn lexp(x : Value) -> Value raise LispError {
  cexp(x)
}

///|
/// `(log x)` — complex result for negative reals, as in CL.
pub fn llog(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_log(x)
    _ => {
      let d = to_double(x)
      if d < 0.0 {
        Cplx(Flo(libm_log(-d)), Flo(@math.PI))
      } else {
        Flo(libm_log(d))
      }
    }
  }
}

///|
/// `(log x base)`
pub fn llog2(x : Value, base : Value) -> Value raise LispError {
  num_div(llog(x), llog(base))
}

///|
/// `(sqrt x)` — complex result for negative reals, as in CL.
pub fn lsqrt(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_sqrt(x)
    _ => {
      let d = to_double(x)
      if d < 0.0 {
        Cplx(Flo(0.0), Flo((-d).sqrt()))
      } else {
        Flo(d.sqrt())
      }
    }
  }
}

///|
fn real_fn(x : Value, f : (Double) -> Double) -> Value raise LispError {
  Flo(f(to_double(x)))
}

///|
pub fn lsin(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (a, b) = cparts_d(x)
      Cplx(Flo(libm_sin(a) * libm_cosh(b)), Flo(libm_cos(a) * libm_sinh(b)))
    }
    _ => real_fn(x, libm_sin)
  }
}

///|
pub fn lcos(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (a, b) = cparts_d(x)
      Cplx(Flo(libm_cos(a) * libm_cosh(b)), Flo(-(libm_sin(a) * libm_sinh(b))))
    }
    _ => real_fn(x, libm_cos)
  }
}

///|
/// `(tan x)`; for complex x, tan z = -i tanh(i z).
pub fn ltan(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (r, i) = cparts_d(complex_tanh(complex_times_i(x)))
      Cplx(Flo(i), Flo(-r))
    }
    _ => real_fn(x, libm_tan)
  }
}

///|
pub fn lsinh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (a, b) = cparts_d(x)
      Cplx(Flo(libm_sinh(a) * libm_cos(b)), Flo(libm_cosh(a) * libm_sin(b)))
    }
    _ => real_fn(x, libm_sinh)
  }
}

///|
pub fn lcosh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => {
      let (a, b) = cparts_d(x)
      Cplx(Flo(libm_cosh(a) * libm_cos(b)), Flo(libm_sinh(a) * libm_sin(b)))
    }
    _ => real_fn(x, libm_cosh)
  }
}

///|
pub fn ltanh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_tanh(x)
    _ => real_fn(x, libm_tanh)
  }
}

///|
/// `(atan y)` or `(atan y x)`
pub fn latan(y : Value, x? : Value) -> Value raise LispError {
  match x {
    Some(xv) => Flo(libm_atan2(to_double(y), to_double(xv)))
    None =>
      match y {
        Cplx(_, _) => complex_atan(y)
        _ => real_fn(y, libm_atan)
      }
  }
}

///|
/// `(asin x)`; complex for |x| > 1.
pub fn lasin(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_asin(x)
    Flo(d) =>
      if d >= -1.0 && d <= 1.0 {
        Flo(libm_asin(d))
      } else {
        complex_asin(Cplx(x, Flo(0.0)))
      }
    _ =>
      if num_ge(x, Fix(-1L)) && num_le(x, Fix(1L)) {
        Flo(libm_asin(to_double(x)))
      } else {
        complex_asin(x)
      }
  }
}

///|
/// `(acos x)`; complex for |x| > 1.
pub fn lacos(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_acos(x)
    Flo(d) =>
      if d >= -1.0 && d <= 1.0 {
        Flo(libm_acos(d))
      } else {
        complex_acos(Cplx(x, Flo(0.0)))
      }
    _ =>
      if num_ge(x, Fix(-1L)) && num_le(x, Fix(1L)) {
        Flo(libm_acos(to_double(x)))
      } else {
        complex_acos(x)
      }
  }
}

///|
pub fn lasinh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_asinh(x)
    _ => real_fn(x, libm_asinh)
  }
}

///|
pub fn lacosh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_acosh(x)
    Flo(d) =>
      if d < 1.0 {
        complex_acosh(Cplx(x, Flo(0.0)))
      } else {
        Flo(libm_acosh(d))
      }
    _ =>
      if num_lt(x, Fix(1L)) {
        complex_acosh(x)
      } else {
        Flo(libm_acosh(to_double(x)))
      }
  }
}

///|
pub fn latanh(x : Value) -> Value raise LispError {
  match x {
    Cplx(_, _) => complex_atanh(x)
    Flo(d) =>
      if d >= -1.0 && d <= 1.0 {
        Flo(libm_atanh(d))
      } else {
        complex_atanh(Cplx(x, Flo(0.0)))
      }
    _ =>
      if num_ge(x, Fix(-1L)) && num_le(x, Fix(1L)) {
        Flo(libm_atanh(to_double(x)))
      } else {
        complex_atanh(x)
      }
  }
}

///|
/// `(cis x)`
pub fn cis(x : Value) -> Value raise LispError {
  let d = to_double(x)
  Cplx(Flo(libm_cos(d)), Flo(libm_sin(d)))
}

///|
/// `(scale-float f k)`
pub fn scale_float(f : Double, k : Int) -> Double {
  @math.scalbn(f, k)
}

///|
/// `(decode-float f)` -> (significand in [0.5,1), exponent, sign)
pub fn decode_float(f : Double) -> (Double, Int, Double) {
  if f == 0.0 {
    return (0.0, 0, if dsignbit(f) { -1.0 } else { 1.0 })
  }
  let (m, e, s) = integer_decode_float(f)
  let len = m.bit_length()
  (@math.scalbn(big_to_double(m), -len), e + len, s.to_double())
}

///|
/// The double-float epsilon used by CL.
pub let double_float_epsilon : Double = 1.1102230246251568e-16

///|
pub let most_positive_double_float : Double = 1.7976931348623157e308

///|
pub let least_positive_double_float : Double = 4.9406564584124654e-324

///|
pub let least_positive_normalized_double_float : Double = 2.2250738585072014e-308

///|
pub let most_positive_fixnum : Value = Fix(4611686018427387903L)

///|
pub let most_negative_fixnum : Value = Fix(-4611686018427387904L)
