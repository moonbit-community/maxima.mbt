// SBCL's float printing for FORMAT's ~F, ~E and ~G directives: a port of
// FLONUM-TO-DIGITS (Burger & Dybvig's free-format algorithm, extended by
// Steele & White's fixed-format rounding), FLONUM-TO-STRING,
// FORMAT-FIXED-AUX, FORMAT-EXP-AUX and FORMAT-GENERAL-AUX (SBCL
// src/code/print.lisp and target-format.lisp), so that these directives
// produce exactly the text of the reference Maxima.  A rational argument
// is printed as a single-float, as SBCL does.

///|
/// A float as FORMAT sees it: the integer-decoded significand and exponent,
/// the float's precision and minimum exponent, the sign bit and whether it
/// is a single-float.
priv struct FFloat {
  f : BigInt
  e : Int
  digits : Int
  min_e : Int
  neg : Bool
  zero : Bool
  single : Bool
  inf_or_nan : Bool
  dval : Double
}

///|
fn ffloat_of_double(d : Double) -> FFloat {
  let bits = d.reinterpret_as_uint64()
  let neg = bits >> 63 != 0UL
  let ex = ((bits >> 52) & 0x7ffUL).to_int()
  let man = bits & 0xfffffffffffffUL
  let (f, e) = if ex == 0 {
    (man, -1074)
  } else {
    (man | 0x10000000000000UL, ex - 1075)
  }
  {
    f: BigInt::from_uint64(f),
    e,
    digits: 53,
    min_e: 2 - 1022 - 53,
    neg,
    zero: d == 0.0,
    single: false,
    inf_or_nan: ex == 0x7ff,
    dval: d,
  }
}

///|
fn ffloat_of_single(x : Float) -> FFloat {
  let bits = x.reinterpret_as_uint()
  let neg = bits >> 31 != 0U
  let ex = ((bits >> 23) & 0xffU).reinterpret_as_int()
  let man = bits & 0x7fffffU
  let (f, e) = if ex == 0 { (man, -149) } else { (man | 0x800000U, ex - 150) }
  {
    f: BigInt::from_uint(f),
    e,
    digits: 24,
    min_e: 2 - 126 - 24,
    neg,
    zero: x.to_double() == 0.0,
    single: true,
    inf_or_nan: ex == 0xff,
    dval: x.to_double(),
  }
}

///|
fn FFloat::abs(self : FFloat) -> FFloat {
  { ..self, neg: false }
}

///|
fn ffloat_pow10(n : Int) -> BigInt {
  BigInt::from_int(10).pow(BigInt::from_int(n))
}

///|
/// SBCL's %FLONUM-TO-DIGITS: the digit string and exponent k of a positive
/// float (value = 0.d1d2... * 10^k); with POSITION, rounded at that
/// decimal position (relative to the leading digit when RELATIVEP).
fn ffloat_to_digits(
  x : FFloat,
  position? : Int? = None,
  relativep? : Bool = false,
) -> (Int, String) {
  if x.zero {
    return (0, "0")
  }
  let mut f = x.f
  let mut e = x.e
  let float_digits = x.digits
  // subnormals: left-align the fraction in a FLOAT-DIGITS wide field
  if f.bit_length() < float_digits {
    let shift = float_digits - f.bit_length()
    f = f << shift
    e = e - shift
  }
  let mut high_ok = f % BigInt::from_int(2) == BigInt::from_int(0)
  let mut low_ok = high_ok
  let two = BigInt::from_int(2)
  let ten = BigInt::from_int(10)
  let hidden = two.pow(BigInt::from_int(float_digits - 1))
  let mut r = BigInt::from_int(0)
  let mut s = BigInt::from_int(0)
  let mut mp = BigInt::from_int(0)
  let mut mm = BigInt::from_int(0)
  if e >= 0 {
    let be = two.pow(BigInt::from_int(e))
    mm = be
    if f != hidden {
      r = f << (e + 1)
      s = two
      mp = be
    } else {
      mp = two.pow(BigInt::from_int(e + 1))
      r = f << (e + 2)
      s = BigInt::from_int(4)
    }
  } else if e == x.min_e || f != hidden {
    r = f * two
    s = two.pow(BigInt::from_int(1 - e))
    mp = BigInt::from_int(1)
    mm = BigInt::from_int(1)
  } else {
    r = f * BigInt::from_int(4)
    s = two.pow(BigInt::from_int(2 - e))
    mp = two
    mm = BigInt::from_int(1)
  }
  let sb = StringBuilder::new()
  let generate = (r0 : BigInt, s : BigInt, mp0 : BigInt, mm0 : BigInt) => {
    let mut r = r0
    let mut mp = mp0
    let mut mm = mm0
    while true {
      let rt = r * ten
      let d = (rt / s).to_int()
      r = rt % s
      mp = mp * ten
      mm = mm * ten
      let tc1 = r < mm || (low_ok && r == mm)
      let tc2 = {
        let rmp = r + mp
        rmp > s || (high_ok && rmp == s)
      }
      if tc1 || tc2 {
        let d = if !tc1 && tc2 {
          d + 1
        } else if tc1 && !tc2 {
          d
        } else if r * two < s {
          d
        } else {
          d + 1
        }
        sb.write_char(Int::unsafe_to_char(48 + d))
        break
      }
      sb.write_char(Int::unsafe_to_char(48 + d))
    }
  }
  match position {
    None => {
      let est = (
        (e + f.bit_length() - 1).to_double() *
          (@math.ln(2.0) / @math.ln(10.0)) -
        1.0e-10
      ).ceil().to_int()
      let (r, s, mp, mm) = if est >= 0 {
        (r, s * ffloat_pow10(est), mp, mm)
      } else {
        let sc = ffloat_pow10(-est)
        (r * sc, s, mp * sc, mm * sc)
      }
      // fixup
      let mut k = est
      let mut s = s
      let rmp = r + mp
      if (if high_ok { rmp >= s } else { rmp > s }) {
        k = k + 1
        s = s * ten
      }
      generate(r, s, mp, mm)
      (k, sb.to_string())
    }
    Some(pos0) => {
      let mut position = pos0
      if relativep {
        // k is \hat{k}: the first k with s*10^k >= r+m+
        let mut k = 0
        let mut l = BigInt::from_int(1)
        while s * l < r + mp {
          k = k + 1
          l = l * ten
        }
        // (< (+ r (* s (/ (expt 10 (- k position)) 2))) (* s l)), in
        // integers: scale both sides by 2*10^max(0, position-k)
        let p = k - position
        let lhs = if p >= 0 {
          r * two + s * ffloat_pow10(p)
        } else {
          r * two * ffloat_pow10(-p) + s
        }
        let rhs = if p >= 0 {
          s * l * two
        } else {
          s * l * two * ffloat_pow10(-p)
        }
        position = if lhs < rhs { k - position } else { k - position - 1 }
      }
      // Scale r, s, m+, m- so that x = s*10^position/2 is an integer.
      let dsc = if position >= 0 {
        two
      } else {
        two * ffloat_pow10(-position)
      }
      r = r * dsc
      s = s * dsc
      mp = mp * dsc
      mm = mm * dsc
      let xv = if position >= 0 {
        s * ffloat_pow10(position) / two
      } else {
        s / (two * ffloat_pow10(-position))
      }
      let low = if mm > xv { mm } else { xv }
      let high = if mp > xv { mp } else { xv }
      if mm <= low {
        mm = low
        low_ok = true
      }
      if mp <= high {
        mp = high
        high_ok = true
      }
      let rmp = r + mp
      let mut k = 0
      while rmp > s || (high_ok && rmp == s) {
        k = k + 1
        s = s * ten
      }
      while r > mm &&
            {
              let xx = (r + mp) * ten
              xx < s || (!high_ok && xx == s)
            } {
        k = k - 1
        r = r * ten
        mp = mp * ten
        mm = mm * ten
      }
      generate(r, s, mp, mm)
      (k, sb.to_string())
    }
  }
}

///|
/// SBCL's FLONUM-EXPONENT.
fn ffloat_exponent(x : FFloat) -> Int {
  if x.zero {
    1
  } else {
    ffloat_to_digits(x).0
  }
}

///|
/// SBCL's FLONUM-TO-STRING: (string, length, leading-point, trailing-point).
fn ffloat_to_string(
  x : FFloat,
  width? : Int? = None,
  fdigits? : Int? = None,
  scale? : Int? = None,
  fmin? : Int? = None,
  exponent_zero? : Int? = None,
) -> (String, Int, Bool, Bool) {
  let sc = scale.unwrap_or(0)
  let (e0, string) = match fdigits {
    Some(fd) =>
      ffloat_to_digits(
        x,
        position=Some(
          (-(fd + sc)).min(-fmin.unwrap_or(0)) + exponent_zero.unwrap_or(0),
        ),
      )
    None =>
      match width {
        Some(w) if w > 1 => {
          let neg_sc = match scale {
            Some(s) if s < 0 => s
            _ => 0
          }
          let pw = w - 1 + neg_sc
          let wv = ffloat_to_digits(
            x,
            position=Some(if pw < 1 { 1 } else { pw }),
            relativep=true,
          )
          let fv = ffloat_to_digits(
            x,
            position=Some(-(fmin.unwrap_or(0) + sc)),
          )
          if wv.1.length() >= fv.1.length() {
            wv
          } else {
            fv
          }
        }
        _ => ffloat_to_digits(x)
      }
  }
  let e1 = match exponent_zero {
    Some(ez) => if x.zero { 0 } else { e0 - ez }
    None => e0
  }
  let e = if x.zero { e1 } else { e1 + sc }
  let out = StringBuilder::new()
  let len = string.length()
  if (e == 0 && exponent_zero is Some(_)) || e > 0 {
    out.write_string(string.substring(end=len.min(e)))
    for _ in 0..<(e - len) {
      out.write_char('0')
    }
    out.write_char('.')
    out.write_string(string.substring(start=len.min(e)))
    match fdigits {
      Some(fd) =>
        for _ in 0..<(fd - (len - len.min(e))) {
          out.write_char('0')
        }
      None => ()
    }
  } else {
    out.write_char('.')
    for _ in 0..<(-e) {
      out.write_char('0')
    }
    match fdigits {
      Some(fd) => {
        let end = len.min(fmin.unwrap_or(0).max(fd + e))
        out.write_string(string.substring(end=end.max(0)))
        for _ in 0..<(fd + e - len) {
          out.write_char('0')
        }
      }
      None => out.write_string(string)
    }
  }
  let res = out.to_string()
  (
    res,
    res.length(),
    res.length() > 0 && res[0] == '.',
    res.length() > 0 && res[res.length() - 1] == '.',
  )
}

///|
fn ffloat_prin1(x : FFloat) -> String {
  if x.single && !x.inf_or_nan {
    float_to_string(x.dval)
  } else {
    float_to_string(x.dval)
  }
}

///|
/// FORMAT-FIXED-AUX; the Bool is true when the field overflowed.
fn ffloat_fixed_aux(
  sb : StringBuilder,
  x : FFloat,
  w : Int?,
  d : Int?,
  k : Int?,
  ovf : Char?,
  pad : Char,
  atsign : Bool,
) -> Bool {
  if x.inf_or_nan {
    sb.write_string(ffloat_prin1(x))
    return false
  }
  let mut spaceleft = w.unwrap_or(0)
  if w is Some(_) && (atsign || x.neg) {
    spaceleft -= 1
  }
  let (str, len, lpoint0, tpoint0) = ffloat_to_string(
    x.abs(),
    width=w.map(_ => spaceleft),
    fdigits=d,
    scale=k,
  )
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  if d is Some(0) {
    tpoint = false
  }
  if w is Some(_) {
    spaceleft -= len
    if lpoint {
      if spaceleft > 0 || tpoint {
        spaceleft -= 1
      } else {
        lpoint = false
      }
    }
    if tpoint {
      if spaceleft > 0 {
        spaceleft -= 1
      } else {
        tpoint = false
      }
    }
  }
  match (w, ovf) {
    (Some(wn), Some(oc)) if spaceleft < 0 => {
      for _ in 0..<wn {
        sb.write_char(oc)
      }
      true
    }
    _ => {
      if w is Some(_) {
        for _ in 0..<spaceleft {
          sb.write_char(pad)
        }
      }
      if x.neg {
        sb.write_char('-')
      } else if atsign {
        sb.write_char('+')
      }
      if lpoint {
        sb.write_char('0')
      }
      sb.write_string(str)
      if tpoint {
        sb.write_char('0')
      }
      false
    }
  }
}

///|
/// FORMAT-EXP-AUX.
fn ffloat_exp_aux(
  sb : StringBuilder,
  x : FFloat,
  w : Int?,
  d : Int?,
  e : Int?,
  k : Int,
  ovf : Char?,
  pad : Char,
  marker : Char?,
  atsign : Bool,
) -> Unit {
  if x.inf_or_nan {
    sb.write_string(ffloat_prin1(x))
    return
  }
  let num = x.abs()
  let num_expt = ffloat_exponent(num)
  let expt = num_expt - k
  let estr = expt.abs().to_string()
  let elen = match e {
    Some(en) => en.max(estr.length())
    None => estr.length()
  }
  let mut spaceleft = 0
  if w is Some(wn) {
    spaceleft = wn - 2 - elen
    if atsign || x.neg {
      spaceleft -= 1
    }
  }
  if w is Some(wn) && ovf is Some(oc) && e is Some(en) && elen > en {
    for _ in 0..<wn {
      sb.write_char(oc)
    }
    return
  }
  let fdig = d.map(dn => if k > 0 { 1 + (dn - k) } else { dn })
  let fmin = if k < 0 { Some(1) } else { fdig }
  let (fstr, flen, lpoint0, tpoint0) = ffloat_to_string(
    num,
    width=w.map(_ => spaceleft),
    fdigits=fdig,
    scale=Some(k),
    fmin~,
    exponent_zero=Some(num_expt),
  )
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  if fdig is Some(0) {
    tpoint = false
  }
  if w is Some(_) {
    spaceleft -= flen
    if lpoint {
      if spaceleft > 0 || tpoint {
        spaceleft -= 1
      } else {
        lpoint = false
      }
    }
    if tpoint {
      if spaceleft <= 0 {
        tpoint = false
      } else {
        spaceleft -= 1
      }
    }
  }
  match (w, ovf) {
    (Some(wn), Some(oc)) if spaceleft < 0 =>
      for _ in 0..<wn {
        sb.write_char(oc)
      }
    _ => {
      if w is Some(_) {
        for _ in 0..<spaceleft {
          sb.write_char(pad)
        }
      }
      if x.neg {
        sb.write_char('-')
      } else if atsign {
        sb.write_char('+')
      }
      if lpoint {
        sb.write_char('0')
      }
      sb.write_string(fstr)
      if tpoint {
        sb.write_char('0')
      }
      sb.write_char(
        match marker {
          Some(m) => m
          None => if x.single { 'f' } else { 'e' }
        },
      )
      sb.write_char(if expt < 0 { '-' } else { '+' })
      match e {
        Some(en) =>
          for _ in 0..<(en - estr.length()) {
            sb.write_char('0')
          }
        None => ()
      }
      sb.write_string(estr)
    }
  }
}

///|
/// FORMAT-GENERAL-AUX.
fn ffloat_general_aux(
  sb : StringBuilder,
  x : FFloat,
  w : Int?,
  d : Int?,
  e : Int?,
  k : Int?,
  ovf : Char?,
  pad : Char,
  marker : Char?,
  atsign : Bool,
) -> Unit {
  if x.inf_or_nan {
    sb.write_string(ffloat_prin1(x))
    return
  }
  let a = x.abs()
  let n = ffloat_exponent(a)
  let d = match d {
    Some(dn) => dn
    None => {
      let len = ffloat_to_string(a).1
      let q = if len == 1 { 1 } else { len - 1 }
      q.max(n.min(7))
    }
  }
  let ee = match e {
    Some(en) => en + 2
    None => 4
  }
  let ww = w.map(wn => wn - ee)
  let dd = d - n
  if 0 <= dd && dd <= d {
    let over = ffloat_fixed_aux(sb, x, ww, Some(dd), None, ovf, pad, atsign)
    let ch = if over {
      match ovf {
        Some(c) => c
        None => ' '
      }
    } else {
      ' '
    }
    for _ in 0..<ee {
      sb.write_char(ch)
    }
  } else {
    ffloat_exp_aux(sb, x, w, Some(d), e, k.unwrap_or(1), ovf, pad, marker, atsign)
  }
}

///|
/// The float FORMAT prints for a real argument: floats as themselves,
/// rationals coerced to single-float.
fn ffloat_of_value(v : Value) -> FFloat? raise LispError {
  match v {
    Flo(d) => Some(ffloat_of_double(d))
    Fix(_) | Big(_) | Ratio(_, _) =>
      Some(ffloat_of_single(Float::from_double(to_double(v))))
    _ => None
  }
}

///|
fn fmt_param_int(p : Value?) -> Int? {
  match p {
    Some(Fix(n)) => Some(n.to_int())
    _ => None
  }
}

///|
fn fmt_param_char(p : Value?) -> Char? {
  match p {
    Some(Char(c)) => Some(c)
    _ => None
  }
}

///|
/// FORMAT-PRINC with mincol W: the printed argument padded on the right.
fn fmt_princ_field(sb : StringBuilder, v : Value, w : Int?, pad : Char) -> Unit {
  let s = princ_to_string(v)
  sb.write_string(s)
  match w {
    Some(wn) =>
      for _ in 0..<(wn - s.length()) {
        sb.write_char(pad)
      }
    None => ()
  }
}

///|
/// Write `(decimal-string number)` right-justified in W (FORMAT-WRITE-FIELD
/// for complex numbers given to ~F/~E/~G).
fn fmt_number_field(sb : StringBuilder, v : Value, w : Int?) -> Unit {
  let s = princ_to_string(v)
  match w {
    Some(wn) =>
      for _ in 0..<(wn - s.length()) {
        sb.write_char(' ')
      }
    None => ()
  }
  sb.write_string(s)
}

///|
/// ~w,d,k,ovf,padF
fn fmt_directive_f(sb : StringBuilder, arg : Value, params : Array[Value?], at : Bool) -> Unit raise LispError {
  let w = fmt_param_int(params.get(0).unwrap_or(None))
  let d = fmt_param_int(params.get(1).unwrap_or(None))
  let k = fmt_param_int(params.get(2).unwrap_or(None))
  let ovf = fmt_param_char(params.get(3).unwrap_or(None))
  let pad = fmt_param_char(params.get(4).unwrap_or(None)).unwrap_or(' ')
  match ffloat_of_value(arg) {
    Some(x) => ffloat_fixed_aux(sb, x, w, d, k, ovf, pad, at) |> ignore
    None =>
      if arg is Cplx(_, _) {
        fmt_number_field(sb, arg, w)
      } else {
        fmt_princ_field(sb, arg, w, pad)
      }
  }
}

///|
/// ~w,d,e,k,ovf,pad,markE
fn fmt_directive_e(sb : StringBuilder, arg : Value, params : Array[Value?], at : Bool) -> Unit raise LispError {
  let w = fmt_param_int(params.get(0).unwrap_or(None))
  let d = fmt_param_int(params.get(1).unwrap_or(None))
  let e = fmt_param_int(params.get(2).unwrap_or(None))
  let k = fmt_param_int(params.get(3).unwrap_or(None)).unwrap_or(1)
  let ovf = fmt_param_char(params.get(4).unwrap_or(None))
  let pad = fmt_param_char(params.get(5).unwrap_or(None)).unwrap_or(' ')
  let mark = fmt_param_char(params.get(6).unwrap_or(None))
  match ffloat_of_value(arg) {
    Some(x) => ffloat_exp_aux(sb, x, w, d, e, k, ovf, pad, mark, at)
    None =>
      if arg is Cplx(_, _) {
        fmt_number_field(sb, arg, w)
      } else {
        fmt_princ_field(sb, arg, w, pad)
      }
  }
}

///|
/// ~w,d,e,k,ovf,pad,markG
fn fmt_directive_g(sb : StringBuilder, arg : Value, params : Array[Value?], at : Bool) -> Unit raise LispError {
  let w = fmt_param_int(params.get(0).unwrap_or(None))
  let d = fmt_param_int(params.get(1).unwrap_or(None))
  let e = fmt_param_int(params.get(2).unwrap_or(None))
  let k = fmt_param_int(params.get(3).unwrap_or(None))
  let ovf = fmt_param_char(params.get(4).unwrap_or(None))
  let pad = fmt_param_char(params.get(5).unwrap_or(None)).unwrap_or(' ')
  let mark = fmt_param_char(params.get(6).unwrap_or(None))
  match ffloat_of_value(arg) {
    Some(x) => ffloat_general_aux(sb, x, w, d, e, k, ovf, pad, mark, at)
    None =>
      if arg is Cplx(_, _) {
        fmt_number_field(sb, arg, w)
      } else {
        fmt_princ_field(sb, arg, w, pad)
      }
  }
}
