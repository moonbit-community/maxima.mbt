// Fortran formatted output (f2cl-lib's FFORMAT / EXECUTE-FORMAT) with the
// CL FORMAT directives f2cl generates (~D, ~A, ~E, ~T, ~%), reproducing what
// SBCL prints.  The text goes to `output_hook` (Maxima's standard output when
// the core sets it).

///|
/// An item of an f2cl format list: literal format text (no arguments), a
/// directive consuming one argument (a list item ("~5D") in the Lisp), a
/// group repeated N times, or a group repeated until the data run out (T).
pub(all) enum FmtItem {
  Lit(String)
  Dir(String)
  Rep(Int, Array[FmtItem])
  Forever(Array[FmtItem])
}

///|
/// A datum of a formatted WRITE (after f2cl's flattening of implied DO
/// lists).
pub(all) enum FArg {
  AI(Int)
  AD(Double)
  AS(String)
  AB(Bool)
  AC(Complex)
  /// A value that formats itself: called with the directive it meets
  /// (e.g. ~/bigfloat:format-e/ of the bigfloat-package COBYLA).
  AFn((String) -> String)
}

///|
/// Where formatted output goes (every Fortran unit is standard output).
pub let output_hook : Ref[(String) -> Unit] = { val: default_output }

///|
let pending_output : StringBuilder = StringBuilder()

///|
/// Without a hook, complete lines go to println.
fn default_output(s : String) -> Unit {
  for c in s {
    if c == '\n' {
      println(pending_output.to_string())
      pending_output.reset()
    } else {
      pending_output.write_char(c)
    }
  }
}

///|
priv struct ArgCursor {
  args : Array[FArg]
  mut pos : Int
}

///|
/// FFORMAT: write `args` to unit `unit` under the format list `items`.
pub fn fformat(unit : Int, items : Array[FmtItem], args : Array[FArg]) -> Unit {
  ignore(unit)
  let sb = StringBuilder()
  let cur = { args, pos: 0 }
  execute_format(true, sb, items, cur)
  (output_hook.val)(sb.to_string())
}

///|
/// EXECUTE-FORMAT of f2cl-lib.
fn execute_format(
  top : Bool,
  sb : StringBuilder,
  format : Array[FmtItem],
  cur : ArgCursor,
) -> Unit {
  let mut i = 0
  while true {
    let empty = cur.pos >= cur.args.length()
    if empty || (!top && i >= format.length()) {
      // print the format text that follows
      while i < format.length() {
        match format[i] {
          Lit(s) => format_text(sb, s)
          _ => break
        }
        i = i + 1
      }
      return
    }
    if i >= format.length() {
      // out of formats but not data: restart at the last repeat group
      let mut last = -1
      for k, it in format {
        match it {
          Rep(_, _) | Forever(_) => last = k
          _ => ()
        }
      }
      i = if last >= 0 { last } else { 0 }
    }
    match format[i] {
      Dir(d) => {
        let a = cur.args[cur.pos]
        cur.pos = cur.pos + 1
        format_directive(sb, d, a)
      }
      Rep(n, grp) =>
        for _k in 0..<n {
          execute_format(false, sb, grp, cur)
          if cur.pos >= cur.args.length() {
            break
          }
        }
      Forever(grp) => {
        while cur.pos < cur.args.length() {
          execute_format(false, sb, grp, cur)
          sb.write_char('\n')
        }
        // The Lisp steps past the T but not past its group, so the text
        // that follows the group is never printed: the data is used up and
        // the trailing strings it would print start at the group.
        return
      }
      Lit(s) => format_text(sb, s)
    }
    i = i + 1
  }
}

///|
/// Parse "~p1,p2,...[@]X" (directive parameters, possibly empty, with 'c
/// character parameters).
priv struct Directive {
  params : Array[String?]
  at : Bool
  ch : Char
  len : Int
}

///|
fn parse_directive(cs : Array[Char], start : Int) -> Directive {
  // cs[start] == '~'
  let params : Array[String?] = []
  let mut i = start + 1
  let mut at = false
  let mut cur = StringBuilder()
  let mut have = false
  while i < cs.length() {
    let c = cs[i]
    if c == '\'' {
      cur.write_char(cs[i + 1])
      have = true
      i = i + 2
      continue
    }
    if c == ',' {
      params.push(if have { Some(cur.to_string()) } else { None })
      cur = StringBuilder()
      have = false
      i = i + 1
      continue
    }
    if (c >= '0' && c <= '9') || c == '-' || c == '+' {
      cur.write_char(c)
      have = true
      i = i + 1
      continue
    }
    if c == '@' {
      at = true
      i = i + 1
      continue
    }
    if have || params.length() > 0 {
      params.push(if have { Some(cur.to_string()) } else { None })
    }
    return { params, at, ch: if c >= 'a' && c <= 'z' { Int::unsafe_to_char(c.to_int() - 32) } else { c }, len: i + 1 - start }
  }
  abort("f2cl format: bad directive")
}

///|
fn parse_int(s : String) -> Int {
  let mut v = 0
  let mut neg = false
  for c in s {
    if c == '-' {
      neg = true
    } else if c >= '0' && c <= '9' {
      v = v * 10 + (c.to_int() - '0'.to_int())
    }
  }
  if neg {
    -v
  } else {
    v
  }
}

///|
fn param_int(d : Directive, k : Int, default : Int) -> Int {
  if k < d.params.length() {
    match d.params[k] {
      Some(s) => parse_int(s)
      None => default
    }
  } else {
    default
  }
}

///|
fn param_int_opt(d : Directive, k : Int) -> Int? {
  if k < d.params.length() {
    match d.params[k] {
      Some(s) => Some(parse_int(s))
      None => None
    }
  } else {
    None
  }
}

///|
fn param_char(d : Directive, k : Int) -> Char? {
  if k < d.params.length() {
    match d.params[k] {
      Some(s) => Some(s.to_array()[0])
      None => None
    }
  } else {
    None
  }
}

///|
/// FORMAT with a control string that takes no arguments.
fn format_text(sb : StringBuilder, s : String) -> Unit {
  let cs = s.to_array()
  let mut i = 0
  while i < cs.length() {
    if cs[i] != '~' {
      sb.write_char(cs[i])
      i = i + 1
      continue
    }
    let d = parse_directive(cs, i)
    i = i + d.len
    match d.ch {
      '%' => for _k in 0..<param_int(d, 0, 1) { sb.write_char('\n') }
      '&' => sb.write_char('\n')
      '~' => sb.write_char('~')
      'T' =>
        if d.at {
          // ~colrel,colinc@T: colrel spaces, then to a multiple of colinc
          for _k in 0..<param_int(d, 0, 1) {
            sb.write_char(' ')
          }
        } else {
          sb.write_char(' ')
        }
      _ => abort("f2cl format: unsupported directive in text")
    }
  }
}

///|
fn format_directive(sb : StringBuilder, s : String, a : FArg) -> Unit {
  if a is AFn(f) {
    sb.write_string(f(s))
    return
  }
  let cs = s.to_array()
  let d = parse_directive(cs, 0)
  match d.ch {
    'D' => {
      let w = param_int(d, 0, 0)
      let str = match a {
        AI(n) => n.to_string()
        _ => farg_princ(a)
      }
      for _k in str.length()..<w {
        sb.write_char(' ')
      }
      sb.write_string(str)
    }
    'A' => {
      let w = param_int(d, 0, 0)
      let str = farg_princ(a)
      sb.write_string(str)
      for _k in str.length()..<w {
        sb.write_char(' ')
      }
    }
    'E' =>
      match a {
        AD(x) =>
          format_exp(
            sb,
            x,
            param_int_opt(d, 0),
            param_int_opt(d, 1),
            param_int_opt(d, 2),
            param_int(d, 3, 1),
            param_char(d, 4),
            match param_char(d, 5) {
              Some(c) => c
              None => ' '
            },
            param_char(d, 6),
            d.at,
          )
        AI(n) =>
          format_exp(
            sb,
            n.to_double(),
            param_int_opt(d, 0),
            param_int_opt(d, 1),
            param_int_opt(d, 2),
            param_int(d, 3, 1),
            param_char(d, 4),
            ' ',
            param_char(d, 6),
            d.at,
          )
        _ => sb.write_string(farg_princ(a))
      }
    _ => abort("f2cl format: unsupported directive ~" + d.ch.to_string())
  }
}

///|
fn farg_princ(a : FArg) -> String {
  match a {
    AI(n) => n.to_string()
    AD(x) => x.to_string()
    AS(s) => s
    AB(b) => if b { "T" } else { "F" }
    AC(c) => "#C(" + c.re.to_string() + " " + c.im.to_string() + ")"
    AFn(f) => f("~A")
  }
}

///|
/// SBCL's FORMAT-EXP-AUX (~w,d,e,k,overflowchar,padchar,exptcharE).
fn format_exp(
  sb : StringBuilder,
  number : Double,
  w : Int?,
  d : Int?,
  e : Int?,
  k0 : Int,
  ovf : Char?,
  pad : Char,
  marker : Char?,
  atsign : Bool,
) -> Unit {
  if number.is_nan() || number.is_inf() {
    sb.write_string(number.to_string())
    return
  }
  // The decimal exponent comes from the shortest digits of the number;
  // the mantissa is then rounded to the requested digits (so a mantissa
  // can round up to 10, as in SBCL: (format nil "~21,13,2,0E"
  // 9.999999999999998d0) is "  1.0000000000000E+01").
  let ax = number.abs()
  let e_dec = if ax == 0.0 { 1 } else { flonum_to_digits(ax, None).0 }
  let k = k0
  let expt = e_dec - k
  let estr = expt.abs().to_string()
  let elen = match e {
    Some(ev) => if estr.length() > ev { estr.length() } else { ev }
    None => estr.length()
  }
  let neg = number.reinterpret_as_int64() < 0L
  let mut spaceleft = 0
  match w {
    Some(wv) => {
      spaceleft = wv - 2 - elen
      if atsign || neg {
        spaceleft = spaceleft - 1
      }
    }
    None => ()
  }
  match (w, ovf, e) {
    (Some(wv), Some(oc), Some(ev)) if elen > ev => {
      for _i in 0..<wv {
        sb.write_char(oc)
      }
      return
    }
    _ => ()
  }
  let fdig = match d {
    Some(dv) => Some(if k > 0 { dv - k + 1 } else { dv })
    None => None
  }
  let fmin = if k < 0 { Some(1) } else { fdig }
  let (fstr, flen, lpoint0, tpoint0) = flonum_to_string(ax, fdig, -expt, fmin)
  let mut lpoint = lpoint0
  let mut tpoint = tpoint0
  if d == Some(0) {
    tpoint = false
  }
  if w is Some(_) {
    spaceleft = spaceleft - flen
    if lpoint {
      if spaceleft > 0 || tpoint {
        spaceleft = spaceleft - 1
      } else {
        lpoint = false
      }
    }
    if tpoint {
      if spaceleft > 0 {
        spaceleft = spaceleft - 1
      } else {
        tpoint = false
      }
    }
  }
  match (w, ovf) {
    (Some(wv), Some(oc)) if spaceleft < 0 => {
      for _i in 0..<wv {
        sb.write_char(oc)
      }
      return
    }
    _ => ()
  }
  if w is Some(_) {
    for _i in 0..<spaceleft {
      sb.write_char(pad)
    }
  }
  if neg {
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
      Some(c) => c
      None => 'e'
    },
  )
  sb.write_char(if expt < 0 { '-' } else { '+' })
  match e {
    Some(ev) =>
      for _i in 0..<(ev - estr.length()) {
        sb.write_char('0')
      }
    None => ()
  }
  sb.write_string(estr)
}

///|
/// SBCL's SB-IMPL::FLONUM-TO-STRING with :fdigits/:scale/:fmin (the only
/// form ~E uses): (string, length, leading point, trailing point).
fn flonum_to_string(
  x : Double,
  fdigits : Int?,
  scale : Int,
  fmin : Int?,
) -> (String, Int, Bool, Bool) {
  let (e0, digits) = match fdigits {
    Some(fd) => {
      let fm = match fmin {
        Some(v) => v
        None => 0
      }
      let a = -(fd + scale)
      let b = -(fm + scale)
      flonum_to_digits(x, Some(if a < b { a } else { b }))
    }
    None => flonum_to_digits(x, None)
  }
  let e = if x == 0.0 { e0 } else { e0 + scale }
  let ds = digits.to_array()
  let n = ds.length()
  let sb = StringBuilder()
  if e > 0 {
    let m = if n < e { n } else { e }
    for i in 0..<m {
      sb.write_char(ds[i])
    }
    for _i in 0..<(e - n) {
      sb.write_char('0')
    }
    sb.write_char('.')
    for i in m..<n {
      sb.write_char(ds[i])
    }
    match fdigits {
      Some(fd) =>
        for _i in 0..<(fd - (n - m)) {
          sb.write_char('0')
        }
      None => ()
    }
  } else {
    sb.write_char('.')
    for _i in 0..<(-e) {
      sb.write_char('0')
    }
    let end = match fdigits {
      Some(fd) => {
        let v = if n < fd + e { n } else { fd + e }
        if v > 0 {
          v
        } else {
          0
        }
      }
      None => n
    }
    for i in 0..<end {
      sb.write_char(ds[i])
    }
    match fdigits {
      Some(fd) =>
        for _i in 0..<(fd + e - n) {
          sb.write_char('0')
        }
      None => ()
    }
  }
  let s = sb.to_string()
  let sc = s.to_array()
  (s, sc.length(), sc[0] == '.', sc[sc.length() - 1] == '.')
}

///|
/// SBCL's SB-IMPL::FLONUM-TO-DIGITS (Burger & Dybvig's free-format
/// algorithm, with SBCL's absolute-position cutoff): (k, digits) with
/// x ~ 0.digits * 10^k.
fn flonum_to_digits(v : Double, position : Int?) -> (Int, String) {
  let bits = v.reinterpret_as_int64()
  let bexp = ((bits >> 52) & 0x7FFL).to_int()
  let mant = bits & 0xFFFFFFFFFFFFFL
  let (f, e) = if bexp == 0 {
    (mant, -1074)
  } else {
    (mant | 0x10000000000000L, bexp - 1075)
  }
  let min_e = -1074
  let mut high_ok = f % 2L == 0L
  let mut low_ok = high_ok
  let bf = @bigint.BigInt::from_int64(f)
  let two = @bigint.BigInt::from_int(2)
  let ten = @bigint.BigInt::from_int(10)
  let hidden = 0x10000000000000L
  let mut r = bf
  let mut s = two
  let mut mp = @bigint.BigInt::from_int(1)
  let mut mm = @bigint.BigInt::from_int(1)
  if e >= 0 {
    let be = two.pow(@bigint.BigInt::from_int(e))
    if f != hidden {
      r = bf * be * two
      s = two
      mp = be
      mm = be
    } else {
      mm = be
      mp = be * two
      r = bf * mp * two
      s = two * two
    }
  } else if e == min_e || f != hidden {
    r = bf * two
    s = two.pow(@bigint.BigInt::from_int(-e)) * two
    mp = @bigint.BigInt::from_int(1)
    mm = @bigint.BigInt::from_int(1)
  } else {
    mm = @bigint.BigInt::from_int(1)
    mp = two
    r = bf * two * two
    s = two.pow(@bigint.BigInt::from_int(1 - e)) * two
  }
  // The cutoff x = s * 10^position / 2 may be a fraction: scale r, s, m+,
  // m- by 2 * 10^(-position) so that everything stays an integer.
  match position {
    Some(pos) => {
      let scl = if pos < 0 {
        ten.pow(@bigint.BigInt::from_int(-pos)) * two
      } else {
        two
      }
      r = r * scl
      mp = mp * scl
      mm = mm * scl
      let xs = if pos < 0 { s } else { s * ten.pow(@bigint.BigInt::from_int(pos)) }
      s = s * scl
      // x = s_orig * 10^pos / 2, in the scaled units: s_orig * 10^pos / 2 * scl
      let x = xs
      if mm <= x {
        mm = x
      }
      low_ok = true
      if mp <= x {
        mp = x
      }
      high_ok = true
    }
    None => ()
  }
  // scale
  let mut k = 0
  while true {
    let rmp = r + mp
    if rmp > s || (high_ok && rmp == s) {
      s = s * ten
      k = k + 1
    } else {
      break
    }
  }
  while true {
    let xx = (r + mp) * ten
    if r > mm && (xx < s || (!high_ok && xx == s)) {
      r = r * ten
      mp = mp * ten
      mm = mm * ten
      k = k - 1
    } else {
      break
    }
  }
  // generate
  let sb = StringBuilder()
  while true {
    let rt = r * ten
    let dq = rt / s
    r = rt - dq * s
    let d = dq.to_int()
    mp = mp * ten
    mm = mm * ten
    let tc1 = r < mm || (low_ok && r == mm)
    let tc2 = r + mp > s || (high_ok && r + mp == s)
    if tc1 || tc2 {
      let dd = if !tc1 && tc2 {
        d + 1
      } else if tc1 && !tc2 {
        d
      } else if r * two < s {
        d
      } else {
        d + 1
      }
      sb.write_char(Int::unsafe_to_char('0'.to_int() + dd))
      break
    }
    sb.write_char(Int::unsafe_to_char('0'.to_int() + d))
  }
  (k, sb.to_string())
}
