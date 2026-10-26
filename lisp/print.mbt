///|
/// Decompose a finite nonzero double into its shortest round-trip decimal
/// digits and exponent: value = 0.d1d2d3... * 10^exp.
pub fn float_digits(d : Double) -> (String, Int) {
  // SBCL's FLONUM-TO-DIGITS: on a tie between two shortest digit strings
  // it rounds the last digit up.
  let (k, digits) = ffloat_to_digits(ffloat_of_double(d.abs()))
  (digits, k)
}

///|
/// SBCL's FLONUM-TO-DIGITS (Burger & Dybvig free-format) for a positive
/// subnormal double. SBCL's INTEGER-DECODE-FLOAT normalizes a subnormal's
/// significand to 53 bits, so its digit generation runs at full double
/// precision and prints more digits than the shortest representation.
/// Returns (digits, exponent) with value = 0.d1d2... * 10^exponent.
fn subnormal_digits(d : Double) -> (String, Int) {
  let (sig, _, _) = integer_decode_float(d)
  let extra = 53 - sig.bit_length()
  let f = sig.shl(extra)
  let e = -1074 - extra
  let high_ok = (f % 2N).is_zero()
  let low_ok = high_ok
  // e < 0 and e != min-e, f != 2^52 (generally): r = 2f, s = 2^(1-e), m = 1
  let two52 = 1N.shl(52)
  let (r0, s0, mp0, mm0) = if f == two52 {
    (f * 4N, 1N.shl(1 - e + 1), 2N, 1N)
  } else {
    (f * 2N, 1N.shl(-e + 1), 1N, 1N)
  }
  let mut r = r0
  let mut s = s0
  let mut mp = mp0
  let mut mm = mm0
  let ten = 10N
  // scale: find k with 10^(k-1) <= (r+m+)/s < 10^k
  let mut k = 0
  while (r + mp) > s || (high_ok && r + mp == s) {
    s = s * ten
    k += 1
  }
  while (r + mp) * ten < s || (!high_ok && (r + mp) * ten == s) {
    r = r * ten
    mp = mp * ten
    mm = mm * ten
    k -= 1
  }
  let sb = StringBuilder::new()
  while true {
    let rr = r * ten
    let dgt = rr / s
    r = rr - dgt * s
    mp = mp * ten
    mm = mm * ten
    let tc1 = r < mm || (low_ok && r == mm)
    let tc2 = r + mp > s || (high_ok && r + mp == s)
    if tc1 || tc2 {
      let dv = if !tc1 && tc2 {
        dgt + 1N
      } else if tc1 && !tc2 {
        dgt
      } else if r * 2N < s {
        dgt
      } else {
        dgt + 1N
      }
      sb.write_string(dv.to_string())
      break
    }
    sb.write_string(dgt.to_string())
  }
  (sb.to_string(), k)
}

///|
/// Print a double the way SBCL's `prin1` does with
/// `*read-default-float-format*` = double-float.
pub fn float_to_string(d : Double) -> String {
  if d.is_nan() {
    return "NaN"
  }
  if d.is_pos_inf() {
    return "Infinity"
  }
  if d.is_neg_inf() {
    return "-Infinity"
  }
  let sign = if dsignbit(d) { "-" } else { "" }
  if d == 0.0 {
    return sign + "0.0"
  }
  let a = d.abs()
  let (digits, e) = if a < 2.2250738585072014e-308 {
    subnormal_digits(a)
  } else {
    float_digits(d)
  }
  if a >= 1.0e-3 && a < 1.0e7 {
    // fixed notation
    if e <= 0 {
      sign + "0." + "0".repeat(-e) + digits
    } else if e >= digits.length() {
      sign + digits + "0".repeat(e - digits.length()) + ".0"
    } else {
      sign + digits.substring(end=e) + "." + digits.substring(start=e)
    }
  } else {
    let frac = if digits.length() > 1 { digits.substring(start=1) } else { "0" }
    sign + digits.substring(end=1) + "." + frac + "e" + (e - 1).to_string()
  }
}

///|
/// Does a symbol name need |escaping| for prin1?
fn needs_escape(name : String) -> Bool {
  if name.length() == 0 || name[0] == '#' || name == "." {
    return true
  }
  for c in name {
    match c {
      ' ' | '(' | ')' | '"' | ';' | '\'' | '`' | ',' | '|' | '\\' | '\n' | '\t' =>
        return true
      _ => if c >= 'A' && c <= 'Z' { return true }
    }
  }
  // looks like a number?
  parse_integer(name) is Some(_)
}

///|
/// The `:print-function` of defstruct types, by type name: a function of
/// (struct stream depth) that writes the printed representation.
pub let struct_print_functions : Map[String, Value] = Map::new()

///|
/// Print a value to a StringBuilder. `escape` is prin1 (true) vs princ.
pub fn print_value(sb : StringBuilder, x : Value, escape : Bool) -> Unit {
  match x {
    Nil => sb.write_string("nil")
    Sym(s) =>
      if escape && needs_escape(s.name) {
        sb.write_char('|')
        for c in s.name {
          if c == '|' || c == '\\' {
            sb.write_char('\\')
          }
          sb.write_char(c)
        }
        sb.write_char('|')
      } else if !s.interned && escape {
        sb.write_string("#:" + s.name)
      } else if !escape && s.name.length() > 1 && s.name.has_prefix(":") && is_keyword_name(s.name) {
        // princ omits the package marker of a keyword
        sb.write_string(s.name.substring(start=1))
      } else {
        sb.write_string(s.name)
      }
    Fix(n) => sb.write_string(n.to_string())
    Big(b) => sb.write_string(b.to_string())
    Ratio(n, d) => sb.write_string(n.to_string() + "/" + d.to_string())
    Flo(d) => sb.write_string(float_to_string(d))
    Cplx(r, i) => {
      sb.write_string("#C(")
      print_value(sb, r, escape)
      sb.write_char(' ')
      print_value(sb, i, escape)
      sb.write_char(')')
    }
    Str(s) =>
      if escape {
        sb.write_char('"')
        for c in s {
          if c == '"' || c == '\\' {
            sb.write_char('\\')
          }
          sb.write_char(c)
        }
        sb.write_char('"')
      } else {
        sb.write_string(s)
      }
    Char(c) =>
      if escape {
        sb.write_string("#\\")
        match c {
          ' ' => sb.write_string("Space")
          '\n' => sb.write_string("Newline")
          '\t' => sb.write_string("Tab")
          _ => sb.write_char(c)
        }
      } else {
        sb.write_char(c)
      }
    Cons(_) => {
      // quote shorthand
      match x {
        Cons({ car: Sym({ name: "quote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
          sb.write_char('\'')
          print_value(sb, q, escape)
          return
        }
        // backquote syntax as the reader produces it
        Cons({ car: Sym({ name: "si::quasiquote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
          sb.write_char('`')
          print_value(sb, q, escape)
          return
        }
        Cons({ car: Sym({ name: "si::unquote", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
          sb.write_char(',')
          print_value(sb, q, escape)
          return
        }
        Cons({ car: Sym({ name: "si::unquote-splicing", .. }), cdr: Cons({ car: q, cdr: Nil }) }) => {
          sb.write_string(",@")
          print_value(sb, q, escape)
          return
        }
        _ => ()
      }
      sb.write_char('(')
      let mut p = x
      let mut first = true
      let mut count = 0
      while true {
        match p {
          // a dotted backquote tail: (a . ,b)
          Cons({ car: Sym({ name: "si::unquote" | "si::unquote-splicing", .. }), cdr: Cons({ cdr: Nil, .. }) }) if !first => {
            sb.write_string(" . ")
            print_value(sb, p, escape)
            break
          }
          Cons(c) => {
            if !first {
              sb.write_char(' ')
            }
            first = false
            print_value(sb, c.car, escape)
            p = c.cdr
            count += 1
            if count > 100000 {
              sb.write_string(" ...")
              break
            }
          }
          Nil => break
          _ => {
            sb.write_string(" . ")
            print_value(sb, p, escape)
            break
          }
        }
      }
      sb.write_char(')')
    }
    Vec(a) =>
      if a.elt == "character" {
        print_value(sb, Str(lstring(x)), escape)
      } else if a.dims.length() != 1 {
        // Multidimensional array: #nA(...) with nested rows, as CL prints it.
        let rank = a.dims.length()
        sb.write_string("#\{rank}A")
        fn rows(k : Int, off : Int) -> Unit {
          if k == rank {
            print_value(sb, a.data[off], escape)
            return
          }
          let mut stride = 1
          for j in (k + 1)..<rank {
            stride *= a.dims[j]
          }
          sb.write_char('(')
          for i in 0..<a.dims[k] {
            if i > 0 {
              sb.write_char(' ')
            }
            rows(k + 1, off + i * stride)
          }
          sb.write_char(')')
        }
        rows(0, 0)
      } else {
        sb.write_string("#(")
        let n = match a.fill {
          Some(f) => f
          None => a.data.length()
        }
        for i in 0..<n {
          if i > 0 {
            sb.write_char(' ')
          }
          print_value(sb, a.data[i], escape)
        }
        sb.write_char(')')
      }
    Hash(_) => sb.write_string("#<HASH-TABLE>")
    Func(f) => sb.write_string("#<FUNCTION \{f.name}>")
    Struct(s) if struct_print_functions.get(s.stype.name) is Some(f) => {
      // defstruct :print-function: (funcall f struct stream depth)
      let st = make_string_output_stream()
      let _ = funcall(f, [x, st, Fix(0L)]) catch { _ => Nil }
      sb.write_string(get_output_stream_string(st))
    }
    Struct(s) => {
      sb.write_string("#S(" + s.stype.name)
      for v in s.slots {
        sb.write_char(' ')
        print_value(sb, v, escape)
      }
      sb.write_char(')')
    }
    Stream(_) => sb.write_string("#<STREAM>")
    Box(b) => sb.write_string("#<\{b.val.tag}>")
  }
}

///|
/// `(prin1-to-string x)`
pub fn prin1_to_string(x : Value) -> String {
  let sb = StringBuilder::new()
  print_value(sb, x, true)
  sb.to_string()
}

///|
/// `(princ-to-string x)`
pub fn princ_to_string(x : Value) -> String {
  let sb = StringBuilder::new()
  print_value(sb, x, false)
  sb.to_string()
}

///|
pub impl Show for Value with output(self, logger) {
  logger.write_string(prin1_to_string(self))
}

///|
/// `(princ x stream)`
pub fn princ(x : Value, stream? : Value = Nil) -> Value {
  write_string(princ_to_string(x), stream~)
  x
}

///|
/// `(prin1 x stream)`
pub fn prin1(x : Value, stream? : Value = Nil) -> Value {
  write_string(prin1_to_string(x), stream~)
  x
}

///|
/// `(print x stream)`
pub fn print(x : Value, stream? : Value = Nil) -> Value {
  write_string("\n" + prin1_to_string(x) + " ", stream~)
  x
}
