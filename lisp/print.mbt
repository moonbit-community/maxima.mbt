///|
/// Decompose a finite nonzero double into its shortest round-trip decimal
/// digits and exponent: value = 0.d1d2d3... * 10^exp.
pub fn float_digits(d : Double) -> (String, Int) {
  let s0 = d.abs().to_string()
  // forms: "123.456", "1e+100", "2.5e-300", "15000000000", "0.001"
  let (mant, e) = match s0.find("e") {
    Some(i) => {
      let m = s0.substring(end=i)
      let es = s0.substring(start=i + 1)
      let ev = es.replace(old="+", new="")
      (m, @string.parse_int(ev) catch { _ => 0 })
    }
    None => (s0, 0)
  }
  // mant is like "1.25" or "125" or "0.00125"
  let (ip, fp) = match mant.find(".") {
    Some(i) => (mant.substring(end=i), mant.substring(start=i + 1))
    None => (mant, "")
  }
  let mut digits = ip + fp
  let mut exp10 = ip.length() + e
  // strip leading zeros
  let mut lead = 0
  while lead < digits.length() - 1 && digits[lead] == '0' {
    lead += 1
  }
  digits = digits.substring(start=lead)
  exp10 -= lead
  // strip trailing zeros
  let mut end = digits.length()
  while end > 1 && digits[end - 1] == '0' {
    end -= 1
  }
  digits = digits.substring(end~)
  (digits, exp10)
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
  let (digits, e) = float_digits(d)
  let a = d.abs()
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
  if name.length() == 0 {
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
        _ => ()
      }
      sb.write_char('(')
      let mut p = x
      let mut first = true
      let mut count = 0
      while true {
        match p {
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
