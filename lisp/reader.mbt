// A small Lisp reader for literal data, using the port's symbol naming:
// unescaped tokens are lower-cased; |escaped| names are case-inverted when
// they are of uniform case (mirroring CL Maxima's print-case inversion).

///|
priv struct LReader {
  cs : Array[Char]
  mut i : Int
}

///|
/// Invert the case of a name if all its letters share one case.
pub fn invert_case(name : String) -> String {
  let mut up = false
  let mut low = false
  for c in name {
    if upper_case_p(c) {
      up = true
    } else if lower_case_p(c) {
      low = true
    }
  }
  if up && !low {
    string_downcase(name)
  } else if low && !up {
    string_upcase(name)
  } else {
    name
  }
}

///|
/// Read one Lisp datum from a string.
pub fn lread(s : String) -> Value raise LispError {
  let r = { cs: string_chars(s), i: 0 }
  r.read()
}

///|
/// Read all data from a string.
pub fn lread_all(s : String) -> Array[Value] raise LispError {
  let r = { cs: string_chars(s), i: 0 }
  let out = []
  while true {
    r.skip_ws()
    if r.i >= r.cs.length() {
      break
    }
    out.push(r.read())
  }
  out
}

///|
fn LReader::skip_ws(self : LReader) -> Unit {
  while self.i < self.cs.length() {
    let c = self.cs[self.i]
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' {
      self.i += 1
    } else if c == ';' {
      while self.i < self.cs.length() && self.cs[self.i] != '\n' {
        self.i += 1
      }
    } else {
      break
    }
  }
}

///|
fn LReader::read(self : LReader) -> Value raise LispError {
  self.skip_ws()
  if self.i >= self.cs.length() {
    raise SimpleError("lread: unexpected end of input")
  }
  let c = self.cs[self.i]
  match c {
    '(' => {
      self.i += 1
      let items = []
      let mut tail = Nil
      while true {
        self.skip_ws()
        if self.i >= self.cs.length() {
          raise SimpleError("lread: unterminated list")
        }
        if self.cs[self.i] == ')' {
          self.i += 1
          break
        }
        if self.cs[self.i] == '.' &&
          self.i + 1 < self.cs.length() &&
          " \t\n(".contains_char(self.cs[self.i + 1]) {
          self.i += 1
          tail = self.read()
          self.skip_ws()
          if self.i < self.cs.length() && self.cs[self.i] == ')' {
            self.i += 1
          }
          break
        }
        items.push(self.read())
      }
      let mut r = tail
      for k = items.length() - 1; k >= 0; k = k - 1 {
        r = cons(items[k], r)
      }
      r
    }
    '\'' => {
      self.i += 1
      list2(sym("quote"), self.read())
    }
    '"' => {
      self.i += 1
      let sb = StringBuilder::new()
      while self.i < self.cs.length() && self.cs[self.i] != '"' {
        if self.cs[self.i] == '\\' {
          self.i += 1
        }
        sb.write_char(self.cs[self.i])
        self.i += 1
      }
      self.i += 1
      Str(sb.to_string())
    }
    '#' => {
      self.i += 1
      let d = self.cs[self.i]
      self.i += 1
      match d {
        '\\' => {
          let start = self.i
          self.i += 1
          while self.i < self.cs.length() && alpha_char_p(self.cs[self.i]) {
            self.i += 1
          }
          let name = chars_to_string(self.cs[start:self.i].to_array())
          if string_length(name) == 1 {
            Char(self.cs[start])
          } else {
            match string_downcase(name) {
              "space" => Char(' ')
              "newline" | "linefeed" => Char('\n')
              "tab" => Char('\t')
              "return" => Char('\r')
              "page" => Char('\u{0C}')
              "backspace" => Char('\u{08}')
              "rubout" => Char('\u{7F}')
              "nul" | "null" => Char('\u{00}')
              _ => {
                self.i = start + 1
                Char(self.cs[start])
              }
            }
          }
        }
        '\'' => list2(sym("function"), self.read())
        '(' => {
          self.i -= 1
          list_to_vector(self.read())
        }
        ':' => {
          let tok = self.token()
          make_symbol(tok.0)
        }
        _ => raise SimpleError("lread: unsupported dispatch #\{d}")
      }
    }
    _ => {
      let (name, escaped) = self.token()
      if !escaped && name == "nil" {
        return Nil
      }
      if !escaped {
        match parse_number_token(name) {
          Some(n) => return n
          None => ()
        }
      }
      sym(name)
    }
  }
}

///|
/// Read a symbol/number token; returns (name in port convention, escaped?).
fn LReader::token(self : LReader) -> (String, Bool) {
  let sb = StringBuilder::new()
  let mut escaped = false
  let mut any_plain_upper = false
  // segments: track escaped text separately for case handling
  let raw = StringBuilder::new()
  while self.i < self.cs.length() {
    let c = self.cs[self.i]
    if " \t\n\r()'\";`,".contains_char(c) {
      break
    }
    if c == '|' {
      escaped = true
      self.i += 1
      let seg = StringBuilder::new()
      while self.i < self.cs.length() && self.cs[self.i] != '|' {
        if self.cs[self.i] == '\\' {
          self.i += 1
        }
        seg.write_char(self.cs[self.i])
        self.i += 1
      }
      self.i += 1
      // escaped text keeps CL case
      sb.write_string(seg.to_string())
      raw.write_string(seg.to_string())
    } else if c == '\\' {
      escaped = true
      self.i += 1
      sb.write_char(self.cs[self.i])
      raw.write_char(self.cs[self.i])
      self.i += 1
    } else {
      if upper_case_p(c) {
        any_plain_upper = true
      }
      // CL reader upcases plain text
      sb.write_char(char_upcase(c))
      raw.write_char(c)
      self.i += 1
    }
  }
  ignore(any_plain_upper)
  if !escaped {
    (string_downcase(raw.to_string()), false)
  } else {
    (invert_case(sb.to_string()), true)
  }
}

///|
/// Parse a numeric token: integer, ratio or float.
pub fn parse_number_token(tok : String) -> Value? {
  if tok.length() == 0 {
    return None
  }
  let mut t = tok
  if t.has_suffix(".") && t.length() > 1 {
    t = t.substring(end=t.length() - 1)
  }
  match parse_integer(t) {
    Some(n) => return Some(n)
    None => ()
  }
  match t.find("/") {
    Some(k) => {
      let a = parse_integer(t.substring(end=k))
      let b = parse_integer(t.substring(start=k + 1))
      match (a, b) {
        (Some(x), Some(y)) =>
          return (fn() -> Value? raise {
            Some(make_ratio(to_big(x), to_big(y)))
          })() catch {
            _ => None
          }
        _ => ()
      }
    }
    None => ()
  }
  // float: digits, optional '.', optional exponent with marker e/d/f/s/l
  let mut has_digit = false
  let mut ok = true
  let sb = StringBuilder::new()
  let mut seen_exp = false
  for c in tok {
    if c.is_ascii_digit() {
      has_digit = true
      sb.write_char(c)
    } else if c == '.' && !seen_exp {
      sb.write_char(c)
    } else if (c == '+' || c == '-') {
      sb.write_char(c)
    } else if !seen_exp && "eEdDfFsSlL".contains_char(c) {
      seen_exp = true
      sb.write_char('e')
    } else {
      ok = false
      break
    }
  }
  if !ok || !has_digit || !(tok.contains(".") || seen_exp) {
    return None
  }
  let st = sb.to_string()
  if st.has_prefix("e") || st.has_prefix(".e") {
    return None
  }
  let st2 = if st.has_prefix(".") { "0" + st } else { st }
  (fn() -> Value? raise { Some(Flo(@string.parse_double(st2))) })() catch {
    _ => None
  }
}
