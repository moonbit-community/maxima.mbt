///|
pub fn lstr(s : String) -> Value {
  Str(s)
}

///|
/// `(stringp x)` — strings and character vectors.
pub fn stringp(x : Value) -> Bool {
  match x {
    Str(_) => true
    Vec(a) => a.elt == "character" && a.dims.length() == 1
    _ => false
  }
}

///|
/// `(characterp x)`
pub fn characterp(x : Value) -> Bool {
  x is Char(_)
}

///|
/// Get the MoonBit string out of a string-like value. Symbols give their
/// name, characters a one-char string (as CL `string`).
pub fn lstring(x : Value) -> String {
  match x {
    Str(s) => s
    Vec(a) => {
      let sb = StringBuilder::new()
      let n = match a.fill {
        Some(f) => f
        None => a.data.length()
      }
      for i in 0..<n {
        match a.data[i] {
          Char(c) => sb.write_char(c)
          _ => ()
        }
      }
      sb.to_string()
    }
    Sym(s) => if is_keyword_name(s.name) { s.name.substring(start=1) } else { s.name }
    Nil => "nil"
    Char(c) => c.to_string()
    _ => ""
  }
}

///|
/// `(string x)`
pub fn string(x : Value) -> Value {
  Str(lstring(x))
}

///|
pub fn char_downcase(c : Char) -> Char {
  if c >= 'A' && c <= 'Z' {
    (c.to_int() + 32).unsafe_to_char()
  } else if c.to_int() > 127 {
    let s = c.to_string().to_lower()
    s.get_char(0).unwrap_or(c)
  } else {
    c
  }
}

///|
pub fn char_upcase(c : Char) -> Char {
  if c >= 'a' && c <= 'z' {
    (c.to_int() - 32).unsafe_to_char()
  } else if c.to_int() > 127 {
    let s = c.to_string().to_upper()
    s.get_char(0).unwrap_or(c)
  } else {
    c
  }
}

///|
pub fn upper_case_p(c : Char) -> Bool {
  (c >= 'A' && c <= 'Z') || (c.to_int() > 127 && char_downcase(c) != c)
}

///|
pub fn lower_case_p(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') || (c.to_int() > 127 && char_upcase(c) != c)
}

///|
pub fn both_case_p(c : Char) -> Bool {
  upper_case_p(c) || lower_case_p(c)
}

///|
pub fn alpha_char_p(c : Char) -> Bool {
  (c >= 'a' && c <= 'z') ||
  (c >= 'A' && c <= 'Z') ||
  (c.to_int() > 127 && (both_case_p(c) || is_unicode_letter(c)))
}

///|
fn is_unicode_letter(c : Char) -> Bool {
  let n = c.to_int()
  // A coarse approximation of Unicode letters beyond Latin-1 case pairs:
  // CJK, Greek, Cyrillic, etc.
  (n >= 0x00C0 && n <= 0x024F && n != 0xD7 && n != 0xF7) ||
  (n >= 0x0370 && n <= 0x03FF) ||
  (n >= 0x0400 && n <= 0x04FF) ||
  (n >= 0x4E00 && n <= 0x9FFF) ||
  (n >= 0x3040 && n <= 0x30FF) ||
  (n >= 0xAC00 && n <= 0xD7AF)
}

///|
pub fn digit_char_p(c : Char, radix? : Int = 10) -> Int? {
  let n = c.to_int()
  let d = if n >= '0'.to_int() && n <= '9'.to_int() {
    n - '0'.to_int()
  } else if n >= 'a'.to_int() && n <= 'z'.to_int() {
    n - 'a'.to_int() + 10
  } else if n >= 'A'.to_int() && n <= 'Z'.to_int() {
    n - 'A'.to_int() + 10
  } else {
    99
  }
  if d < radix {
    Some(d)
  } else {
    None
  }
}

///|
pub fn alphanumericp(c : Char) -> Bool {
  alpha_char_p(c) || (c >= '0' && c <= '9')
}

///|
/// `(char-code c)`
pub fn char_code(c : Char) -> Int {
  c.to_int()
}

///|
/// `(code-char n)`
pub fn code_char(n : Int) -> Char {
  n.unsafe_to_char()
}

///|
/// `(string-upcase s)`
pub fn string_upcase(s : String) -> String {
  let sb = StringBuilder::new()
  for c in s {
    sb.write_char(char_upcase(c))
  }
  sb.to_string()
}

///|
/// `(string-downcase s)`
pub fn string_downcase(s : String) -> String {
  let sb = StringBuilder::new()
  for c in s {
    sb.write_char(char_downcase(c))
  }
  sb.to_string()
}

///|
/// Characters of a string as an array (code points).
pub fn string_chars(s : String) -> Array[Char] {
  let r = []
  for c in s {
    r.push(c)
  }
  r
}

///|
/// String from characters.
pub fn chars_to_string(cs : Array[Char]) -> String {
  let sb = StringBuilder::new()
  for c in cs {
    sb.write_char(c)
  }
  sb.to_string()
}

///|
/// `(char s i)` by code point index.
pub fn char_at(s : String, i : Int) -> Char {
  let cs = string_chars(s)
  cs[i]
}

///|
/// `(subseq s start end)` on strings, by code point.
pub fn substring(s : String, start : Int, end? : Int) -> String {
  let cs = string_chars(s)
  let e = end.unwrap_or(cs.length())
  chars_to_string(cs[start:e].to_array())
}

///|
/// Number of code points in a string.
pub fn string_length(s : String) -> Int {
  let mut n = 0
  for _ in s {
    n += 1
  }
  n
}

///|
/// `(string-trim bag s)`
pub fn string_trim(bag : String, s : String) -> String {
  string_left_trim(bag, string_right_trim(bag, s))
}

///|
pub fn string_left_trim(bag : String, s : String) -> String {
  let cs = string_chars(s)
  let bs = string_chars(bag)
  let mut i = 0
  while i < cs.length() && bs.contains(cs[i]) {
    i += 1
  }
  chars_to_string(cs[i:].to_array())
}

///|
pub fn string_right_trim(bag : String, s : String) -> String {
  let cs = string_chars(s)
  let bs = string_chars(bag)
  let mut j = cs.length()
  while j > 0 && bs.contains(cs[j - 1]) {
    j -= 1
  }
  chars_to_string(cs[0:j].to_array())
}

///|
/// `(search sub s)`: index of sub in s (code points), or -1.
pub fn string_search(sub : String, s : String, start? : Int = 0) -> Int {
  let a = string_chars(sub)
  let b = string_chars(s)
  if a.length() == 0 {
    return start
  }
  for i = start; i + a.length() <= b.length(); i = i + 1 {
    let mut ok = true
    for j in 0..<a.length() {
      if a[j] != b[i + j] {
        ok = false
        break
      }
    }
    if ok {
      return i
    }
  }
  -1
}

///|
/// `(string< a b)` etc: lexicographic compare by code point.
pub fn string_compare(a : String, b : String) -> Int {
  let x = string_chars(a)
  let y = string_chars(b)
  let n = x.length().min(y.length())
  for i in 0..<n {
    if x[i] != y[i] {
      return if x[i] < y[i] { -1 } else { 1 }
    }
  }
  x.length().compare(y.length())
}

///|
/// `(string-equal a b)`: case-insensitive.
pub fn string_equal(a : String, b : String) -> Bool {
  string_downcase(a) == string_downcase(b)
}

///|
/// `(concatenate 'string ...)`
pub fn concat_strings(xs : Array[Value]) -> Value {
  let sb = StringBuilder::new()
  for x in xs {
    match x {
      Char(c) => sb.write_char(c)
      Cons(_) =>
        for y in x.iter() {
          match y {
            Char(c) => sb.write_char(c)
            _ => sb.write_string(lstring(y))
          }
        }
      _ => sb.write_string(lstring(x))
    }
  }
  Str(sb.to_string())
}

///|
/// `(coerce string 'list)` — list of characters.
pub fn string_to_char_list(s : String) -> Value {
  list(string_chars(s).map(c => Char(c)))
}

///|
/// `(coerce chars 'string)` from a list of characters.
pub fn char_list_to_string(l : Value) -> String {
  let sb = StringBuilder::new()
  for x in l.iter() {
    match x {
      Char(c) => sb.write_char(c)
      _ => sb.write_string(lstring(x))
    }
  }
  sb.to_string()
}

///|
/// `(parse-integer s :radix r :junk-allowed j)`
pub fn parse_integer(s : String, radix? : Int = 10) -> Value? {
  let t = string_trim(" \t\n", s)
  if t.length() == 0 {
    return None
  }
  let cs = string_chars(t)
  let mut i = 0
  let mut neg = false
  if cs[0] == '-' || cs[0] == '+' {
    neg = cs[0] == '-'
    i = 1
  }
  if i >= cs.length() {
    return None
  }
  let rb = BigInt::from_int(radix)
  let mut acc = 0N
  while i < cs.length() {
    match digit_char_p(cs[i], radix~) {
      Some(d) => acc = acc * rb + BigInt::from_int(d)
      None => return None
    }
    i += 1
  }
  Some(from_big(if neg { -acc } else { acc }))
}

///|
/// Split a string on a separator character.
pub fn split_string(s : String, sep : Char) -> Array[String] {
  let r = []
  let sb = StringBuilder::new()
  for c in s {
    if c == sep {
      r.push(sb.to_string())
      sb.reset()
    } else {
      sb.write_char(c)
    }
  }
  r.push(sb.to_string())
  r
}
