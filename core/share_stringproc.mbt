// Port of share/stringproc/stringproc.lisp: Maxima string processing.
//
// Strings of length 1 are Maxima characters. Position indices in strings
// are 1-indexed like in Maxima lists:  charlist(str)[i] = charat(str, i).
//
// Strings are MoonBit (UTF-16) strings; all positions and lengths are in
// code points, as Lisp characters are in SBCL.
//
// The port follows the SBCL/unix branches of the reader conditionals:
// *parse-utf-8-input* is NIL, encodings are SBCL keywords and the default
// external format is :UTF-8.
//
// Files: the port has no Lisp file streams. OPENW, OPENA and OPENR create
// character streams (LStream) backed by a whole file: input streams hold
// the decoded file contents; output streams collect the text and write the
// encoded file when they are flushed or closed. The encoder/decoder below
// (share_stringproc__encode/decode, also used by cryptools) implements the
// common SBCL external formats.

///|
/// A file stream: the file and its external format.
priv struct ShareStringprocFile {
  path : String
  enc : Value
  /// existing file contents (output stream opened with :if-exists :append)
  prefix : Bytes
  /// output text written so far
  buf : StringBuilder
  output : Bool
  /// input streams: the decoded contents
  text : Array[Char]
  mut closed : Bool
}

///|
let share_stringproc__files : Array[(LStream, ShareStringprocFile)] = []

///|
fn share_stringproc__file_of(s : Value) -> ShareStringprocFile? {
  match s {
    Stream(st) => {
      for e in share_stringproc__files {
        if physical_equal(e.0, st) {
          return Some(e.1)
        }
      }
      None
    }
    _ => None
  }
}

// -------------------------------------------------------------------------
// Encodings (SBCL external formats)

///|
/// cp1252 code points of the octets #x80..#x9F (-1: undefined).
let share_stringproc__cp1252_high : Array[Int] = [
  0x20AC, -1, 0x201A, 0x0192, 0x201E, 0x2026, 0x2020, 0x2021, 0x02C6, 0x2030, 0x0160,
  0x2039, 0x0152, -1, 0x017D, -1, -1, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013,
  0x2014, 0x02DC, 0x2122, 0x0161, 0x203A, 0x0153, -1, 0x017E, 0x0178,
]

///|
/// latin-9 (ISO-8859-15): the octets that differ from latin-1.
let share_stringproc__latin9 : Array[(Int, Int)] = [
  (0xA4, 0x20AC),
  (0xA6, 0x0160),
  (0xA8, 0x0161),
  (0xB4, 0x017D),
  (0xB8, 0x017E),
  (0xBC, 0x0152),
  (0xBD, 0x0153),
  (0xBE, 0x0178),
]

///|
/// Canonical name of the external format ENC (a keyword or :default) and
/// the CL name used in error messages.
fn share_stringproc__enc_canon(enc : Value) -> (String, String) raise {
  let n0 = match enc {
    Sym(s) => s.name
    Nil => ":utf-8"
    _ => raise LispError::SimpleError("Undefined external-format: " + princ_to_string(enc))
  }
  let n = string_downcase(if n0.has_prefix(":") { n0.substring(start=1) } else { n0 })
  let canon = match n {
    "default" | "utf-8" | "utf8" => "utf-8"
    "latin-1" | "latin1" | "iso-8859-1" | "iso8859-1" => "latin-1"
    "ascii" | "us-ascii" | "ansi_x3.4-1968" | "iso-646" | "iso-646-us" | "646" =>
      "ascii"
    "latin-9" | "latin9" | "iso-8859-15" | "iso8859-15" => "latin-9"
    "cp1252" | "windows-1252" => "cp1252"
    "utf-16le" | "utf16le" => "utf-16le"
    "utf-16be" | "utf16be" => "utf-16be"
    "utf-32le" | "utf32le" => "utf-32le"
    "utf-32be" | "utf32be" => "utf-32be"
    "ucs-2le" | "ucs2le" => "ucs-2le"
    "ucs-2be" | "ucs2be" => "ucs-2be"
    "ucs-4le" | "ucs4le" => "ucs-4le"
    "ucs-4be" | "ucs4be" => "ucs-4be"
    "cp1250" | "windows-1250" | "cp1251" | "windows-1251" | "cp1253" | "windows-1253"
    | "cp1254" | "cp1255" | "windows-1255" | "cp1256" | "windows-1256" | "cp1257"
    | "windows-1257" | "cp1258" | "windows-1258" | "cp437" | "cp850" | "cp852"
    | "cp855" | "cp857" | "cp860" | "cp861" | "cp862" | "cp863" | "cp864" | "cp865"
    | "cp866" | "cp869" | "cp874" | "ebcdic-us" | "cp037" | "ibm-037" | "ibm037"
    | "iso-8859-2" | "iso-8859-3" | "iso-8859-4" | "iso-8859-5" | "iso-8859-6"
    | "iso-8859-7" | "iso-8859-8" | "iso-8859-9" | "iso-8859-10" | "iso-8859-11"
    | "iso-8859-13" | "iso-8859-14" | "latin-2" | "latin-3" | "latin-4" | "latin-5"
    | "latin-6" | "latin-7" | "latin-8" | "koi8-r" | "koi8-u" | "x-mac-cyrillic"
    | "mac-roman" | "macroman" | "mac" | "macintosh" | "gbk" | "cp936" | "euc-jp"
    | "eucjp" | "shift_jis" | "sjis" | "cp932" =>
      raise LispError::SimpleError(
        "external format " + invert_case(n0) + " is not supported in this port",
      )
    _ => raise LispError::SimpleError("Undefined external-format: " + invert_case(n0))
  }
  (canon, ":" + string_upcase(canon))
}

///|
fn share_stringproc__encode_error(code : Int, cl : String) -> Unit raise {
  raise LispError::SimpleError(
    "Unable to encode character \{code} as \{cl}.",
  )
}

///|
fn share_stringproc__decode_error(pos : Int, cl : String) -> Unit raise {
  raise LispError::SimpleError(
    "Illegal \{cl} character starting at byte position \{pos}.",
  )
}

///|
/// Encode the characters CS in the external format ENC (SBCL
/// STRING-TO-OCTETS).
fn share_stringproc__encode_chars(cs : Array[Char], enc : Value) -> Array[Int] raise {
  let (canon, cl) = share_stringproc__enc_canon(enc)
  let out : Array[Int] = []
  for c in cs {
    let code = c.to_int()
    let surrogate = code >= 0xD800 && code <= 0xDFFF
    match canon {
      "utf-8" => {
        if surrogate {
          share_stringproc__encode_error(code, cl)
        }
        if code < 0x80 {
          out.push(code)
        } else if code < 0x800 {
          out.push(0xC0 | (code >> 6))
          out.push(0x80 | (code & 0x3F))
        } else if code < 0x10000 {
          out.push(0xE0 | (code >> 12))
          out.push(0x80 | ((code >> 6) & 0x3F))
          out.push(0x80 | (code & 0x3F))
        } else {
          out.push(0xF0 | (code >> 18))
          out.push(0x80 | ((code >> 12) & 0x3F))
          out.push(0x80 | ((code >> 6) & 0x3F))
          out.push(0x80 | (code & 0x3F))
        }
      }
      "latin-1" =>
        if code < 256 {
          out.push(code)
        } else {
          share_stringproc__encode_error(code, cl)
        }
      "ascii" =>
        if code < 128 {
          out.push(code)
        } else {
          share_stringproc__encode_error(code, cl)
        }
      "latin-9" => {
        let mut b = -1
        for p in share_stringproc__latin9 {
          if p.1 == code {
            b = p.0
          }
        }
        if b < 0 && code < 256 {
          let mut replaced = false
          for p in share_stringproc__latin9 {
            if p.0 == code {
              replaced = true
            }
          }
          if !replaced {
            b = code
          }
        }
        if b < 0 {
          share_stringproc__encode_error(code, cl)
        }
        out.push(b)
      }
      "cp1252" => {
        let mut b = -1
        if code < 128 || (code >= 0xA0 && code < 256) {
          b = code
        } else {
          for i, u in share_stringproc__cp1252_high {
            if u == code {
              b = 0x80 + i
            }
          }
        }
        if b < 0 {
          share_stringproc__encode_error(code, cl)
        }
        out.push(b)
      }
      "utf-16le" | "utf-16be" | "ucs-2le" | "ucs-2be" => {
        let units = if code >= 0x10000 {
          if canon.has_prefix("ucs") {
            share_stringproc__encode_error(code, cl)
          }
          let v = code - 0x10000
          [0xD800 | (v >> 10), 0xDC00 | (v & 0x3FF)]
        } else {
          if surrogate && canon.has_prefix("utf") {
            share_stringproc__encode_error(code, cl)
          }
          [code]
        }
        for u in units {
          if canon.has_suffix("le") {
            out.push(u & 0xFF)
            out.push(u >> 8)
          } else {
            out.push(u >> 8)
            out.push(u & 0xFF)
          }
        }
      }
      _ => {
        // utf-32 / ucs-4
        if surrogate && canon.has_prefix("utf") {
          share_stringproc__encode_error(code, cl)
        }
        let bs = [code & 0xFF, (code >> 8) & 0xFF, (code >> 16) & 0xFF, code >> 24]
        if canon.has_suffix("le") {
          for b in bs {
            out.push(b)
          }
        } else {
          for i = 3; i >= 0; i = i - 1 {
            out.push(bs[i])
          }
        }
      }
    }
  }
  out
}

///|
/// Decode the octets BS in the external format ENC (SBCL
/// OCTETS-TO-STRING).
fn share_stringproc__decode_bytes(bs : Array[Int], enc : Value) -> Array[Char] raise {
  let (canon, cl) = share_stringproc__enc_canon(enc)
  let out : Array[Char] = []
  let n = bs.length()
  let mut i = 0
  while i < n {
    let b = bs[i]
    match canon {
      "utf-8" => {
        let (len, init) = if b < 0x80 {
          (1, b)
        } else if b >= 0xC2 && b < 0xE0 {
          (2, b & 0x1F)
        } else if b >= 0xE0 && b < 0xF0 {
          (3, b & 0x0F)
        } else if b >= 0xF0 && b < 0xF5 {
          (4, b & 0x07)
        } else {
          (0, 0)
        }
        if len == 0 || i + len > n {
          share_stringproc__decode_error(i, cl)
        }
        let mut code = init
        for k in 1..<len {
          let c = bs[i + k]
          if (c & 0xC0) != 0x80 {
            share_stringproc__decode_error(i, cl)
          }
          code = (code << 6) | (c & 0x3F)
        }
        let overlong = (len == 3 && code < 0x800) || (len == 4 && code < 0x10000)
        if overlong || (code >= 0xD800 && code <= 0xDFFF) || code > 0x10FFFF {
          share_stringproc__decode_error(i, cl)
        }
        out.push(code.unsafe_to_char())
        i += len
      }
      "latin-1" => {
        out.push(b.unsafe_to_char())
        i += 1
      }
      "ascii" => {
        if b >= 128 {
          share_stringproc__decode_error(i, cl)
        }
        out.push(b.unsafe_to_char())
        i += 1
      }
      "latin-9" => {
        let mut code = b
        for p in share_stringproc__latin9 {
          if p.0 == b {
            code = p.1
          }
        }
        out.push(code.unsafe_to_char())
        i += 1
      }
      "cp1252" => {
        let code = if b >= 0x80 && b < 0xA0 {
          share_stringproc__cp1252_high[b - 0x80]
        } else {
          b
        }
        if code < 0 {
          share_stringproc__decode_error(i, cl)
        }
        out.push(code.unsafe_to_char())
        i += 1
      }
      "utf-16le" | "utf-16be" | "ucs-2le" | "ucs-2be" => {
        let le = canon.has_suffix("le")
        let unit = fn(j : Int) -> Int {
          if le {
            bs[j] | (bs[j + 1] << 8)
          } else {
            (bs[j] << 8) | bs[j + 1]
          }
        }
        if i + 2 > n {
          share_stringproc__decode_error(i, cl)
        }
        let u = unit(i)
        if canon.has_prefix("utf") && u >= 0xD800 && u <= 0xDFFF {
          if u >= 0xDC00 || i + 4 > n {
            share_stringproc__decode_error(i, cl)
          }
          let u2 = unit(i + 2)
          if u2 < 0xDC00 || u2 > 0xDFFF {
            share_stringproc__decode_error(i, cl)
          }
          out.push((0x10000 + ((u - 0xD800) << 10) + (u2 - 0xDC00)).unsafe_to_char())
          i += 4
        } else {
          out.push(u.unsafe_to_char())
          i += 2
        }
      }
      _ => {
        if i + 4 > n {
          share_stringproc__decode_error(i, cl)
        }
        let code = if canon.has_suffix("le") {
          bs[i] | (bs[i + 1] << 8) | (bs[i + 2] << 16) | (bs[i + 3] << 24)
        } else {
          (bs[i] << 24) | (bs[i + 1] << 16) | (bs[i + 2] << 8) | bs[i + 3]
        }
        if code < 0 ||
          code > 0x10FFFF ||
          (canon.has_prefix("utf") && code >= 0xD800 && code <= 0xDFFF) {
          share_stringproc__decode_error(i, cl)
        }
        out.push(code.unsafe_to_char())
        i += 4
      }
    }
  }
  out
}

///|
fn share_stringproc__bytes_to_ints(b : Bytes) -> Array[Int] {
  let r : Array[Int] = []
  for x in b {
    r.push(x.to_int())
  }
  r
}

///|
fn share_stringproc__ints_to_bytes(a : Array[Int]) -> Bytes {
  Bytes::makei(a.length(), i => a[i].to_byte())
}

// -------------------------------------------------------------------------
// Strings as code point arrays

///|
/// The characters of a string designator (string, character or symbol).
fn share_stringproc__chars(v : Value) -> Array[Char] raise {
  match v {
    Str(s) => string_chars(s)
    Char(c) => [c]
    Sym(_) => string_chars(symbol_name(v))
    Nil => string_chars("NIL")
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(v) + " is not of type (OR STRING SYMBOL CHARACTER)",
      )
  }
}

///|
fn share_stringproc__str(cs : Array[Char]) -> Value {
  Str(chars_to_string(cs))
}

///|
/// A Lisp index argument (non-negative fixnum).
fn share_stringproc__index(v : Value) -> Int raise {
  match v {
    Fix(n) if n >= 0L && n <= 0x7FFFFFFFL => n.to_int()
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(v) + " is not of type (MOD 4611686018427387901)",
      )
  }
}

///|
/// Validate the bounding indices START and END (NIL = length) of a
/// sequence of length LEN, as SUBSEQ does.
fn share_stringproc__bounds(len : Int, start : Value, end : Value) -> (Int, Int) raise {
  let s = share_stringproc__index(start)
  let e = if end is Nil { len } else { share_stringproc__index(end) }
  if s > e || e > len {
    raise LispError::SimpleError(
      "The bounding indices \{s} and \{e} are bad for a sequence of length \{len}.",
    )
  }
  (s, e)
}

///|
/// (subseq str start end)
fn share_stringproc__subseq(str : Value, start : Value, end : Value) -> Value raise {
  let cs = share_stringproc__chars(str)
  let (s, e) = share_stringproc__bounds(cs.length(), start, end)
  share_stringproc__str(cs[s:e].to_array())
}

///|
/// The upper case partner of the lower case character with code N in the
/// common alphabets (Latin-1, Latin Extended-A, Greek, Cyrillic), or -1.
/// Only round-trip case pairs count, as in SBCL.
fn share_stringproc__upper_of(n : Int) -> Int {
  if n >= 0xE0 && n <= 0xFE && n != 0xF7 {
    n - 32
  } else if n == 0xFF {
    0x178
  } else if n >= 0x100 && n <= 0x17F {
    if (n >= 0x101 && n <= 0x12F && n % 2 == 1) ||
      (n >= 0x133 && n <= 0x137 && n % 2 == 1) ||
      (n >= 0x14B && n <= 0x177 && n % 2 == 1) {
      n - 1
    } else if (n >= 0x13A && n <= 0x148 && n % 2 == 0) ||
      (n >= 0x17A && n <= 0x17E && n % 2 == 0) {
      n - 1
    } else {
      -1
    }
  } else if n >= 0x3B1 && n <= 0x3C9 && n != 0x3C2 {
    n - 32
  } else if n >= 0x430 && n <= 0x44F {
    n - 32
  } else if n >= 0x450 && n <= 0x45F {
    n - 80
  } else {
    -1
  }
}

///|
fn share_stringproc__lower_of(n : Int) -> Int {
  if n >= 0xC0 && n <= 0xDE && n != 0xD7 {
    n + 32
  } else if n == 0x178 {
    0xFF
  } else if n >= 0x100 && n <= 0x17F {
    let l = n + 1
    if share_stringproc__upper_of(l) == n {
      l
    } else {
      -1
    }
  } else if n >= 0x391 && n <= 0x3A9 && n != 0x3A2 {
    n + 32
  } else if n >= 0x410 && n <= 0x42F {
    n + 32
  } else if n >= 0x400 && n <= 0x40F {
    n + 80
  } else {
    -1
  }
}

///|
/// SBCL CHAR-UPCASE (only characters with a case pair change).
fn share_stringproc__char_upcase(c : Char) -> Char {
  if c.to_int() < 128 {
    return char_upcase(c)
  }
  let u = share_stringproc__upper_of(c.to_int())
  if u >= 0 {
    u.unsafe_to_char()
  } else {
    c
  }
}

///|
/// SBCL CHAR-DOWNCASE.
fn share_stringproc__char_downcase(c : Char) -> Char {
  if c.to_int() < 128 {
    return char_downcase(c)
  }
  let l = share_stringproc__lower_of(c.to_int())
  if l >= 0 {
    l.unsafe_to_char()
  } else {
    c
  }
}

///|
fn share_stringproc__upper_case_p(c : Char) -> Bool {
  share_stringproc__char_downcase(c) != c
}

///|
fn share_stringproc__lower_case_p(c : Char) -> Bool {
  share_stringproc__char_upcase(c) != c
}

///|
/// The code CHAR-EQUAL and friends compare (case folded to lower case).
fn share_stringproc__equal_code(c : Char) -> Int {
  share_stringproc__char_downcase(c).to_int()
}

///|
fn share_stringproc__graphic_char_p(c : Char) -> Bool {
  let n = c.to_int()
  (n > 31 && n < 127) || n > 159
}

///|
fn share_stringproc__digit_weight(c : Char) -> Int? {
  let n = c.to_int()
  if n >= 48 && n <= 57 {
    return Some(n - 48)
  }
  // a few Unicode decimal digit blocks
  for z in [0x660, 0x6F0, 0x7C0, 0x966, 0x9E6, 0xA66, 0xAE6, 0xB66, 0xBE6, 0xC66,
    0xCE6, 0xD66, 0xE50, 0xED0, 0xF20, 0x1040, 0xFF10] {
    if n >= z && n <= z + 9 {
      return Some(n - z)
    }
  }
  None
}

///|
fn share_stringproc__lchar(v : Value) -> Char raise {
  match v {
    Char(c) => c
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(v) + " is not of type CHARACTER",
      )
  }
}

///|
/// The :TEST of SEARCH/MISMATCH: $SEQUAL (string=), $SEQUALIGNORE
/// (string-equal) or any function of two characters.
fn share_stringproc__test(test_ : Value, a : Char, b : Char) -> Bool raise {
  if eq(test_, q_d_sequal) {
    a == b
  } else if eq(test_, q_d_sequalignore) {
    share_stringproc__equal_code(a) == share_stringproc__equal_code(b)
  } else {
    funcall(test_, [Char(a), Char(b)]).truthy()
  }
}

///|
/// (search seq str :test test :start2 start :end2 end)
fn share_stringproc__search(
  seq : Array[Char],
  str : Array[Char],
  test_ : Value,
  start : Value,
  end : Value,
) -> Value raise {
  let (s, e) = share_stringproc__bounds(str.length(), start, end)
  let m = seq.length()
  let mut i = s
  while i + m <= e {
    let mut ok = true
    for j in 0..<m {
      if !share_stringproc__test(test_, seq[j], str[i + j]) {
        ok = false
        break
      }
    }
    if ok {
      return int(i)
    }
    i += 1
  }
  Nil
}

///|
/// (mismatch s1 s2 :test test)
fn share_stringproc__mismatch(
  a : Array[Char],
  b : Array[Char],
  test_ : Value,
) -> Value raise {
  let n = a.length().min(b.length())
  for i in 0..<n {
    if !share_stringproc__test(test_, a[i], b[i]) {
      return int(i)
    }
  }
  if a.length() == b.length() {
    Nil
  } else {
    int(n)
  }
}

///|
/// Stable merge sort.
fn share_stringproc__stable_sort(
  a : Array[Value],
  less : (Value, Value) -> Bool raise,
) -> Array[Value] raise {
  if a.length() <= 1 {
    return a.copy()
  }
  let mid = a.length() / 2
  let l = share_stringproc__stable_sort(a[0:mid].to_array(), less)
  let r = share_stringproc__stable_sort(a[mid:].to_array(), less)
  let out : Array[Value] = []
  let mut i = 0
  let mut j = 0
  while i < l.length() && j < r.length() {
    if less(r[j], l[i]) {
      out.push(r[j])
      j += 1
    } else {
      out.push(l[i])
      i += 1
    }
  }
  while i < l.length() {
    out.push(l[i])
    i += 1
  }
  while j < r.length() {
    out.push(r[j])
    j += 1
  }
  out
}

// -------------------------------------------------------------------------

///|
/// Find the right value for *parse-utf-8-input* (SBCL, unix: NIL).
fn init__starparse_utf_8_input_star() -> Value raise {
  Nil
}

///|
/// When *parse-utf-8-input* is t read raw bytes according to the default
/// external format (cp1252).
fn string_to_raw_bytes(str : Value) -> Value raise {
  let bs = share_stringproc__encode_chars(share_stringproc__chars(str), kw("cp1252"))
  vector(bs.map(b => int(b)))
}

///|
fn set__starparse_utf_8_input_star(assign_var : Value, arg : Value) -> Value raise {
  ignore(assign_var)
  set(
    q_ear_parse_utf_8_input,
    if arg.truthy() {
      Nil
    } else {
      init__starparse_utf_8_input_star()
    },
  )
}

// -- frequently used error messages ----------------------------------------

///|
fn io_error(name : Value, which : Value) -> Value raise {
  gf_merror(Str("`~m': ~m argument must be a stream."), list([name, which]))
}

///|
fn s_error1(name : Value, which : Value) -> Value raise {
  gf_merror(Str("`~m': ~m argument must be a string."), list([name, which]))
}

///|
fn s_error2(name : Value, which : Value) -> Value raise {
  gf_merror(Str("`~m': ~m arguments must be strings."), list([name, which]))
}

///|
fn s_pos_error1(name : Value, pos : Value) -> Value raise {
  gf_merror(Str("`~m': unsuitable position index ~m"), list([name, pos]))
}

///|
fn s_pos_error2(name : Value) -> Value raise {
  gf_merror(Str("`~m': unsuitable start or end position."), list([name]))
}

// -------------------------------------------------------------------------
// 1. I/O

///|
fn share_stringproc__file_error(path : String, what : String) -> LispError {
  LispError::Condition(
    intern("file-error"),
    "error opening " + prin1_to_string(Str(path)) + ": " + what,
    Str(path),
  )
}

///|
fn share_stringproc__read_file_bytes(path : String) -> Bytes raise {
  @fs.read_file_to_bytes(path) catch {
    _ =>
      raise share_stringproc__file_error(path, "No such file or directory")
  }
}

///|
/// A new character output stream on the file PATH.
fn share_stringproc__open_output(path : String, enc : Value, append : Bool) -> Value raise {
  // validate the external format first
  share_stringproc__enc_canon(enc) |> ignore
  let prefix : Bytes = if append && probe_file(path) {
    share_stringproc__read_file_bytes(path)
  } else {
    b""
  }
  // :if-exists :supersede / :if-does-not-exist :create
  @fs.write_bytes_to_file(path, prefix) catch {
    _ => raise share_stringproc__file_error(path, "Permission denied")
  }
  let buf = StringBuilder::new()
  let st : LStream = {
    input: "",
    pos: 0,
    unread: [],
    out: None,
    name: path,
    sink: Some(s => buf.write_string(s)),
    column: 0,
    line: 1,
    is_input: false,
    eof: false,
  }
  share_stringproc__files.push((
    st,
    { path, enc, prefix, buf, output: true, text: [], closed: false },
  ))
  Stream(st)
}

///|
/// The bytes of an output file stream.
fn share_stringproc__output_bytes(f : ShareStringprocFile) -> Array[Int] raise {
  let r = share_stringproc__bytes_to_ints(f.prefix)
  for b in share_stringproc__encode_chars(string_chars(f.buf.to_string()), f.enc) {
    r.push(b)
  }
  r
}

///|
/// Write an output file stream's contents to its file.
fn share_stringproc__write_out(f : ShareStringprocFile) -> Unit raise {
  if f.output && !f.closed {
    let bs = share_stringproc__output_bytes(f)
    @fs.write_bytes_to_file(f.path, share_stringproc__ints_to_bytes(bs)) catch {
      _ => raise share_stringproc__file_error(f.path, "Permission denied")
    }
  }
}

///|
fn d_openw(file : Value, enc? : Value = Nil) -> Value raise {
  if !stringp(file) {
    s_error1(Str("openw"), Str("the")) |> ignore
  }
  share_stringproc__open_output(
    lstring(file),
    get_encoding(enc, Str("openw")),
    false,
  )
}

///|
/// The encoding of OPENA/OPENR without an encoding argument: the encoding
/// inferred from the byte order mark, else the default.
fn share_stringproc__inferred_or_default(
  file : Value,
  enc : Value,
  name : String,
) -> Value raise {
  if enc.truthy() {
    get_encoding(enc, Str(name))
  } else {
    let inferred_encoding = unicode_sniffer(file)
    if inferred_encoding.truthy() {
      let checked_encoding = check_encoding(inferred_encoding)
      if checked_encoding is Nil {
        merr(
          name +
          ": inferred encoding ~M for file ~M is not recognized by this Lisp implementation.",
          [inferred_encoding, file],
        )
        |> ignore
      }
      inferred_encoding
    } else {
      get_encoding(enc, Str(name))
    }
  }
}

///|
fn d_opena(file : Value, enc? : Value = Nil) -> Value raise {
  if !stringp(file) {
    s_error1(Str("opena"), Str("the")) |> ignore
  }
  let encoding_to_use = share_stringproc__inferred_or_default(file, enc, "opena")
  share_stringproc__open_output(lstring(file), encoding_to_use, true)
}

///|
fn d_openr(file : Value, enc? : Value = Nil) -> Value raise {
  if !stringp(file) {
    s_error1(Str("openr"), Str("the")) |> ignore
  }
  if !probe_file(lstring(file)) {
    gf_merror(Str("`openr': file does not exist: ~m"), list([file])) |> ignore
  }
  let encoding_to_use = share_stringproc__inferred_or_default(file, enc, "openr")
  let path = lstring(file)
  let bytes = share_stringproc__bytes_to_ints(
    share_stringproc__read_file_bytes(path),
  )
  let text = share_stringproc__decode_bytes(bytes, encoding_to_use)
  let st : LStream = {
    input: chars_to_string(text),
    pos: 0,
    unread: [],
    out: None,
    name: path,
    sink: None,
    column: 0,
    line: 1,
    is_input: true,
    eof: false,
  }
  share_stringproc__files.push((
    st,
    {
      path,
      enc: encoding_to_use,
      prefix: b"",
      buf: StringBuilder::new(),
      output: false,
      text,
      closed: false,
    },
  ))
  let s = Value::Stream(st)
  if peek_char(stream=s) is Char('\u{FEFF}') {
    read_char(stream=s) |> ignore
  }
  s
}

///|
fn d_make_string_input_stream(
  str : Value,
  start? : Value = Fix(1L),
  end? : Value = Nil,
) -> Value raise {
  if !stringp(str) {
    s_error1(Str("make_string_input_stream"), Str("first")) |> ignore
  }
  let start = num_sub(start, int(1))
  let end = if end.truthy() { num_sub(end, int(1)) } else { end }
  let r = errset(() => {
    let cs = string_chars(lstring(str))
    let (s, e) = share_stringproc__bounds(cs.length(), start, end)
    make_string_input_stream(chars_to_string(cs[s:e].to_array()))
  })
  match r {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("make_string_input_stream"))
  }
}

///|
fn d_make_string_output_stream() -> Value raise {
  make_string_output_stream()
}

///|
/// Ignore the :element-type keyword (default :element-type character).
fn d_get_output_stream_string(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("get_output_stream_string"), Str("the")) |> ignore
  }
  match stream {
    Stream({ out: Some(_), .. }) => Str(get_output_stream_string(stream))
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(stream) + " is not of type SB-IMPL::STRING-OUTPUT-STREAM",
      )
  }
}

///|
fn d_close(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("close"), Str("the")) |> ignore
  }
  match share_stringproc__file_of(stream) {
    Some(f) => {
      share_stringproc__write_out(f)
      f.closed = true
    }
    None => ()
  }
  t
}

///|
/// So $flush_output and $close both return t.
fn d_flush_output(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("flush_output"), Str("the")) |> ignore
  }
  match share_stringproc__file_of(stream) {
    Some(f) => share_stringproc__write_out(f)
    None => finish_output(stream~)
  }
  t
}

///|
fn d_flength(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("flength"), Str("the")) |> ignore
  }
  match share_stringproc__file_of(stream) {
    Some(f) =>
      if f.output {
        int(share_stringproc__output_bytes(f).length())
      } else {
        int(share_stringproc__encode_chars(f.text, f.enc).length())
      }
    None =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(stream) + " is not of type FILE-STREAM",
      )
  }
}

///|
/// Number of characters consumed from an input stream.
fn share_stringproc__input_chars_read(st : LStream) -> Int {
  string_length(st.input.substring(end=st.pos)) - st.unread.length()
}

///|
/// (file-position stream) and (file-position stream pos).
fn share_stringproc__file_position(stream : Value, pos : Value?) -> Value raise {
  let st = match stream {
    Stream(st) => st
    _ => return Nil
  }
  let f = share_stringproc__file_of(stream)
  match pos {
    None =>
      if st.is_input {
        let n = share_stringproc__input_chars_read(st)
        match f {
          Some(f) =>
            int(share_stringproc__encode_chars(f.text[0:n].to_array(), f.enc).length())
          None => int(n)
        }
      } else {
        match f {
          Some(f) => int(share_stringproc__output_bytes(f).length())
          None =>
            match st.out {
              Some(sb) => int(string_length(sb.to_string()))
              None => Nil
            }
        }
      }
    Some(p) => {
      let p = share_stringproc__index(p)
      if !st.is_input {
        return Nil
      }
      let cs = string_chars(st.input)
      // character index for octet (or character) position p
      let ci = match f {
        Some(f) => {
          let mut off = 0
          let mut k = 0
          while k < cs.length() && off < p {
            off += share_stringproc__encode_chars([cs[k]], f.enc).length()
            k += 1
          }
          if off != p {
            return Nil
          }
          k
        }
        None => if p <= cs.length() { p } else { return Nil }
      }
      st.pos = chars_to_string(cs[0:ci].to_array()).length()
      st.unread.clear()
      t
    }
  }
}

///|
fn d_fposition(stream : Value, pos? : Value = Nil) -> Value raise {
  if !streamp(stream) {
    io_error(Str("fposition"), Str("first")) |> ignore
  }
  let mut pos = pos
  let r = errset(() => if pos.truthy() {
    // set file-pos, return t (or nil)
    share_stringproc__file_position(stream, Some(num_sub(pos, int(1))))
  } else {
    // get file-pos, return pos (or nil)
    pos = share_stringproc__file_position(stream, None)
    if pos.truthy() {
      num_add(pos, int(1))
    } else {
      Nil
    }
  })
  match r {
    Some(v) if v.truthy() => v
    _ => s_pos_error1(Str("fposition"), pos)
  }
}

///|
fn d_readline(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("readline"), Str("the")) |> ignore
  }
  match read_line(stream~) {
    // Trim carriage return from end of string, if any.
    Some(line) => Str(string_right_trim("\r", line))
    None => Nil
  }
}

///|
fn d_readchar(stream : Value) -> Value raise {
  if !streamp(stream) {
    io_error(Str("readchar"), Str("the")) |> ignore
  }
  match read_char(stream~) {
    Char(c) => Str(c.to_string())
    _ => Nil
  }
}

///|
/// The port has no binary streams.
fn d_readbyte(stream : Value) -> Value raise {
  ignore(stream)
  gf_merror(Str("`readbyte': argument must be a binary stream."), Nil)
}

///|
fn d_writebyte(i : Value, stream : Value) -> Value raise {
  ignore(i)
  ignore(stream)
  gf_merror(Str("`writebyte': argument must be a binary stream."), Nil)
}

///|
fn d_freshline(stream? : Value = Nil) -> Value raise {
  if stream.truthy() && !streamp(stream) {
    io_error(Str("freshline"), Str("optional")) |> ignore
  }
  lbool(fresh_line(stream~))
}

///|
fn d_newline(stream? : Value = Nil) -> Value raise {
  if stream.truthy() && !streamp(stream) {
    io_error(Str("newline"), Str("optional")) |> ignore
  }
  terpri(stream~)
  Nil
}

// -- get or set a suitable encoding ----------------------------------------

///|
fn get_encoding(enc : Value, name : Value) -> Value raise {
  if enc.truthy() {
    // set encoding:
    if !stringp(enc) {
      gf_merror(
        Str("`~m': the optional second argument must be a string."),
        list([name]),
      )
      |> ignore
    }
    // All Lisps must recognize :default, per CLHS.
    if lstring(enc) == "DEFAULT" {
      return kw("default")
    }
    // (intern (string-upcase enc) :keyword)
    sym(":" + invert_case(string_upcase(lstring(enc))))
  } else {
    // get encoding: sb-impl::*default-external-format*
    q_kw_utf_8
  }
}

///|
fn is_ignored(enc : Value, name : Value, adds : Value) -> Value raise {
  format(t, "`~a': The argument ~s is ignored. Enter~%", [
    name,
    Str(string_downcase(share_unicode_sniffer__cl_keyword_name(enc))),
  ])
  |> ignore
  format(t, "adjust_external_format();~%~a.~%", [adds])
}

///|
/// SBCL: the external format of *standard-input* is utf-8, so nothing is
/// changed.
fn d_adjust_external_format() -> Value raise {
  format(t, "The external format is ~a~%and has not been changed.~%", [
    Str("NIL"),
  ])
}

///|
fn use_cp(name : Value, id : Value) -> Value raise {
  format(
    t,
    "Command line: To change the terminal encoding to ~a insert a line~%",
    [name],
  )
  |> ignore
  let prefix = if boundp(q_ear_maxima_prefix) {
    princ_to_string(symval(q_ear_maxima_prefix))
  } else {
    ""
  }
  format(t, "chcp ~a~%immediately below of '@echo off' in~%~s~%", [
    id,
    Str(prefix + "/bin/maxima.bat"),
  ])
  |> ignore
  format(
    t,
    "and in the properties of the terminal window set the font to a true type font.~%",
    [],
  )
}

// -------------------------------------------------------------------------
// 2. characters

///|
/// Check if object is a Maxima character.
fn d_charp(obj : Value) -> Value raise {
  lbool(
    stringp(obj) &&
    (if symval(q_ear_parse_utf_8_input).truthy() {
      to_int(utf_8_slength(obj))
    } else {
      string_length(lstring(obj))
    }) ==
    1,
  )
}

///|
/// Convert a string of length 1 into a Lisp character (at Maxima level only
/// for testing).
fn d_lchar(mc : Value) -> Value raise {
  l_char(mc)
}

///|
fn l_char(mc : Value) -> Value raise {
  if !(stringp(mc) && string_length(lstring(mc)) == 1) {
    gf_merror(
      Str("package stringproc: ~m cannot be converted into a Lisp character."),
      list([mc]),
    )
    |> ignore
  }
  Char(string_chars(lstring(mc))[0])
}

///|
/// Convert a Lisp character into a string of length 1.
fn cunlisp(lc : Value) -> Value raise {
  match lc {
    Char(c) => Str(c.to_string())
    _ => gf_merror(Str("cunlisp: argument must be a Lisp character"), Nil)
  }
}

///|
/// Check if object is a Lisp character (for testing only).
fn d_lcharp(obj : Value) -> Value raise {
  lbool(characterp(obj))
}

///|
fn d_constituent(mc : Value) -> Value raise {
  constituent(l_char(mc))
}

///|
fn d_alphanumericp(mc : Value) -> Value raise {
  lbool(alphanumericp(share_stringproc__lchar(l_char(mc))))
}

///|
fn d_alphacharp(mc : Value) -> Value raise {
  lbool(alpha_char_p(share_stringproc__lchar(l_char(mc))))
}

///|
fn d_lowercasep(mc : Value) -> Value raise {
  lbool(share_stringproc__lower_case_p(share_stringproc__lchar(l_char(mc))))
}

///|
fn d_uppercasep(mc : Value) -> Value raise {
  lbool(share_stringproc__upper_case_p(share_stringproc__lchar(l_char(mc))))
}

///|
fn d_digitcharp(mc : Value) -> Value raise {
  let nr = share_stringproc__lchar(l_char(mc)).to_int()
  lbool(nr > 47 && nr < 58)
}

///|
/// $cint returns the corresponding unicode code point.
fn d_cint(mc : Value) -> Value raise {
  if !d_charp(mc).truthy() {
    gf_merror(Str("`cint': argument must be a Maxima character."), Nil) |> ignore
  }
  mc2int(mc)
}

///|
fn mc2int(mc : Value) -> Value raise {
  if symval(q_ear_parse_utf_8_input).truthy() {
    // arguments larger than 16 bit might cause errors
    errset(() => utf8_to_uc(vector_to_list(string_to_raw_bytes(mc)))).unwrap_or(
      Nil,
    )
  } else {
    int(share_stringproc__chars(mc)[0].to_int())
  }
}

///|
/// $ascii returns a Maxima us-ascii-character for code points < 128.
fn d_ascii(int_ : Value) -> Value raise {
  if !(integerp(int_) && num_lt(int_, int(128))) {
    gf_merror(
      Str(
        "`ascii': argument must be a non-negative integer less than 128.\nPlease use `unicode' for code points larger than 127.",
      ),
      Nil,
    )
    |> ignore
  }
  Str(share_stringproc__code_char(int_).to_string())
}

///|
/// (code-char n)
fn share_stringproc__code_char(n : Value) -> Char raise {
  match n {
    Fix(k) if k >= 0L && k < 0x110000L => k.to_int().unsafe_to_char()
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(n) + " is not of type (MOD 1114112)",
      )
  }
}

///|
/// Character names known to the port's reader of #\name (SBCL names are
/// Unicode character names; only a few are known here).
let share_stringproc__char_names : Array[(String, Int)] = [
  ("NUL", 0),
  ("NULL", 0),
  ("SOH", 1),
  ("STX", 2),
  ("ETX", 3),
  ("EOT", 4),
  ("ENQ", 5),
  ("ACK", 6),
  ("BEL", 7),
  ("BELL", 7),
  ("BACKSPACE", 8),
  ("BS", 8),
  ("TAB", 9),
  ("HT", 9),
  ("NEWLINE", 10),
  ("LINEFEED", 10),
  ("LF", 10),
  ("VT", 11),
  ("PAGE", 12),
  ("FF", 12),
  ("RETURN", 13),
  ("CR", 13),
  ("SO", 14),
  ("SI", 15),
  ("ESCAPE", 27),
  ("ESC", 27),
  ("ALTMODE", 27),
  ("SPACE", 32),
  ("SP", 32),
  ("RUBOUT", 127),
  ("DELETE", 127),
  ("DEL", 127),
  ("NO-BREAK_SPACE", 0xA0),
  ("ZERO_WIDTH_NO-BREAK_SPACE", 0xFEFF),
  ("BYTE_ORDER_MARK", 0xFEFF),
  ("REPLACEMENT_CHARACTER", 0xFFFD),
  ("EURO_SIGN", 0x20AC),
  ("DEGREE_SIGN", 0xB0),
  ("MICRO_SIGN", 0xB5),
  ("INFINITY", 0x221E),
  ("LATIN_SMALL_LETTER_SHARP_S", 0xDF),
  ("LATIN_CAPITAL_LETTER_A_WITH_DIAERESIS", 0xC4),
  ("LATIN_CAPITAL_LETTER_O_WITH_DIAERESIS", 0xD6),
  ("LATIN_CAPITAL_LETTER_U_WITH_DIAERESIS", 0xDC),
  ("LATIN_SMALL_LETTER_A_WITH_DIAERESIS", 0xE4),
  ("LATIN_SMALL_LETTER_O_WITH_DIAERESIS", 0xF6),
  ("LATIN_SMALL_LETTER_U_WITH_DIAERESIS", 0xFC),
]

///|
/// Greek letter names (GREEK_SMALL_LETTER_ALPHA etc.).
let share_stringproc__greek : Array[String] = [
  "ALPHA", "BETA", "GAMMA", "DELTA", "EPSILON", "ZETA", "ETA", "THETA", "IOTA", "KAPPA",
  "LAMDA", "MU", "NU", "XI", "OMICRON", "PI", "RHO", "FINAL_SIGMA", "SIGMA", "TAU",
  "UPSILON", "PHI", "CHI", "PSI", "OMEGA",
]

///|
/// The character named NAME, as read by #\name.
fn share_stringproc__name_char(name : String) -> Char? {
  let cs = string_chars(name)
  if cs.length() == 1 {
    return Some(cs[0])
  }
  let up = string_upcase(name)
  for p in share_stringproc__char_names {
    if p.0 == up {
      return Some(p.1.unsafe_to_char())
    }
  }
  // U+XXXX, UXXXX
  if up.has_prefix("U") && cs.length() > 1 {
    let hex = if up.has_prefix("U+") { up.substring(start=2) } else { up.substring(start=1) }
    match parse_integer(hex, radix=16) {
      Some(Fix(n)) if n >= 0L && n < 0x110000L && hex.length() > 0 =>
        return Some(n.to_int().unsafe_to_char())
      _ => ()
    }
  }
  for i, g in share_stringproc__greek {
    let code = 0x3B1 + i
    if up == "GREEK_SMALL_LETTER_" + g {
      return Some(code.unsafe_to_char())
    }
    if up == "GREEK_CAPITAL_LETTER_" + g && g != "FINAL_SIGMA" {
      return Some((code - 32).unsafe_to_char())
    }
  }
  None
}

///|
/// $unicode returns a Maxima character for a given code point or name.
fn d_unicode(arg : Value) -> Value raise {
  if integerp(arg) {
    // arguments larger than 16 bit might cause errors
    errset(() => if symval(q_ear_parse_utf_8_input).truthy() {
      let ol = uc_to_utf8(arg)
      utf_8_m_char(int(length(ol)), ol)
    } else {
      Str(share_stringproc__code_char(arg).to_string())
    }).unwrap_or(Nil)
  } else if stringp(arg) {
    // (read "#\\" + name): ($ssubst "_" " " arg)
    let name = lstring(d_ssubst(Str("_"), Str(" "), arg, Nil))
    match share_stringproc__name_char(name) {
      Some(c) => Str(c.to_string())
      None => Nil
    }
  } else {
    gf_merror(
      Str("`unicode': argument must be a string or a non-negative integer."),
      Nil,
    )
  }
}

///|
/// Code point conversion utf-8 --> unicode.
fn d_utf8_to_unicode(utf8 : Value) -> Value raise {
  if !listp(utf8) {
    utf8_to_unicode_error() |> ignore
  }
  utf8_to_uc(cdr(utf8))
}

///|
fn d_unicode_to_utf8(uc : Value) -> Value raise {
  if !integerp(uc) {
    gf_merror(
      Str("`unicode_to_utf8': argument must be a non-negative integer."),
      Nil,
    )
    |> ignore
  }
  cons(list2(q_mlist, q_simp), uc_to_utf8(uc))
}

///|
fn utf8_to_unicode_error() -> Value raise {
  gf_merror(
    Str(
      "`utf8_to_unicode': argument must be a list of octets representing a single character.",
    ),
    Nil,
  )
}

///|
/// (ldb (byte size pos) n)
fn share_stringproc__ldb(size : Int, pos : Int, n : Value) -> Value raise {
  logand(ash(n, -pos), int((1 << size) - 1))
}

///|
fn utf8_to_uc(u : Value) -> Value raise {
  let l = length(u)
  let ldb = share_stringproc__ldb
  if l == 1 {
    if logbitp(7, car(u)) {
      utf8_to_unicode_error() |> ignore
    }
    car(u)
  } else if l == 2 {
    // check the first octet only
    if !num_eq(ldb(3, 5, car(u)), int(0b110)) {
      utf8_to_unicode_error() |> ignore
    }
    logior(ash(ldb(5, 0, car(u)), 6), ldb(6, 0, cadr(u)))
  } else if l == 3 {
    if !num_eq(ldb(4, 4, car(u)), int(0b1110)) {
      utf8_to_unicode_error() |> ignore
    }
    logior(
      logior(ash(ldb(4, 0, car(u)), 12), ash(ldb(6, 0, cadr(u)), 6)),
      ldb(6, 0, caddr(u)),
    )
  } else if l == 4 {
    if !num_eq(ldb(5, 3, car(u)), int(0b11110)) {
      utf8_to_unicode_error() |> ignore
    }
    logior(
      logior(ash(ldb(3, 0, car(u)), 18), ash(ldb(6, 0, cadr(u)), 12)),
      logior(ash(ldb(6, 0, caddr(u)), 6), ldb(6, 0, cadddr(u))),
    )
  } else {
    utf8_to_unicode_error()
  }
}

///|
fn uc_to_utf8(uc : Value) -> Value raise {
  let ldb = share_stringproc__ldb
  let mut utf8 : Value = Nil
  if num_lt(uc, int(0x7f)) {
    utf8 = cons(uc, utf8)
  } else if num_lt(uc, int(0x7ff)) {
    utf8 = cons(logior(int(128), ldb(6, 0, uc)), utf8)
    utf8 = cons(logior(int(192), ldb(5, 6, uc)), utf8)
  } else if num_lt(uc, int(0xffff)) {
    for i in [0, 6] {
      utf8 = cons(logior(int(128), ldb(6, i, uc)), utf8)
    }
    utf8 = cons(logior(int(224), ldb(4, 12, uc)), utf8)
  } else {
    for i in [0, 6, 12] {
      utf8 = cons(logior(int(128), ldb(6, i, uc)), utf8)
    }
    utf8 = cons(logior(int(240), ldb(3, 18, uc)), utf8)
  }
  utf8
}

///|
fn share_stringproc__code(mc : Value) -> Int raise {
  share_stringproc__lchar(l_char(mc)).to_int()
}

///|
fn share_stringproc__fold(mc : Value) -> Int raise {
  share_stringproc__equal_code(share_stringproc__lchar(l_char(mc)))
}

///|
fn d_cequal(mc1 : Value, mc2 : Value) -> Value raise {
  if symval(q_ear_parse_utf_8_input).truthy() {
    lbool(num_eq(mc2int(mc1), mc2int(mc2)))
  } else {
    lbool(share_stringproc__code(mc1) == share_stringproc__code(mc2))
  }
}

///|
fn d_clessp(mc1 : Value, mc2 : Value) -> Value raise {
  if symval(q_ear_parse_utf_8_input).truthy() {
    lbool(num_lt(mc2int(mc1), mc2int(mc2)))
  } else {
    lbool(share_stringproc__code(mc1) < share_stringproc__code(mc2))
  }
}

///|
fn d_cgreaterp(mc1 : Value, mc2 : Value) -> Value raise {
  if symval(q_ear_parse_utf_8_input).truthy() {
    lbool(num_gt(mc2int(mc1), mc2int(mc2)))
  } else {
    lbool(share_stringproc__code(mc1) > share_stringproc__code(mc2))
  }
}

///|
fn d_cequalignore(mc1 : Value, mc2 : Value) -> Value raise {
  lbool(share_stringproc__fold(mc1) == share_stringproc__fold(mc2))
}

///|
fn d_clesspignore(mc1 : Value, mc2 : Value) -> Value raise {
  lbool(share_stringproc__fold(mc1) < share_stringproc__fold(mc2))
}

///|
fn d_cgreaterpignore(mc1 : Value, mc2 : Value) -> Value raise {
  lbool(share_stringproc__fold(mc1) > share_stringproc__fold(mc2))
}

// Comparison - test functions - at Lisp level (Lisp chars assumed)

///|
fn cequal(c1 : Value, c2 : Value) -> Value raise {
  lbool(share_stringproc__lchar(c1) == share_stringproc__lchar(c2))
}

///|
fn clessp(c1 : Value, c2 : Value) -> Value raise {
  lbool(share_stringproc__lchar(c1).to_int() < share_stringproc__lchar(c2).to_int())
}

///|
fn cgreaterp(c1 : Value, c2 : Value) -> Value raise {
  lbool(share_stringproc__lchar(c1).to_int() > share_stringproc__lchar(c2).to_int())
}

///|
fn cequalignore(c1 : Value, c2 : Value) -> Value raise {
  lbool(
    share_stringproc__equal_code(share_stringproc__lchar(c1)) ==
    share_stringproc__equal_code(share_stringproc__lchar(c2)),
  )
}

///|
fn clesspignore(c1 : Value, c2 : Value) -> Value raise {
  lbool(
    share_stringproc__equal_code(share_stringproc__lchar(c1)) <
    share_stringproc__equal_code(share_stringproc__lchar(c2)),
  )
}

///|
fn cgreaterpignore(c1 : Value, c2 : Value) -> Value raise {
  lbool(
    share_stringproc__equal_code(share_stringproc__lchar(c1)) >
    share_stringproc__equal_code(share_stringproc__lchar(c2)),
  )
}

///|
/// Returns Maxima tab character; can be autoloaded.
fn d_tab() -> Value raise {
  symval(q_d_tab)
}

// -------------------------------------------------------------------------
// 3. strings
//
// 3.0 tools for parsing UTF-8 encoded strings

///|
/// Remove the first n octets which form an UTF-8 character from a list of
/// octets. Values: 1. A reference to the rest of the list. 2. The first n
/// octets.
fn rm_first_utf_8_char(ol : Value) -> (Value, Value) raise {
  let oct = car(ol)
  if logbitp(7, oct) {
    if logbitp(6, oct) {
      if logbitp(5, oct) {
        if logbitp(4, oct) {
          (nthcdr(4, ol), firstn(int(4), ol))
        } else {
          (nthcdr(3, ol), firstn(int(3), ol))
        }
      } else {
        (cddr(ol), firstn(int(2), ol))
      }
    } else {
      gf_merror(Str("error while encoding"), Nil) |> ignore
      (Nil, Nil)
    }
  } else {
    (cdr(ol), firstn(int(1), ol))
  }
}

///|
/// Retrieve an UTF-8 character from a list of octets.
fn utf_8_m_char(len : Value, ol : Value) -> Value raise {
  if num_eq(len, int(1)) {
    Str(share_stringproc__code_char(car(ol)).to_string())
  } else {
    let sb = StringBuilder::new()
    let mut l = ol
    for _ in 0..<to_int(len) {
      if l is Nil {
        break
      }
      sb.write_char(share_stringproc__code_char(car(l)))
      l = cdr(l)
    }
    // (make-string len) is filled with the default element
    for _ in 0..<(to_int(len) - length(ol)) {
      sb.write_char('\u{0}')
    }
    Str(sb.to_string())
  }
}

///|
/// The decrement we need to adjust octet positions to string positions
/// (string position = octet position - decrement).
fn utf_8_pos_dec(str : Value, pos : Value) -> Value raise {
  let ov = string_to_raw_bytes(str)
  let mut n = 0
  for i in 0..<to_int(pos) {
    if to_int(logand(aref1(ov, i), int(192))) == 128 {
      n += 1
    }
  }
  int(n)
}

///|
/// Fix start and end character positions according to given UTF-8 octets.
fn utf_8_fix_start_end(ov : Value, args : Value) -> Value raise {
  let mut start = cadr(args)
  let mut end = caddr(args)
  let inc = utf_8_pos_inc(ov, int(0), start)
  start = num_add(start, inc)
  rplaca(cdr(args), start) |> ignore
  if end.truthy() {
    end = num_add(end, inc)
    end = num_add(end, utf_8_pos_inc(ov, start, end))
    rplaca(cddr(args), end) |> ignore
  }
  args
}

///|
/// Compute the position increment we need to find the right octet
/// position (octet position = string position + increment).
fn utf_8_pos_inc(ov : Value, off : Value, pos : Value) -> Value raise {
  let pos0 = to_int(pos)
  let mut pos = pos0
  let mut i = to_int(off)
  while i != pos {
    let oct = aref1(ov, i)
    if logbitp(7, oct) && logbitp(6, oct) {
      if logbitp(5, oct) {
        if logbitp(4, oct) {
          pos += 3
        } else {
          pos += 2
        }
      } else {
        pos += 1
      }
    }
    i += 1
  }
  int(pos - pos0)
}

// 3.1 functions for strings

///|
fn d_stringp(obj : Value) -> Value raise {
  lbool(stringp(obj))
}

///|
fn d_scopy(s : Value) -> Value raise {
  if !stringp(s) {
    s_error1(Str("scopy"), Str("")) |> ignore
  }
  Str(lstring(s))
}

///|
fn d_smake(n : Value, mc : Value) -> Value raise {
  if !integerp(n) {
    gf_merror(Str("`smake': first argument must be an integer."), Nil) |> ignore
  }
  if !d_charp(mc).truthy() {
    gf_merror(Str("`smake': second argument must be a Maxima character."), Nil)
    |> ignore
  }
  if symval(q_ear_parse_utf_8_input).truthy() {
    let mut acc = mc
    for _ in 1..<to_int(n) {
      acc = d_sconcat(list2(acc, mc))
    }
    acc
  } else {
    let c = share_stringproc__chars(mc)[0]
    let sb = StringBuilder::new()
    for _ in 0..<share_stringproc__index(n) {
      sb.write_char(c)
    }
    Str(sb.to_string())
  }
}

///|
fn d_charat(str : Value, pos : Value) -> Value raise {
  if !stringp(str) {
    s_error1(Str("charat"), Str("first")) |> ignore
  }
  let mut end = pos
  let mut pos = num_sub(pos, int(1))
  let r = errset(() => {
    if symval(q_ear_parse_utf_8_input).truthy() {
      let ov = string_to_raw_bytes(str)
      let args = utf_8_fix_start_end(ov, list([Nil, pos, end]))
      pos = cadr(args)
      end = caddr(args)
    }
    share_stringproc__subseq(str, pos, end)
  })
  match r {
    Some(v) if v.truthy() => v
    _ => s_pos_error1(Str("charat"), num_add(pos, int(1)))
  }
}

///|
fn d_charlist(str : Value) -> Value raise {
  if !stringp(str) {
    s_error1(Str("charlist"), Str("")) |> ignore
  }
  let cl = string_chars(lstring(str))
  cons(
    list2(q_mlist, q_simp),
    if symval(q_ear_parse_utf_8_input).truthy() {
      utf_8_charlist(list(cl.map(c => Value::Char(c))))
    } else {
      list(cl.map(c => Str(c.to_string())))
    },
  )
}

///|
fn utf_8_charlist(cl : Value) -> Value raise {
  let mut ol = mapcar(c => int(share_stringproc__lchar(c).to_int()), cl)
  let mut m_chars : Value = Nil
  while !(ol is Nil) {
    let (rest, ch) = rm_first_utf_8_char(ol)
    ol = rest
    m_chars = cons(utf_8_m_char(int(length(ch)), ch), m_chars)
  }
  nreverse(m_chars)
}

///|
/// sexplode is the same as charlist.
fn d_sexplode(str : Value) -> Value raise {
  d_charlist(str)
}

///|
/// $tokens is an interface to `tokens' by Paul Graham.
fn d_tokens(str : Value, test_? : Value = q_d_constituent) -> Value raise {
  if !stringp(str) {
    s_error1(Str("tokens"), Str("first")) |> ignore
  }
  let test_ = stripdollar(test_)
  let name = match test_ {
    Sym(s) => s.name
    _ => ""
  }
  if !(
      [
        "constituent", "alphanumericp", "alphacharp", "digitcharp", "lowercasep", "uppercasep",
        "charp",
      ].contains(name)
    ) {
    gf_merror(
      Str(
        "`tokens': optional second argument must be one of ~%\nconstituent, alphanumericp, alphacharp, digitcharp, lowercasep, uppercasep, charp",
      ),
      Nil,
    )
    |> ignore
  }
  cons(list2(q_mlist, q_simp), tokens(str, test_, int(0)))
}

///|
/// Apply a $tokens test function to a character.
fn share_stringproc__char_test(test_ : Value, ch : Char) -> Bool raise {
  let name = match test_ {
    Sym(s) => s.name
    _ => ""
  }
  match name {
    "constituent" => constituent(Char(ch)).truthy()
    "alphanumericp" => alphanumericp(ch)
    "alphacharp" => alpha_char_p(ch)
    "digitcharp" => share_stringproc__digit_weight(ch) is Some(_)
    "lowercasep" => share_stringproc__lower_case_p(ch)
    "uppercasep" => share_stringproc__upper_case_p(ch)
    "charp" => true
    _ => funcall(test_, [Char(ch)]).truthy()
  }
}

///|
/// The original version by Paul Graham (ANSI Common Lisp, 1996, page 67).
fn tokens(str : Value, test_ : Value, start : Value) -> Value raise {
  let cs = share_stringproc__chars(str)
  let (s0, _) = share_stringproc__bounds(cs.length(), start, Nil)
  let mut pos1 = -1
  for i in s0..<cs.length() {
    if share_stringproc__char_test(test_, cs[i]) {
      pos1 = i
      break
    }
  }
  if pos1 < 0 {
    return Nil
  }
  let mut pos2 = -1
  for i in pos1..<cs.length() {
    if !share_stringproc__char_test(test_, cs[i]) {
      pos2 = i
      break
    }
  }
  if pos2 < 0 {
    cons(share_stringproc__str(cs[pos1:].to_array()), Nil)
  } else {
    cons(
      share_stringproc__str(cs[pos1:pos2].to_array()),
      tokens(str, test_, int(pos2)),
    )
  }
}

// test functions for $tokens on Lisp level:

///|
/// Paul Graham - ANSI Common Lisp, 1996, page 67
fn constituent(ch : Value) -> Value raise {
  let c = share_stringproc__lchar(ch)
  lbool(share_stringproc__graphic_char_p(c) && c != ' ')
}

///|
fn alphacharp(ch : Value) -> Value raise {
  lbool(alpha_char_p(share_stringproc__lchar(ch)))
}

///|
fn digitcharp(ch : Value) -> Value raise {
  match share_stringproc__digit_weight(share_stringproc__lchar(ch)) {
    Some(w) => int(w)
    None => Nil
  }
}

///|
fn lowercasep(ch : Value) -> Value raise {
  lbool(share_stringproc__lower_case_p(share_stringproc__lchar(ch)))
}

///|
fn uppercasep(ch : Value) -> Value raise {
  lbool(share_stringproc__upper_case_p(share_stringproc__lchar(ch)))
}

///|
fn charp(ch : Value) -> Value raise {
  lbool(characterp(ch))
}

///|
/// Split a string at an optional user defined delimiter string. In case of
/// a multiple delimiter string an optional flag may be set.
fn d_split(str : Value, args : Value) -> Value raise {
  if !stringp(str) {
    s_error1(Str("split"), Str("first")) |> ignore
  }
  // delimiter string; treat multiple occurencies of ds as one?
  let mut ds : Value = Str(" ")
  let mut multiple_q = t
  for a in args.iter() {
    if stringp(a) {
      ds = a
    } else if eq(a, t) || a is Nil {
      multiple_q = a
    } else {
      gf_merror(Str("`split': unsuitable optional arguments."), Nil) |> ignore
    }
  }
  if lstring(ds) == "" {
    d_charlist(str)
  } else {
    cons(list2(q_mlist, q_simp), split(str, ds, multiple_q~))
  }
}

///|
fn split(str : Value, ds : Value, multiple_q? : Value = t) -> Value raise {
  let s = share_stringproc__chars(str)
  let d = share_stringproc__chars(ds)
  let search = fn(start : Int) raise {
    share_stringproc__search(d, s, q_d_sequal, int(start), Nil)
  }
  let multiple = multiple_q.truthy()
  let pos1 = search(0)
  if pos1 is Nil {
    return list1(str)
  }
  let mut pos1 = to_int(pos1)
  let mut ss = share_stringproc__str(s[0:pos1].to_array())
  let mut lst : Value = Nil
  if !(multiple && lstring(ss) == "") {
    lst = cons(ss, lst)
  }
  let mut pos2 = int(pos1)
  while true {
    if pos2 is Nil {
      if multiple && lstring(ss) == "" {
        lst = cons(ss, lst)
      }
      return nreverse(lst)
    }
    let off = pos1 + d.length()
    pos2 = search(off)
    ss = if pos2 is Nil {
      share_stringproc__subseq(str, int(off), Nil)
    } else {
      share_stringproc__subseq(str, int(off), pos2)
    }
    if pos2.truthy() {
      pos1 = to_int(pos2)
    }
    if !(multiple && lstring(ss) == "") {
      lst = cons(ss, lst)
    }
  }
  Nil
}

///|
/// $sconcat for lists; optional: insert a user defined delimiter string.
fn d_simplode(li : Value, ds? : Value = Str("")) -> Value raise {
  if !listp(li) {
    gf_merror(Str("`simplode': first argument must be a list."), Nil) |> ignore
  }
  if !stringp(ds) {
    s_error1(Str("simplode"), Str("optional second")) |> ignore
  }
  let mut li = cdr(li)
  if li is Nil {
    d_sconcat(Nil)
  } else if cdr(li) is Nil {
    d_sconcat(list1(car(li)))
  } else if lstring(ds) == "" {
    // (reduce #'$sconcat li)
    let mut acc = car(li)
    for x in cdr(li).iter() {
      acc = d_sconcat(list2(acc, x))
    }
    acc
  } else {
    let sb = StringBuilder::new()
    while true {
      sb.write_string(lstring(d_sconcat(list1(car(li)))))
      li = cdr(li)
      if li is Nil {
        break
      }
      sb.write_string(lstring(ds))
    }
    Str(sb.to_string())
  }
}

///|
fn d_slength(str : Value) -> Value raise {
  if !stringp(str) {
    s_error1(Str("slength"), Str("")) |> ignore
  }
  if symval(q_ear_parse_utf_8_input).truthy() {
    utf_8_slength(str)
  } else {
    int(string_length(lstring(str)))
  }
}

///|
/// If we don't know the number of non-ascii characters, we have to count.
fn utf_8_slength(str : Value) -> Value raise {
  let ov = string_to_raw_bytes(str)
  let len = as_array(ov).data.length()
  let mut n = 0
  for i in 0..<len {
    if to_int(logand(aref1(ov, i), int(192))) != 128 {
      n += 1
    }
  }
  int(n)
}

///|
fn d_sposition(mc : Value, str : Value) -> Value raise {
  if !(
      stringp(mc) &&
      (if symval(q_ear_parse_utf_8_input).truthy() {
        to_int(d_slength(mc))
      } else {
        string_length(lstring(mc))
      }) ==
      1
    ) {
    gf_merror(Str("`sposition': first argument must be a Maxima character."), Nil)
    |> ignore
  }
  if !stringp(str) {
    s_error1(Str("sposition"), Str("second")) |> ignore
  }
  if symval(q_ear_parse_utf_8_input).truthy() {
    d_ssearch(mc, str, Nil)
  } else {
    let c = share_stringproc__chars(mc)[0]
    let cs = share_stringproc__chars(str)
    for i, x in cs {
      if x == c {
        return int(i + 1)
      }
    }
    Nil
  }
}

///|
fn d_sreverse(str : Value) -> Value raise {
  if !stringp(str) {
    s_error1(Str("sreverse"), Str("")) |> ignore
  }
  if symval(q_ear_parse_utf_8_input).truthy() {
    utf_8_sreverse(str)
  } else {
    let cs = share_stringproc__chars(str)
    cs.rev_in_place()
    share_stringproc__str(cs)
  }
}

///|
fn utf_8_sreverse(str : Value) -> Value raise {
  let mut ol = list(share_stringproc__chars(str).map(c => int(c.to_int())))
  let mut m_chars : Value = Nil
  while !(ol is Nil) {
    let (rest, ch) = rm_first_utf_8_char(ol)
    ol = rest
    m_chars = cons(utf_8_m_char(int(length(ch)), ch), m_chars)
  }
  let sb = StringBuilder::new()
  for s in m_chars.iter() {
    sb.write_string(lstring(s))
  }
  Str(sb.to_string())
}

///|
fn d_substring(str : Value, start : Value, end? : Value = Nil) -> Value raise {
  if !stringp(str) {
    s_error1(Str("substring"), Str("first")) |> ignore
  }
  let mut start = num_sub(start, int(1))
  let mut end = if end.truthy() { num_sub(end, int(1)) } else { end }
  let r = errset(() => {
    if symval(q_ear_parse_utf_8_input).truthy() {
      let ov = string_to_raw_bytes(str)
      let args = utf_8_fix_start_end(ov, list([Nil, start, end]))
      start = cadr(args)
      end = caddr(args)
    }
    share_stringproc__subseq(str, start, end)
  })
  match r {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("substring"))
  }
}

// comparison - test functions - at Maxima and Lisp level

///|
fn d_sequal(s1 : Value, s2 : Value) -> Value raise {
  lbool(share_stringproc__chars(s1) == share_stringproc__chars(s2))
}

///|
fn d_sequalignore(s1 : Value, s2 : Value) -> Value raise {
  let a = share_stringproc__chars(s1)
  let b = share_stringproc__chars(s2)
  if a.length() != b.length() {
    return Nil
  }
  for i in 0..<a.length() {
    if share_stringproc__equal_code(a[i]) != share_stringproc__equal_code(b[i]) {
      return Nil
    }
  }
  t
}

///|
fn d_slessp(s1 : Value, s2 : Value) -> Value raise {
  scompare(s1, s2, Str("slessp"), q_d_sequal, t, q_d_clessp)
}

///|
fn d_sgreaterp(s1 : Value, s2 : Value) -> Value raise {
  scompare(s1, s2, Str("sgreaterp"), q_d_sequal, Nil, q_d_cgreaterp)
}

///|
fn d_slesspignore(s1 : Value, s2 : Value) -> Value raise {
  scompare(s1, s2, Str("slesspignore"), q_d_sequalignore, t, q_d_clesspignore)
}

///|
fn d_sgreaterpignore(s1 : Value, s2 : Value) -> Value raise {
  scompare(s1, s2, Str("sgreaterpignore"), q_d_sequalignore, Nil, q_d_cgreaterpignore)
}

///|
fn scompare(
  s1 : Value,
  s2 : Value,
  name : Value,
  test_ : Value,
  lessp_q : Value,
  ccomp : Value,
) -> Value raise {
  if !(stringp(s1) && stringp(s2)) {
    s_error2(name, Str("the two")) |> ignore
  }
  let pos = share_stringproc__mismatch(
    share_stringproc__chars(s1),
    share_stringproc__chars(s2),
    test_,
  )
  let len = fn(s : Value) { int(string_length(lstring(s))) }
  if pos is Nil ||
    num_ge(pos, len(if lessp_q.truthy() { s2 } else { s1 })) {
    Nil
  } else if num_ge(pos, len(if lessp_q.truthy() { s1 } else { s2 })) {
    t
  } else {
    apply(ccomp, chars_to_compare(s1, s2, pos))
  }
}

///|
fn chars_to_compare(s1 : Value, s2 : Value, pos : Value) -> Value raise {
  let mut pos = to_int(pos)
  let mut l1 = 1
  let mut l2 = 1
  let c1 = share_stringproc__chars(s1)
  let c2 = share_stringproc__chars(s2)
  if symval(q_ear_parse_utf_8_input).truthy() {
    // When mismatch finds a pos somewhere in an utf-8 octet sequence we
    // have to identify the beginning and the length.
    while (c1[pos].to_int() & 192) == 128 {
      pos -= 1
    }
    l1 = to_int(parse_utf_8_header(s1, int(pos)))
    l2 = to_int(parse_utf_8_header(s2, int(pos)))
  }
  ignore(c2)
  list2(
    share_stringproc__subseq(s1, int(pos), int(pos + l1)),
    share_stringproc__subseq(s2, int(pos), int(pos + l2)),
  )
}

///|
/// The position start is the beginning of an utf-8 octet sequence; return
/// the length of this sequence.
fn parse_utf_8_header(str : Value, start : Value) -> Value raise {
  let h = int(share_stringproc__chars(str)[to_int(start)].to_int())
  let ldb = share_stringproc__ldb
  if !logbitp(7, h) {
    int(1)
  } else if num_eq(ldb(3, 5, h), int(0b110)) {
    int(2)
  } else if num_eq(ldb(4, 4, h), int(0b1110)) {
    int(3)
  } else if num_eq(ldb(5, 3, h), int(0b11110)) {
    int(4)
  } else {
    gf_merror(Str("`parse-utf-8-header': ~m is no utf-8 header"), list([h]))
  }
}

///|
fn d_smismatch(s1 : Value, s2 : Value, test_? : Value = q_d_sequal) -> Value raise {
  if !(stringp(s1) && stringp(s2)) {
    s_error2(Str("smismatch"), Str("first two")) |> ignore
  }
  if !(eq(test_, q_d_sequal) || eq(test_, q_d_sequalignore)) {
    gf_merror(
      Str("`smismatch': optional third argument must be `sequal' or `sequalignore'."),
      Nil,
    )
    |> ignore
  }
  let pos = share_stringproc__mismatch(
    share_stringproc__chars(s1),
    share_stringproc__chars(s2),
    test_,
  )
  if pos.truthy() {
    if symval(q_ear_parse_utf_8_input).truthy() {
      let p = to_int(pos)
      num_sub(
        int(p + 1),
        utf_8_pos_dec(
          s1,
          int(if p == string_length(lstring(s1)) { p } else { p + 1 }),
        ),
      )
    } else {
      num_add(pos, int(1))
    }
  } else {
    Nil
  }
}

// searching: the optional args are test, start, end (see s-optional-args)

///|
fn d_ssearch(seq : Value, str : Value, args : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("ssearch"), Str("first two")) |> ignore
  }
  let args = s_optional_args(Str("ssearch"), str, args)
  let r = errset(() => {
    let pos = ssearch(
      seq,
      str,
      test_=nth(0, args),
      start=nth(1, args),
      end=nth(2, args),
    )
    if pos.truthy() {
      if symval(q_ear_parse_utf_8_input).truthy() {
        num_sub(num_add(pos, int(1)), utf_8_pos_dec(str, pos))
      } else {
        num_add(pos, int(1))
      }
    } else {
      // (return-from $ssearch nil)
      Str("")
    }
  })
  match r {
    Some(Str("")) => Nil
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("ssearch"))
  }
}

///|
fn ssearch(
  seq : Value,
  str : Value,
  test_? : Value = q_d_sequal,
  start? : Value = Fix(0L),
  end? : Value = Nil,
) -> Value raise {
  share_stringproc__search(
    share_stringproc__chars(seq),
    share_stringproc__chars(str),
    test_,
    start,
    end,
  )
}

///|
/// Allow arbitrary order of the optional args test, start, end (where
/// start is of course the first integer in sequence).
fn s_optional_args(name : Value, str : Value, args : Value) -> Value raise {
  let mut test_ = q_d_sequal
  let mut start = int(1)
  let mut end : Value = Nil
  let mut i = 0
  for a in args.iter() {
    if i == 0 && integerp(a) {
      start = a
      i = 1
    } else if i == 1 && (integerp(a) || a is Nil) {
      end = a
      i = 2
    } else if eq(a, q_d_sequal) || eq(a, q_d_sequalignore) {
      test_ = a
    } else {
      gf_merror(Str("~m: unsuitable optional arguments."), list([name])) |> ignore
    }
  }
  let mut args = list([
    test_,
    num_sub(start, int(1)),
    if end.truthy() {
      num_sub(end, int(1))
    } else {
      Nil
    },
  ])
  if symval(q_ear_parse_utf_8_input).truthy() {
    let a0 = args
    match errset(() => utf_8_fix_start_end(string_to_raw_bytes(str), a0)) {
      Some(v) if v.truthy() => args = v
      _ => s_pos_error2(name) |> ignore
    }
  }
  args
}

// functions for string manipulation

///|
fn d_ssubstfirst(new_ : Value, old : Value, str : Value, args : Value) -> Value raise {
  if !(stringp(new_) && stringp(old) && stringp(str)) {
    s_error2(Str("ssubstfirst"), Str("first three")) |> ignore
  }
  let args = s_optional_args(Str("ssubstfirst"), str, args)
  match
    errset(() => ssubstfirst(
      new_,
      old,
      str,
      test_=nth(0, args),
      start=nth(1, args),
      end=nth(2, args),
    )) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("ssubstfirst"))
  }
}

///|
fn ssubstfirst(
  new_ : Value,
  old : Value,
  str : Value,
  test_? : Value = q_d_sequal,
  start? : Value = Fix(0L),
  end? : Value = Nil,
  matched_q? : Value = Nil,
) -> Value raise {
  let len = string_length(lstring(old))
  let pos = if matched_q.truthy() {
    start
  } else {
    share_stringproc__search(
      share_stringproc__chars(old),
      share_stringproc__chars(str),
      test_,
      start,
      end,
    )
  }
  if pos is Nil {
    str
  } else {
    let cs = share_stringproc__chars(str)
    let p = to_int(pos)
    let (_, _) = share_stringproc__bounds(cs.length(), pos, Nil)
    let (_, _) = share_stringproc__bounds(cs.length(), int(p + len), Nil)
    Str(
      chars_to_string(cs[0:p].to_array()) +
      lstring(new_) +
      chars_to_string(cs[p + len:].to_array()),
    )
  }
}

///|
fn d_ssubst(new_ : Value, old : Value, str : Value, args : Value) -> Value raise {
  if !(stringp(new_) && stringp(old) && stringp(str)) {
    s_error2(Str("ssubst"), Str("first three")) |> ignore
  }
  let args = s_optional_args(Str("ssubst"), str, args)
  match
    errset(() => ssubst(
      new_,
      old,
      str,
      test_=nth(0, args),
      start=nth(1, args),
      end=nth(2, args),
    )) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("ssubst"))
  }
}

///|
fn ssubst(
  new_ : Value,
  old : Value,
  str : Value,
  test_? : Value = q_d_sequal,
  start? : Value = Fix(0L),
  end? : Value = Nil,
) -> Value raise {
  let n = string_length(lstring(new_))
  let o = string_length(lstring(old))
  let oc = share_stringproc__chars(old)
  let mut str = str
  let mut start = start
  let mut end = end
  while true {
    let pos = share_stringproc__search(
      oc,
      share_stringproc__chars(str),
      test_,
      start,
      end,
    )
    if pos is Nil {
      break
    }
    str = ssubstfirst(new_, old, str, test_~, start=pos, end~, matched_q=t)
    start = num_add(pos, int(n))
    end = if end.truthy() { num_sub(num_add(end, int(n)), int(o)) } else { Nil }
  }
  str
}

///|
fn d_sremovefirst(seq : Value, str : Value, args : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("sremovefirst"), Str("first two")) |> ignore
  }
  let args = s_optional_args(Str("sremovefirst"), str, args)
  match
    errset(() => sremovefirst(
      seq,
      str,
      test_=nth(0, args),
      start=nth(1, args),
      end=nth(2, args),
    )) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("sremovefirst"))
  }
}

///|
fn sremovefirst(
  seq : Value,
  str : Value,
  test_? : Value = q_d_sequal,
  start? : Value = Fix(0L),
  end? : Value = Nil,
) -> Value raise {
  let len = string_length(lstring(seq))
  let pos = share_stringproc__search(
    share_stringproc__chars(seq),
    share_stringproc__chars(str),
    test_,
    start,
    end,
  )
  let sq1 = share_stringproc__subseq(str, int(0), pos)
  let sq2 = if pos.truthy() {
    share_stringproc__subseq(str, int(to_int(pos) + len), Nil)
  } else {
    Str("")
  }
  Str(lstring(sq1) + lstring(sq2))
}

///|
fn d_sremove(seq : Value, str : Value, args : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("sremove"), Str("first two")) |> ignore
  }
  let args = s_optional_args(Str("sremove"), str, args)
  match
    errset(() => sremove(
      seq,
      str,
      test_=nth(0, args),
      start=nth(1, args),
      end=nth(2, args),
    )) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("sremove"))
  }
}

///|
fn sremove(
  seq : Value,
  str : Value,
  test_? : Value = q_d_sequal,
  start? : Value = Fix(0L),
  end? : Value = Nil,
) -> Value raise {
  let sc = share_stringproc__chars(seq)
  let mut str = str
  let mut end = end
  let mut pos = share_stringproc__search(
    sc,
    share_stringproc__chars(str),
    test_,
    start,
    end,
  )
  while !(pos is Nil) {
    str = sremovefirst(seq, str, test_~, start=pos, end~)
    if end.truthy() {
      end = num_sub(end, int(sc.length()))
    }
    pos = share_stringproc__search(
      sc,
      share_stringproc__chars(str),
      test_,
      pos,
      end,
    )
  }
  str
}

///|
fn d_sinsert(seq : Value, str : Value, pos : Value) -> Value raise {
  let mut pos = num_sub(pos, int(1))
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("sinsert"), Str("first two")) |> ignore
  }
  match
    errset(() => {
      if symval(q_ear_parse_utf_8_input).truthy() {
        pos = num_add(pos, utf_8_pos_inc(string_to_raw_bytes(str), int(0), pos))
      }
      let sq1 = share_stringproc__subseq(str, int(0), pos)
      let sq2 = share_stringproc__subseq(str, pos, Nil)
      Str(lstring(sq1) + lstring(seq) + lstring(sq2))
    }) {
    Some(v) if v.truthy() => v
    _ => s_pos_error1(Str("sinsert"), num_add(pos, int(1)))
  }
}

///|
fn d_ssort(str : Value, test_? : Value = q_d_clessp) -> Value raise {
  if !stringp(str) {
    s_error1(Str("ssort"), Str("first")) |> ignore
  }
  if symval(q_ear_parse_utf_8_input).truthy() {
    if !(eq(test_, q_d_clessp) || eq(test_, q_d_cgreaterp)) {
      let alt = "and the external format is not adjusted to UTF-8"
      gf_merror(
        Str(
          "`ssort': when us_ascii_only is false ~a \nthe optional second argument must be `clessp' or `cgreaterp'.",
        ),
        list1(Str(alt)),
      )
      |> ignore
    }
  } else if !(
      eq(test_, q_d_clessp) ||
      eq(test_, q_d_cgreaterp) ||
      eq(test_, q_d_clesspignore) ||
      eq(test_, q_d_cgreaterpignore)
    ) {
    gf_merror(
      Str(
        "`ssort': optional second argument must be one of ~%clessp[ignore], cgreaterp[ignore]",
      ),
      Nil,
    )
    |> ignore
  }
  let test_ = stripdollar(test_)
  if symval(q_ear_parse_utf_8_input).truthy() {
    utf_8_ssort(str, test_~)
  } else {
    let cs = share_stringproc__chars(str).map(c => Value::Char(c))
    let sorted = share_stringproc__stable_sort(cs, (a, b) => funcall(test_, [a, b]).truthy())
    let out : Array[Char] = []
    for c in sorted {
      out.push(share_stringproc__lchar(c))
    }
    share_stringproc__str(out)
  }
}

///|
fn utf_8_ssort(str : Value, test_? : Value = q_clessp) -> Value raise {
  let lessp = equal(test_, q_clessp)
  let mut ol = vector_to_list(string_to_raw_bytes(str))
  let code_pts : Array[Value] = []
  while !(ol is Nil) {
    let (rest, utf8) = rm_first_utf_8_char(ol)
    ol = rest
    code_pts.insert(0, utf8_to_uc(utf8))
  }
  let sorted = share_stringproc__stable_sort(code_pts, (a, b) => if lessp {
    num_lt(a, b)
  } else {
    num_gt(a, b)
  })
  let sb = StringBuilder::new()
  for n in sorted {
    sb.write_string(lstring(d_unicode(n)))
  }
  Str(sb.to_string())
}

///|
fn d_strim(seq : Value, str : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("strim"), Str("")) |> ignore
  }
  Str(string_trim(lstring(seq), lstring(str)))
}

///|
fn d_striml(seq : Value, str : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("striml"), Str("")) |> ignore
  }
  Str(string_left_trim(lstring(seq), lstring(str)))
}

///|
fn d_strimr(seq : Value, str : Value) -> Value raise {
  if !(stringp(seq) && stringp(str)) {
    s_error2(Str("strimr"), Str("")) |> ignore
  }
  Str(string_right_trim(lstring(seq), lstring(str)))
}

///|
/// (string-upcase / string-downcase str :start start :end end)
fn share_stringproc__case_fun(up : Bool) -> Value {
  lfunc(if up { "string-upcase" } else { "string-downcase" }, args => {
    let cs = share_stringproc__chars(arg(args, 0))
    let (s, e) = share_stringproc__bounds(cs.length(), arg(args, 1), arg(args, 2))
    for i in s..<e {
      cs[i] = if up {
        share_stringproc__char_upcase(cs[i])
      } else {
        share_stringproc__char_downcase(cs[i])
      }
    }
    share_stringproc__str(cs)
  })
}

///|
fn d_supcase(str : Value, start? : Value = Fix(1L), end? : Value = Nil) -> Value raise {
  change_case(str, Str("supcase"), share_stringproc__case_fun(true), start, end)
}

///|
fn d_sdowncase(str : Value, start? : Value = Fix(1L), end? : Value = Nil) -> Value raise {
  change_case(str, Str("sdowncase"), share_stringproc__case_fun(false), start, end)
}

///|
fn change_case(
  str : Value,
  name : Value,
  sfun : Value,
  start : Value,
  end : Value,
) -> Value raise {
  if !stringp(str) {
    s_error1(name, Str("first")) |> ignore
  }
  let start = num_sub(start, int(1))
  let end = if end.truthy() { num_sub(end, int(1)) } else { end }
  match
    errset(() => if symval(q_ear_parse_utf_8_input).truthy() {
      let ov = string_to_raw_bytes(str)
      let args = utf_8_fix_start_end(ov, list([Nil, start, end]))
      funcall(sfun, [str, cadr(args), caddr(args)])
    } else {
      funcall(sfun, [str, start, end])
    }) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(name)
  }
}

///|
fn d_sinvertcase(str : Value, start? : Value = Fix(1L), end? : Value = Nil) -> Value raise {
  if !stringp(str) {
    s_error1(Str("sinvertcase"), Str("first")) |> ignore
  }
  let mut start = num_sub(start, int(1))
  let mut end = if end.truthy() { num_sub(end, int(1)) } else { end }
  match
    errset(() => {
      if symval(q_ear_parse_utf_8_input).truthy() {
        let ov = string_to_raw_bytes(str)
        let args = utf_8_fix_start_end(ov, list([Nil, start, end]))
        start = cadr(args)
        end = caddr(args)
      }
      let sq1 = share_stringproc__subseq(str, int(0), start)
      let sq2 = s_invert_case(share_stringproc__subseq(str, start, end))
      let sq3 = if end.truthy() {
        share_stringproc__subseq(str, end, Nil)
      } else {
        Str("")
      }
      Str(lstring(sq1) + lstring(sq2) + lstring(sq3))
    }) {
    Some(v) if v.truthy() => v
    _ => s_pos_error2(Str("sinvertcase"))
  }
}

///|
fn s_invert_case(str : Value) -> Value raise {
  let cs = share_stringproc__chars(str)
  let sb = StringBuilder::new()
  for c in cs {
    sb.write_char(share_stringproc__lchar(c_invert_case(Char(c))))
  }
  Str(sb.to_string())
}

///|
fn c_invert_case(ch : Value) -> Value raise {
  let c = share_stringproc__lchar(ch)
  if share_stringproc__upper_case_p(c) {
    Char(share_stringproc__char_downcase(c))
  } else {
    Char(share_stringproc__char_upcase(c))
  }
}

// -------------------------------------------------------------------------

///|
fn init_share_stringproc() -> Unit raise {
  defvar_init(q_ear_parse_utf_8_input, init__starparse_utf_8_input_star())
  putprop(q_d_us_ascii_only, q_set__starparse_utf_8_input_star, q_assign)
  |> ignore
  // Special Maxima characters
  let string_pred = list2(
    lfunc("stringp", args => lbool(stringp(arg(args, 0)))),
    Str("must be a string"),
  )
  for p in [(q_d_newline, "\n"), (q_d_tab, "\t"), (q_d_space, " ")] {
    defmvar(p.0, val=Str(p.1), list([kw("setting-predicate"), string_pred]))
    |> ignore
  }
}
