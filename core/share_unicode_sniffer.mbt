// Port of share/stringproc/unicode-sniffer.lisp: attempt to determine the
// Unicode encoding of a file by inspecting its initial bytes (byte order
// mark), as described at https://en.wikipedia.org/wiki/Byte_order_mark.
//
// Encodings are keywords, as in SBCL (the port name of CL :UTF-8 is
// ":utf-8").

///|
/// The names of the external formats that SBCL's CHECK-ENCODING-SBCL
/// recognizes (the EXTERNAL-FORMAT objects of SB-IMPL::*EXTERNAL-FORMATS*
/// in SBCL 2.6), as port keyword names.
let share_unicode_sniffer__sbcl_formats : Array[Array[String]] = [
  [":ucs-2le", ":ucs2le"],
  [":ucs-2be", ":ucs2be"],
  [":ucs-4le", ":ucs4le"],
  [":ucs-4be", ":ucs4be"],
  [":utf-16le", ":utf16le"],
  [":utf-16be", ":utf16be"],
  [":utf-32le", ":utf32le"],
  [":utf-32be", ":utf32be"],
  [":gbk", ":cp936"],
  [":euc-jp", ":eucjp", ":EUCJP"],
  [":shift_jis", ":sjis", ":SHIFT_JIS", ":cp932"],
]

///|
/// Raw bytes of the file F, as CL OPEN with element type (unsigned-byte 8)
/// would read them.
fn share_unicode_sniffer__file_bytes(f : String) -> Bytes raise {
  @fs.read_file_to_bytes(f) catch {
    _ =>
      raise LispError::Condition(
        intern("file-error"),
        "error opening " + f + ": No such file or directory",
        Str(f),
      )
  }
}

///|
fn sniffer_match(initial_bytes : Value, signature_bytes : Value) -> Value raise {
  let m = length(signature_bytes)
  // (subseq initial-bytes 0 m)
  if length(initial_bytes) < m {
    raise LispError::SimpleError(
      "The bounding indices 0 and \{m} are bad for a sequence of length \{length(initial_bytes)}.",
    )
  }
  let initial_bytes_subseq = firstn(int(m), initial_bytes)
  let byte_pairs = share_unicode_sniffer__mapcar2(
    (a, b) => list2(a, b),
    initial_bytes_subseq,
    signature_bytes,
  )
  for p in byte_pairs.iter() {
    if !equal(car(p), cadr(p)) {
      return Nil
    }
  }
  t
}

///|
/// (mapcar f l1 l2)
fn share_unicode_sniffer__mapcar2(f : (Value, Value) -> Value raise, l1 : Value, l2 : Value) -> Value raise {
  let c = Collector::new()
  let mut a = l1
  let mut b = l2
  while consp(a) && consp(b) {
    c.add(f(car(a), car(b)))
    a = cdr(a)
    b = cdr(b)
  }
  c.result()
}

///|
fn sniffer_match_search(initial_bytes : Value) -> Value raise {
  for x in symval(q_unicode_signatures).iter() {
    if sniffer_match(initial_bytes, car(x)).truthy() {
      return cdr(x)
    }
  }
  Nil
}

///|
/// Given a file name F, returns a Unicode encoding designator if the
/// initial bytes of F match any signature in the UNICODE-SIGNATURES table,
/// otherwise NIL.
fn unicode_sniffer(f : Value) -> Value raise {
  let bytes = share_unicode_sniffer__file_bytes(lstring(f))
  let mut signature_length_max = 0
  for x in symval(q_unicode_signatures).iter() {
    signature_length_max = signature_length_max.max(length(car(x)))
  }
  let c = Collector::new()
  for i in 0..<signature_length_max {
    c.add(if i < bytes.length() { int(bytes[i].to_int()) } else { Nil })
  }
  sniffer_match_search(c.result())
}

///|
/// Expose UNICODE-SNIFFER to Maxima user. Returns the symbol name of the
/// encoding, if any was found, otherwise "DEFAULT".
fn d_inferred_encoding(f : Value) -> Value raise {
  let e = unicode_sniffer(f)
  if e.truthy() {
    Str(share_unicode_sniffer__cl_keyword_name(e))
  } else {
    Str("DEFAULT")
  }
}

///|
/// The CL symbol name of a keyword (port name ":utf-8" -> "UTF-8").
fn share_unicode_sniffer__cl_keyword_name(e : Value) -> String raise {
  let n = symbol_name(e)
  invert_case(if n.has_prefix(":") { n.substring(start=1) } else { n })
}

///|
/// Try to verify that the inferred encoding is among the encodings known
/// to this Lisp implementation (SBCL).
fn check_encoding(e : Value) -> Value raise {
  check_encoding_sbcl(e)
}

///|
/// SBCL: look E up among the names of the external formats.
fn check_encoding_sbcl(e : Value) -> Value raise {
  let n = match e {
    Sym(s) => s.name
    _ => return Nil
  }
  for names in share_unicode_sniffer__sbcl_formats {
    for i, nm in names {
      if nm == n {
        let c = Collector::new()
        for j in i..<names.length() {
          c.add(sym(names[j]))
        }
        return c.result()
      }
    }
  }
  Nil
}

///|
/// Expose CHECK-ENCODING to Maxima user. Argument is an encoding symbol
/// name, such as that returned by $INFERRED_ENCODING.
fn d_recognized_encoding_p(e : Value) -> Value raise {
  let es = lstring(e)
  let e_up = string_upcase(es)
  let e_down = string_downcase(es)
  if e_up == "DEFAULT" {
    return t
  }
  // (find-symbol name :keyword): CL keyword names are upper case, so the
  // port name of the keyword found for CL name N is ":" + (invert-case N).
  let s = {
    let mut found : Value = Nil
    for nm in [es, e_up, e_down] {
      let pn = ":" + invert_case(nm)
      if share_unicode_sniffer__keyword_exists(pn) {
        found = sym(pn)
        break
      }
    }
    found
  }
  if s.truthy() {
    let x = check_encoding(s)
    lbool(x.truthy())
  } else {
    Nil
  }
}

///|
/// Does a keyword named PN (port name) exist?  All external format names
/// are keywords in SBCL.
fn share_unicode_sniffer__keyword_exists(pn : String) -> Bool {
  for names in share_unicode_sniffer__sbcl_formats {
    for nm in names {
      if nm == pn {
        return true
      }
    }
  }
  false
}

///|
fn init_share_unicode_sniffer() -> Unit raise {
  // Sort signatures in order of decreasing length, so longer signatures
  // are tested first (stable sort).
  let sigs : Array[(Array[Int], String)] = [
    ([0xEF, 0xBB, 0xBF], "utf-8"),
    ([0xFE, 0xFF], "utf-16be"),
    ([0xFF, 0xFE], "utf-16le"),
    ([0x00, 0x00, 0xFE, 0xFF], "utf-32be"),
    ([0xFF, 0xFE, 0x00, 0x00], "utf-32le"),
    ([0x2B, 0x2F, 0x76, 0x38], "utf-7"),
    ([0x2B, 0x2F, 0x76, 0x39], "utf-7"),
    ([0x2B, 0x2F, 0x76, 0x2B], "utf-7"),
    ([0x2B, 0x2F, 0x76, 0x2F], "utf-7"),
    ([0x2B, 0x2F, 0x76, 0x38, 0x2D], "utf-7"),
    ([0xF7, 0x64, 0x4C], "utf-1"),
    ([0xDD, 0x73, 0x66, 0x73], "utf-ebcdic"),
    ([0x0E, 0xFE, 0xFF], "scsu"),
    ([0xFB, 0xEE, 0x28], "bocu-1"),
    ([0x84, 0x31, 0x95, 0x33], "cp936"),
  ]
  let sorted : Array[(Array[Int], String)] = []
  for len = 5; len >= 1; len = len - 1 {
    for s in sigs {
      if s.0.length() == len {
        sorted.push(s)
      }
    }
  }
  let c = Collector::new()
  for s in sorted {
    c.add(cons(list(s.0.map(b => int(b))), kw(s.1)))
  }
  set(q_unicode_signatures, c.result()) |> ignore
}
