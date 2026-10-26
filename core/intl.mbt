// Port of src/intl.lisp: the INTL message-catalog package (gettext).
//
// Translated code uses the glue `gettext(s)` (identity) for
// `(intl:gettext s)`.  The functions here follow the Lisp implementation,
// with these limitations of the runtime:
// - streams are character streams: READ-LELONG/READ-BELONG read character
//   codes as bytes;
// - binary .mo files cannot be read (no byte streams or FILE-POSITION), so
//   LOAD-DOMAIN never loads a catalog and messages stay untranslated;
// - there is no readtable, so INSTALL cannot install the reader macros
//   (the reader functions are still provided).

///|
/// DOMAIN-ENTRY structure:
/// (domain locale file plurals hash encoding readfn)
fn intl__make_domain_entry() -> Value {
  make_struct("domain-entry", [
    Str(""),
    Str(""),
    Str(""),
    Nil,
    make_hash_table(kind=Equal),
    Nil,
    Nil,
  ])
}

///|
fn intl__de_locale(d : Value) -> Value raise {
  struct_ref(d, 1)
}

///|
fn intl__de_plurals(d : Value) -> Value raise {
  struct_ref(d, 3)
}

///|
fn intl__de_hash(d : Value) -> Value raise {
  struct_ref(d, 4)
}

///|
fn intl__de_encoding(d : Value) -> Value raise {
  struct_ref(d, 5)
}

///|
fn intl__read_byte(stream : Value) -> Int32 raise {
  match read_char(stream~, eof_value=Nil) {
    Char(c) => c.to_int() & 255
    _ => raise LispError::SimpleError("end of file")
  }
}

///|
fn intl_read_lelong(stream : Value) -> Value raise {
  let b0 = intl__read_byte(stream)
  let b1 = intl__read_byte(stream)
  let b2 = intl__read_byte(stream)
  let b3 = intl__read_byte(stream)
  int64(
    b0.to_int64() +
    (b1.to_int64() << 8) +
    (b2.to_int64() << 16) +
    (b3.to_int64() << 24),
  )
}

///|
fn intl_read_belong(stream : Value) -> Value raise {
  let b0 = intl__read_byte(stream)
  let b1 = intl__read_byte(stream)
  let b2 = intl__read_byte(stream)
  let b3 = intl__read_byte(stream)
  int64(
    (b0.to_int64() << 24) +
    (b1.to_int64() << 16) +
    (b2.to_int64() << 8) +
    b3.to_int64(),
  )
}

///|
fn intl_locate_domain_file(
  domain : Value,
  locale : Value,
  locale_dir : Value,
) -> Value raise {
  let path = (loc : String, base : Value) => {
    lstring(string(base)) + loc + "/LC_MESSAGES/" + lstring(domain) + ".mo"
  }
  let alias = gethash(locale, symval(q_ear_locale_aliases))
  let locale = lstring(if alias.truthy() { alias } else { locale })
  let bases = if listp(locale_dir) { locale_dir } else { list1(locale_dir) }
  let cs = string_chars(locale)
  let cut = (c : Char) => {
    match cs.search(c) {
      Some(i) => Some(substring(locale, 0, end=i))
      None => None
    }
  }
  for base in bases.iter() {
    let candidates = [Some(locale), cut('.'), cut('@'), cut('_')]
    for c in candidates {
      match c {
        Some(loc) => {
          let p = path(loc, base)
          if probe_file(p) {
            return Str(p)
          }
        }
        None => ()
      }
    }
  }
  Nil
}

///|
fn intl_find_encoding(domain : Value) -> Value raise {
  if intl__de_encoding(domain) is Nil {
    struct_set(domain, 5, kw("iso-8859-1")) |> ignore
    let header = lstring(intl_domain_lookup(Str(""), domain))
    let ctype = string_search(header, "Content-Type: ")
    if ctype >= 0 {
      let hs = string_chars(header)
      let mut eoln = hs.length()
      for i in ctype..<hs.length() {
        if hs[i] == '\n' {
          eoln = i
          break
        }
      }
      let charset = string_search(
        substring(header, 0, end=eoln),
        "; charset=",
        start=ctype,
      )
      if charset >= 0 {
        let start = charset + 10
        let mut i = start
        while i < eoln && (alphanumericp(hs[i]) || hs[i] == '-') {
          i += 1
        }
        // (intern (nstring-upcase ...) :keyword), as a port name
        struct_set(
          domain,
          5,
          kw(string_downcase(substring(header, start, end=i))),
        )
        |> ignore
      }
    }
  }
  domain
}

///|
fn intl_parse_plurals(domain : Value) -> (Value, Value) raise {
  let header = lstring(intl_domain_lookup(Str(""), domain))
  let plurals = string_search(header, "Plural-Forms: ")
  let default = lfunc("default-plural", args => {
    if num_eq(arg(args, 0), Fix(1L)) {
      Fix(0L)
    } else {
      Fix(1L)
    }
  })
  let n = string_length(header)
  if plurals >= 0 &&
    n > plurals + 36 &&
    substring(header, plurals + 14, end=plurals + 23) == "nplurals=" {
    let hs = string_chars(header)
    let mut j = plurals + 23
    while j < n && hs[j] >= '0' && hs[j] <= '9' {
      j += 1
    }
    let nplurals = match parse_integer(substring(header, plurals + 23, end=j)) {
      Some(v) => v
      None => Nil
    }
    let mut semi = plurals + 23
    while semi < n && hs[semi] != ';' {
      semi += 1
    }
    let point = semi + 2
    if n > point + 10 && substring(header, point, end=point + 7) == "plural=" {
      (intl_parse_expr(Str(header), int(point + 7)), nplurals)
    } else {
      (default, Fix(2L))
    }
  } else {
    (default, Fix(2L))
  }
}

///|
/// The plural-expression parser state.
priv struct IntlParser {
  cs : Array[Char]
  mut pos : Int32
}

///|
fn intl__ch(p : IntlParser, i : Int32) -> Char {
  if i < p.cs.length() {
    p.cs[i]
  } else {
    '\u{00}'
  }
}

///|
fn intl__next(p : IntlParser) -> Value raise {
  while intl__ch(p, p.pos) == ' ' ||
        intl__ch(p, p.pos) == '\t' ||
        intl__ch(p, p.pos) == '\n' {
    p.pos += 1
  }
  if p.pos >= p.cs.length() {
    raise LispError::SimpleError("end of string")
  }
  let c = p.cs[p.pos]
  p.pos += 1
  let s = (name : String) => sym(name)
  match c {
    'n' => s("n")
    '?' => s("if")
    ':' => s("then")
    '(' => s("lpar")
    ')' => s("rpar")
    '^' => s("logxor")
    '+' => s("add")
    '-' => s("sub")
    '*' => s("mul")
    '/' => s("floor")
    '%' => s("mod")
    '~' => s("lognot32")
    ';' => s("end")
    '|' =>
      if intl__ch(p, p.pos) == '|' {
        p.pos += 1
        s("cor")
      } else {
        s("logior")
      }
    '&' =>
      if intl__ch(p, p.pos) == '&' {
        p.pos += 1
        s("cand")
      } else {
        s("logand")
      }
    '=' =>
      if intl__ch(p, p.pos) == '=' {
        p.pos += 1
        s("cmp=")
      } else {
        raise LispError::SimpleError("Encountered illegal token: =")
      }
    '!' =>
      if intl__ch(p, p.pos) == '=' {
        p.pos += 1
        s("cmp/=")
      } else {
        s("not")
      }
    '<' =>
      match intl__ch(p, p.pos) {
        '=' => {
          p.pos += 1
          s("cmp<=")
        }
        '<' => {
          p.pos += 1
          s("shl")
        }
        _ => s("cmp<")
      }
    '>' =>
      match intl__ch(p, p.pos) {
        '=' => {
          p.pos += 1
          s("cmp>=")
        }
        '>' => {
          p.pos += 1
          s("shr")
        }
        _ => s("cmp>")
      }
    _ =>
      if c >= '0' && c <= '9' {
        let mut n = c.to_int() - '0'.to_int()
        while intl__ch(p, p.pos) >= '0' && intl__ch(p, p.pos) <= '9' {
          n = n * 10 + (intl__ch(p, p.pos).to_int() - '0'.to_int())
          p.pos += 1
        }
        int(n)
      } else {
        raise LispError::SimpleError(
          format_to_string("Encountered illegal token: ~C", [Char(c)]),
        )
      }
  }
}

///|
fn intl__is(tok : Value, names : Array[String]) -> Bool {
  match tok {
    Sym(s) => names.contains(s.name)
    _ => false
  }
}

///|
/// A left-associative binary level of the grammar.
fn intl__binary(
  p : IntlParser,
  tok : Value,
  ops : Array[String],
  sub : (IntlParser, Value) -> (Value, Value) raise,
) -> (Value, Value) raise {
  let (t0, k0) = sub(p, tok)
  let mut tree = t0
  let mut tok = k0
  while intl__is(tok, ops) {
    let (right, next) = sub(p, intl__next(p))
    tree = list3(tok, tree, right)
    tok = next
  }
  (tree, tok)
}

///|
fn intl__conditional(p : IntlParser, tok : Value) -> (Value, Value) raise {
  let (t0, k0) = intl__logical_or(p, tok)
  let mut tree = t0
  let mut tok = k0
  if intl__is(tok, ["if"]) {
    let (right, next) = intl__logical_or(p, intl__next(p))
    if !intl__is(next, ["then"]) {
      raise LispError::SimpleError("Expected : in ?: construct")
    }
    let (else_, next) = intl__conditional(p, intl__next(p))
    tree = list4(tok, list2(sym("zerop"), tree), else_, right)
    tok = next
  }
  (tree, tok)
}

///|
fn intl__logical_or(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["cor"], intl__logical_and)
}

///|
fn intl__logical_and(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["cand"], intl__inclusive_or)
}

///|
fn intl__inclusive_or(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["logior"], intl__exclusive_or)
}

///|
fn intl__exclusive_or(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["logxor"], intl__bitwise_and)
}

///|
fn intl__bitwise_and(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["logand"], intl__equality)
}

///|
fn intl__equality(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["cmp=", "cmp/="], intl__relational)
}

///|
fn intl__relational(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["cmp<", "cmp>", "cmp<=", "cmp>="], intl__shift)
}

///|
fn intl__shift(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["shl", "shr"], intl__additive)
}

///|
fn intl__additive(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["add", "sub"], intl__multiplicative)
}

///|
fn intl__multiplicative(p : IntlParser, tok : Value) -> (Value, Value) raise {
  intl__binary(p, tok, ["mul", "floor", "mod"], intl__unary)
}

///|
fn intl__unary(p : IntlParser, tok : Value) -> (Value, Value) raise {
  if intl__is(tok, ["lpar"]) {
    let (tree, tok) = intl__conditional(p, intl__next(p))
    if !intl__is(tok, ["rpar"]) {
      raise LispError::SimpleError("Expected close-paren.")
    }
    (tree, intl__next(p))
  } else if numberp(tok) || intl__is(tok, ["n"]) {
    (tok, intl__next(p))
  } else if intl__is(tok, ["add"]) {
    intl__unary(p, intl__next(p))
  } else if intl__is(tok, ["sub"]) {
    let (tree, tok) = intl__unary(p, intl__next(p))
    (list2(sym("-"), tree), tok)
  } else if intl__is(tok, ["lognot32"]) {
    let (tree, tok) = intl__unary(p, intl__next(p))
    (list2(sym("lognot32"), tree), tok)
  } else if intl__is(tok, ["not"]) {
    let (tree, tok) = intl__unary(p, intl__next(p))
    (list2(sym("cnot"), tree), tok)
  } else {
    raise LispError::SimpleError(
      format_to_string("Unexpected token: ~S.", [tok]),
    )
  }
}

///|
/// Evaluate a parsed plural expression for N (the compiled lambda of the
/// Lisp version, with 32-bit unsigned arithmetic).
fn intl__eval(tree : Value, n : Int64) -> Int64 raise {
  let mask = 0xFFFFFFFFL
  match tree {
    Fix(v) => v
    Sym(s) if s.name == "n" => n
    Cons(_) => {
      let op = symbol_name(car(tree))
      let a = () => intl__eval(cadr(tree), n)
      let b = () => intl__eval(caddr(tree), n)
      let bool = (x : Bool) => if x { 1L } else { 0L }
      match op {
        "add" => (a() + b()) & mask
        "sub" => (a() - b()) & mask
        "mul" => (a() * b()) & mask
        "shl" => (a() << b().to_int()) & mask
        "shr" => a() >> b().to_int()
        "floor" => {
          let y = b()
          if y == 0L {
            raise division_by_zero()
          }
          a() / y
        }
        "mod" => {
          let y = b()
          if y == 0L {
            raise division_by_zero()
          }
          a() % y
        }
        "logxor" => a() ^ b()
        "logior" => a() | b()
        "logand" => a() & b()
        "cmp=" => bool(a() == b())
        "cmp/=" => bool(a() != b())
        "cmp<" => bool(a() < b())
        "cmp<=" => bool(a() <= b())
        "cmp>" => bool(a() > b())
        "cmp>=" => bool(a() >= b())
        "cand" => if a() == 0L || b() == 0L { 0L } else { 1L }
        "cor" => if a() == 0L && b() == 0L { 0L } else { 1L }
        // (cnot a) = (if a 0 1): A is always a number, hence true
        "cnot" => 0L
        "lognot32" => a().lnot() & mask
        "-" => -a()
        "zerop" => bool(a() == 0L)
        // (if (zerop x) else then)
        "if" =>
          if intl__eval(cadr(tree), n) != 0L {
            intl__eval(caddr(tree), n)
          } else {
            intl__eval(cadddr(tree), n)
          }
        _ => raise LispError::SimpleError("bad plural expression")
      }
    }
    _ => raise LispError::SimpleError("bad plural expression")
  }
}

///|
/// Parse a C plural-forms expression starting at POS and return a Lisp
/// function of N computing it.
fn intl_parse_expr(string_ : Value, pos : Value) -> Value raise {
  let p : IntlParser = { cs: string_chars(lstring(string_)), pos: to_int(pos), }
  let (tree, end) = intl__conditional(p, intl__next(p))
  if !intl__is(end, ["end"]) {
    raise LispError::SimpleError(
      format_to_string("Expecting end of expression.  ~S.", [end]),
    )
  }
  lfunc("plural", args => int64(intl__eval(tree, to_int64(arg(args, 0)))))
}

///|
/// Load the message catalog DOMAIN for LOCALE.  The port cannot read
/// binary .mo files, so no catalog is ever loaded: returns NIL.
fn intl_load_domain(
  domain : Value,
  locale : Value,
  locale_dir? : Value,
) -> Value raise {
  let locale_dir = match locale_dir {
    Some(d) => d
    None => symval(q_ear_locale_directories)
  }
  let file = intl_locate_domain_file(domain, locale, locale_dir)
  if file is Nil {
    return Nil
  }
  // Reading the .mo file (magic number, message tables) needs byte
  // streams with FILE-POSITION, which the runtime does not provide.
  Nil
}

///|
fn intl_find_domain(
  domain : Value,
  locale : Value,
  locale_dir? : Value,
) -> Value raise {
  let found = gethash(domain, symval(q_ear_loaded_domains))
  if found.truthy() && lstring(intl__de_locale(found)) == lstring(locale) {
    found
  } else {
    intl_load_domain(domain, locale, locale_dir?)
  }
}

///|
fn intl__latin1_p(encoding : Value) -> Bool {
  match encoding {
    Sym(s) =>
      s.name == ":iso-8859-1" || s.name == ":latin-1" || s.name == ":latin1"
    _ => false
  }
}

///|
fn intl_string_to_octets(string_ : Value, encoding : Value) -> Value raise {
  let out : Array[Value] = []
  for c in string_chars(lstring(string_)) {
    let code = c.to_int()
    if intl__latin1_p(encoding) {
      out.push(int(if code < 256 { code } else { '?'.to_int() }))
    } else if code < 0x80 {
      out.push(int(code))
    } else if code < 0x800 {
      out.push(int(0xC0 | (code >> 6)))
      out.push(int(0x80 | (code & 0x3F)))
    } else if code < 0x10000 {
      out.push(int(0xE0 | (code >> 12)))
      out.push(int(0x80 | ((code >> 6) & 0x3F)))
      out.push(int(0x80 | (code & 0x3F)))
    } else {
      out.push(int(0xF0 | (code >> 18)))
      out.push(int(0x80 | ((code >> 12) & 0x3F)))
      out.push(int(0x80 | ((code >> 6) & 0x3F)))
      out.push(int(0x80 | (code & 0x3F)))
    }
  }
  vector(out)
}

///|
fn intl_octets_to_string(octets : Value, encoding : Value) -> Value raise {
  let bytes = as_array(octets).data.map(b => to_int(b))
  let sb = StringBuilder::new()
  if intl__latin1_p(encoding) {
    for b in bytes {
      sb.write_char(code_char(b))
    }
  } else {
    let mut i = 0
    while i < bytes.length() {
      let b = bytes[i]
      let (code, len) = if b < 0x80 {
        (b, 1)
      } else if b < 0xE0 && i + 1 < bytes.length() {
        (((b & 0x1F) << 6) | (bytes[i + 1] & 0x3F), 2)
      } else if b < 0xF0 && i + 2 < bytes.length() {
        (
          ((b & 0x0F) << 12) |
          ((bytes[i + 1] & 0x3F) << 6) |
          (bytes[i + 2] & 0x3F),
          3,
        )
      } else if i + 3 < bytes.length() {
        (
          ((b & 0x07) << 18) |
          ((bytes[i + 1] & 0x3F) << 12) |
          ((bytes[i + 2] & 0x3F) << 6) |
          (bytes[i + 3] & 0x3F),
          4,
        )
      } else {
        (0xFFFD, 1)
      }
      sb.write_char(code_char(code))
      i += len
    }
  }
  Str(sb.to_string())
}

///|
fn intl_octets_eq(
  a : Value,
  b : Value,
  start1~ : Value = Fix(0L),
  end1? : Value,
  start2~ : Value = Fix(0L),
  end2? : Value,
) -> Value raise {
  let av = as_array(a).data
  let bv = as_array(b).data
  let mut s1 = to_int(start1)
  let mut s2 = to_int(start2)
  let e1 = match end1 {
    Some(e) => to_int(e)
    None => av.length()
  }
  let e2 = match end2 {
    Some(e) => to_int(e)
    None => bv.length()
  }
  if s1 < e1 && s2 < e2 {
    while true {
      if !num_eq(av[s1], bv[s2]) {
        return Nil
      }
      s1 += 1
      s2 += 1
      if s1 == e1 || s2 == e2 {
        return t
      }
    }
  }
  Nil
}

///|
/// Search the catalog file of DOMAIN for OCTETS among the candidate
/// entries POS.  Needs byte-level file access; since no catalog is ever
/// loaded in the port (see LOAD-DOMAIN), nothing is found.
fn intl_search_domain(
  octets : Value,
  domain : Value,
  pos : Value,
) -> (Value, Value) raise {
  ignore(octets)
  ignore(domain)
  ignore(pos)
  (Nil, Nil)
}

///|
fn intl_domain_lookup(string_ : Value, domain : Value) -> Value raise {
  if intl__de_encoding(domain) is Nil {
    return string_
  }
  let hash = intl__de_hash(domain)
  let v = gethash(string_, hash)
  if v.truthy() {
    return v
  }
  let octets = intl_string_to_octets(string_, intl__de_encoding(domain))
  let length = int(as_array(octets).data.length())
  let pos = gethash(length, hash)
  let (tmp, entry) = intl_search_domain(octets, domain, pos)
  if tmp.truthy() {
    let temp = remove(entry, pos)
    if temp.truthy() {
      sethash(length, hash, temp) |> ignore
    } else {
      remhash(length, hash) |> ignore
    }
    sethash(
      copy_seq(string_),
      hash,
      intl_octets_to_string(tmp, intl__de_encoding(domain)),
    )
  } else {
    Nil
  }
}

///|
fn intl_domain_lookup_plural(
  singular : Value,
  plural : Value,
  domain : Value,
) -> Value raise {
  if intl__de_encoding(domain) is Nil {
    return Nil
  }
  let hash = intl__de_hash(domain)
  let v = gethash(cons(singular, plural), hash)
  if v.truthy() {
    return v
  }
  let enc = intl__de_encoding(domain)
  let a = as_array(intl_string_to_octets(singular, enc)).data
  let b = as_array(intl_string_to_octets(plural, enc)).data
  let c = a.copy()
  c.push(Fix(0L))
  for x in b {
    c.push(x)
  }
  let octets = vector(c)
  let length = int(c.length())
  let pos = gethash(length, hash)
  let (tmp, entry) = intl_search_domain(octets, domain, pos)
  if tmp is Nil {
    return Nil
  }
  // split TMP at the NUL bytes
  let parts = Collector::new()
  let bytes = as_array(tmp).data
  let mut i = 0
  while true {
    let mut j = i
    while j < bytes.length() && !num_eq(bytes[j], Fix(0L)) {
      j += 1
    }
    parts.add(intl_octets_to_string(vector(bytes[i:j].to_array()), enc))
    if j >= bytes.length() {
      break
    }
    i = j + 1
  }
  let result = sethash(
    cons(copy_seq(singular), copy_seq(plural)),
    hash,
    parts.result(),
  )
  let temp = remove(entry, pos)
  if temp.truthy() {
    sethash(length, hash, temp) |> ignore
  } else {
    remhash(length, hash) |> ignore
  }
  if intl__de_plurals(domain) is Nil {
    struct_set(domain, 3, intl_parse_plurals(domain).0) |> ignore
  }
  result
}

///|
fn intl_getenv(var_ : Value) -> Value raise {
  match getenv(lstring(var_)) {
    Some("") | None => Nil
    Some(v) => Str(v)
  }
}

///|
fn intl_setlocale(locale~ : Value = Nil) -> Value raise {
  let mut v = locale
  for name in ["LANGUAGE", "LC_ALL", "LC_MESSAGES", "LANG"] {
    if v.truthy() {
      break
    }
    v = intl_getenv(Str(name))
  }
  if v is Nil {
    v = symval(q_ear_locale)
  }
  set(q_ear_locale, v)
}

///|
/// `(textdomain domain)`: set the message-lookup domain.
fn intl_textdomain(domain : Value) -> Value raise {
  set(q_ear_default_domain, domain)
}

///|
/// Look up STRING in the current message domain and return its
/// translation.
fn intl_gettext(string_ : Value) -> Value raise {
  intl_dgettext(symval(q_ear_default_domain), string_)
}

///|
/// Look up the singular or plural form of a message in the current domain.
fn intl_ngettext(singular : Value, plural : Value, n : Value) -> Value raise {
  intl_dngettext(symval(q_ear_default_domain), singular, plural, n)
}

///|
/// Look up STRING in the specified message domain and return its
/// translation.
fn intl_dgettext(domain : Value, string_ : Value) -> Value raise {
  let domain = if domain.truthy() {
    intl_find_domain(domain, symval(q_ear_locale))
  } else {
    Nil
  }
  if domain.truthy() {
    let r = intl_domain_lookup(string_, domain)
    if r.truthy() {
      return r
    }
  }
  string_
}

///|
/// Look up the singular or plural form of a message in the specified
/// domain.
fn intl_dngettext(
  domain : Value,
  singular : Value,
  plural : Value,
  n : Value,
) -> Value raise {
  let domain = if domain.truthy() {
    intl_find_domain(domain, symval(q_ear_locale))
  } else {
    Nil
  }
  let list_ = if domain.truthy() {
    intl_domain_lookup_plural(singular, plural, domain)
  } else {
    Nil
  }
  if list_.truthy() {
    nth(to_int(funcall(intl__de_plurals(domain), [n])), list_)
  } else if num_eq(n, Fix(1L)) {
    singular
  } else {
    plural
  }
}

///|
fn intl__translations() -> Value {
  if !boundp(q_ear_translations) {
    set(q_ear_translations, make_hash_table(kind=Equal)) |> ignore
  }
  symval(q_ear_translations)
}

///|
fn intl_note_translatable(
  domain : Value,
  string_ : Value,
  plural~ : Value = Nil,
) -> Value raise {
  if domain.truthy() {
    let translations = intl__translations()
    let hash = {
      let h = gethash(domain, translations)
      if h.truthy() {
        h
      } else {
        sethash(domain, translations, make_hash_table(kind=Equal))
      }
    }
    let key = if plural.truthy() { cons(string_, plural) } else { string_ }
    let val = {
      let v = gethash(key, hash)
      if v.truthy() {
        v
      } else {
        cons(Nil, Nil)
      }
    }
    let comment = symval(q_ear_translator_comment)
    if member_equal(comment, car(val)) is Nil {
      rplaca(val, cons(comment, car(val))) |> ignore
    }
    // *compile-file-pathname* is NIL at run time
    if member_equal(Nil, cdr(val)) is Nil {
      rplacd(val, cons(Nil, cdr(val))) |> ignore
    }
    sethash(key, hash, val) |> ignore
  }
  set(q_ear_translator_comment, Nil)
}

///|
/// Read a string literal (the opening quote not yet consumed).
fn intl__read_string(stream : Value) -> Value raise {
  match read_char(stream~, eof_value=Nil) {
    Char('"') => ()
    _ => raise LispError::SimpleError("expected a string")
  }
  let sb = StringBuilder::new()
  while true {
    match read_char(stream~, eof_value=Nil) {
      Char('"') => break
      Char('\\') =>
        match read_char(stream~, eof_value=Nil) {
          Char(c) => sb.write_char(c)
          _ => raise LispError::SimpleError("end of file in string")
        }
      Char(c) => sb.write_char(c)
      _ => raise LispError::SimpleError("end of file in string")
    }
  }
  Str(sb.to_string())
}

///|
/// The reader macro for `_"..."` (-> `(intl:gettext "...")`) and `_N"..."`
/// (a noted translatable string).
fn intl_read_translatable_string(stream : Value, char_ : Value) -> Value raise {
  ignore(char_)
  match peek_char(stream~, eof_value=Nil) {
    Char('"') => {
      let string_ = intl__read_string(stream)
      list2(sym("intl::gettext"), string_)
    }
    Char('N') => {
      read_char(stream~) |> ignore
      let string_ = intl__read_string(stream)
      intl_note_translatable(symval(q_ear_default_domain), string_) |> ignore
      string_
    }
    Char('@') =>
      raise LispError::SimpleError("_@ is a reserved reader macro prefix.")
    _ => sym("_")
  }
}

///|
/// The ; reader macro noting "TRANSLATORS: " comments.
fn intl_read_comment(stream : Value, char_ : Value) -> Value raise {
  ignore(char_)
  let marker = string_chars("TRANSLATORS: ")
  let mut state = 0
  let mut index = 0
  let mut text : StringBuilder? = None
  while true {
    let c = match read_char(stream~, eof_value=Nil) {
      Char(c) => c
      _ => break
    }
    if c == '\n' {
      break
    }
    if state == 0 && c == ' ' {
      state = 1
    } else if state == 0 && c == 'T' {
      state = 1
      index = 1
    } else if state == 0 && c != ';' {
      state = 2
    } else if state == 1 && index == 0 && c == ' ' {
      // ignore
      ()
    } else if state == 1 {
      if c == marker[index] {
        index += 1
        if index == 13 {
          state = 3
        }
      } else {
        state = 2
      }
    } else if state == 3 {
      if text is None {
        text = Some(StringBuilder::new())
      }
      text.unwrap().write_char(c)
    }
  }
  match text {
    Some(sb) => set(q_ear_translator_comment, Str(sb.to_string())) |> ignore
    None => ()
  }
  Nil
}

///|
/// The #| reader macro noting "TRANSLATORS: " comments.
fn intl_read_nested_comment(
  stream : Value,
  subchar : Value,
  arg : Value,
) -> Value raise {
  ignore(subchar)
  ignore(arg)
  let marker = string_chars("TRANSLATORS: ")
  let rc = () => {
    match read_char(stream~, eof_value=Nil) {
      Char(c) => c
      _ => raise LispError::SimpleError("end of file in comment")
    }
  }
  let mut level = 1
  let mut state = 0
  let mut index = 0
  let mut text : StringBuilder? = None
  let mut prev = rc()
  let mut char_ = rc()
  while true {
    if prev == '|' && char_ == '#' {
      level -= 1
      if level == 0 {
        match text {
          Some(sb) =>
            set(
              q_ear_translator_comment,
              Str(string_right_trim(" \n", sb.to_string())),
            )
            |> ignore
          None => ()
        }
        break
      }
    } else if prev == '#' && char_ == '|' {
      state = 2
      level += 1
    } else if state == 0 && prev == ' ' {
      state = 1
    } else if state == 0 && prev == 'T' {
      state = 1
      index = 1
    } else if state == 0 {
      state = 2
    } else if state == 1 && index == 0 && prev == ' ' {
      // ignore
      ()
    } else if state == 1 {
      if prev == marker[index] {
        index += 1
        if index == 13 {
          state = 3
        }
      } else {
        state = 2
      }
    } else if state == 3 {
      if text is None {
        text = Some(StringBuilder::new())
      }
      text.unwrap().write_char(prev)
    }
    prev = char_
    char_ = rc()
  }
  Nil
}

///|
/// Installs the reader macros in CL; the port has no readtable.
fn intl_install() -> Value raise {
  t
}

///|
/// Write STRING[start:end] escaping " and \.
fn intl__wstr(
  out : StringBuilder,
  cs : Array[Char],
  start : Int32,
  end : Int32,
) -> Unit {
  for i in start..<end {
    if cs[i] == '"' || cs[i] == '\\' {
      out.write_char('\\')
    }
    out.write_char(cs[i])
  }
}

///|
/// Last position in [a, b) of a character satisfying P, or -1.
fn intl__rpos(
  cs : Array[Char],
  a : Int32,
  b : Int32,
  p : (Char) -> Bool,
) -> Int32 {
  let mut i = (if b < cs.length() { b } else { cs.length() }) - 1
  while i >= a {
    if p(cs[i]) {
      return i
    }
    i -= 1
  }
  -1
}

///|
/// Print STRING as a (possibly multi-line) .pot string starting at column
/// COL.
fn intl__str(
  out : StringBuilder,
  cs : Array[Char],
  col : Int32,
  start : Int32,
) -> Unit {
  let len = cs.length()
  if col > 0 && len > 76 - col {
    out.write_string("\"\"\n")
  }
  let mut nl = -1
  for i in start..<len {
    if cs[i] == '\n' {
      nl = i
      break
    }
  }
  if nl >= 0 && nl - start < 76 {
    out.write_char('"')
    intl__wstr(out, cs, start, nl)
    out.write_string("\\n\"\n")
    intl__str(out, cs, 0, nl + 1)
  } else if len - start < 76 {
    out.write_char('"')
    intl__wstr(out, cs, start, len)
    out.write_char('"')
  } else {
    let a = start + 1
    let b = start + 76
    let b1 = intl__rpos(cs, a, b, c => c == ' ')
    let b2 = intl__rpos(cs, a, b, c => ";:,?!)]}".contains_char(c))
    let b3 = intl__rpos(cs, a, b, c => "\"'-".contains_char(c))
    let b4 = intl__rpos(cs, a, b, c => c >= '0' && c <= '9')
    let b5 = intl__rpos(cs, a, b, c => alpha_char_p(c))
    let goodness = (bi : Int32, w : Double) => {
      if bi >= 0 {
        (b - bi).to_double() * (b - bi).to_double() * w
      } else {
        10000.0
      }
    }
    let g1 = goodness(b1, 0.03)
    let g2 = goodness(b2, 0.20)
    let g3 = goodness(b3, 0.97)
    let g4 = goodness(b4, 1.3)
    let g5 = goodness(b5, 2.0)
    let g = [g1, g2, g3, g4, g5].fold(init=10000.0, (x, y) => {
      if y < x {
        y
      } else {
        x
      }
    })
    let end = 1 +
      (if g > 750.0 {
        b
      } else if g == g1 {
        b1
      } else if g == g2 {
        b2
      } else if g == g3 {
        b3
      } else if g == g4 {
        b4
      } else {
        b5
      })
    out.write_char('"')
    intl__wstr(out, cs, start, end)
    out.write_char('"')
    out.write_char('\n')
    intl__str(out, cs, 0, end)
  }
}

///|
/// Write the noted translatable strings as .pot files to standard output.
fn intl_dump_pot_files(copyright~ : Value = Nil) -> Value raise {
  let out = StringBuilder::new()
  let fresh = () => {
    let s = out.to_string()
    if s.length() > 0 && !s.has_suffix("\n") {
      out.write_char('\n')
    }
  }
  maphash(
    (domain, hash) => {
      fresh()
      out.write_string("#@ " + princ_to_string(domain) + "\n\n")
      fresh()
      out.write_string("# SOME DESCRIPTIVE TITLE\n")
      if copyright.truthy() {
        fresh()
        out.write_string(
          "# Copyright (C) YEAR " + princ_to_string(copyright) + "\n",
        )
      }
      fresh()
      out.write_string("# FIRST AUTHOR <EMAIL@ADDRESS>, YEAR\n")
      fresh()
      out.write_string("#\n#, fuzzy\nmsgid \"\"\nmsgstr \"\"\n")
      for
        line in [
          "\"Project-Id-Version: PACKAGE VERSION\\n\"", "\"Report-Msgid-Bugs-To: \\n\"",
          "\"PO-Revision-Date: YEAR-MO-DA HO:MI +ZONE\\n\"", "\"Last-Translator: FULL NAME <EMAIL@ADDRESS>\\n\"",
          "\"Language-Team: LANGUAGE <LL@li.org>\\n\"", "\"MIME-Version: 1.0\\n\"",
          "\"Content-Type: text/plain; charset=UTF-8\\n\"",
        ] {
        fresh()
        out.write_string(line + "\n")
      }
      fresh()
      out.write_string("\"Content-Transfer-Encoding: 8bit\\n\"\n\n")
      maphash(
        (key, data) => {
          let comments = remove(Nil, car(data))
          if comments.truthy() {
            for c in comments.iter() {
              fresh()
              out.write_string("#. " + princ_to_string(c))
            }
            out.write_char('\n')
          }
          let files = remove(Nil, cdr(data))
          if files.truthy() {
            fresh()
            out.write_string("#: ")
            let mut first = true
            for f in files.iter() {
              if !first {
                out.write_char(' ')
              }
              first = false
              out.write_string(princ_to_string(f))
            }
            out.write_char('\n')
          }
          if consp(key) {
            fresh()
            out.write_string("msgid ")
            intl__str(out, string_chars(lstring(car(key))), 6, 0)
            fresh()
            out.write_string("msgid_plural ")
            intl__str(out, string_chars(lstring(cdr(key))), 13, 0)
            fresh()
            out.write_string("msgstr[0] \"\"\n\n")
          } else {
            fresh()
            out.write_string("msgid ")
            intl__str(out, string_chars(lstring(key)), 6, 0)
            fresh()
            out.write_string("msgstr \"\"\n\n")
          }
        },
        hash,
      )
    },
    intl__translations(),
  )
  write_string(out.to_string())
  Nil
}

///|
fn init_intl() -> Unit raise {
  defvar_init(q_ear_loaded_domains, make_hash_table(kind=Equal))
  defvar_init(q_ear_locale_aliases, make_hash_table(kind=Equal))
  defvar_init(q_ear_translations, make_hash_table(kind=Equal))
}
