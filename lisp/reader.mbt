// The Lisp reader, using the port's symbol naming: unescaped tokens are
// lower-cased; |escaped| names are case-inverted when they are of uniform
// case (mirroring CL Maxima's print-case inversion).
//
// `lread`/`lread_all` read literal data (always in base 10, as the porter
// wrote it). The source reader used by the Lisp evaluator (`lread_stream`,
// `lread_source_all`) also honours *READ-BASE*, the current package of
// IN-PACKAGE, *FEATURES* for #+/#-, and the hooks for #. and #$.
//
// Backquote reads as (si::quasiquote x), with (si::unquote x) and
// (si::unquote-splicing x) for , and ,@ (the evaluator expands them).

///|
priv struct LReader {
  s : LStream
  base_sensitive : Bool
  labels : Map[Int, Value]
}

///|
/// `#.form`: evaluate a form at read time (installed by the evaluator).
pub let read_eval_hook : Ref[(Value) -> Value raise] = Ref(fn(x) raise {
  raise SimpleError("read: #. is not supported here: " + x.to_string())
})

///|
/// `#$expr$`: parse Maxima syntax at read time (installed by the evaluator).
pub let read_maxima_hook : Ref[(String) -> Value raise] = Ref(fn(s) raise {
  raise SimpleError("read: #$ is not supported here: " + s)
})

///|
/// The current package (as set by IN-PACKAGE), lower case.
pub let reader_package : Ref[String] = Ref("maxima")

///|
/// The symbols the reader produces for backquote syntax.
pub let qq_quasiquote : Value = sym("si::quasiquote")

///|
pub let qq_unquote : Value = sym("si::unquote")

///|
pub let qq_unquote_splicing : Value = sym("si::unquote-splicing")

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
  let r = { s: out_or_in_stream(s), base_sensitive: false, labels: {} }
  match r.read_top() {
    Some(v) => v
    None => raise SimpleError("lread: unexpected end of input")
  }
}

///|
/// Read all data from a string.
pub fn lread_all(s : String) -> Array[Value] raise LispError {
  let r = { s: out_or_in_stream(s), base_sensitive: false, labels: {} }
  let out = []
  while r.read_top() is Some(v) {
    out.push(v)
  }
  out
}

///|
/// Read all forms of Lisp source text (honouring *read-base*, packages,
/// features). `each` is called on every form as soon as it is read, so that
/// IN-PACKAGE or a change of *READ-BASE* affects the following forms.
pub fn lread_source_all(
  s : String,
  each : (Value) -> Unit raise,
) -> Unit raise {
  let r = { s: out_or_in_stream(s), base_sensitive: true, labels: {} }
  while true {
    let v = r.read_top() catch {
      LispError::SimpleError(msg) =>
        raise SimpleError(msg + " (line \{r.s.line})")
      e => raise e
    }
    match v {
      Some(x) => each(x)
      None => break
    }
  }
}

///|
/// `(read stream eof-error-p eof-value)`: read one datum from an input
/// stream (with *read-base* etc.). At end of file returns `eof_value`, or
/// raises an end-of-file error when `eof_error` is true.
pub fn lread_stream(
  stream : Value,
  eof_error? : Bool = true,
  eof_value? : Value = Nil,
) -> Value raise LispError {
  let st = match stream {
    Stream(st) => st
    _ => raise SimpleError("read: not a stream")
  }
  let r = { s: st, base_sensitive: true, labels: {} }
  match r.read_top() {
    Some(v) => {
      // READ consumes the whitespace character that ends the datum
      match st.peek_char() {
        Some(c) if is_ws(c) => st.read_char() |> ignore
        _ => ()
      }
      v
    }
    None =>
      if eof_error {
        raise Condition(intern("end-of-file"), "end of file on stream", stream)
      } else {
        eof_value
      }
  }
}

///|
/// `(read-from-string s eof-error-p eof-value :start n)`: the datum and the
/// index (in characters) of the first character not read.
pub fn lread_from_string(
  s : String,
  start? : Int = 0,
  eof_error? : Bool = true,
  eof_value? : Value = Nil,
) -> (Value, Int) raise LispError {
  let chars = string_chars(s)
  let st = out_or_in_stream(chars_to_string(chars[start:].to_array()))
  let v = lread_stream(Stream(st), eof_error~, eof_value~)
  // the number of characters consumed, minus those pushed back
  let consumed_units = st.pos
  let prefix = st.input.substring(end=consumed_units)
  let consumed = string_chars(prefix).length() - st.unread.length()
  (v, start + consumed)
}

///|
fn out_or_in_stream(s : String) -> LStream {
  match make_string_input_stream(s) {
    Stream(st) => st
    _ => panic()
  }
}

///|
fn LReader::peek(self : LReader) -> Char? {
  self.s.peek_char()
}

///|
fn LReader::next(self : LReader) -> Char? {
  self.s.read_char()
}

///|
fn LReader::next_or_eof(self : LReader) -> Char raise LispError {
  match self.s.read_char() {
    Some(c) => c
    None => raise SimpleError("read: end of file")
  }
}

///|
fn is_ws(c : Char) -> Bool {
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\u{0C}'
}

///|
fn is_terminating(c : Char) -> Bool {
  is_ws(c) || "()'\";`,".contains_char(c)
}

///|
fn LReader::skip_ws(self : LReader) -> Unit {
  while self.peek() is Some(c) {
    if is_ws(c) {
      self.next() |> ignore
    } else if c == ';' {
      while self.next() is Some(d) {
        if d == '\n' {
          break
        }
      }
    } else {
      break
    }
  }
}

///|
/// Read the next datum at top level; None at end of input.
fn LReader::read_top(self : LReader) -> Value? raise LispError {
  while true {
    self.skip_ws()
    if self.peek() is None {
      return None
    }
    match self.read_inner() {
      Some(v) => return Some(v)
      None => continue
    }
  }
  None
}

///|
/// Read a datum that must be present.
fn LReader::read(self : LReader) -> Value raise LispError {
  while true {
    self.skip_ws()
    if self.peek() is None {
      raise SimpleError("read: unexpected end of file")
    }
    match self.read_inner() {
      Some(v) => return v
      None => continue
    }
  }
  Nil
}

///|
/// Read one datum; None when the syntax read produced no value (a #|...|#
/// comment, a #+/#- that skipped its form).
fn LReader::read_inner(self : LReader) -> Value? raise LispError {
  let c = self.next_or_eof()
  match c {
    '(' => Some(self.read_list(')'))
    ')' => raise SimpleError("read: unmatched close parenthesis")
    '\'' => Some(list2(sym("quote"), self.read()))
    '`' => Some(list2(qq_quasiquote, self.read()))
    ',' =>
      match self.peek() {
        Some('@') | Some('.') => {
          self.next() |> ignore
          Some(list2(qq_unquote_splicing, self.read()))
        }
        _ => Some(list2(qq_unquote, self.read()))
      }
    '"' => {
      let sb = StringBuilder::new()
      while true {
        let d = self.next_or_eof()
        if d == '"' {
          break
        }
        if d == '\\' {
          sb.write_char(self.next_or_eof())
        } else {
          sb.write_char(d)
        }
      }
      Some(Str(sb.to_string()))
    }
    '#' => self.read_dispatch()
    _ => {
      self.s.unread_char(c)
      Some(self.read_token_value())
    }
  }
}

///|
fn LReader::read_list(self : LReader, close : Char) -> Value raise LispError {
  let items = []
  let mut tail = Nil
  while true {
    self.skip_ws()
    match self.peek() {
      None => raise SimpleError("read: unterminated list")
      Some(d) if d == close => {
        self.next() |> ignore
        break
      }
      Some('.') => {
        // A lone dot: dotted pair.
        self.next() |> ignore
        match self.peek() {
          Some(e) if is_terminating(e) && e != ')' => {
            tail = self.read()
            self.skip_ws()
            while self.peek() is Some(f) && f != close {
              // tolerate trailing comments handled by skip_ws
              self.read_inner() |> ignore
              self.skip_ws()
            }
            self.next() |> ignore
            break
          }
          _ => {
            self.s.unread_char('.')
            match self.read_inner() {
              Some(v) => items.push(v)
              None => ()
            }
          }
        }
      }
      Some(_) =>
        match self.read_inner() {
          Some(v) => items.push(v)
          None => ()
        }
    }
  }
  let mut r = tail
  for k = items.length() - 1; k >= 0; k = k - 1 {
    r = cons(items[k], r)
  }
  r
}

///|
/// The current *READ-BASE* (10 for literal reading).
fn LReader::base(self : LReader) -> Int {
  if !self.base_sensitive {
    return 10
  }
  match intern("*read-base*") {
    { bound: true, value: Fix(n), .. } if n >= 2L && n <= 36L => n.to_int()
    _ => 10
  }
}

///|
/// Read the rest of a token (after its first character has been pushed
/// back). Returns the CL-case name, whether any character was escaped, and
/// the package prefix (CL case) with the internal flag.
fn LReader::token(
  self : LReader,
) -> (String, Bool, String?, Bool) raise LispError {
  let sb = StringBuilder::new()
  let mut escaped = false
  let mut pkg : String? = None
  let mut internal = false
  while self.peek() is Some(c) {
    if is_terminating(c) {
      break
    }
    self.next() |> ignore
    if c == '|' {
      escaped = true
      while true {
        let d = self.next_or_eof()
        if d == '|' {
          break
        }
        if d == '\\' {
          sb.write_char(self.next_or_eof())
        } else {
          sb.write_char(d)
        }
      }
    } else if c == '\\' {
      escaped = true
      sb.write_char(self.next_or_eof())
    } else if c == ':' && pkg is None {
      pkg = Some(sb.to_string())
      sb.reset()
      if self.peek() is Some(':') {
        self.next() |> ignore
        internal = true
      }
    } else {
      sb.write_char(char_upcase(c))
    }
  }
  (sb.to_string(), escaped, pkg, internal)
}

///|
/// Packages whose symbols are the port's plain symbols.
fn plain_package(p : String) -> Bool {
  match p {
    "" | "maxima" | "cl" | "common-lisp" | "cl-user" | "common-lisp-user" | "user" =>
      true
    _ => false
  }
}

///|
/// The symbol for a name read in package `p`: the port names symbols of
/// other packages `p::name` when the port defines such a symbol (see
/// tools/gen.py:mangle); otherwise the plain name.
fn package_symbol(p : String, name : String) -> Value {
  if p == "cl" || p == "common-lisp" {
    // a CL symbol shadowed by Maxima (e.g. CL:SIGNUM), when the port
    // defines it as `cl::name`
    match find_symbol("cl::" + name) {
      Sym(_) as s => return s
      _ => ()
    }
  }
  if plain_package(p) {
    return sym(name)
  }
  match find_symbol(p + "::" + name) {
    Sym(_) as s => s
    _ => sym(name)
  }
}

///|
fn LReader::read_token_value(self : LReader) -> Value raise LispError {
  let (clname, escaped, pkg, _) = self.token()
  let name = invert_case(clname)
  match pkg {
    Some(p) => {
      let pn = string_downcase(p)
      if pn == "" || pn == "keyword" {
        return sym(":" + name)
      }
      if name == "nil" && plain_package(pn) {
        return Nil
      }
      return package_symbol(pn, name)
    }
    None => ()
  }
  if !escaped {
    if name == "." {
      raise SimpleError("read: dot context error")
    }
    match self.parse_number(clname) {
      Some(n) => return n
      None => ()
    }
  }
  if name == "nil" {
    return Nil
  }
  if self.base_sensitive {
    package_symbol(reader_package.val, name)
  } else {
    sym(name)
  }
}

///|
fn LReader::parse_number(self : LReader, tok : String) -> Value? {
  let base = self.base()
  if base == 10 {
    return parse_number_token(tok)
  }
  // a trailing decimal point forces a decimal integer
  if tok.has_suffix(".") && tok.length() > 1 {
    match parse_integer(tok.substring(end=tok.length() - 1)) {
      Some(n) => return Some(n)
      None => ()
    }
  }
  match parse_integer(tok, radix=base) {
    Some(n) => return Some(n)
    None => ()
  }
  match tok.find("/") {
    Some(k) =>
      match
        (
          parse_integer(tok.substring(end=k), radix=base),
          parse_integer(tok.substring(start=k + 1), radix=base),
        ) {
        (Some(x), Some(y)) =>
          return (fn() -> Value? raise {
            Some(make_ratio(to_big(x), to_big(y)))
          })() catch {
            _ => None
          }
        _ => ()
      }
    None => ()
  }
  match parse_number_token(tok) {
    Some(Flo(_) as f) => Some(f)
    _ => None
  }
}

///|
/// Character names accepted after #\ (lower case).
fn char_by_name(name : String) -> Char? {
  match string_downcase(name) {
    "space" => Some(' ')
    "newline" | "linefeed" | "nl" => Some('\n')
    "tab" => Some('\t')
    "return" => Some('\r')
    "page" => Some('\u{0C}')
    "backspace" => Some('\u{08}')
    "rubout" | "delete" | "del" => Some('\u{7F}')
    "nul" | "null" => Some('\u{00}')
    "escape" | "esc" | "altmode" => Some('\u{1B}')
    "bell" | "bel" => Some('\u{07}')
    _ => {
      let n = string_downcase(name)
      let hex = if n.has_prefix("u+") {
        n.substring(start=2)
      } else if n.has_prefix("u") {
        n.substring(start=1)
      } else {
        return None
      }
      match parse_integer(hex, radix=16) {
        Some(Fix(k)) => Some(code_char(k.to_int()))
        _ => None
      }
    }
  }
}

///|
/// Evaluate a feature expression against *FEATURES*.
fn feature_true(x : Value) -> Bool {
  match x {
    Sym(s) => {
      let name = if s.name.has_prefix(":") { s.name } else { ":" + s.name }
      let feats = intern("*features*")
      if !feats.bound {
        return false
      }
      let mut l = feats.value
      while l is Cons(c) {
        if c.car is Sym(f) && (f.name == name || ":" + f.name == name) {
          return true
        }
        l = c.cdr
      }
      false
    }
    Cons({ car: Sym(op), cdr: args }) => {
      let o = if op.name.has_prefix(":") {
        op.name.substring(start=1)
      } else {
        op.name
      }
      match o {
        "or" => {
          for a in args.iter() {
            if feature_true(a) {
              return true
            }
          }
          false
        }
        "and" => {
          for a in args.iter() {
            if !feature_true(a) {
              return false
            }
          }
          true
        }
        "not" => !feature_true(car(args))
        _ => false
      }
    }
    _ => false
  }
}

///|
/// Read a feature expression: symbols are read in the keyword package.
fn LReader::read_feature(self : LReader) -> Value raise LispError {
  let saved = reader_package.val
  reader_package.val = "maxima"
  defer {
    reader_package.val = saved
  }
  let x = self.read()
  fn kwify(v : Value) -> Value {
    match v {
      Sym(s) if !s.name.has_prefix(":") => sym(":" + s.name)
      Cons(_) => {
        let c = Collector::new()
        for e in v.iter() {
          c.add(kwify(e))
        }
        c.result()
      }
      _ => v
    }
  }

  kwify(x)
}

///|
fn LReader::read_dispatch(self : LReader) -> Value? raise LispError {
  // optional decimal argument
  let mut arg = -1
  let mut d = self.next_or_eof()
  while d >= '0' && d <= '9' {
    arg = (if arg < 0 { 0 } else { arg }) * 10 + (d.to_int() - '0'.to_int())
    d = self.next_or_eof()
  }
  match d {
    '\\' => {
      // a character: one char, or a name
      let first = self.next_or_eof()
      let sb = StringBuilder::new()
      sb.write_char(first)
      while self.peek() is Some(c) && !is_terminating(c) {
        sb.write_char(c)
        self.next() |> ignore
      }
      let name = sb.to_string()
      if string_length(name) == 1 {
        Some(Char(first))
      } else {
        match char_by_name(name) {
          Some(ch) => Some(Char(ch))
          None => raise SimpleError("read: unknown character name #\\" + name)
        }
      }
    }
    '\'' => Some(list2(sym("function"), self.read()))
    '(' => Some(list_to_vector(self.read_list(')')))
    ':' => {
      let (n, _, _, _) = self.token()
      Some(make_symbol(invert_case(n)))
    }
    '|' => {
      // nested block comment
      let mut depth = 1
      let mut prev = ' '
      while depth > 0 {
        let c = self.next_or_eof()
        if prev == '|' && c == '#' {
          depth -= 1
          prev = ' '
        } else if prev == '#' && c == '|' {
          depth += 1
          prev = ' '
        } else {
          prev = c
        }
      }
      None
    }
    '+' | '-' => {
      let feat = self.read_feature()
      let ok = feature_true(feat)
      let want = d == '+'
      if ok == want {
        Some(self.read())
      } else {
        // skip the next form, without interning or evaluating anything
        let saved = read_eval_hook.val
        let saved_m = read_maxima_hook.val
        read_eval_hook.val = fn(_x) { Nil }
        read_maxima_hook.val = fn(_s) { Nil }
        defer {
          read_eval_hook.val = saved
          read_maxima_hook.val = saved_m
        }
        self.read() |> ignore
        None
      }
    }
    '.' => {
      let form = self.read()
      Some((read_eval_hook.val)(form)) catch {
        LispError::SimpleError(m) => raise SimpleError(m)
        LispError::Condition(s, m, p) => raise Condition(s, m, p)
        LispError::Throw(a, b) => raise Throw(a, b)
        LispError::ReturnFrom(a, b) => raise ReturnFrom(a, b)
        LispError::Go(a) => raise Go(a)
        e => raise SimpleError(e.to_string())
      }
    }
    '$' => {
      // Maxima syntax up to the terminating $ (nparse.lisp's $-READ-AUX):
      // #$expr$ reads as (meval* 'expr), #$$expr$ as 'expr.
      self.skip_ws()
      let mut meval_flag = true
      if self.peek() is Some('$') {
        self.next() |> ignore
        meval_flag = false
      }
      let sb = StringBuilder::new()
      while true {
        let c = self.next_or_eof()
        sb.write_char(c)
        if c == '$' {
          break
        }
      }
      let expr = (read_maxima_hook.val)(sb.to_string()) catch {
        LispError::SimpleError(m) => raise SimpleError(m)
        LispError::Condition(s, m, p) => raise Condition(s, m, p)
        e => raise SimpleError(e.to_string())
      }
      let q = list2(sym("quote"), expr)
      Some(if meval_flag { list2(sym("meval*"), q) } else { q })
    }
    '=' => {
      // #n= object: a label for shared structure
      let placeholder = cons(sym("si::label-placeholder"), Nil)
      self.labels[arg] = placeholder
      let v = self.read()
      self.labels[arg] = v
      Some(replace_placeholder(v, placeholder, v))
    }
    '#' =>
      match self.labels.get(arg) {
        Some(v) => Some(v)
        None => raise SimpleError("read: undefined label #\{arg}#")
      }
    'x' | 'X' => Some(self.read_radix(16))
    'o' | 'O' => Some(self.read_radix(8))
    'b' | 'B' => Some(self.read_radix(2))
    'r' | 'R' => Some(self.read_radix(arg))
    'c' | 'C' => {
      let parts = self.read()
      Some(complex(car(parts), i=cadr(parts)))
    }
    'p' | 'P' => Some(self.read())
    '*' => {
      let bits = []
      while self.peek() is Some(c) && (c == '0' || c == '1') {
        bits.push(int(c.to_int() - '0'.to_int()))
        self.next() |> ignore
      }
      Some(vector(bits))
    }
    'a' | 'A' => {
      let contents = self.read()
      // SBCL prints strings readably as #A((n) BASE-CHAR . "text")
      if arg < 0 {
        match contents {
          Cons({ car: Cons(_), cdr: Cons({ car: _, cdr: Str(_) as s }) }) =>
            return Some(s)
          _ => ()
        }
      }
      let rank = if arg < 0 { 1 } else { arg }
      let dims : Array[Int] = []
      let mut level = contents
      for _ in 0..<rank {
        dims.push(length(level))
        level = car(level)
      }
      let data : Array[Value] = []
      fn flat(x : Value, k : Int) -> Unit {
        if k == rank {
          data.push(x)
        } else {
          let mut l = x
          while l is Cons(c) {
            flat(c.car, k + 1)
            l = c.cdr
          }
        }
      }

      flat(contents, 0)
      let arr = make_array(dims)
      match arr {
        Vec(a) => a.data = data
        _ => ()
      }
      Some(arr)
    }
    _ => raise SimpleError("read: unsupported dispatch #\{d}")
  }
}

///|
fn LReader::read_radix(self : LReader, radix : Int) -> Value raise LispError {
  let (n, _, _, _) = self.token()
  let t = string_downcase(n)
  match parse_integer(t, radix~) {
    Some(v) => v
    None =>
      match t.find("/") {
        Some(k) =>
          match
            (
              parse_integer(t.substring(end=k), radix~),
              parse_integer(t.substring(start=k + 1), radix~),
            ) {
            (Some(x), Some(y)) => make_ratio(to_big(x), to_big(y))
            _ => raise SimpleError("read: bad number #r" + n)
          }
        None => raise SimpleError("read: bad number in radix \{radix}: " + n)
      }
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
    } else if c == '+' || c == '-' {
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

///|
/// Replace a #n= placeholder inside `x` by the labelled object (in place).
fn replace_placeholder(x : Value, ph : Value, v : Value) -> Value {
  if physical_equal_value(x, ph) {
    return v
  }
  let mut l = x
  while l is Cons(c) {
    if physical_equal_value(c.car, ph) {
      c.car = v
    } else {
      replace_placeholder(c.car, ph, v) |> ignore
    }
    if physical_equal_value(c.cdr, ph) {
      c.cdr = v
      break
    }
    l = c.cdr
  }
  x
}
