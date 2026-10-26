// Port of src/commac.lisp: Maclisp compatibility utilities (exploden,
// implode, getchar, ...), float formatting for EXPLODEN, and the date/time
// functions timedate, parse_timedate, encode_time and decode_time.
//
// Notes on the port:
// - print-invert-case / maybe-invert-string-case are the identity (symbol
//   names are already the user-visible names).
// - The runtime has no notion of the local time zone: whenever the Lisp
//   code lets DECODE-UNIVERSAL-TIME / ENCODE-UNIVERSAL-TIME use the local
//   time zone, the port uses UTC without daylight saving time.
// - The pregexp patterns are matched by hand-written matchers returning the
//   same match-position lists `((start . end) (start . end) ...)`.

///|
fn commac__q(name : String) -> Value {
  sym(name)
}

///|
fn appears(tree : Value, var_ : Value) -> Value raise {
  if equal(tree, var_) {
    throw_tag(q_appears, t) |> ignore
  } else if atom(tree) {
    ()
  } else {
    appears(car(tree), var_) |> ignore
    appears(cdr(tree), var_) |> ignore
  }
  Nil
}

///|
fn appears1(tree : Value, var_ : Value) -> Value raise {
  if eq(tree, var_) {
    throw_tag(q_appears, t) |> ignore
  } else if atom(tree) {
    ()
  } else {
    appears(car(tree), var_) |> ignore
    appears(cdr(tree), var_) |> ignore
  }
  Nil
}

///|
/// Yields t if var appears in tree
fn appears_in(tree : Value, var_ : Value) -> Value raise {
  catch_tag(q_appears, () => {
    if symbolp(var_) || fixnump(var_) {
      appears1(tree, var_)
    } else {
      appears(tree, var_)
    }
  })
}

///|
/// A small CL TYPEP for the type names used with ML-TYPEP.
fn commac__typep(x : Value, type_ : Value) -> Bool raise {
  let name = match type_ {
    Sym(s) => s.name
    Nil => return false
    _ => return false
  }
  match name {
    "t" => true
    "null" => x is Nil
    "cons" => consp(x)
    "list" => listp(x)
    "atom" => atom(x)
    "symbol" => symbolp(x)
    "keyword" => keywordp(x)
    "fixnum" => fixnump(x)
    "bignum" => bignump(x)
    "integer" => integerp(x)
    "ratio" => ratiop(x)
    "rational" => rationalp(x)
    "float" | "flonum" | "double-float" => floatp(x)
    "real" => realp(x)
    "number" => numberp(x)
    "complex" => complexp(x)
    "string" => stringp(x)
    "character" => characterp(x)
    "array" | "vector" => arrayp(x) || stringp(x)
    "hash-table" => hash_table_p(x)
    "function" | "compiled-function" => functionp(x)
    _ =>
      match x {
        Struct(s) => s.stype.name == name
        _ => false
      }
  }
}

///|
/// CL TYPE-OF (approximately, SBCL style) for values not covered by
/// ML-TYPEP's TYPECASE.
fn commac__type_of(x : Value) -> Value {
  match x {
    Nil => q_null
    Sym(s) => if s.name == "t" { q_boolean } else { q_symbol }
    Char(_) => q_character
    Func(_) => commac__q("compiled-function")
    Struct(s) => s.stype.to_value()
    Stream(_) => commac__q("stream")
    _ => t
  }
}

///|
/// A more portable implementation of ml-typep.
fn ml_typep(x : Value, type_~ : Value = Nil) -> Value raise {
  if type_.truthy() {
    let pred = get(type_, q_ml_typep)
    if pred.truthy() {
      funcall(pred, [x])
    } else {
      lbool(commac__typep(x, type_))
    }
  } else {
    match x {
      Cons(_) => q_list
      Fix(_) => q_fixnum
      Big(_) => q_bignum
      Flo(_) => q_flonum
      Ratio(_, _) | Cplx(_, _) => q_number
      Vec(_) | Str(_) => q_array
      Hash(_) => q_hash_table
      _ => commac__type_of(x)
    }
  }
}

///|
/// `(*array name maclisp-type &rest dimlist)`
fn n_stararray(
  name : Value,
  maclisp_type : Value,
  dimlist : Value,
) -> Value raise {
  if eq(maclisp_type, q_readtable) || eq(maclisp_type, q_obarray) {
    raise LispError::SimpleError(
      format_to_string(" bad type ~S", [maclisp_type]),
    )
  }
  // for tracking down old ones.
  if memq(name, symval(q_ear_maxima_arrays)) is Nil {
    set(q_ear_maxima_arrays, cons(name, symval(q_ear_maxima_arrays))) |> ignore
  }
  let initial : Value = if eq(maclisp_type, q_fixnum) {
    Fix(0L)
  } else if eq(maclisp_type, q_flonum) {
    Flo(0.0)
  } else {
    Nil
  }
  let dims = list_to_array(dimlist).map(d => to_int(d))
  let aarray = make_array(dims, initial~)
  if name is Nil {
    aarray
  } else if symbolp(name) {
    setf_get(name, q_array, aarray) |> ignore
    name
  } else {
    raise LispError::SimpleError(
      format_to_string("~S is illegal first arg for *array", [name]),
    )
  }
}

///|
/// `(maxima-error datum &rest args)` = `(cerror "without any special
/// action" datum args...)`; there is no restart in the port, so it
/// signals an error with the formatted message.
fn maxima_error(datum : Value, args : Value) -> Value raise {
  let msg = match datum {
    Str(s) => format_to_string(s, list_to_array(args))
    _ => princ_to_string(datum)
  }
  raise LispError::SimpleError(msg)
}

///|
/// `(show v ...)`: print "The value of v is <value>" for each value.  (The
/// macro prints the unevaluated form; as a function only the values are
/// available, so the value is used for both.)
fn show(l : Value) -> Value raise {
  for v in l.iter() {
    format(t, "~%The value of ~A is ~A", [v, v]) |> ignore
  }
  Nil
}

///|
fn onep(x : Value) -> Value raise {
  lbool(eql(Fix(1L), x))
}

///|
/// `(member (type-of x) '(bignum rational float))`: in SBCL TYPE-OF
/// returns BIGNUM only for bignums (RATIO and DOUBLE-FLOAT otherwise).
fn extended_number_p(x : Value) -> Value raise {
  if bignump(x) {
    list3(q_bignum, q_rational, q_float)
  } else {
    Nil
  }
}

///|
/// ($mkey '$demo) ==> :demo
fn d_mkey(variable : Value) -> Value raise {
  kw(string_left_trim("$", lstring(string(variable))))
}

///|
/// `(arg x)` refers to the lexical NARG-REST-ARGUMENT of a Maclisp lexpr;
/// in translated code use `narg1(x, args)` with the lexpr's argument list.
/// This returns the expansion.
fn arg_(x : Value) -> Value raise {
  list3(q_narg1, x, q_narg_rest_argument)
}

///|
fn narg1(x : Value, l : Value) -> Value raise {
  if x is Nil {
    int(length(l))
  } else {
    let tem = nthcdr(to_int(x) - 1, l)
    if tem is Nil {
      raise LispError::SimpleError(
        format_to_string("arg ~A beyond range ~A ", [x, int(length(l))]),
      )
    } else {
      car(tem)
    }
  }
}

///|
/// `(listify x)`: expansion `(listify1 x narg-rest-argument)`.
fn listify(x : Value) -> Value raise {
  list3(q_listify1, x, q_narg_rest_argument)
}

///|
/// `(setarg i val)`: expansion `(setarg1 i val narg-rest-argument)`.
fn setarg(i : Value, val : Value) -> Value raise {
  list4(q_setarg1, i, val, q_narg_rest_argument)
}

///|
fn setarg1(i : Value, val : Value, l : Value) -> Value raise {
  rplaca(nthcdr(to_int(i) - 1, l), val) |> ignore
  val
}

///|
fn listify1(n : Value, narg_rest_argument : Value) -> Value raise {
  if minusp(n) {
    let k = -to_int(n)
    let len = length(narg_rest_argument)
    copy_list(nthcdr(if k >= len { 0 } else { len - k }, narg_rest_argument))
  } else if zerop(n) {
    Nil
  } else {
    subseq(narg_rest_argument, 0, end=to_int(n))
  }
}

///|
/// The current *print-base* (10 if unset).
fn commac__print_base() -> Int32 raise {
  let b = symval(q_ear_print_base)
  if fixnump(b) {
    to_int(b)
  } else {
    10
  }
}

///|
/// The printed name of SYM (PRINC-TO-STRING with the case inversion of
/// the CL readtable, which is the identity on the port's names).
fn print_invert_case(sym_ : Value) -> Value raise {
  Str(princ_to_string(sym_))
}

///|
fn exploden(symb : Value) -> Value raise {
  let string_ = if symbolp(symb) {
    lstring(print_invert_case(symb))
  } else if floatp(symb) {
    lstring(exploden_format_float(symb))
  } else if integerp(symb) {
    // When obase > 10, prepend leading zero to ensure that output is
    // readable as a number.
    let base = commac__print_base()
    let s = if base == 10 {
      format_to_string("~A", [symb])
    } else {
      to_big(symb).to_string(radix=base).to_upper()
    }
    let chars = string_to_char_list(s)
    if base > 10 {
      match car(chars) {
        Char(c) if digit_char_p(c, radix=10) is None =>
          return cons(Char('0'), chars)
        _ => ()
      }
    }
    return chars
  } else {
    format_to_string("~A", [symb])
  }
  string_to_char_list(string_)
}

///|
fn exploden_format_float(symb : Value) -> Value raise {
  let p = symval(q_d_fpprintprec)
  if num_eq(p, Fix(0L)) || num_gt(p, Fix(16L)) {
    exploden_format_float_readably_except_special_values(symb)
  } else {
    exploden_format_float_pretty(symb).0
  }
}

///|
/// Return a readable string, EXCEPT for not-a-number and infinity, if
/// present; for those, return a probably-nonreadable string.
fn exploden_format_float_readably_except_special_values(
  x : Value,
) -> Value raise {
  if float_inf_p(x).truthy() || float_nan_p(x).truthy() {
    Str(format_to_string("~a", [x]))
  } else {
    // SBCL needs no fix up of the printed representation.
    Str(prin1_to_string(x))
  }
}

///|
/// (1) If string looks like "n.nnnD0" or "n.nnnd0", return just "n.nnn".
/// (2) Otherwise, replace #\D or #\d (if present) with #\E or #\e,
///     respectively.
/// (3) Otherwise, return S unchanged.
fn fix_up_exponent_in_place(s : Value) -> Value raise {
  let str = lstring(s)
  let cs = string_chars(str)
  let n = cs.length()
  if n > 2 {
    if (cs[n - 2] == 'D' || cs[n - 2] == 'd') && cs[n - 1] == '0' {
      Str(substring(str, 0, end=n - 2))
    } else {
      match cs.search('D') {
        Some(i) => {
          cs[i] = 'E'
          Str(chars_to_string(cs))
        }
        None =>
          match cs.search('d') {
            Some(i) => {
              cs[i] = 'e'
              Str(chars_to_string(cs))
            }
            None => s
          }
      }
    }
  } else {
    s
  }
}

///|
/// Replace "nnnn.Ennn" or "nnn.ennn" with "nnn.0Ennn" or nnn.0ennn",
/// respectively.
fn insert_zero_before_exponent(s : Value) -> Value raise {
  let str = lstring(s)
  let cs = string_chars(str)
  let n = cs.length()
  match cs.search('.') {
    Some(i) if i < n - 1 => {
      let c = cs[i + 1]
      if c == 'E' || c == 'e' {
        Str(substring(str, 0, end=i + 1) + "0" + substring(str, i + 1, end=n))
      } else {
        s
      }
    }
    _ => s
  }
}

///|
/// Lower case the exponent marker and drop a #\+ in front of a positive
/// exponent ("9.87E+52" -> "9.87e52").
fn normalize_exponent(s : Value) -> Value raise {
  let str = lstring(s)
  let cs = string_chars(str)
  let n = cs.length()
  let mut i = -1
  for j in 1..<n {
    if alpha_char_p(cs[j]) {
      i = j
      break
    }
  }
  if i >= 0 && i + 1 < n {
    let rest_ = if cs[i + 1] == '+' {
      substring(str, i + 2)
    } else {
      substring(str, i + 1)
    }
    Str(substring(str, 0, end=i) + char_downcase(cs[i]).to_string() + rest_)
  } else {
    s
  }
}

///|
/// Format a float with $fpprintprec significant digits.  (The second
/// value of the declared tuple is always NIL: the Lisp function returns a
/// single value.)
fn exploden_format_float_pretty(symb : Value) -> (Value, Value) raise {
  let a = num_abs(symb)
  let fpprintprec = to_int(symval(q_d_fpprintprec))
  let mut string_ = ""
  if symval(q_ear_fortran_print).truthy() {
    // When printing out something for Fortran, we want to be sure to print
    // the exponent marker so that Fortran knows what kind of number it is.
    string_ = if float_nan_p(symb).truthy() {
      "NAN"
    } else if float_inf_p(symb).truthy() {
      if num_lt(symb, Fix(0L)) {
        "-INF"
      } else {
        "INF"
      }
    } else {
      format_to_string("~e", [symb])
    }
  } else {
    let ad = to_double(a)
    let (form, digits) = if zerop(a) {
      ("~,vf", 1)
    } else if 0.001 <= ad && ad <= 1.0e7 {
      let integer_log10 = (dlog(ad) / 2.302585092994046).floor().to_int()
      let scale = 1 + integer_log10
      if scale < fpprintprec {
        ("~,vf", fpprintprec - scale)
      } else {
        ("~,ve", fpprintprec - 1)
      }
    } else if float_inf_p(symb).truthy() || float_nan_p(symb).truthy() {
      return (Str(format_to_string("~a", [symb])), Nil)
    } else {
      ("~,ve", fpprintprec - 1)
    }
    // Call FORMAT using format string chosen above.
    string_ = format_to_string(form, [int(digits), a])
    // EXPLODEN is often called after NFORMAT, so it doesn't usually see a
    // negative argument.  I can't guarantee a non-negative argument, so
    // handle negative here.
    if num_lt(symb, Fix(0L)) {
      string_ = "-" + string_
    }
  }
  let s : Value = Str(string_)
  if symval(q_ear_exploden_strip_float_zeros).truthy() {
    let r = strip_float_zeros(s)
    (if r.truthy() { r } else { s }, Nil)
  } else {
    (s, Nil)
  }
}

///|
/// Match `.*\.[0-9]*[1-9]` followed by `00*` on cs[0:end]: the end of the
/// group, or -1.
fn commac__match_f0(cs : Array[Char], end : Int32) -> Int32 {
  // the last non-zero character
  let mut k = end - 1
  while k >= 0 && cs[k] == '0' {
    k -= 1
  }
  if k < 0 || k >= end - 1 {
    return -1
  }
  if !(cs[k] >= '1' && cs[k] <= '9') {
    return -1
  }
  let mut j = k - 1
  while j >= 0 && cs[j] >= '0' && cs[j] <= '9' {
    j -= 1
  }
  if j >= 0 && cs[j] == '.' {
    k + 1
  } else {
    -1
  }
}

///|
/// Match `.*\.0` followed by `00*` on cs[0:end]: the end of the group, or -1.
fn commac__match_f1(cs : Array[Char], end : Int32) -> Int32 {
  let mut k = end - 1
  while k >= 0 && cs[k] == '0' {
    k -= 1
  }
  if k >= 0 && cs[k] == '.' && end - (k + 1) >= 2 {
    k + 2
  } else {
    -1
  }
}

///|
/// Start of the group `[^0-9][+-][0-9]*$`, or -1.
fn commac__match_exponent_tail(cs : Array[Char]) -> Int32 {
  let n = cs.length()
  let mut q = n - 1
  while q >= 0 && cs[q] >= '0' && cs[q] <= '9' {
    q -= 1
  }
  if q >= 1 &&
    (cs[q] == '+' || cs[q] == '-') &&
    !(cs[q - 1] >= '0' && cs[q - 1] <= '9') {
    q - 1
  } else {
    -1
  }
}

///|
fn commac__pos(a : Int32, b : Int32) -> Value {
  cons(int(a), int(b))
}

///|
/// "^(.*\\.[0-9]*[1-9])00*$"
fn trailing_zeros_regex_f_0(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let e = commac__match_f0(cs, cs.length())
  if e < 0 {
    Nil
  } else {
    list2(commac__pos(0, cs.length()), commac__pos(0, e))
  }
}

///|
/// "^(.*\\.0)00*$"
fn trailing_zeros_regex_f_1(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let e = commac__match_f1(cs, cs.length())
  if e < 0 {
    Nil
  } else {
    list2(commac__pos(0, cs.length()), commac__pos(0, e))
  }
}

///|
/// "^(.*\\.[0-9]*[1-9])00*([^0-9][+-][0-9]*)$"
fn trailing_zeros_regex_e_0(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let m = commac__match_exponent_tail(cs)
  if m < 0 {
    return Nil
  }
  let e = commac__match_f0(cs, m)
  if e < 0 {
    Nil
  } else {
    list3(
      commac__pos(0, cs.length()),
      commac__pos(0, e),
      commac__pos(m, cs.length()),
    )
  }
}

///|
/// "^(.*\\.0)00*([^0-9][+-][0-9]*)$"
fn trailing_zeros_regex_e_1(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  let m = commac__match_exponent_tail(cs)
  if m < 0 {
    return Nil
  }
  let e = commac__match_f1(cs, m)
  if e < 0 {
    Nil
  } else {
    list3(
      commac__pos(0, cs.length()),
      commac__pos(0, e),
      commac__pos(m, cs.length()),
    )
  }
}

///|
fn commac__group_string(s : String, g : Value) -> String raise {
  substring(s, to_int(car(g)), end=to_int(cdr(g)))
}

///|
/// Return S with trailing zero digits stripped off, or NIL if there are
/// none.
fn strip_float_zeros(s : Value) -> Value raise {
  let str = lstring(s)
  let m1 = {
    let m = trailing_zeros_regex_f_0(s)
    if m.truthy() {
      m
    } else {
      trailing_zeros_regex_f_1(s)
    }
  }
  if m1.truthy() {
    return Str(commac__group_string(str, nth(1, m1)))
  }
  let m2 = {
    let m = trailing_zeros_regex_e_0(s)
    if m.truthy() {
      m
    } else {
      trailing_zeros_regex_e_1(s)
    }
  }
  if m2.truthy() {
    Str(
      commac__group_string(str, nth(1, m2)) +
      commac__group_string(str, nth(2, m2)),
    )
  } else {
    Nil
  }
}

///|
/// is called for symbols and numbers
fn explodec(symb : Value) -> Value raise {
  let c = Collector::new()
  for ch in string_chars(lstring(print_invert_case(symb))) {
    c.add(sym(ch.to_string()))
  }
  c.result()
}

///|
/// If the string is all the same case, CL inverts the case.  The port's
/// symbol names are already the user-visible names, so this is the
/// identity.
fn maybe_invert_string_case(string_ : Value) -> Value raise {
  string_
}

///|
/// Like read-from-string with readtable-case :invert (the identity
/// conversion in the port).
fn intern_invert_case(string_ : Value) -> Value raise {
  sym(lstring(maybe_invert_string_case(string_)))
}

///|
fn implode(list_ : Value) -> Value raise {
  let sb = StringBuilder::new()
  for v in list_.iter() {
    match v {
      Char(c) => sb.write_char(c)
      Nil | Sym(_) => sb.write_char(char_at(symbol_name(v), 0))
      Fix(n) => sb.write_char(code_char(n.to_int()))
      _ => raise type_error(v, "(or character symbol integer)")
    }
  }
  intern_invert_case(Str(sb.to_string()))
}

///|
/// Note: symb can also be a number, not just a symbol.
fn explode(symb : Value) -> Value raise {
  let c = Collector::new()
  for ch in string_chars(prin1_to_string(symb)) {
    c.add(sym(ch.to_string()))
  }
  c.result()
}

///|
/// return the first character of the name of a symbol or a string or char
fn get_first_char(symb : Value) -> Value raise {
  Char(char_at(lstring(string(symb)), 0))
}

///|
fn getchar(symb : Value, i : Value) -> Value raise {
  let str = lstring(string(symb))
  let n = string_length(str)
  if num_le(Fix(1L), i) && num_le(i, int(n)) {
    sym(char_at(str, to_int(i) - 1).to_string())
  } else {
    Nil
  }
}

///|
fn ascii(n : Value) -> Value raise {
  sym(lstring(string(n)))
}

///|
fn maknam(lis : Value) -> Value raise {
  let sb = StringBuilder::new()
  for v in lis.iter() {
    match v {
      Nil | Sym(_) => sb.write_char(char_at(symbol_name(v), 0))
      Char(c) => sb.write_char(c)
      _ => maxima_error(Str("bad entry"), Nil) |> ignore
    }
  }
  make_symbol(lstring(maybe_invert_string_case(Str(sb.to_string()))))
}

///|
/// for those window labels etc. that are wrong type.  Is not only called
/// for symbols, but also on numbers
fn flatc(sym_ : Value) -> Value raise {
  int(length(explodec(sym_)))
}

///|
fn flatsize(sym_ : Value) -> Value raise {
  int(length(exploden(sym_)))
}

///|
fn safe_zerop(x : Value) -> Value raise {
  lbool(numberp(x) && zerop(x))
}

///|
/// `(signp sym x)`: SYM is one of E L LE G GE N.
fn signp(sym_ : Value, x : Value) -> Value raise {
  if !numberp(x) {
    return Nil
  }
  let name = match sym_ {
    Sym(s) => s.name
    _ => ""
  }
  match name {
    "e" => lbool(zerop(x))
    "l" => lbool(num_lt(x, Fix(0L)))
    "le" => lbool(num_le(x, Fix(0L)))
    "g" => lbool(num_gt(x, Fix(0L)))
    "ge" => lbool(num_ge(x, Fix(0L)))
    "n" => lbool(!zerop(x))
    _ => Nil
  }
}

///|
fn tyi_raw(stream? : Value, eof_option~ : Value = Nil) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_input)
  }
  // The runtime has no READ-CHAR-NO-HANG; a blocking read is equivalent
  // except for the optional read-hang prompt.
  read_char(stream~, eof_value=eof_option)
}

///|
let commac__previous_tyi : Ref[Value] = Ref::new(Char('a'))

///|
/// The sequences of characters
///   <anything-except-backslash>
///   (<backslash> <newline> | <backslash> <return> | <backslash> <return> <newline>)+
///   <anything>
/// are reduced to <anything-except-backslash> <anything> .
fn backslash_check(
  ch : Value,
  stream : Value,
  eof_option : Value,
) -> Value raise {
  if eql(commac__previous_tyi.val, Char('\\')) {
    commac__previous_tyi.val = Char('a')
    ch
  } else {
    commac__previous_tyi.val = if eql(ch, Char('\\')) {
      let next_char = peek_char(stream~, eof_value=eof_option)
      if eql(next_char, Char('\n')) || eql(next_char, Char('\r')) {
        eat_continuations(ch, stream, eof_option)
      } else {
        ch
      }
    } else {
      ch
    }
    commac__previous_tyi.val
  }
}

///|
/// We have just read <backslash> and we know the next character is
/// <newline> or <return>.  Eat line continuations until we come to
/// something which doesn't match, or we reach eof.
fn eat_continuations(
  ch : Value,
  stream : Value,
  eof_option : Value,
) -> Value raise {
  let mut ch = tyi_raw(stream~, eof_option~)
  while eql(ch, Char('\n')) || eql(ch, Char('\r')) {
    let next_char = peek_char(stream~, eof_value=eof_option)
    if eql(ch, Char('\r')) && eql(next_char, Char('\n')) {
      tyi_raw(stream~, eof_option~) |> ignore
    }
    ch = tyi_raw(stream~, eof_option~)
    let next_char = peek_char(stream~, eof_value=eof_option)
    if eql(ch, Char('\\')) &&
      (eql(next_char, Char('\r')) || eql(next_char, Char('\n'))) {
      ch = tyi_raw(stream~, eof_option~)
    } else {
      return ch
    }
  }
  ch
}

///|
fn tyi(stream? : Value, eof_option~ : Value = Nil) -> Value raise {
  let stream = match stream {
    Some(s) => s
    None => symval(standard_input)
  }
  let ch = tyi_raw(stream~, eof_option~)
  if eql(ch, eof_option) {
    ch
  } else {
    backslash_check(ch, stream, eof_option)
  }
}

// ---------------------------------------------------------------------------
// Universal time (seconds since 1900-01-01 00:00:00 GMT).

///|
/// Days since 1970-01-01 of a proleptic Gregorian date.
fn commac__days_from_civil(y : Int64, m : Int64, d : Int64) -> Int64 {
  let y = if m <= 2L { y - 1L } else { y }
  let era = (if y >= 0L { y } else { y - 399L }) / 400L
  let yoe = y - era * 400L
  let mp = (m + 9L) % 12L
  let doy = (153L * mp + 2L) / 5L + d - 1L
  let doe = yoe * 365L + yoe / 4L - yoe / 100L + doy
  era * 146097L + doe - 719468L
}

///|
/// (year, month, day) of a day count since 1970-01-01.
fn commac__civil_from_days(z : Int64) -> (Int64, Int64, Int64) {
  let z = z + 719468L
  let era = (if z >= 0L { z } else { z - 146096L }) / 146097L
  let doe = z - era * 146097L
  let yoe = (doe - doe / 1460L + doe / 36524L - doe / 146096L) / 365L
  let y = yoe + era * 400L
  let doy = doe - (365L * yoe + yoe / 4L - yoe / 100L)
  let mp = (5L * doy + 2L) / 153L
  let d = doy - (153L * mp + 2L) / 5L + 1L
  let m = if mp < 10L { mp + 3L } else { mp - 9L }
  (if m <= 2L { y + 1L } else { y }, m, d)
}

///|
/// Days between 1900-01-01 and 1970-01-01.
let commac__days_1900_1970 : Int64 = 25567L

///|
/// CL DECODE-UNIVERSAL-TIME: (second minute hour date month year
/// day-of-week dst-p tz).  TZ is hours west of Greenwich; NIL means the
/// local time zone, which the port takes to be UTC without DST.
fn commac__decode_universal_time(
  ut : Value,
  tz : Value,
) -> (Value, Value, Value, Value, Value, Value, Value, Value, Value) raise {
  let tz : Value = if tz is Nil { Fix(0L) } else { tz }
  let local = floor1(num_sub(ut, num_mul(tz, Fix(3600L))))
  let (days, secs) = num_floor(local, b=Fix(86400L))
  let days = to_int64(days)
  let secs = to_int64(secs)
  let (y, m, d) = commac__civil_from_days(days - commac__days_1900_1970)
  // 1900-01-01 was a Monday (day 0).
  let dow = (days % 7L + 7L) % 7L
  (
    int64(secs % 60L),
    int64(secs / 60L % 60L),
    int64(secs / 3600L),
    int64(d),
    int64(m),
    int64(y),
    int64(dow),
    Nil,
    tz,
  )
}

///|
/// CL ENCODE-UNIVERSAL-TIME (TZ NIL means UTC in the port).
fn commac__encode_universal_time(
  second : Value,
  minute : Value,
  hour : Value,
  date : Value,
  month : Value,
  year : Value,
  tz : Value,
) -> Value raise {
  let days = commac__days_from_civil(
      to_int64(year),
      to_int64(month),
      to_int64(date),
    ) +
    commac__days_1900_1970
  let mut r = num_mul(int64(days), Fix(86400L))
  r = num_add(r, num_mul(hour, Fix(3600L)))
  r = num_add(r, num_mul(minute, Fix(60L)))
  r = num_add(r, second)
  if tz.truthy() {
    r = num_add(r, num_mul(tz, Fix(3600L)))
  }
  r
}

///|
/// CL GET-UNIVERSAL-TIME
fn commac__get_universal_time() -> Value {
  int64((wall_time_ms() / 1000UL).reinterpret_as_int64() + 2208988800L)
}

///|
/// A Maxima number (integer, ((rat) n d), float) as a CL rational.
fn commac__cl_rational(x : Value) -> Value raise {
  match x {
    Cons(_) if is_op(x, q_rat) => num_div(second(x), third(x))
    Flo(_) => rationalize(x)
    _ => x
  }
}

///|
/// A CL rational as a Maxima number.
fn commac__maxima_number(x : Value) -> Value raise {
  match x {
    Ratio(_, _) => mk_simp(q_rat, [numerator(x), denominator(x)])
    _ => x
  }
}

///|
fn commac__ratio(n : Int32, d : Int32) -> Value raise {
  num_div(int(n), int(d))
}

///|
fn d_timedate(time? : Value, tz~ : Value = Nil) -> Value raise {
  let time = match time {
    Some(t0) => t0
    None => commac__get_universal_time()
  }
  let mut tz = tz
  if consp(tz) && eq(caar(tz), q_rat) {
    tz = num_div(second(tz), third(tz))
  } else if floatp(tz) {
    tz = rationalize(tz)
  }
  if tz.truthy() {
    tz = num_div(num_round(tz, b=commac__ratio(1, 60)).0, Fix(60L))
  }
  let mut time_integer = mfuncall(q_d_floor, list1(time))
  let time_fraction = sub(time, time_integer)
  let mut time_millis = mfuncall(
    q_d_round,
    list1(mul2(Fix(1000L), time_fraction)),
  )
  if num_eq(time_millis, Fix(1000L)) {
    time_integer = one_plus(time_integer)
    time_millis = Fix(0L)
  }
  let (second_, minute, hour, date, month, year, _, dst_p, tz) = commac__decode_universal_time(
    time_integer,
    if tz.truthy() {
      num_neg(tz)
    } else {
      Nil
    },
  )
  // DECODE-UNIVERSAL-TIME might return a timezone offset which is a
  // multiple of 1/3600 but not 1/60.  We need a multiple of 1/60 because
  // our formatted timezone offset has only minutes and seconds.
  if !zerop(num_mod(tz, commac__ratio(1, 60))) {
    d_timedate(
      time=time_integer,
      tz=num_div(num_round(num_neg(tz), b=commac__ratio(1, 60)).0, Fix(60L)),
    )
  } else {
    let tz_offset = if dst_p.truthy() {
      num_sub(Fix(1L), tz)
    } else {
      num_neg(tz)
    }
    let (tz_hours, tz_hour_fraction) = num_truncate(tz_offset)
    let tz_sign : Value = if num_le(Fix(0L), tz_offset) {
      Char('+')
    } else {
      Char('-')
    }
    let tz_minutes = floor1(num_mul(Fix(60L), num_abs(tz_hour_fraction)))
    if num_eq(time_millis, Fix(0L)) {
      format(Nil, "~4,'0d-~2,'0d-~2,'0d ~2,'0d:~2,'0d:~2,'0d~a~2,'0d:~2,'0d", [
        year,
        month,
        date,
        hour,
        minute,
        second_,
        tz_sign,
        num_abs(tz_hours),
        tz_minutes,
      ])
    } else {
      format(
        Nil,
        "~4,'0d-~2,'0d-~2,'0d ~2,'0d:~2,'0d:~2,'0d.~3,'0d~a~2,'0d:~2,'0d",
        [
          year,
          month,
          date,
          hour,
          minute,
          second_,
          time_millis,
          tz_sign,
          num_abs(tz_hours),
          tz_minutes,
        ],
      )
    }
  }
}

///|
fn commac__digit(c : Char) -> Bool {
  c >= '0' && c <= '9'
}

///|
/// Check that cs[start:start+len] are all digits.
fn commac__digits(cs : Array[Char], start : Int32, len : Int32) -> Bool {
  if start + len > cs.length() {
    return false
  }
  for i in start..<(start + len) {
    if !commac__digit(cs[i]) {
      return false
    }
  }
  true
}

///|
/// ^([0-9][0-9][0-9][0-9])-([0-9][0-9])-([0-9][0-9])
fn match_date_yyyy_mm_dd(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if commac__digits(cs, 0, 4) &&
    cs.length() >= 10 &&
    cs[4] == '-' &&
    commac__digits(cs, 5, 2) &&
    cs[7] == '-' &&
    commac__digits(cs, 8, 2) {
    list([
      commac__pos(0, 10),
      commac__pos(0, 4),
      commac__pos(5, 7),
      commac__pos(8, 10),
    ])
  } else {
    Nil
  }
}

///|
/// ^[ T]([0-9][0-9]):([0-9][0-9]):([0-9][0-9])
fn match_time_hh_mm_ss(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if cs.length() >= 9 &&
    (cs[0] == ' ' || cs[0] == 'T') &&
    commac__digits(cs, 1, 2) &&
    cs[3] == ':' &&
    commac__digits(cs, 4, 2) &&
    cs[6] == ':' &&
    commac__digits(cs, 7, 2) {
    list([
      commac__pos(0, 9),
      commac__pos(1, 3),
      commac__pos(4, 6),
      commac__pos(7, 9),
    ])
  } else {
    Nil
  }
}

///|
/// ^[,.]([0-9][0-9]*)
fn match_fraction_nnn(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if cs.length() >= 2 && (cs[0] == ',' || cs[0] == '.') && commac__digit(cs[1]) {
    let mut e = 1
    while e < cs.length() && commac__digit(cs[e]) {
      e += 1
    }
    list2(commac__pos(0, e), commac__pos(1, e))
  } else {
    Nil
  }
}

///|
/// ^([+-])([0-9][0-9]):([0-9][0-9])$
fn match_tz_hh_mm(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if cs.length() == 6 &&
    (cs[0] == '+' || cs[0] == '-') &&
    commac__digits(cs, 1, 2) &&
    cs[3] == ':' &&
    commac__digits(cs, 4, 2) {
    list([
      commac__pos(0, 6),
      commac__pos(0, 1),
      commac__pos(1, 3),
      commac__pos(4, 6),
    ])
  } else {
    Nil
  }
}

///|
/// ^([+-])([0-9][0-9])([0-9][0-9])$
fn match_tz_hhmm(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if cs.length() == 5 &&
    (cs[0] == '+' || cs[0] == '-') &&
    commac__digits(cs, 1, 4) {
    list([
      commac__pos(0, 5),
      commac__pos(0, 1),
      commac__pos(1, 3),
      commac__pos(3, 5),
    ])
  } else {
    Nil
  }
}

///|
/// ^([+-])([0-9][0-9])$
fn match_tz_hh(s : Value) -> Value raise {
  let cs = string_chars(lstring(s))
  if cs.length() == 3 &&
    (cs[0] == '+' || cs[0] == '-') &&
    commac__digits(cs, 1, 2) {
    list([commac__pos(0, 3), commac__pos(0, 1), commac__pos(1, 3)])
  } else {
    Nil
  }
}

///|
/// ^Z$
fn match_tz_z(s : Value) -> Value raise {
  if lstring(s) == "Z" {
    list1(commac__pos(0, 1))
  } else {
    Nil
  }
}

///|
/// The integers (or signs) of the groups of MATCHES in S.
fn commac__extract_groups(matches : Value, s : Value) -> Array[Value] raise {
  let str = lstring(s)
  list_to_array(cdr(matches)).map(ab => {
    parse_integer_or_sign(Str(commac__group_string(str, ab)))
  })
}

///|
/// Parse date/time strings in these formats (and only these):
///
///   YYYY-MM-DD([ T]hh:mm:ss)?([,.]n+)?([+-]hh:mm)?
///   YYYY-MM-DD([ T]hh:mm:ss)?([,.]n+)?([+-]hhmm)?
///   YYYY-MM-DD([ T]hh:mm:ss)?([,.]n+)?([+-]hh)?
///   YYYY-MM-DD([ T]hh:mm:ss)?([,.]n+)?[Z]?
///
/// Trailing unparsed stuff causes the parser to fail (return NIL).
fn d_parse_timedate(s : Value) -> Value raise {
  let mut s : Value = Str(string_trim(" \t\n\r", lstring(s)))
  let mut hours : Value = Fix(0L)
  let mut minutes : Value = Fix(0L)
  let mut seconds : Value = Fix(0L)
  let mut seconds_fraction : Value = Fix(0L)
  let mut tz : Value = Nil
  let matches = match_date_yyyy_mm_dd(s)
  if matches is Nil {
    return Nil
  }
  let g = commac__extract_groups(matches, s)
  let year = g[0]
  let month = g[1]
  let day = g[2]
  s = subseq(s, to_int(cdr(car(matches))))
  let matches = match_time_hh_mm_ss(s)
  if matches.truthy() {
    let g = commac__extract_groups(matches, s)
    hours = g[0]
    minutes = g[1]
    seconds = g[2]
    s = subseq(s, to_int(cdr(car(matches))))
  }
  let matches = match_fraction_nnn(s)
  if matches.truthy() {
    let g = commac__extract_groups(matches, s)
    let seconds_fraction_numerator = g[0]
    let group1 = nth(1, matches)
    seconds_fraction = div(
      seconds_fraction_numerator,
      expt(Fix(10L), num_sub(cdr(group1), car(group1))),
    )
    s = subseq(s, to_int(cdr(car(matches))))
  }
  let str = lstring(s)
  let m1 = match_tz_hh_mm(s)
  let m2 = match_tz_hhmm(s)
  let m3 = match_tz_hh(s)
  if m1.truthy() {
    let g = commac__extract_groups(m1, s)
    tz = num_mul(g[0], num_add(g[1], num_div(g[2], Fix(60L))))
  } else if m2.truthy() {
    let g = commac__extract_groups(m2, s)
    tz = num_mul(g[0], num_add(g[1], num_div(g[2], Fix(60L))))
  } else if m3.truthy() {
    let g = commac__extract_groups(m3, s)
    tz = num_mul(g[0], g[1])
  } else if match_tz_z(s).truthy() {
    tz = Fix(0L)
  } else if string_length(str) > 0 {
    return Nil
  }
  encode_time_with_all_parts(
    year,
    month,
    day,
    hours,
    minutes,
    seconds,
    seconds_fraction,
    if tz.truthy() {
      num_neg(tz)
    } else {
      Nil
    },
  )
}

///|
/// `(values-list ...)` of the parsed groups.  The declared tuple holds the
/// first two values only; d_parse_timedate uses all of them.
fn pregexp_extract_groups_integers(
  matches : Value,
  s : Value,
) -> (Value, Value) raise {
  let g = commac__extract_groups(matches, s)
  (
    if g.length() > 0 {
      g[0]
    } else {
      Nil
    },
    if g.length() > 1 {
      g[1]
    } else {
      Nil
    },
  )
}

///|
fn parse_integer_or_sign(s : Value) -> Value raise {
  let str = lstring(s)
  if str == "+" {
    Fix(1L)
  } else if str == "-" {
    Fix(-1L)
  } else {
    match parse_integer(str) {
      Some(n) => n
      None =>
        raise LispError::SimpleError(format_to_string("junk in string ~S", [s]))
    }
  }
}

///|
fn encode_time_with_all_parts(
  year : Value,
  month : Value,
  day : Value,
  hours : Value,
  minutes : Value,
  seconds_integer : Value,
  seconds_fraction : Value,
  tz : Value,
) -> Value raise {
  add2(
    seconds_fraction,
    commac__encode_universal_time(
      seconds_integer, minutes, hours, day, month, year, tz,
    ),
  )
}

///|
fn d_encode_time(
  year : Value,
  month : Value,
  day : Value,
  hours : Value,
  minutes : Value,
  seconds : Value,
  tz_offset~ : Value = Nil,
) -> Value raise {
  let mut tz_offset = tz_offset
  if tz_offset.truthy() {
    tz_offset = sub(Fix(0L), tz_offset)
    if consp(tz_offset) && eq(caar(tz_offset), q_rat) {
      tz_offset = num_div(second(tz_offset), third(tz_offset))
    } else if floatp(tz_offset) {
      tz_offset = rationalize(tz_offset)
    }
    tz_offset = num_div(
      num_round(tz_offset, b=commac__ratio(1, 3600)).0,
      Fix(3600L),
    )
  }
  let seconds_integer = mfuncall(q_d_floor, list1(seconds))
  let seconds_fraction = sub(seconds, seconds_integer)
  encode_time_with_all_parts(
    year, month, day, hours, minutes, seconds_integer, seconds_fraction, tz_offset,
  )
}

///|
fn d_decode_time(seconds : Value, tz~ : Value = Nil) -> Value raise {
  let mut tz = tz
  if consp(tz) && eq(caar(tz), q_rat) {
    tz = num_div(second(tz), third(tz))
  } else if floatp(tz) {
    tz = rationalize(tz)
  }
  if tz.truthy() {
    tz = num_div(num_round(tz, b=commac__ratio(1, 3600)).0, Fix(3600L))
  }
  let seconds_integer = mfuncall(q_d_floor, list1(seconds))
  let seconds_fraction = sub(seconds, seconds_integer)
  let (secs, minutes, hours, day, month, year, _, dst_p, tz) = commac__decode_universal_time(
    seconds_integer,
    if tz.truthy() {
      num_neg(tz)
    } else {
      Nil
    },
  )
  let tz_offset = if dst_p.truthy() {
    num_sub(Fix(1L), tz)
  } else {
    num_neg(tz)
  }
  list([
    list1(q_mlist),
    year,
    month,
    day,
    hours,
    minutes,
    add2(secs, seconds_fraction),
    d_ratsimp(commac__maxima_number(tz_offset), Nil),
  ])
}

///|
/// Some systems make everything functionp including macros:
fn functionp_(x : Value) -> Value raise {
  if symbolp(x) {
    lbool(fboundp(x))
  } else {
    lbool(functionp(x))
  }
}

///|
fn init_commac() -> Unit raise {
  let pred = (name : String, f : (Value) -> Bool) => {
    lfunc(name, args => lbool(f(arg(args, 0))))
  }
  putprop(kw("extended-number"), q_extended_number_p, q_ml_typep) |> ignore
  putprop(q_array, pred("arrayp", x => arrayp(x) || stringp(x)), q_ml_typep)
  |> ignore
  putprop(q_atom, pred("atom", atom), q_ml_typep) |> ignore
  putprop(
    commac__q("compiled-function"),
    pred("compiled-function-p", x => functionp(x) && !symbolp(x)),
    q_ml_typep,
  )
  |> ignore
  putprop(commac__q("extended-number"), q_extended_number_p, q_ml_typep)
  |> ignore
  putprop(q_fixnum, q_fixnump, q_ml_typep) |> ignore
  putprop(q_list, pred("consp", consp), q_ml_typep) |> ignore
  putprop(q_number, pred("numberp", numberp), q_ml_typep) |> ignore
  putprop(q_string, pred("stringp", stringp), q_ml_typep) |> ignore
  putprop(q_symbol, pred("symbolp", symbolp), q_ml_typep) |> ignore
  // These symbols are shadowed because we use them also as special
  // variables.
  defun(q_break, args => {
    let msg = if args.length() > 0 && stringp(args[0]) {
      format_to_string(lstring(args[0]), args[1:].to_array())
    } else {
      "break"
    }
    raise LispError::SimpleError(msg)
  })
  defun(q_gcd, args => {
    let mut g : Value = Fix(0L)
    for a in args {
      g = num_gcd(g, a)
    }
    g
  })
}
