// Port of share/contrib/maximaMathML/mathml-maxima.lisp: enabling Maxima
// to receive MathML content-coded input (Paul S. Wang, 2000).

///|
let share_mathml_maxima__q_g : Value = sym("g")

///|
let share_mathml_maxima__q_special_proc : Value = sym("*special-proc*")

///|
/// mathml(): read MathML content code from the input and evaluate it.
fn d_mathml() -> Value raise {
  meval(mltoma(ear_in=symval(q_ear_parse_stream)))
}

///|
/// mltoma is the top-level mathml input function
fn mltoma(ear_in? : Value = Nil) -> Value raise {
  with_special(q_ear_in, ear_in, () => {
    if symval(q_ear_in) is Nil {
      set(q_ear_in, t) |> ignore
    }
    set(share_mathml_maxima__q_g, get_tag()) |> ignore
    if !eq(symval(share_mathml_maxima__q_g), q_math) {
      return Nil
    }
    let ans = ml2ma()
    set(share_mathml_maxima__q_g, get_tag()) |> ignore // this should be </math>
    ans
  })
}

///|
fn ml2ma() -> Value raise {
  let (tag, attributes) = get_tag_mv()
  set(q_ear_tag, tag) |> ignore
  if eq(tag, q_ci) {
    ml_ci(attributes)
  } else if eq(tag, q_cn) {
    ml_cn(attributes)
  } else if eq(tag, q_apply) {
    ml_apply()
  } else if memq(tag, list([q_bvar, q_lowlimit, q_uplimit])).truthy() {
    let ans = ml2ma()
    get_tag() |> ignore
    ans
  } else if eq(tag, sym("/apply")) {
    Nil
  } else {
    merr("unknown or invalid mathml tag: ~A", [tag])
  }
}

///|
fn ml_apply() -> Value raise {
  with_special(share_mathml_maxima__q_special_proc, Nil, () => {
    let op = get_op()
    if op is Nil {
      let proc = symval(share_mathml_maxima__q_special_proc)
      if proc.truthy() {
        return apply(proc, Nil)
      } else {
        merr("internal error: null mct-proc", []) |> ignore
      }
    }
    // ml2ma returns nil after seeing </apply>
    let mut ans : Value = Nil
    let mut operand = ml2ma()
    while operand.truthy() {
      ans = cons(operand, ans)
      operand = ml2ma()
    }
    cons(op, nreverse(ans))
  })
}

///|
/// <apply>
/// <diff/> <apply> <fn>G</fn><ci>X</ci> </apply>
/// <bvar><ci>X</ci><degree><cn type="integer">2</cn></degree></bvar>
/// </apply>
/// => (($DIFF) (($F) $X) $X 2)
fn mctdiff() -> Value raise {
  let fn_ = ml2ma()
  let var_deg = diff_bvar()
  get_tag() |> ignore // lose </apply>
  cons(list1(q_d_diff), cons(fn_, var_deg))
}

///|
fn mctintegrate() -> Value raise {
  let var_ = get_bvar()
  let nt = ml2ma()
  if eq(symval(q_ear_tag), q_lowlimit) {
    let ll = nt
    let up = ml2ma()
    if eq(symval(q_ear_tag), q_uplimit) {
      let grand = ml2ma()
      get_tag() |> ignore // lose </apply> for <int\>
      return list([list1(q_d_integrate), grand, var_, ll, up])
    } else {
      merr("definite intergral error", []) |> ignore
    }
  }
  // indefinte integral
  let grand = nt
  get_tag() |> ignore // lose </apply>
  list([list1(q_d_integrate), grand, var_])
}

///|
fn get_bvar() -> Value raise {
  let tag = get_tag()
  if !eq(tag, q_bvar) {
    merr("Expecting bvar but got ~A", [tag]) |> ignore
  }
  let v = ml2ma()
  get_tag() |> ignore // lose </bvar>
  v
}

///|
fn diff_bvar() -> Value raise {
  let tag = get_tag()
  if !eq(tag, q_bvar) {
    merr("Expecting bvar but got ~A", [tag]) |> ignore
  }
  let v = ml2ma()
  let tag = get_tag()
  if !eq(tag, q_degree) {
    merr("Expecting degree but got ~A", [tag]) |> ignore
  }
  let d = ml2ma()
  get_tag() |> ignore
  get_tag() |> ignore // skip closing tags
  list([v, d])
}

///|
fn ml_cn(attributes : Value) -> Value raise {
  let type_ = find_attribute(Str("type"), attributes) // always has type
  let number = if equal(type_, Str("integer")) || equal(type_, Str("float")) {
    get_number()
  } else if equal(type_, Str("constant")) {
    let n = share_mathml_maxima__coerce_string(get_token())
    mathml_constant_to_maxima_constant(n)
  } else {
    // Dunno what we could do here to handle an arbitrary type.
    // For now, just raise an error.
    merr("Unrecognized type ``~a'' in <cn> tag.~%", [type_])
  }
  get_token() |> ignore // skip to >
  number
}

///|
fn ml_ci(attributes : Value) -> Value raise {
  with_specials([(q_parse_tyipeek, Nil), (q_ear_parse_stream, Nil)], () => {
    let type_ = find_attribute(Str("type"), attributes) // may or may not have type
    let a = if equal(type_, Str("constant")) {
      // math constants
      let a = share_mathml_maxima__coerce_string(get_token())
      mathml_constant_to_maxima_constant(a)
    } else {
      // normal identifier
      share_mathml_maxima__read_from_string(
        "$" + share_mathml_maxima__str(share_mathml_maxima__coerce_string(get_token())),
      )
    }
    get_token() |> ignore // skip to >
    a
  })
}

///|
fn mathml_constant_to_maxima_constant(name_string : Value) -> Value raise {
  if equal(name_string, Str("&pi;")) {
    q_d__pctpi
  } else if equal(name_string, Str("&ee;")) {
    q_d__pcte
  } else if equal(name_string, Str("&ii;")) {
    q_d__pcti
  } else if equal(name_string, Str("&gamma;")) {
    sym("$%gamma")
  } else {
    let bare_name = string_left_trim(
      "&",
      string_right_trim(";", share_mathml_maxima__str(name_string)),
    )
    share_mathml_maxima__read_from_string("$" + bare_name)
  }
}

///|
fn get_number() -> Value raise {
  let s = get_str(endc=Char('<'))
  if s.truthy() {
    share_mathml_maxima__read_from_string(share_mathml_maxima__str(s))
  } else {
    Nil
  }
}

///|
/// returns next non-white non #\> char (or -1?)
fn next_char() -> Value raise {
  // Gobble whitespace
  while true {
    let c = tyi(stream=symval(q_ear_in), eof_option=Fix(-1L))
    if !member(
        c,
        list([
          Char('>'),
          Char('\t'),
          Char(' '),
          Char('\n'),
          Char('\r'),
          Char('\x0c'),
        ]),
      ).truthy() {
      return c
    }
  }
  Nil
}

///|
fn share_mathml_maxima__char(c : Value) -> Char raise {
  match c {
    Char(ch) => ch
    _ =>
      raise LispError::SimpleError(
        "The value " + prin1_to_string(c) + " is not of type CHARACTER",
      )
  }
}

///|
fn get_tag(endc? : Value = Char('>')) -> Value raise {
  get_tag_mv(endc~).0
}

///|
/// GET-TAG returns the two values of GET-ATAG: the tag and its attributes.
fn get_tag_mv(endc? : Value = Char('>')) -> (Value, Value) raise {
  let c = next_char()
  if share_mathml_maxima__char(c) != '<' {
    return (Nil, Nil)
  }
  get_atag(endc~)
}

///|
fn get_atag(endc? : Value = Nil) -> (Value, Value) raise {
  let str = get_str(endc~)
  if str is Nil {
    return (Nil, Nil)
  }
  let tag_attributes = share_mathml_maxima__split_string(
    share_mathml_maxima__str(str),
    "\t \n\r\x0c",
  )
  let tag = car(tag_attributes)
  let attributes = mapcar(a => split_attribute(a), cdr(tag_attributes))
  (share_mathml_maxima__read_from_string(share_mathml_maxima__str(tag)), attributes)
}

///|
/// (split-string string bag) from mdebug.lisp: the maximal runs of
/// characters not in BAG.
fn share_mathml_maxima__split_string(s : String, bag : String) -> Value {
  let parts = Collector::new()
  let sb = StringBuilder::new()
  let mut any = false
  for c in string_chars(s) {
    if bag.contains_char(c) {
      if any {
        parts.add(Str(sb.to_string()))
        sb.reset()
        any = false
      }
    } else {
      sb.write_char(c)
      any = true
    }
  }
  if any {
    parts.add(Str(sb.to_string()))
  }
  parts.result()
}

///|
/// Split "FOO=\"BAR\"" into ("FOO" . "BAR")
fn split_attribute(attr_string : Value) -> Value raise {
  let s = share_mathml_maxima__str(attr_string)
  match s.find("=") {
    None => list1(attr_string)
    Some(i) => {
      let name = substring(s, 0, end=i)
      let value = dequotify(Str(substring(s, i + 1)))
      cons(Str(name), value)
    }
  }
}

///|
/// Remove first character and last characters if the first character is
/// a single or double quote and last character is the same as the first.
fn dequotify(s : Value) -> Value raise {
  if s is Nil {
    return s
  }
  let chars = string_chars(share_mathml_maxima__str(s))
  if chars.length() < 2 {
    return s
  }
  let first_char = chars[0]
  let last_char = chars[chars.length() - 1]
  if (first_char == '"' || first_char == '\'') && last_char == first_char {
    let sb = StringBuilder::new()
    for i in 1..<(chars.length() - 1) {
      sb.write_char(chars[i])
    }
    Str(sb.to_string())
  } else {
    s
  }
}

///|
fn find_attribute(attr : Value, attrs_list : Value) -> Value raise {
  cdr(assoc_equal(attr, attrs_list))
}

///|
fn get_str(endc? : Value = Nil) -> Value raise {
  let str = get_token(endc~)
  if str.truthy() {
    share_mathml_maxima__coerce_string(str)
  } else {
    Nil
  }
}

///|
/// returns list of chars for next token
fn get_token(endc? : Value = Nil) -> Value raise {
  // Read at least one char ...
  let in_ = symval(q_ear_in)
  let mut c = tyi(stream=in_, eof_option=Fix(-1L))
  let mut l : Value = Nil
  while true {
    if equal(c, Fix(-1L)) {
      break
    }
    if endc.truthy() && share_mathml_maxima__char(c) == share_mathml_maxima__char(
        endc,
      ) {
      break
    }
    if endc is Nil &&
      member(
        c,
        list([
          Char('<'),
          Char('>'),
          Char('\t'),
          Char(' '),
          Char('\n'),
          Char('\r'),
          Char('\x0c'),
        ]),
      ).truthy() {
      break
    }
    let next = tyi(stream=in_, eof_option=Fix(-1L))
    l = cons(c, l)
    c = next
  }
  nreverse(
    if l.truthy() {
      l
    } else {
      list1(tyi(stream=in_, eof_option=Fix(-1L)))
    },
  )
}

///|
fn get_op() -> Value raise {
  let op = get_tag()
  if eq(op, q_fn) {
    let op = get_str()
    if op is Nil {
      merr("get-op: invalid null function", []) |> ignore
    }
    let opa = share_mathml_maxima__read_from_string(share_mathml_maxima__str(op))
    let opa = get(opa, q_mmfun)
    get_token() |> ignore
    if opa.truthy() {
      return list1(opa)
    }
    return list1(
      share_mathml_maxima__read_from_string("$" + share_mathml_maxima__str(op)),
    )
  } else {
    let proc = get(op, q_mct_proc)
    set(sym("proc"), proc) |> ignore
    if proc.truthy() {
      set(share_mathml_maxima__q_special_proc, proc) |> ignore
      return Nil
    }
  }
  let mop = get(op, q_mmfun)
  if mop.truthy() {
    list1(mop)
  } else {
    list1(op) // should not reach here
  }
}

///|
fn set_table(arg : Value) -> Value raise {
  if length(arg) == 2 {
    let mut a = car(cdr(cadr(arg)))
    let b = caadr(arg)
    if stringp(a) {
      a = share_mathml_maxima__read_from_string(share_mathml_maxima__str(a))
    }
    putprop(a, car(arg), b)
  } else if length(arg) == 3 {
    let arg = cdr(arg)
    let b = car(arg)
    let mut a = cadr(cadr(arg))
    if stringp(a) {
      a = share_mathml_maxima__read_from_string(share_mathml_maxima__str(a))
    }
    putprop(a, cadr(b), car(b))
  } else {
    Nil
  }
}

///|
fn share_mathml_maxima__str(x : Value) -> String raise {
  match x {
    Str(s) => s
    _ => princ_to_string(x)
  }
}

///|
/// (coerce list-of-characters 'string)
fn share_mathml_maxima__coerce_string(l : Value) -> Value raise {
  let sb = StringBuilder::new()
  for c in l.iter() {
    sb.write_char(share_mathml_maxima__char(c))
  }
  Str(sb.to_string())
}

///|
/// READ-FROM-STRING with the Lisp reader (symbol names follow the port's
/// naming convention).
fn share_mathml_maxima__read_from_string(s : String) -> Value raise {
  lread(s)
}

///|
fn init_share_mathml_maxima() -> Unit raise {
  set(q_parse_tyipeek, Nil) |> ignore // look-ahead in nparse.lisp
  defvar_init(q_ear_in, symval(q_ear_parse_stream))
  let s = (x : String) => Value::Str(x)
  let mm = (name : Value, v : String) => set_table(
    list([name, list([q_mmfun, s(v)])]),
  )
  let table : Array[(Value, String)] = [
    (sym("%ln"), "ln/"),
    (q_p_log, "log/"),
    (sym("$sin"), "sin/"),
    (sym("$cos"), "cos/"),
    (sym("$tan"), "tan/"),
    (sym("$cot"), "cot/"),
    (sym("$sec"), "sec/"),
    (sym("$csc"), "csc/"),
    (sym("$asin"), "arcsin/"),
    (sym("$acos"), "arccos/"),
    (sym("$atan"), "arctan/"),
    (sym("$acot"), "acot/"),
    (sym("$asec"), "asec/"),
    (sym("$acsc"), "acsc/"),
    (sym("$sinh"), "sinh/"),
    (sym("$cosh"), "cosh/"),
    (sym("$tanh"), "tanh/"),
    (sym("$coth"), "coth/"),
    (sym("$sech"), "sec/"),
    (sym("$csch"), "csch/"),
    (sym("$asinh"), "asinh/"),
    (sym("$acosh"), "acosh/"),
    (sym("$atanh"), "atanh/"),
    (sym("$acoth"), "acoth/"),
    (sym("$asech"), "asec/"),
    (sym("$acsch"), "acsch/"),
    (sym("$ln"), "ln/"),
    (sym("$log"), "log/"),
    // Operators and functions
    (q_mand, "and/"),
    (q_mor, "or/"),
    (q_mnot, "not/"),
    (q_d_xor, "xor/"),
    (q_mplus, "plus/"),
    (q_mminus, "minus/"),
    (q_d_remainder, "rem/"),
    (q_d_max, "max/"),
    (q_d_min, "min/"),
    (q_mfactorial, "factorial/"),
    (q_mabs, "abs/"),
  ]
  for e in table {
    mm(e.0, e.1) |> ignore
  }
  set_table(list([q_p_abs, list([q_mct_proc, q_abs])])) |> ignore
  let table2 : Array[(Value, String)] = [
    (q_mtimes, "times/"),
    (q_mexpt, "power/"),
    (q_mquotient, "quotient/"),
    (q_p_sqrt, "sqrt/"),
    (q_mquote, "quote/"),
  ]
  for e in table2 {
    mm(e.0, e.1) |> ignore
  }
  let rels : Array[(Value, String)] = [
    (q_mgreaterp, "gt/"),
    (q_mgeqp, "geq/"),
    (q_mequal, "eq/"),
    (q_mnotequal, "neq/"),
    (q_mleqp, "leq/"),
    (q_mlessp, "lt/"),
  ]
  for e in rels {
    set_table(
      list([e.0, list([q_mct_proc, q_relation]), list([q_mmfun, s(e.1)])]),
    )
    |> ignore
  }
  set_table(list([q_mdefine, list([q_mct_proc, q_def_fun])])) |> ignore
  mm(q_msetq, "&Assign;") |> ignore
  let procs : Array[(Value, Value, String)] = [
    (q_p_sum, q_sumprod, "sum/"),
    (q_p_product, q_sumprod, "product/"),
    (q_p_integrate, q_mctintegrate, "int/"),
    (q_d_diff, q_mctdiff, "diff/"),
    (q_d_limit, sym("mctlimit"), "limit/"),
  ]
  for e in procs {
    set_table(list([e.0, list([q_mct_proc, e.1]), list([q_mmfun, s(e.2)])]))
    |> ignore
  }
}
