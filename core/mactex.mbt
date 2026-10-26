// Port of src/mactex.lisp: TeX output of Maxima expressions.
//
// Producing TeX from a macsyma internal expression is done by a reversal of
// the parsing process: a traversal of the expression tree with appropriate
// substitutions and recognition of the infix / prefix / postfix / matchfix
// relations on symbols. The binding powers of the operators decide where
// parentheses must be inserted. `lop` and `rop` are special variables
// holding the operators to the left and right of the current subexpression.

///|
/// A Lisp list of strings.
fn mactex__strs(a : Array[String]) -> Value {
  list(a.map(s => Str(s)))
}

///|
/// `(string x)` as a MoonBit string (strings, symbols, characters).
fn mactex__string(x : Value) -> String raise {
  match x {
    Str(s) => s
    Char(c) => c.to_string()
    Nil => "nil"
    Sym(_) => symbol_name(x)
    _ =>
      match string(x) {
        Str(s) => s
        _ => princ_to_string(x)
      }
  }
}

///|
/// Pathname string of a file designator (string or symbol).
fn mactex__path(x : Value) -> String raise {
  match x {
    Str(s) => s
    _ => mactex__string(x)
  }
}

///|
/// Append `text` to the file `path`, creating it if needed (CL `open`
/// with `:if-exists :append :if-does-not-exist :create`).
fn mactex__append_to_file(path : String, text : String) -> Unit raise {
  let old = if probe_file(path) { read_file(path) } else { "" }
  write_file(path, old + text)
}

///|
fn d_get_tex_environment_default() -> Value raise {
  let e = symval(q_ear_tex_environment_default)
  mk(q_mlist, [car(e), cdr(e)])
}

///|
fn d_get_tex_environment(x : Value) -> Value raise {
  let mut x = x
  if getopr(x).truthy() {
    x = getopr(x)
  }
  let e = get_tex_environment(x)
  mk(q_mlist, [car(e), cdr(e)])
}

///|
fn d_set_tex_environment_default(
  env_open : Value,
  env_close : Value,
) -> Value raise {
  let env_open = d_sconcat(list1(env_open))
  let env_close = d_sconcat(list1(env_close))
  set(q_ear_tex_environment_default, cons(env_open, env_close)) |> ignore
  d_get_tex_environment_default()
}

///|
fn d_set_tex_environment(
  x : Value,
  env_open : Value,
  env_close : Value,
) -> Value raise {
  let env_open = d_sconcat(list1(env_open))
  let env_close = d_sconcat(list1(env_close))
  let mut x = x
  if getopr(x).truthy() {
    x = getopr(x)
  }
  setf_get(x, q_tex_environment, cons(env_open, env_close)) |> ignore
  d_get_tex_environment(x)
}

///|
fn get_tex_environment(x : Value) -> Value raise {
  if symbolp(x) {
    let e = get(x, q_tex_environment)
    if e.truthy() {
      e
    } else {
      symval(q_ear_tex_environment_default)
    }
  } else if atom(x) {
    symval(q_ear_tex_environment_default)
  } else {
    get_tex_environment(caar(x))
  }
}

///|
/// Top level command: the result of tex'ing the expression.
/// If a filename or stream is supplied but it is `false`, return a string.
fn d_tex(l : Value) -> Value raise {
  let args = cdr(l)
  let n = length(args)
  if n != 1 && n != 2 {
    wna_err(q_d_tex) |> ignore
  }
  if cdr(args).truthy() && cadr(args) is Nil {
    let s = make_string_output_stream()
    with_special(standard_output, s, () => {
      tex1(car(args), filename_or_stream=cadr(args)) |> ignore
      Str(get_output_stream_string(s))
    })
  } else {
    tex1(car(args), filename_or_stream=cadr(args))
  }
}

///|
fn quote_chars(sym_ : Value, ch_str : Value) -> Value raise {
  // Lisp: recursively insert a backslash before each character of SYM_
  // that occurs in CH_STR; done here in one linear pass.
  let strsym = mactex__string(sym_)
  let chs = string_chars(mactex__string(ch_str))
  let sb = StringBuilder::new()
  for c in strsym {
    if chs.contains(c) {
      sb.write_char('\\')
    }
    sb.write_char(c)
  }
  Str(sb.to_string())
}

///|
fn quote__pct(sym_ : Value) -> Value raise {
  quote_chars(sym_, Str("$%&_"))
}

///|
fn tex1(mexplabel : Value, filename_or_stream? : Value = Nil) -> Value raise {
  let mut mexplabel = mexplabel
  let mut itsalabel = false
  let mut need_to_close_texport = false
  let mut file_path = ""
  reset_ccol() |> ignore
  // collect the file-name, if any, and open a port if needed
  let filename_or_stream = meval(filename_or_stream)
  let texport = if filename_or_stream is Nil {
    symval(standard_output)
  } else if eq(filename_or_stream, t) {
    symval(standard_output)
  } else if streamp(filename_or_stream) {
    filename_or_stream
  } else {
    need_to_close_texport = true
    file_path = mactex__path(filename_or_stream)
    make_string_output_stream()
  }
  // do a normal evaluation of the expression in macsyma
  let mut mexp = meval(mexplabel)
  if memq(mexplabel, symval(q_d_labels)).truthy() {
    // leave it if it is a label
    mexplabel = Str("(" + mactex__string(stripdollar(mexplabel)) + ")")
    itsalabel = true
  } else {
    mexplabel = Nil
  }
  // maybe it is a function?
  if symbolp(mexp) {
    let x = d_verbify(mexp)
    let y = mget(x, q_mexpr)
    if y.truthy() {
      mexp = list3(list1(q_mdefine), cons(list1(x), cdadr(y)), caddr(y))
    } else {
      let y = mget(x, q_mmacro)
      if y.truthy() {
        mexp = list3(list1(q_mdefmacro), cons(list1(x), cdadr(y)), caddr(y))
      } else {
        let y = mget(x, q_aexpr)
        if y.truthy() {
          mexp = list3(
            list1(q_mdefine),
            cons(list2(x, q_array), cdadr(y)),
            caddr(y),
          )
        }
      }
    }
  }
  let label_is_input = () => {
    let inchar = mactex__string(symval(q_d_inchar))
    let outchar = mactex__string(symval(q_d_outchar))
    let lab = mactex__string(mexplabel)
    let li = string_length(inchar)
    let lo = string_length(outchar)
    let ll = string_length(lab)
    li <= ll &&
    substring(inchar, 1, end=li) == substring(lab, 1, end=li) &&
    !(
      lo <= ll && substring(outchar, 1, end=lo) == substring(lab, 1, end=lo)
    )
  }
  if !atom(mexp) &&
    (eq(caar(mexp), q_mdefine) || eq(caar(mexp), q_mdefmacro)) {
    format(texport, mactex__string(car(get_tex_environment(caar(mexp)))), [])
    |> ignore
    if mexplabel.truthy() {
      format(texport, "~a ", [mexplabel]) |> ignore
    }
    mgrind(mexp, texport) |> ignore
    format(texport, mactex__string(cdr(get_tex_environment(caar(mexp)))), [])
    |> ignore
  } else if itsalabel && label_is_input() {
    // aha, this is a C-line: do the grinding:
    format(texport, mactex__string(car(get_tex_environment(q_mlabel))), [])
    |> ignore
    format(texport, "~a", [mexplabel]) |> ignore
    mgrind(mexp, texport) |> ignore
    format(texport, mactex__string(cdr(get_tex_environment(q_mlabel))), [])
    |> ignore
  } else {
    if mexplabel.truthy() {
      mexplabel = quote__pct(mexplabel)
    }
    // display the expression for TeX now:
    myprinc(car(get_tex_environment(mexp)), texport=texport) |> ignore
    // initially the left and right contexts are empty lists, and there are
    // implicit parens around the whole expression
    for x in tex(mexp, Nil, Nil, q_mparen, q_mparen).iter() {
      myprinc(x, texport=texport) |> ignore
    }
    if mexplabel.truthy() {
      format(texport, "\\leqno{\\tt ~a}", [mexplabel]) |> ignore
    }
    format(texport, mactex__string(cdr(get_tex_environment(mexp))), [])
    |> ignore
  }
  terpri(stream=texport)
  if need_to_close_texport {
    mactex__append_to_file(file_path, get_output_stream_string(texport))
  }
  mexplabel
}

// myprinc is an intelligent low level printing routine. It keeps track of
// the size of the output for purposes of allowing the TeX file to have a
// reasonable line length. myprinc will break it at a space once it crosses
// a threshold.

///|
let mactex__ccol : Ref[Int] = Ref(1)

///|
fn reset_ccol() -> Value raise {
  mactex__ccol.val = 1
  Fix(1L)
}

///|
fn myprinc(chstr : Value, texport? : Value = Nil) -> Value raise {
  let chlst = exploden(chstr)
  if length(chlst) + mactex__ccol.val > to_int(symval(q_d_linel)) &&
    (stringp(chstr) || eq(chstr, sym(" "))) {
    terpri(stream=texport) // would have exceeded the line length
    mactex__ccol.val = 1
    myprinc(Str(" "), texport~) |> ignore // lead off with a space for safety
  }
  let mut colc = mactex__ccol.val
  for ch in chlst.iter() {
    match ch {
      Char(c) => write_char(c, stream=texport)
      _ => write_string(mactex__string(ch), stream=texport)
    }
    colc += 1
  }
  mactex__ccol.val = colc
  Nil
}

///|
/// x is the expression of interest; l is the list of strings to its left,
/// r to its right. lop and rop are the operators on the left and right of
/// x in the tree, and will determine if parens must be inserted.
fn tex(x : Value, l : Value, r : Value, lop : Value, rop : Value) -> Value raise {
  with_specials([(q_lop, lop), (q_rop, rop)], () => {
    let x = nformat(x)
    if atom(x) {
      tex_atom(x, l, r)
    } else if num_le(tex_lbp(caar(x)), tex_rbp(lop)) ||
      num_gt(tex_lbp(rop), tex_rbp(caar(x))) {
      tex_paren(x, l, r)
    } else if memq(q_array, cdar(x)).truthy() {
      // special check needed because macsyma notates arrays peculiarly
      tex_array(x, l, r)
    } else if get(caar(x), q_tex).truthy() {
      // dispatch for object-oriented tex-ifiying
      funcall(get(caar(x), q_tex), [x, l, r])
    } else {
      tex_function(x, l, r, Nil)
    }
  })
}

///|
fn tex_atom(x : Value, l : Value, r : Value) -> Value raise {
  let item = if numberp(x) {
    texnumformat(x)
  } else if symbolp(x) &&
    (get(x, q_texword).truthy() ||
    get(get(x, q_reversealias), q_texword).truthy()) {
    let w = get(x, q_texword)
    if w.truthy() {
      w
    } else {
      get(get(x, q_reversealias), q_texword)
    }
  } else if stringp(x) {
    let s : Value = if symval(q_d_stringdisp).truthy() {
      Str("``" + mactex__string(x) + "''")
    } else {
      x
    }
    tex_string(quote__pct(s))
  } else if characterp(x) {
    tex_char(x)
  } else if symbolp(x) {
    let ra = get(x, q_reversealias)
    tex_stripdollar(if ra.truthy() { ra } else { x })
  } else {
    let ty = marray_type(x)
    let s = if eq(ty, q_array) || eq(ty, q_hash_table) || eq(ty, q_d_functional) {
      d_sconcat(list1(x))
    } else {
      format(Nil, "~A", [x])
    }
    // Do not apply stringdisp here -- we are outputting a string only
    // because we don't have a better way to handle Lisp arrays.
    tex_string(quote_chars(s, Str("#$%&_")))
  }
  append(l, cons(item, r))
}

///|
fn tex_string(x : Value) -> Value raise {
  let s = mactex__string(x)
  if s == "" {
    Str("")
  } else if char_at(s, 0) == '\\' {
    x
  } else {
    Str("\\mbox{ " + s + " }")
  }
}

///|
fn tex_char(x : Value) -> Value raise {
  match x {
    Char('|') => Str("\\mbox{\\verb/|/}")
    _ => Str("\\mbox{\\verb|" + mactex__string(x) + "|}")
  }
}

///|
/// Read forms from file F1 and output them to F2.
fn tex_forms(f1 : Value, f2 : Value) -> Value raise {
  let st = open_input_file(mactex__path(f1))
  while true {
    let tem = mread_raw(st, ear_mread_eof_obj=Nil)
    if tem is Nil {
      break
    }
    tex1(third(tem), filename_or_stream=f2) |> ignore
  }
  Nil
}

///|
/// Detect and extract groups of trailing digits, e.g. foo_mm_nn, and then
/// punt foo[mm, nn] to TEX-ARRAY. Otherwise, treat SYM as a simple symbol.
fn tex_stripdollar(sym_ : Value) -> Value raise {
  let nn_list = extract_trailing_digits(Str(symbol_name(sym_)))
  if nn_list.truthy() {
    // If SYM matches $%I[_0-9]+, then we should not treat it as a
    // subscripted imaginary sqrt(-1)=$%I. Wrap %I in braces {} in order to
    // avoid this.
    if mactex__string(car(nn_list)) == "$%i" {
      rplaca(nn_list, Str("{%i}")) |> ignore
    }
    // SYM matches foo_mm_nn.
    let head = list2(sym(mactex__string(first(nn_list))), list2(q_quote, q_array))
    let parts = tex_array(cons(head, rest(nn_list)), Nil, Nil)
    let sb = StringBuilder::new()
    for p in parts.iter() {
      sb.write_string(mactex__string(p))
    }
    Str(sb.to_string())
  } else {
    // SYM is a simple symbol.
    let s = mactex__string(quote__pct(stripdollar(sym_)))
    if string_length(s) > 1 {
      Str("{\\it " + s + "}")
    } else {
      Str(s)
    }
  }
}

///|
fn mactex__all_digits(s : String, from : Int) -> Bool {
  let cs = string_chars(s)
  if from >= cs.length() {
    return false
  }
  for i in from..<cs.length() {
    let c = cs[i]
    if c < '0' || c > '9' {
      return false
    }
  }
  true
}

///|
/// Given a string foo_mm_nn, return foo, mm, and nn, where mm and nn are
/// integers (not strings of digits). Return NIL if argument doesn't have
/// trailing digits.
fn extract_trailing_digits(s : Value) -> Value raise {
  let mut s = mactex__string(s)
  let mut nn_list : Value = Nil
  while true {
    let n = string_length(s)
    let mut found = false
    // "[^_](__*)([0-9][0-9]*)$"
    for p in 0..<n {
      if char_at(s, p) != '_' && p + 1 < n && char_at(s, p + 1) == '_' {
        let mut q = p + 1
        while q < n && char_at(s, q) == '_' {
          q += 1
        }
        if mactex__all_digits(s, q) {
          let nn = substring(s, q)
          s = substring(s, 0, end=p + 1)
          nn_list = cons(parse_integer(nn).unwrap_or(Nil), nn_list)
          found = true
          break
        }
      }
    }
    if !found {
      // "[^_]([0-9][0-9]*)$"
      for p in 0..<n {
        if char_at(s, p) != '_' && mactex__all_digits(s, p + 1) {
          let nn = substring(s, p + 1)
          s = substring(s, 0, end=p + 1)
          nn_list = cons(parse_integer(nn).unwrap_or(Nil), nn_list)
          found = true
          break
        }
      }
    }
    if !found {
      break
    }
  }
  if nn_list.truthy() {
    cons(Str(s), nn_list)
  } else {
    Nil
  }
}

///|
fn strcat(args : Value) -> Value raise {
  let sb = StringBuilder::new()
  for a in args.iter() {
    sb.write_string(mactex__string(a))
  }
  Str(sb.to_string())
}

///|
/// Convert 1.2e20 to 1.2 \times 10^{20}.
fn texnumformat(atom_ : Value) -> Value raise {
  if integerp(atom_) {
    Str(char_list_to_string(exploden(atom_)))
  } else {
    let r = exploden(atom_)
    let is_e = (c : Value) => match c {
      Char('e') | Char('E') => true
      _ => false
    }
    // is it ddd.ddde+EE
    let mut exponent = r
    while exponent.truthy() && !is_e(car(exponent)) {
      exponent = cdr(exponent)
    }
    if exponent is Nil {
      Str(char_list_to_string(r))
    } else {
      let mut rr = reverse(r)
      while rr.truthy() && !is_e(car(rr)) {
        rr = cdr(rr)
      }
      let firstpart = nreverse(cdr(rr))
      strcat(
        list([
          strcat(firstpart),
          Str(" \\times 10^{"),
          strcat(cdr(exponent)),
          Str("}"),
        ]),
      )
    }
  }
}

///|
fn tex_paren(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    x,
    append(l, mactex__strs(["\\left("])),
    cons(Str("\\right)"), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn tex_array(x : Value, l : Value, r : Value) -> Value raise {
  tex_array_display_indices(x, l, r)
}

///|
fn tex_array_display_indices(x : Value, l : Value, r : Value) -> Value raise {
  let base_symbol = caar(x)
  let indices = cdr(x)
  let display_indices = safe_mget(base_symbol, q_display_indices)
  if display_indices is Nil || length(display_indices) != length(indices) {
    // Ignore DISPLAY-INDICES if it's empty, or nonempty and not the same
    // size as INDICES.
    tex_array_simple(x, l, r)
  } else {
    let pre_subscripts = extract_indices(
      indices, display_indices, q_d_presubscript,
    )
    let pre_superscripts = extract_indices(
      indices, display_indices, q_d_presuperscript,
    )
    let post_subscripts = extract_indices(
      indices, display_indices, q_d_postsubscript,
    )
    let post_superscripts = extract_indices(
      indices, display_indices, q_d_postsuperscript,
    )
    let close = mactex__strs(["}"])
    let mut l = l
    let mut r = r
    if pre_subscripts.truthy() || pre_superscripts.truthy() {
      l = append_n([
        l,
        mactex__strs(["{}"]),
        if pre_subscripts.truthy() {
          cons(Str("_{"), tex_list(pre_subscripts, Nil, close, Str(",")))
        } else {
          Nil
        },
        if pre_superscripts.truthy() {
          cons(Str("^{"), tex_list(pre_superscripts, Nil, close, Str(",")))
        } else {
          Nil
        },
      ])
    }
    if post_subscripts.truthy() || post_superscripts.truthy() {
      r = append_n([
        if post_subscripts.truthy() {
          cons(
            Str("_{"),
            tex_list(post_subscripts, Nil, mactex__strs(["}"]), Str(",")),
          )
        } else {
          Nil
        },
        if post_superscripts.truthy() {
          cons(
            Str("^{"),
            tex_list(post_superscripts, Nil, mactex__strs(["}"]), Str(",")),
          )
        } else {
          Nil
        },
        r,
      ])
    }
    tex_atom(base_symbol, l, r)
  }
}

///|
fn tex_array_simple(x : Value, l : Value, r : Value) -> Value raise {
  let mut x = x
  let mut l = l
  // I believe this test always fails; TEX-MQAPPLY calls TEX-ARRAY w/ X =
  // second argument of MQAPPLY.
  if eq(caar(x), q_mqapply) {
    let f = cadr(x)
    x = cdr(x)
    l = tex(
      f,
      append(l, mactex__strs(["\\left("])),
      mactex__strs(["\\right)"]),
      q_mparen,
      q_mparen,
    )
  } else {
    let f = caar(x)
    l = tex(f, l, Nil, symval(q_lop), q_mfunction)
  }
  let r = nconc(tex_list(cdr(x), Nil, mactex__strs(["}"]), Str(",")), r)
  nconc(l, cons(Str("_{"), r))
}

///|
fn tex_function(x : Value, l : Value, r : Value, op : Value) -> Value raise {
  ignore(op)
  let l = tex(caar(x), l, Nil, q_mparen, q_mparen)
  let r = tex(cons(list1(q_mprogn), cdr(x)), Nil, r, q_mparen, q_mparen)
  nconc(l, r)
}

///|
/// Set up a list, separated by symbols (, * ...) and then tack on the
/// ending item (e.g. "]" or perhaps ")").
fn tex_list(x : Value, l : Value, r : Value, sym_ : Value) -> Value raise {
  if x is Nil {
    return r
  }
  let mut x = x
  let mut l = l
  let mut nl : Value = Nil
  while cdr(x).truthy() {
    nl = nconc(nl, tex(car(x), l, list1(sym_), q_mparen, q_mparen))
    x = cdr(x)
    l = Nil
  }
  nconc(nl, tex(car(x), l, r, q_mparen, q_mparen))
}

///|
fn tex_prefix(x : Value, l : Value, r : Value) -> Value raise {
  tex(cadr(x), append(l, texsym(caar(x))), r, caar(x), symval(q_rop))
}

///|
fn tex_infix(x : Value, l : Value, r : Value) -> Value raise {
  twoargcheck(x) |> ignore
  let l = tex(cadr(x), l, Nil, symval(q_lop), caar(x))
  tex(caddr(x), append(l, texsym(caar(x))), r, caar(x), symval(q_rop))
}

///|
fn tex_postfix(x : Value, l : Value, r : Value) -> Value raise {
  tex(cadr(x), l, append(texsym(caar(x)), r), symval(q_lop), caar(x))
}

///|
fn tex_nary(x : Value, l : Value, r : Value) -> Value raise {
  let op = caar(x)
  let sym_ = texsym(op)
  let mut y = cdr(x)
  let ext_lop = symval(q_lop)
  let ext_rop = symval(q_rop)
  if y is Nil {
    tex_function(x, l, r, t) // this should not happen
  } else if cdr(y) is Nil {
    tex_function(x, l, r, t) // this should not happen, too
  } else {
    let mut nl : Value = Nil
    let mut l = l
    let mut lop = ext_lop
    let mut rop = op
    while cdr(y).truthy() {
      nl = append(nl, tex(car(y), l, sym_, lop, rop))
      y = cdr(y)
      l = Nil
      lop = op
      rop = if cdr(y) is Nil { ext_rop } else { op }
    }
    append(nl, tex(car(y), l, r, lop, rop))
  }
}

///|
fn tex_nofix(x : Value, l : Value, r : Value) -> Value raise {
  tex(car(texsym(caar(x))), l, r, caar(x), symval(q_rop))
}

///|
fn tex_matchfix(x : Value, l : Value, r : Value) -> Value raise {
  // car of texsym of a matchfix operator is the lead op
  let l = append(l, car(texsym(caar(x))))
  // cdr is the trailing op
  let r = append(list1(nth(1, texsym(caar(x)))), r)
  let sep = {
    let s = nth(2, texsym(caar(x)))
    if s.truthy() {
      s
    } else {
      Str(" , ")
    }
  }
  let x = tex_list(cdr(x), Nil, r, sep)
  append(l, x)
}

///|
fn texsym(x : Value) -> Value raise {
  let a = get(x, q_texsym)
  if a.truthy() {
    return a
  }
  let b = get(x, q_strsym)
  if b.truthy() {
    return b
  }
  let c = get(x, q_dissym)
  if c.truthy() {
    return c
  }
  stripdollar(x)
}

///|
fn texword(x : Value) -> Value raise {
  let a = get(x, q_texword)
  if a.truthy() {
    a
  } else {
    stripdollar(x)
  }
}

///|
/// For 1.2345b678, generate TeX output 1.2345_B \times 10^{678}.
/// If the exponent is 0, then ... \times 10^{0} is generated (no attempt to
/// strip off zero exponent).
fn tex_bigfloat(x : Value, l : Value, r : Value) -> Value raise {
  let formatted = fpformat(x)
  let lb = sym("B") // CL |b|
  let ub = sym("b") // CL |B|
  // There should always be a '|b| or '|B| in the FPFORMAT output.
  // Play it safe -- check anyway.
  if find(lb, formatted).truthy() || find(ub, formatted).truthy() {
    let c = Collector::new()
    for e in formatted.iter() {
      if eq(e, lb) || eq(e, ub) {
        c.append_list(
          list([Str("_B"), sym(" "), Str("\\times"), sym(" "), Str("10^{")]),
        )
      } else {
        c.add(e)
      }
    }
    c.add(sym("}"))
    append_n([l, c.result(), r])
  } else {
    append_n([l, formatted, r])
  }
}

///|
fn tex_mqapply(x : Value, l : Value, r : Value) -> Value raise {
  let l = tex(cadr(x), l, mactex__strs(["("]), symval(q_lop), q_mfunction)
  let r = tex_list(cddr(x), Nil, cons(Str(")"), r), Str(","))
  append(l, r)
}

///|
fn tex_gamma(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    cadr(x),
    append(l, mactex__strs(["\\Gamma\\left("])),
    append(mactex__strs(["\\right)"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
/// If the number contains a exponent marker when printed, we need to put
/// parens around it.
fn numneedsparen(number : Value) -> Value raise {
  if integerp(number) {
    return Nil
  }
  let mut r = exploden(number)
  while r.truthy() {
    match car(r) {
      Char('e') | Char('E') => return r
      _ => ()
    }
    r = cdr(r)
  }
  Nil
}

///|
fn tex_mexpt_trig_like_fn_p(f : Value) -> Value raise {
  memq(f, symval(q_ear_tex_mexpt_trig_like_fns))
}

///|
/// Here is where we have to check for f(x)^b to be displayed as f^b(x), as
/// is the case for sin(x)^2, which should be sin^2 x rather than (sin x)^2
/// or (sin(x))^2; yet we must not display (a+b)^2 as +^2(a,b)... or
/// (sin(x))^(-1) as sin^(-1)x, which would be arcsine x.
fn maybe_tex_mexpt_trig_like(x : Value, l : Value, r : Value) -> Value raise {
  let fx = cadr(x) // this is f(x)
  let f = if !atom(fx) && atom(caar(fx)) { caar(fx) } else { Nil } // this is f [or nil]
  let bascdr = if f.truthy() { cdr(fx) } else { Nil } // this is (x) [maybe (x,y..), or nil]
  let expon = caddr(x) // this is the exponent
  let doit = f.truthy() &&
    tex_mexpt_trig_like_fn_p(f).truthy() &&
    (match get_first_char(f) {
      Char('%') | Char('$') => true
      _ => false
    }) &&
    memq(q_array, cdar(fx)) is Nil &&
    (
      (atom(expon) && !numberp(expon)) ||
      (atom(expon) && numberp(expon) && num_gt(expon, Fix(0L)))
    )
  if doit {
    let l = tex(mk(q_mexpt, [f, expon]), l, Nil, q_mparen, q_mparen)
    let r = if cdr(bascdr) is Nil && eq(get(f, q_tex), q_tex_prefix) {
      tex(car(bascdr), Nil, r, f, q_mparen)
    } else {
      tex(cons(list1(q_mprogn), bascdr), Nil, r, q_mparen, q_mparen)
    }
    append(l, r)
  } else {
    Nil
  }
}

///|
/// Insert left-angle-brackets for mncexpt. a^<n> is how a^^n looks.
fn tex_mexpt(x : Value, l : Value, r : Value) -> Value raise {
  let nc = eq(caar(x), q_mncexpt) // true if a^^b rather than a^b
  if eq(caar(x), q_mexpt) {
    let v = maybe_tex_mexpt_trig_like(x, l, r)
    if v.truthy() {
      return v
    }
  }
  let base = cadr(x)
  let l = if d_bfloatp(base).truthy() ||
    (numberp(base) && numneedsparen(base).truthy()) {
    tex(
      base,
      append(l, mactex__strs(["\\left("])),
      mactex__strs(["\\right)"]),
      symval(q_lop),
      caar(x),
    )
  } else {
    tex(base, l, Nil, symval(q_lop), caar(x))
  }
  let x = nformat(caddr(x))
  let r = if mmminusp(x).truthy() {
    // the change in base-line makes parens unnecessary
    if nc {
      tex(
        cadr(x),
        mactex__strs(["^ {-\\langle "]),
        cons(Str("\\rangle }"), r),
        q_mparen,
        q_mparen,
      )
    } else {
      tex(cadr(x), mactex__strs(["^ {- "]), cons(Str(" }"), r), q_mminus, q_mparen)
    }
  } else if nc {
    tex(
      x,
      mactex__strs(["^{\\langle "]),
      cons(Str("\\rangle}"), r),
      q_mparen,
      q_mparen,
    )
  } else if integerp(x) && num_lt(x, Fix(10L)) {
    tex(x, mactex__strs(["^"]), cons(Str(""), r), q_mparen, q_mparen)
  } else {
    tex(x, mactex__strs(["^{"]), cons(Str("}"), r), q_mparen, q_mparen)
  }
  append(l, r)
}

///|
/// Format as \sqrt { } assuming implicit parens for sqr grouping.
fn tex_sqrt(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    cadr(x),
    append(l, mactex__strs(["\\sqrt{"])),
    append(mactex__strs(["}"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
/// Macsyma doesn't know about cube (or nth) roots, but if it did, this is
/// what it would look like.
fn tex_cubrt(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    cadr(x),
    append(l, mactex__strs(["\\root 3 \\of{"])),
    append(mactex__strs(["}"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn tex_mquotient(x : Value, l : Value, r : Value) -> Value raise {
  twoargcheck(x) |> ignore
  // the divide bar groups things
  let l = tex(cadr(x), append(l, mactex__strs(["{{"])), Nil, q_mparen, q_mparen)
  let r = tex(
    caddr(x),
    mactex__strs(["}\\over{"]),
    append(mactex__strs(["}}"]), r),
    q_mparen,
    q_mparen,
  )
  append(l, r)
}

///|
/// TeX dialects either offer a \pmatrix command or a pmatrix environment
/// so we let the TeX decide which one to use.
fn tex_matrix(x : Value, l : Value, r : Value) -> Value raise {
  let rows = mapcan(
    y => tex_list(cdr(y), Nil, mactex__strs(["\\cr "]), Str("&")),
    cdr(x),
  )
  append_n([
    l,
    mactex__strs(["\\ifx\\endpmatrix\\undefined\\pmatrix{\\else\\begin{pmatrix}\\fi "]),
    rows,
    mactex__strs(["\\ifx\\endpmatrix\\undefined}\\else\\end{pmatrix}\\fi "]),
    r,
  ])
}

///|
fn tex_lsum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_lsum) { Str("\\sum_{") } else { Nil }
  // 4th arg of tex is changed from mparen to (caar x) to reflect the
  // operator precedence correctly.
  let s1 = tex(cadr(x), Nil, Nil, caar(x), symval(q_rop)) // summand
  let index = tex(
    mk_simp(q_min, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  append_n([
    l,
    list1(op),
    index,
    mactex__strs(["}}{"]),
    s1,
    mactex__strs(["}"]),
    r,
  ])
}

///|
fn tex_sum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_sum) {
    Str("\\sum_{")
  } else if eq(caar(x), q_p_product) {
    Str("\\prod_{")
  } else {
    Nil
  }
  let s1 = tex(cadr(x), Nil, Nil, caar(x), symval(q_rop)) // summand
  let index = tex(
    mk_simp(q_mequal, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  let toplim = tex(car(cddddr(x)), Nil, Nil, q_mparen, q_mparen)
  append_n([
    l,
    list1(op),
    index,
    mactex__strs(["}^{"]),
    toplim,
    mactex__strs(["}{"]),
    s1,
    mactex__strs(["}"]),
    r,
  ])
}

///|
fn tex_int(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, q_mparen) // integrand delims / & d
  let var_ = tex(caddr(x), Nil, Nil, q_mparen, symval(q_rop)) // variable
  if length(x) == 3 {
    append_n([
      l,
      mactex__strs(["\\int {"]),
      s1,
      mactex__strs(["}{\\;d"]),
      var_,
      mactex__strs(["}"]),
      r,
    ])
  } else {
    // presumably length 5
    let low = tex(nth(3, x), Nil, Nil, q_mparen, q_mparen)
    let hi = tex(nth(4, x), Nil, Nil, q_mparen, q_mparen)
    append_n([
      l,
      mactex__strs(["\\int_{"]),
      low,
      mactex__strs(["}^{"]),
      hi,
      mactex__strs(["}{"]),
      s1,
      mactex__strs(["\\;d"]),
      var_,
      mactex__strs(["}"]),
      r,
    ])
  }
}

///|
fn tex_limit(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // limit function
  let direction = fifth(x)
  // the thing underneath "limit"
  let arrow = if eq(direction, q_d_plus) {
    "\\downarrow "
  } else if eq(direction, q_d_minus) {
    "\\uparrow "
  } else {
    "\\rightarrow "
  }
  let subfun = subst(
    Str(arrow),
    sym("="),
    tex(mk_simp(q_mequal, [caddr(x), cadddr(x)]), Nil, Nil, q_mparen, q_mparen),
  )
  append_n([
    l,
    mactex__strs(["\\lim_{"]),
    subfun,
    mactex__strs(["}{"]),
    s1,
    mactex__strs(["}"]),
    r,
  ])
}

///|
/// e.g. at(diff(f(x)),x=a)
fn tex_at(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, symval(q_lop), symval(q_rop))
  let sub = tex(caddr(x), Nil, Nil, q_mparen, q_mparen)
  append_n([
    l,
    mactex__strs(["\\left."]),
    s1,
    mactex__strs(["\\right|_{"]),
    sub,
    mactex__strs(["}"]),
    r,
  ])
}

///|
/// e.g. 'at_difference(f(x), x, a, b)
fn tex_at_difference(e : Value, l : Value, r : Value) -> Value raise {
  let f = first(rest(e))
  let x = second(rest(e))
  let a = third(rest(e))
  let b = fourth(rest(e))
  let tex_f = tex(f, Nil, Nil, symval(q_lop), symval(q_rop))
  let tex_sub = tex(mk(q_mequal, [x, a]), Nil, Nil, q_mparen, q_mparen)
  let tex_sup = tex(mk(q_mequal, [x, b]), Nil, Nil, q_mparen, q_mparen)
  append_n([
    l,
    mactex__strs(["\\left."]),
    tex_f,
    mactex__strs(["\\right|_{"]),
    tex_sub,
    mactex__strs(["}^{"]),
    tex_sup,
    mactex__strs(["}"]),
    r,
  ])
}

///|
/// \boxed is defined in amsmath.sty.
fn tex_mbox(x : Value, l : Value, r : Value) -> Value raise {
  append_n([
    l,
    mactex__strs(["\\boxed{"]),
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    mactex__strs(["}"]),
    r,
  ])
}

///|
fn tex_mlabox(x : Value, l : Value, r : Value) -> Value raise {
  append_n([
    l,
    mactex__strs(["\\stackrel{"]),
    tex(caddr(x), Nil, Nil, q_mparen, q_mparen),
    mactex__strs(["}{\\boxed{"]),
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    mactex__strs(["}}"]),
    r,
  ])
}

///|
/// Binomial coefficients.
fn tex_choose(x : Value, l : Value, r : Value) -> Value raise {
  append_n([
    l,
    mactex__strs(["{{"]),
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    mactex__strs(["}\\choose{"]),
    tex(caddr(x), Nil, Nil, q_mparen, q_mparen),
    mactex__strs(["}}"]),
    r,
  ])
}

///|
fn tex_rat(x : Value, l : Value, r : Value) -> Value raise {
  tex_mquotient(x, l, r)
}

///|
fn tex_mplus(x : Value, l : Value, r : Value) -> Value raise {
  let mut r = r
  if memq(q_trunc, car(x)).truthy() {
    r = cons(Str("+\\cdots "), r)
  }
  if cddr(x) is Nil {
    if cdr(x) is Nil {
      tex_function(x, l, r, t)
    } else {
      tex(cadr(x), append(l, mactex__strs(["+"])), r, q_mplus, symval(q_rop))
    }
  } else {
    let l0 = tex(cadr(x), l, Nil, symval(q_lop), q_mplus)
    let mut x = cddr(x)
    let mut nl = l0
    while true {
      let (term, dissym) = if mmminusp(car(x)).truthy() {
        (cadar(x), mactex__strs(["-"]))
      } else {
        (car(x), mactex__strs(["+"]))
      }
      if cdr(x) is Nil {
        let r = tex(term, dissym, r, q_mplus, symval(q_rop))
        return append(nl, r)
      }
      nl = append(nl, tex(term, dissym, Nil, q_mplus, q_mplus))
      x = cdr(x)
    }
    Nil
  }
}

///|
/// Make sin(x) display as sin x, but sin(x+y) as sin(x+y), etc.
fn tex_setup(x : Value) -> Value raise {
  let a = car(x)
  let b = cadr(x)
  setf_get(a, q_tex, q_tex_prefix) |> ignore
  setf_get(a, q_texword, b) |> ignore // This means "sin" will always be roman
  setf_get(a, q_texsym, list1(b)) |> ignore
  setf_get(a, q_tex_rbp, Fix(130L))
}

///|
fn tex_derivative(x : Value, l : Value, r : Value) -> Value raise {
  let e = if symval(q_d_derivabbrev).truthy() {
    tex_dabbrev(x)
  } else {
    tex_d(x, dim_derivative_sym(x, q_d_d, Str("\\partial")))
  }
  tex(e, l, r, symval(q_lop), symval(q_rop))
}

///|
/// Format the macsyma derivative form so it looks sort of like a quotient
/// times the deriva-dand. dsym should be $d or "\\partial".
fn tex_d(x : Value, dsym : Value) -> Value raise {
  let arg_ = cadr(x) // the function being differentiated
  let difflist = cddr(x) // list of derivs e.g. (x 1 y 2)
  let ords = odds(difflist, Fix(0L)) // e.g. (1 2)
  let vars = odds(difflist, Fix(1L)) // e.g. (x y)
  let numer = mk(q_mexpt, [dsym, cons(list1(q_mplus), ords)]) // d^n numerator
  let c = Collector::new()
  let mut vs = vars
  let mut os = ords
  while vs.truthy() && os.truthy() {
    c.add(dsym)
    c.add(simplifya(mk(q_mexpt, [car(vs), car(os)]), Nil))
    vs = cdr(vs)
    os = cdr(os)
  }
  let denom = cons(list1(q_mtimes), c.result())
  mk(q_mtimes, [mk(q_mquotient, [simplifya(numer, Nil), denom]), arg_])
}

///|
/// Format diff(f,x,1,y,1) so that it looks like f subscripted by x y.
fn tex_dabbrev(x : Value) -> Value raise {
  let arg_ = cadr(x) // the function being differentiated
  let difflist = cddr(x) // list of derivs e.g. (x 1 y 2)
  let ords = odds(difflist, Fix(0L)) // e.g. (1 2)
  let vars = odds(difflist, Fix(1L)) // e.g. (x y)
  let head = if symbolp(arg_) {
    list1(list2(arg_, q_array))
  } else {
    list2(list2(q_mqapply, q_array), arg_)
  }
  let tail = if length(vars) == 1 && num_eq(car(ords), Fix(1L)) {
    vars
  } else {
    let c = Collector::new()
    let mut vs = vars
    let mut os = ords
    while vs.truthy() && os.truthy() {
      for _ in 0..<to_int(car(os)) {
        c.add(car(vs))
      }
      vs = cdr(vs)
      os = cdr(os)
    }
    list1(cons(list1(q_mtimes), c.result()))
  }
  append(head, tail)
}

///|
fn odds(list_ : Value, c : Value) -> Value raise {
  let start = if eql(c, Fix(1L)) {
    list_ // get the odd terms (first, third...)
  } else if eql(c, Fix(0L)) {
    cdr(list_) // get the (second, fourth ... ) element
  } else {
    raise LispError::SimpleError("ODDS: fell through ECASE expression; wanted one of (1 0)")
  }
  let col = Collector::new()
  let mut e = start
  while e.truthy() {
    col.add(car(e))
    e = cddr(e)
  }
  col.result()
}

///|
fn mactex__mcond_recurse(x : Value, l : Value, r : Value) -> Value raise {
  let tail = cddr(x)
  let ends = tail is Nil ||
    equal(tail, list2(t, Nil)) ||
    equal(tail, list2(t, q_d_false))
  append(
    tex(car(x), l, mactex__strs(["\\;\\mathbf{then}\\;"]), q_mparen, q_mparen),
    if ends {
      tex(second(x), Nil, r, q_mcond, symval(q_rop))
    } else if eq(third(x), t) && nthcdr(4, x) is Nil {
      append(
        tex(second(x), Nil, Nil, q_mparen, q_mparen),
        tex(
          fourth(x),
          mactex__strs(["\\;\\mathbf{else}\\;"]),
          r,
          q_mcond,
          symval(q_rop),
        ),
      )
    } else {
      append(
        tex(second(x), Nil, Nil, q_mparen, q_mparen),
        mactex__mcond_recurse(
          cddr(x),
          mactex__strs(["\\;\\mathbf{elseif}\\;"]),
          r,
        ),
      )
    },
  )
}

///|
/// The format of MCOND expressions is documented above the definition of
/// DIM-MCOND in displa.lisp. Like DIM-MCOND, the final "else" is omitted
/// when it is `false` or missing.
fn tex_mcond(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    mactex__mcond_recurse(cdr(x), mactex__strs(["\\mathbf{if}\\;"]), r),
  )
}

///|
fn tex_lbp(x : Value) -> Value raise {
  let v = get(x, q_tex_lbp)
  if v.truthy() {
    v
  } else {
    lbp(x)
  }
}

///|
fn tex_rbp(x : Value) -> Value raise {
  let v = get(x, q_tex_rbp)
  if v.truthy() {
    v
  } else {
    rbp(x)
  }
}

///|
fn tex_mdo(x : Value, l : Value, r : Value) -> Value raise {
  tex_list(texmdo(x), l, r, Str("\\;"))
}

///|
fn tex_mdoin(x : Value, l : Value, r : Value) -> Value raise {
  tex_list(texmdoin(x), l, r, Str("\\;"))
}

///|
fn mactex__mdo_tail(x : Value) -> Value raise {
  let thru = if nth(5, x).truthy() {
    list2(Str("\\mathbf{thru}"), nth(5, x))
  } else {
    Nil
  }
  let cond_ = nth(6, x)
  let wh : Value = if cond_ is Nil {
    Nil
  } else if eq(caar(cond_), q_mnot) {
    list2(Str("\\mathbf{while}"), cadr(cond_))
  } else {
    list2(Str("\\mathbf{unless}"), cond_)
  }
  nconc_n([thru, wh, list2(Str("\\mathbf{do}"), nth(7, x))])
}

///|
fn texmdo(x : Value) -> Value raise {
  let for_ = if second(x).truthy() {
    list2(Str("\\mathbf{for}"), second(x))
  } else {
    Nil
  }
  let from : Value = if equal(Fix(1L), third(x)) {
    Nil
  } else if third(x).truthy() {
    list2(Str("\\mathbf{from}"), third(x))
  } else {
    Nil
  }
  let step : Value = if equal(Fix(1L), fourth(x)) {
    Nil
  } else if fourth(x).truthy() {
    list2(Str("\\mathbf{step}"), fourth(x))
  } else if fifth(x).truthy() {
    list2(Str("\\mathbf{next}"), fifth(x))
  } else {
    Nil
  }
  nconc_n([for_, from, step, mactex__mdo_tail(x)])
}

///|
fn texmdoin(x : Value) -> Value raise {
  nconc(
    list([Str("\\mathbf{for}"), second(x), Str("\\mathbf{in}"), third(x)]),
    mactex__mdo_tail(x),
  )
}

///|
fn tex_try_sym(x : Value) -> Value raise {
  if symbolp(x) {
    let tx = get(x, q_texsym)
    if tx.truthy() {
      tx
    } else {
      x
    }
  } else {
    x
  }
}

///|
fn tex_mtext(x : Value, l : Value, r : Value) -> Value raise {
  tex_list(mapcar(e => tex_try_sym(e), cdr(x)), l, r, Str(""))
}

///|
fn tex_mlabel(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    caddr(x),
    append(
      l,
      if cadr(x).truthy() {
        list1(
          format(Nil, "\\mbox{\\tt\\red(~A) \\black}", [
            tex_stripdollar(cadr(x)),
          ]),
        )
      } else {
        Nil
      },
    ),
    r,
    q_mparen,
    q_mparen,
  )
}

///|
fn tex_spaceout(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    cons(format(Nil, "\\hspace{~dmm}", [num_mul(Fix(3L), cadr(x))]), r),
  )
}

///|
/// Run some code initialize file before $tex is run.
fn d_texinit(file : Value) -> Value raise {
  ignore(file)
  q_d_done
}

///|
/// This just prints a \end on the file.
fn d_texend(filename : Value) -> Value raise {
  mactex__append_to_file(mactex__path(stripdollar(filename)), "\\end\n")
  q_d_done
}

///|
/// Construct a Lisp function and attach it to the TEX property of operator
/// OP. The constructed function calls a Maxima function F to generate TeX
/// output for OP. F must take 1 argument (an expression which has operator
/// OP) and must return a string (the TeX output).
fn make_maxima_tex_glue(op : Value, f : Value, previous_f : Value) -> Value raise {
  let glue_f = gensym(prefix="tex-glue-")
  defun(glue_f, args => {
    let x = arg(args, 0)
    let l = arg(args, 1)
    let r = arg(args, 2)
    let f_x = mfuncall(f, list1(x))
    if stringp(f_x) {
      append(l, cons(f_x, r))
    } else if f_x is Nil {
      if previous_f.truthy() {
        funcall(previous_f, [x, l, r])
      } else {
        tex_function(x, l, r, Nil)
      }
    } else {
      merr(
        "tex: function ~s returned something other than a string or 'false'.~%",
        [d_sconcat(list1(f))],
      )
    }
  })
  setf_get(op, q_tex, glue_f) |> ignore
  f
}

///|
/// Convenience function to allow user to process expression X and get a
/// string (TeX output for X) in return.
fn d_tex1(x : Value) -> Value raise {
  let parts = tex(x, Nil, Nil, q_mparen, q_mparen)
  if parts is Nil {
    strcat(Nil)
  } else {
    let mut acc = car(parts)
    for p in cdr(parts).iter() {
      acc = strcat(list2(acc, p))
    }
    acc
  }
}

///|
/// A TeX control word is a backslash followed by letters, and it swallows
/// any letters that follow it. Strings arriving through texput get a
/// trailing space so that e.g. texput("-->", "\\rightarrow", infix)
/// produces TeX that compiles.
fn tex_space_after_control_word(s : Value) -> Value raise {
  match s {
    Str(str) if string_length(str) > 0 &&
      alpha_char_p(char_at(str, string_length(str) - 1)) => {
      let n = string_length(str)
      let mut bs = -1
      for i = n - 1; i >= 0; i = i - 1 {
        if char_at(str, i) == '\\' {
          bs = i
          break
        }
      }
      if bs >= 0 && bs + 1 < n {
        let mut all_alpha = true
        for i in (bs + 1)..<n {
          if !alpha_char_p(char_at(str, i)) {
            all_alpha = false
            break
          }
        }
        if all_alpha {
          Str(str + " ")
        } else {
          s
        }
      } else {
        s
      }
    }
    _ => s
  }
}

///|
fn d_texput(e : Value, s : Value, tx? : Value = Nil) -> Value raise {
  let mut e = e
  if stringp(e) {
    e = d_verbify(e)
  } else if !symbolp(e) {
    merr(
      "texput: first argument must be a string or a symbol; found: ~M",
      [e],
    )
    |> ignore
  }
  let s = if d_listp(s).truthy() { margs(s) } else { list1(s) }
  let s = mapcar(x => tex_space_after_control_word(x), s)
  if tx is Nil {
    // texput was called as texput(op, foo) where foo is a string or a
    // symbol; when foo is a string, assign TEXWORD property, when foo is a
    // symbol, construct glue function to call the Maxima function named by
    // foo.
    let s0 = nth(0, s)
    if stringp(s0) {
      if get(e, q_texsym).truthy() {
        putprop(e, list1(s0), q_texsym) |> ignore
      }
      putprop(e, s0, q_texword)
    } else {
      make_maxima_tex_glue(e, s0, get(e, q_tex)) // assigns TEX property
    }
  } else if eq(tx, q_d_matchfix) {
    putprop(e, q_tex_matchfix, q_tex) |> ignore
    let n = length(s)
    if n < 2 {
      merr(
        "texput: expected a list of two items for matchfix operator.",
        [],
      )
      |> ignore
    } else if n == 2 {
      putprop(e, list2(list1(first(s)), second(s)), q_texsym) |> ignore
    } else {
      putprop(e, list3(list1(first(s)), second(s), third(s)), q_texsym)
      |> ignore
    }
    cons(list1(q_mlist), s)
  } else if eq(tx, q_d_nofix) {
    putprop(e, q_tex_nofix, q_tex) |> ignore
    putprop(e, s, q_texsym) |> ignore
    if get(e, q_texword).truthy() {
      putprop(e, nth(0, s), q_texword) |> ignore
    }
    car(s)
  } else if eq(tx, q_d_prefix) {
    putprop(e, q_tex_prefix, q_tex) |> ignore
    if get(e, q_grind) is Nil {
      putprop(e, Fix(180L), q_tex_rbp) |> ignore
    }
    putprop(e, s, q_texsym) |> ignore
    if get(e, q_texword).truthy() {
      putprop(e, nth(0, s), q_texword) |> ignore
    }
    car(s)
  } else if eq(tx, q_d_infix) {
    putprop(e, q_tex_infix, q_tex) |> ignore
    if get(e, q_grind) is Nil {
      putprop(e, Fix(180L), q_tex_lbp) |> ignore
      putprop(e, Fix(180L), q_tex_rbp) |> ignore
    }
    putprop(e, s, q_texsym) |> ignore
    if get(e, q_texword).truthy() {
      putprop(e, nth(0, s), q_texword) |> ignore
    }
    car(s)
  } else if eq(tx, q_d_nary) {
    putprop(e, q_tex_nary, q_tex) |> ignore
    if get(e, q_grind) is Nil {
      putprop(e, Fix(180L), q_tex_lbp) |> ignore
      putprop(e, Fix(180L), q_tex_rbp) |> ignore
    }
    putprop(e, s, q_texsym) |> ignore
    if get(e, q_texword).truthy() {
      putprop(e, nth(0, s), q_texword) |> ignore
    }
    car(s)
  } else if eq(tx, q_d_postfix) {
    putprop(e, q_tex_postfix, q_tex) |> ignore
    if get(e, q_grind) is Nil {
      putprop(e, Fix(180L), q_tex_lbp) |> ignore
    }
    putprop(e, s, q_texsym) |> ignore
    if get(e, q_texword).truthy() {
      putprop(e, nth(0, s), q_texword) |> ignore
    }
    car(s)
  } else {
    Nil
  }
}

///|
fn init_mactex() -> Unit raise {
  let verbatim = cons(
    Str("\n\\begin{verbatim}\n"),
    Str(";\n\\end{verbatim}\n"),
  )
  for op in [q_mdefine, q_mdefmacro, q_mlabel] {
    setf_get(op, q_tex_environment, verbatim) |> ignore
  }
  // tex dispatch properties
  let tex_props = [
    (q_bigfloat, q_tex_bigfloat),
    (q_mprogn, q_tex_matchfix),
    (q_mlist, q_tex_matchfix),
    (q_mabs, q_tex_matchfix),
    (q_mqapply, q_tex_mqapply),
    (q_p_gamma, q_tex_gamma),
    (q_mquote, q_tex_prefix),
    (q_msetq, q_tex_infix),
    (q_mset, q_tex_infix),
    (q_mdefine, q_tex_infix),
    (q_mdefmacro, q_tex_infix),
    (q_marrow, q_tex_infix),
    (q_mfactorial, q_tex_postfix),
    (q_mexpt, q_tex_mexpt),
    (q_mncexpt, q_tex_mexpt),
    (q_mnctimes, q_tex_nary),
    (q_mtimes, q_tex_nary),
    (q_p_sqrt, q_tex_sqrt),
    (q_d_cubrt, q_tex_cubrt),
    (q_mquotient, q_tex_mquotient),
    (q_d_matrix, q_tex_matrix),
    (q_p_sum, q_tex_sum),
    (q_p_lsum, q_tex_lsum),
    (q_p_product, q_tex_sum),
    (q_p_integrate, q_tex_int),
    (q_p_limit, q_tex_limit),
    (q_p_at, q_tex_at),
    (q_p_at_difference, q_tex_at_difference),
    (q_mbox, q_tex_mbox),
    (q_mlabox, q_tex_mlabox),
    (q_p_binomial, q_tex_choose),
    (q_rat, q_tex_rat),
    (q_mplus, q_tex_mplus),
    (q_mminus, q_tex_prefix),
    (q_min, q_tex_infix),
    (q_mequal, q_tex_infix),
    (q_mnotequal, q_tex_infix),
    (q_mgreaterp, q_tex_infix),
    (q_mgeqp, q_tex_infix),
    (q_mlessp, q_tex_infix),
    (q_mleqp, q_tex_infix),
    (q_mnot, q_tex_prefix),
    (q_mand, q_tex_nary),
    (q_mor, q_tex_nary),
  ]
  for p in tex_props {
    putprop(p.0, p.1, q_tex) |> ignore
  }
  // texword properties
  let words = [
    (q_mprog, "\\mathbf{block}\\;"),
    (q_p_erf, "\\mathrm{erf}"),
    (q_d_erf, "\\mathrm{erf}"), // etc for multicharacter names
    (q_d_true, "\\mathbf{true}"),
    (q_d_false, "\\mathbf{false}"),
    (q_d_done, "\\mathbf{done}"),
    (q_d__pcti, "i"),
    (q_d__pcte, "e"),
    (q_d_inf, "\\infty "),
    (q_d_minf, " -\\infty "),
    (q_p_laplace, "\\mathcal{L}"),
    (q_d_alpha, "\\alpha"),
    (q_d_beta, "\\beta"),
    (q_d_gamma, "\\gamma"),
    (q_p_gamma, "\\gamma"),
    (q_d__pctgamma, "\\gamma"),
    (q_p_gamma_incomplete, "\\Gamma"),
    (q_p_gamma_incomplete_regularized, "Q"),
    (q_p_gamma_incomplete_generalized, "\\Gamma"),
    (q_d_gamma_incomplete_lower, "\\gamma"),
    (q_d_delta, "\\delta"),
    (q_d_epsilon, "\\varepsilon"),
    (q_d_zeta, "\\zeta"),
    (q_d_eta, "\\eta"),
    (q_d_theta, "\\vartheta"),
    (q_d_iota, "\\iota"),
    (q_d_kappa, "\\kappa"),
    (q_lambda, "\\lambda"),
    (q_d_lambda, "\\lambda"),
    (q_d_mu, "\\mu"),
    (q_d_nu, "\\nu"),
    (q_d_xi, "\\xi"),
    (q_d_omicron, " o"),
    (q_d__pctpi, "\\pi"),
    (q_d_pi, "\\pi"),
    (q_d_rho, "\\rho"),
    (q_d_sigma, "\\sigma"),
    (q_d_tau, "\\tau"),
    (q_d_upsilon, "\\upsilon"),
    (q_d_phi, "\\varphi"),
    (q_d__pctphi, "\\varphi"),
    (q_d_chi, "\\chi"),
    (q_d_psi, "\\psi"),
    (q_d_omega, "\\omega"),
    (sym("$Alpha"), "{\\rm A}"),
    (sym("$Beta"), "{\\rm B}"),
    (sym("$Gamma"), "\\Gamma"),
    (sym("$Delta"), "\\Delta"),
    (sym("$Epsilon"), "{\\rm E}"),
    (sym("$Zeta"), "{\\rm Z}"),
    (sym("$Eta"), "{\\rm H}"),
    (sym("$Theta"), "\\Theta"),
    (sym("$Iota"), "{\\rm I}"),
    (sym("$Kappa"), "{\\rm K}"),
    (sym("$Lambda"), "\\Lambda"),
    (sym("$Mu"), "{\\rm M}"),
    (sym("$Nu"), "{\\rm N}"),
    (sym("$Xi"), "\\Xi"),
    (sym("$Omicron"), "{\\rm O}"),
    (sym("$Pi"), "\\Pi"),
    (sym("$Rho"), "{\\rm P}"),
    (sym("$Sigma"), "\\Sigma"),
    (sym("$Tau"), "{\\rm T}"),
    (sym("$Upsilon"), "\\Upsilon"),
    (sym("$Phi"), "\\Phi"),
    (sym("$Chi"), "{\\rm X}"),
    (sym("$Psi"), "\\Psi"),
    (sym("$Omega"), "\\Omega"),
    (q_p_atan2, "{\\rm atan2}"),
  ]
  for w in words {
    putprop(w.0, Str(w.1), q_texword) |> ignore
  }
  // texsym properties
  let s = mactex__strs
  putprop(q_mprogn, list2(s(["\\left("]), Str("\\right)")), q_texsym) |> ignore
  putprop(q_mlist, list2(s(["\\left[ "]), Str(" \\right] ")), q_texsym)
  |> ignore
  setf_get(q_p_mlist, q_tex, get(q_mlist, q_tex)) |> ignore
  setf_get(q_p_mlist, q_texsym, get(q_mlist, q_texsym)) |> ignore
  putprop(q_mabs, list2(s(["\\left| "]), Str("\\right| ")), q_texsym) |> ignore
  let syms = [
    (q_mquote, s(["\\mbox{{}'{}}"])),
    (q_msetq, s([":"])),
    (q_mset, s(["::"])),
    (q_mdefine, s([":="])),
    (q_mdefmacro, s(["::="])),
    (q_marrow, s(["\\rightarrow "])),
    (q_mfactorial, s(["!"])),
    (q_mnctimes, s(["\\cdot "])),
    (q_mtimes, s(["\\,"])),
    (q_mquotient, s(["\\over"])),
    (q_mminus, s(["-"])),
    (q_min, s(["\\in{"])),
    (q_mequal, list1(sym("="))),
    (q_mnotequal, s(["\\neq "])),
    (q_mgreaterp, list1(sym(">"))),
    (q_mgeqp, s(["\\geq "])),
    (q_mlessp, list1(sym("<"))),
    (q_mleqp, s(["\\leq "])),
    (q_mnot, s(["\\neg "])),
    (q_mand, s(["\\land "])),
    (q_mor, s(["\\lor "])),
    (q_p_del, s(["d"])),
  ]
  for p in syms {
    putprop(p.0, p.1, q_texsym) |> ignore
  }
  putprop(q_p_sum, Fix(110L), q_tex_rbp) |> ignore // added by BLW, 1 Oct 2001
  putprop(q_p_product, Fix(115L), q_tex_rbp) |> ignore // added by BLW, 1 Oct 2001
  // MIN = "Maxima in", apparently -- not to be confused with the least
  // value of a set.
  putprop(q_min, Fix(80L), q_tex_lbp) |> ignore
  putprop(q_min, Fix(80L), q_tex_rbp) |> ignore
  // JM 09/01 expand and re-order to follow table of "log-like" functions,
  // see table in Lamport, 2nd edition, 1994, p. 44, table 3.9.
  let setups = [
    (q_p_acos, "\\arccos "),
    (q_p_asin, "\\arcsin "),
    (q_p_atan, "\\arctan "),
    (q_p_cos, "\\cos "),
    (q_p_cosh, "\\cosh "),
    (q_p_cot, "\\cot "),
    (q_p_coth, "\\coth "),
    (q_p_csc, "\\csc "),
    (q_p_determinant, "\\det "),
    (q_p_dim, "\\dim "),
    (q_p_exp, "\\exp "),
    (q_p_gcd, "\\gcd "),
    (q_p_inf, "\\inf "), // many will prefer "\\infty". Hmmm.
    (q_p_ln, "\\ln "),
    (q_p_log, "\\log "),
    (q_p_max, "\\max "),
    (q_p_min, "\\min "),
    (q_p_sec, "\\sec "),
    (q_p_sin, "\\sin "),
    (q_p_sinh, "\\sinh "),
    (q_p_tan, "\\tan "),
    (q_p_tanh, "\\tanh "),
    // Maxima built-in functions which do not have corresponding TeX symbols.
    (q_p_asec, "{\\rm arcsec}\\; "),
    (q_p_acsc, "{\\rm arccsc}\\; "),
    (q_p_acot, "{\\rm arccot}\\; "),
    (q_p_sech, "{\\rm sech}\\; "),
    (q_p_csch, "{\\rm csch}\\; "),
    (q_p_asinh, "{\\rm asinh}\\; "),
    (q_p_acosh, "{\\rm acosh}\\; "),
    (q_p_atanh, "{\\rm atanh}\\; "),
    (q_p_asech, "{\\rm asech}\\; "),
    (q_p_acsch, "{\\rm acsch}\\; "),
    (q_p_acoth, "{\\rm acoth}\\; "),
  ]
  for p in setups {
    tex_setup(list2(p.0, Str(p.1))) |> ignore
  }
  let more = [
    (q_mcond, q_tex_mcond),
    (q_p_mcond, q_tex_mcond),
    (q_p_del, q_tex_prefix),
    (q_p_derivative, q_tex_derivative),
    (q_mdo, q_tex_mdo),
    (q_mdoin, q_tex_mdoin),
    (q_p_mdo, q_tex_mdo),
    (q_p_mdoin, q_tex_mdoin),
    (q_mtext, q_tex_mtext),
    (q_text_string, q_tex_mtext),
    (q_mlabel, q_tex_mlabel),
    (q_spaceout, q_tex_spaceout),
  ]
  for p in more {
    putprop(p.0, p.1, q_tex) |> ignore
  }
  // Additions by Marek Rychlik: this handles setting of LET rules.
  putprop(sym(" --> "), Str("\\longrightarrow "), q_texsym) |> ignore
  putprop(sym(" where "), Str("\\;\\mathbf{where}\\;"), q_texsym) |> ignore
}
