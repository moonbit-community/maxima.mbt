// Port of share/contrib/lurkmathml/mathml.lisp: MathML printing (David
// Drysdale, 2002--2003), closely based on the TeX conversion code in
// mactex.lisp.
//
// Producing MathML from a macsyma internal expression is done by a
// reversal of the parsing process. Fundamentally, a traversal of the
// expression tree is produced by the program, with appropriate
// substitutions and recognition of the infix / prefix / postfix / matchfix
// relations on symbols.

///|
/// The named MathML spaces and their lengths in `em' units. CL Maxima
/// formats the ratios n/18 with ~F, which prints them as single floats.
let share_mathml__mathspaces : Array[(String, String)] = [
  ("veryverythinmathspace", "0.055555556em"),
  ("verythinmathspace", "0.11111111em"),
  ("thinmathspace", "0.16666667em"),
  ("mediummathspace", "0.22222222em"),
  ("thickmathspace", "0.2777778em"),
  ("verythickmathspace", "0.33333334em"),
  ("veryverythickmathspace", "0.3888889em"),
  ("negativeveryverythinmathspace", "-0.055555556em"),
  ("negativeverythinmathspace", "-0.11111111em"),
  ("negativethinmathspace", "-0.16666667em"),
  ("negativemediummathspace", "-0.22222222em"),
  ("negativethickmathspace", "-0.2777778em"),
  ("negativeverythickmathspace", "-0.33333334em"),
  ("negativeveryverythickmathspace", "-0.3888889em"),
]

///|
/// Translation of named spaces to their length in `em' units.
fn get_mathml_mathspace(sym_ : Value) -> Value raise {
  for p in share_mathml__mathspaces {
    if eq(sym_, sym(p.0)) {
      return Str(p.1)
    }
  }
  sym_
}

///|
fn share_mathml__space(name : String) -> String raise {
  share_mathml__str(get_mathml_mathspace(sym(name)))
}

///|
fn share_mathml__str(x : Value) -> String raise {
  match x {
    Str(s) => s
    _ => princ_to_string(x)
  }
}

///|
fn share_mathml__strs(a : Array[String]) -> Value {
  list(a.map(s => Value::Str(s)))
}

///|
/// (defmspec $mathml (l) ...): mexplabel, and optional filename. If a
/// filename is supplied but is 'nil' then return a string.
fn share_mathml__d_mathml(l : Value) -> Value raise {
  let args = cdr(l)
  if cdr(args).truthy() && cadr(args) is Nil {
    let st = make_string_output_stream()
    with_special(standard_output, st, () => {
      share_mathml__apply_mathml1(args) |> ignore
      Value::Nil
    })
    |> ignore
    Str(get_output_stream_string(st))
  } else {
    share_mathml__apply_mathml1(args)
  }
}

///|
fn share_mathml__apply_mathml1(args : Value) -> Value raise {
  apply(q_mathml1, args)
}

///|
fn d_xml_sanitize(x : Value, strings? : Value = Str("'\"<>&;#")) -> Value raise {
  let html_entities : Array[(Char, Array[Char])] = []
  for c in string_chars(share_mathml__str(strings)) {
    let code = c.to_int()
    let ent = "&#x" + format_to_string("~x", [int(code)]) + ";"
    html_entities.push((c, string_chars(ent)))
  }
  let chars = string_chars(share_mathml__str(x))
  if chars.length() == 0 {
    // FLATTEN returns (NIL), which COERCE cannot make into a string.
    raise LispError::SimpleError(
      "The value NIL is not of type CHARACTER when coercing to STRING",
    )
  }
  let sb = StringBuilder::new()
  for c in chars {
    let mut done = false
    for e in html_entities {
      if e.0 == c {
        for d in e.1 {
          sb.write_char(d)
        }
        done = true
        break
      }
    }
    if !done {
      sb.write_char(c)
    }
  }
  Str(sb.to_string())
}

///|
fn mathml1(mexplabel : Value, filename? : Value = Nil) -> Value raise {
  // CCOL is bound here as in CL, but MYPRINC keeps its column in its own
  // closure (mactex.lisp), so the binding does not affect it.
  with_specials([(q_texport, Nil), (q_d_gcprint, Nil)], () => {
    let mut mexplabel = mexplabel
    if mexplabel is Nil {
      displa(Str(" No eqn given to MathML")) |> ignore
      return Nil
    }
    // collect the file-name, if any, and open a port if needed
    let texport = if filename is Nil {
      symval(standard_output)
    } else {
      make_string_output_stream()
    }
    set(q_texport, texport) |> ignore
    // go back and analyze the first arg more thoroughly now.
    // do a normal evaluation of the expression in macsyma
    let mut mexp = meval(mexplabel)
    let mut itsalabel = false
    if memq(mexplabel, symval(q_d_labels)).truthy() {
      // leave it if it is a label
      itsalabel = true
    } else {
      mexplabel = Nil // flush it otherwise
    }
    // maybe it is a function?
    if symbolp(mexp) {
      let x = d_verbify(mexp)
      let y = mget(x, q_mexpr)
      if y.truthy() {
        mexp = list([list1(q_mdefine), cons(list1(x), cdadr(y)), caddr(y)])
      } else {
        let y = mget(x, q_mmacro)
        if y.truthy() {
          mexp = list([
            list1(q_mdefmacro),
            cons(list1(x), cdadr(y)),
            caddr(y),
          ])
        } else {
          let y = mget(x, q_aexpr)
          if y.truthy() {
            mexp = list([
              list1(q_mdefine),
              cons(list([x, q_array]), cdadr(y)),
              caddr(y),
            ])
          }
        }
      }
    }
    if (!atom(mexp) &&
      memq(caar(mexp), list([q_mdefine, q_mdefmacro])).truthy()) ||
      itsalabel {
      let lab = if mexplabel.truthy() {
        aformat(Nil, Str("(~a) "), list1(stripdollar(mexplabel)))
      } else {
        Str("")
      }
      let grind = Value::Str(with_output_to_string(st => mgrind(mexp, st) |> ignore))
      format(texport, "<pre>~%~a~a;~%</pre>~%", [lab, d_xml_sanitize(grind)])
      |> ignore
    } else {
      // display the expression for MathML now:
      myprinc(
        Str("<math xmlns=\"http://www.w3.org/1998/Math/MathML\"> "),
        texport~,
      )
      |> ignore
      // initially the left and right contexts are empty lists, and there
      // are implicit parens around the whole expression
      for x in mathml(mexp, Nil, Nil, q_mparen, q_mparen).iter() {
        myprinc(x, texport~) |> ignore
      }
      if mexplabel.truthy() {
        aformat(
          texport,
          Str("<mspace width=\"~a\"/> <mtext>~a</mtext> "),
          list([
            get_mathml_mathspace(sym("verythickmathspace")),
            stripdollar(mexplabel),
          ]),
        )
        |> ignore
      }
      format(texport, "</math>~%", []) |> ignore
    }
    if filename.truthy() {
      // and drain port if not terminal
      terpri(stream=texport) |> ignore
      mactex__append_to_file(
        share_mathml__str(stripdollar(filename)),
        get_output_stream_string(texport),
      )
    }
    mexplabel
  })
}

///|
/// x is the expression of interest; l is the list of strings to its left,
/// r to its right. lop and rop are the operators on the left and right of
/// x in the tree, and will determine if parens must be inserted.
fn mathml(
  x : Value,
  l : Value,
  r : Value,
  lop : Value,
  rop : Value,
) -> Value raise {
  with_specials([(q_lop, lop), (q_rop, rop)], () => {
    let x = nformat(x)
    if atom(x) {
      mathml_atom(x, l, r)
    } else if num_le(mathml_lbp(caar(x)), mathml_rbp(lop)) ||
      num_gt(mathml_lbp(rop), mathml_rbp(caar(x))) {
      mathml_paren(x, l, r)
    } else if memq(q_array, cdar(x)).truthy() {
      // special check needed because macsyma notates arrays peculiarly
      mathml_array(x, l, r)
    } else if get(caar(x), q_mathml).truthy() {
      // dispatch for object-oriented mathml-ifiying
      funcall(get(caar(x), q_mathml), [x, l, r])
    } else {
      mathml_function(x, l, r, Nil)
    }
  })
}

// NOTE that we try to include spaces after closing tags (e.g.
// "</mwhatever> ") so that the line breaking algorithm in myprinc has some
// spaces where it can choose to line break.

///|
fn mathml_atom(x : Value, l : Value, r : Value) -> Value raise {
  let item = if numberp(x) {
    mathmlnumformat(x)
  } else if (match x {
      Str(s) => s.length() > 0 && char_at(s, 0) != '<'
      _ => false
    }) {
    format(Nil, "<mtext>~a</mtext>", [x])
  } else if stringp(x) {
    x
  } else if symbolp(x) {
    let w = get(x, q_mathmlword)
    if w.truthy() {
      w
    } else {
      let m = get(x, q_reversealias)
      let w2 = if m.truthy() {
        let mw = get(m, q_mathmlword)
        if mw.truthy() {
          mw
        } else {
          mathml_stripdollar(m)
        }
      } else {
        Nil
      }
      if w2.truthy() {
        w2
      } else {
        mathml_stripdollar(x)
      }
    }
  } else {
    // adapted from mactex.lisp
    let s = if member(
        marray_type(x),
        list([q_array, q_hash_table, q_d_functional]),
      ).truthy() {
      d_sconcat(list1(x))
    } else {
      format(Nil, "~A", [x])
    }
    // Do not apply stringdisp here -- we are outputting a string only
    // because we don't have a better way to handle Lisp arrays.
    format(Nil, "<mtext>~a</mtext>", [
      d_xml_sanitize(Str(string_trim("\"", share_mathml__str(s)))),
    ])
  }
  append(l, cons(item, r))
}

///|
fn mathmlnumformat(atom_ : Value) -> Value raise {
  if integerp(atom_) {
    strcat(
      list([Str("<mn>"), format(Nil, "~d", [atom_]), Str("</mn> ")]),
    )
  } else {
    let r = explode(atom_)
    let is_e = (c : Value) => match c {
      Sym(_) => {
        let n = symbol_name(c)
        n == "e" || n == "E"
      }
      _ => false
    }
    // is it ddd.ddde+EE
    let mut exponent = r
    while exponent.truthy() && !is_e(car(exponent)) {
      exponent = cdr(exponent)
    }
    if exponent is Nil {
      strcat(
        list([
          Str("<mn>"),
          format(Nil, "~a", [implode(exploden(atom_))]),
          Str("</mn> "),
        ]),
      )
    } else {
      let mut rr = reverse(r)
      while rr.truthy() && !is_e(car(rr)) {
        rr = cdr(rr)
      }
      let firstpart = nreverse(cdr(rr))
      strcat(
        list([
          Str("<mrow><mn>"),
          strcat(firstpart),
          Str("</mn><mo>&times;</mo> <msup><mn>10</mn><mn>"),
          strcat(cdr(exponent)),
          Str("</mn></msup> </mrow> "),
        ]),
      )
    }
  }
}

///|
/// If SYM is not a symbol, then return SYM; else if either
/// $MATHML_UNDERSCORE_IS_SUBSCRIPT is NIL or less than 1, then apply
/// MATHML-STRIPDOLLAR-DEFAULT to SYM; else split the symbol-name of SYM
/// along the underscores, collect the subscripts until we have enough (or
/// all of them), and return the remaining symbol-name with the subscripts.
fn mathml_stripdollar(sym_ : Value) -> Value raise {
  let uis = symval(q_d_mathml_underscore_is_subscript)
  if !(uis is Nil || eq(uis, t) || fixnump(uis)) {
    raise LispError::SimpleError(
      "`mathml_underscore_is_subscript' should be an integer or `true' or `false'",
    )
  }
  if !symbolp(sym_) {
    sym_
  } else if uis is Nil || (fixnump(uis) && num_lt(uis, Fix(1L))) {
    mathml_stripdollar_default(sym_)
  } else if eq(t, uis) {
    with_special(
      q_d_mathml_underscore_is_subscript,
      Fix(4611686018427387903L),
      () => mathml_stripdollar(sym_),
    )
  } else if fixnump(uis) && num_ge(uis, Fix(1L)) {
    let name = string_left_trim("$", symbol_name(sym_))
    let s = mfuncall(q_d_split, list([Str(name), Str("_")]))
    let l = length(s)
    let n_max = num_min(int(l - 2), uis)
    if l < 3 {
      return strcat(list([Str("<mi>"), cadr(s), Str("</mi>")]))
    }
    let nonnum = symval(q_d_mathml_non_numeric_subscripts).truthy()
    let all_subscript = (p : Value) => {
      let mut ok = true
      for c in string_chars(share_mathml__str(p)) {
        if !(nonnum || (c >= '0' && c <= '9')) {
          ok = false
          break
        }
      }
      ok
    }
    let mut sn = reverse(cdr(s))
    let mut n = 1
    let mut num = all_subscript(car(sn))
    let mut r : Value = if num {
      list([Str("<mi>"), car(sn), Str("</mi>")])
    } else {
      Nil
    }
    let mut e = if num { " </msub>" } else { "" }
    while !(cdr(sn) is Nil || !num || num_ge(int(n), n_max)) {
      sn = cdr(sn)
      n = n + 1
      num = all_subscript(car(sn))
      if num {
        r = append(list([Str("<msub><mi>"), car(sn), Str("</mi>")]), r)
        e = e + "</msub>"
      }
    }
    // (CAR SN) is a subscript, but the loop did not have a chance to
    // discard it from SN, so we do it manually
    if num && num_le(int(n), n_max) && length(sn) > 1 {
      sn = cdr(sn)
    }
    format(Nil, "~a<mi>~{~a~^_~}</mi> ~{~a ~} ~a", [
      Str(if e == "" { "" } else { "<msub>" }),
      reverse(sn),
      r,
      Str(e),
    ])
  } else {
    // we should never get here
    raise LispError::SimpleError("MATHML-STRIPDOLLAR-DEFAULT: ")
  }
}

///|
fn mathml_stripdollar_default(sym_ : Value) -> Value raise {
  if !symbolp(sym_) {
    return sym_
  }
  let pname = string_left_trim("$", symbol_name(sym_))
  let chars = string_chars(pname)
  let l = chars.length()
  let mut begin_sub = -1
  let mut i = l - 1
  while true {
    if i < 0 {
      raise LispError::SimpleError(
        "MATHML-STRIPDOLLAR-DEFAULT: invalid symbol name " + pname,
      )
    }
    if !(chars[i] >= '0' && chars[i] <= '9') {
      begin_sub = i + 1
      break
    }
    i -= 1
  }
  if begin_sub < l {
    // need to do subscripting
    Str(
      "<msub><mi>" +
      substring(pname, 0, end=begin_sub) +
      "</mi> <mn>" +
      substring(pname, begin_sub, end=l) +
      "</mn></msub> ",
    )
  } else {
    // no subscripting needed
    Str("<mi>" + pname + "</mi> ")
  }
}

///|
fn mathml_paren(x : Value, l : Value, r : Value) -> Value raise {
  mathml(
    x,
    append(l, share_mathml__strs(["<mrow><mo>(</mo>"])),
    cons(Str("<mo>)</mo></mrow> "), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn mathml_array(x : Value, l : Value, r : Value) -> Value raise {
  let mut x = x
  let mut l = l
  if eq(q_mqapply, caar(x)) {
    let f = cadr(x)
    x = cdr(x)
    l = mathml(
      f,
      append(l, share_mathml__strs(["<mrow>"])),
      share_mathml__strs(["</mrow> "]),
      q_mparen,
      q_mparen,
    )
  } else {
    let f = caar(x)
    l = mathml(
      mathmlword(f),
      append(l, share_mathml__strs(["<msub><mrow>"])),
      Nil,
      symval(q_lop),
      q_mfunction,
    )
  }
  let r = nconc(
    mathml_list(
      cdr(x),
      Nil,
      share_mathml__strs(["</mrow></msub> "]),
      Str("<mo>,</mo>"),
    ),
    r,
  )
  nconc(l, cons(Str("</mrow><mrow>"), r))
}

///|
/// set up a list, separated by symbols (, * ...) and then tack on the
/// ending item (e.g. "]" or perhaps ")"
fn mathml_list(x : Value, l : Value, r : Value, sym_ : Value) -> Value raise {
  if x is Nil {
    return r
  }
  let mut x = x
  let mut l = l
  let mut nl : Value = Nil
  while cdr(x).truthy() {
    nl = nconc(nl, mathml(car(x), l, list1(sym_), q_mparen, q_mparen))
    x = cdr(x)
    l = Nil
  }
  nconc(nl, mathml(car(x), l, r, q_mparen, q_mparen))
}

///|
/// we could patch this so sin x rather than sin(x), but instead we made sin
/// a prefix operator
fn mathml_function(
  x : Value,
  l : Value,
  r : Value,
  _op : Value,
) -> Value raise {
  let l = mathml(mathmlword(caar(x)), l, Nil, q_mparen, q_mparen)
  let r = mathml(cons(list1(q_mprogn), cdr(x)), Nil, r, q_mparen, q_mparen)
  nconc(l, r)
}

// Now we have functions which are called via property lists

///|
fn mathml_prefix(x : Value, l : Value, r : Value) -> Value raise {
  mathml(cadr(x), append(l, mathmlsym(caar(x))), r, caar(x), symval(q_rop))
}

///|
fn mathml_infix(x : Value, l : Value, r : Value) -> Value raise {
  // check for 2 args
  if cddr(x) is Nil || cdddr(x).truthy() {
    wna_err(caar(x)) |> ignore
  }
  let l = mathml(cadr(x), l, Nil, symval(q_lop), caar(x))
  mathml(caddr(x), append(l, mathmlsym(caar(x))), r, caar(x), symval(q_rop))
}

///|
fn mathml_postfix(x : Value, l : Value, r : Value) -> Value raise {
  mathml(cadr(x), l, append(mathmlsym(caar(x)), r), symval(q_lop), caar(x))
}

///|
fn mathml_nary(x : Value, l : Value, r : Value) -> Value raise {
  let op = caar(x)
  let sym_ = mathmlsym(op)
  let mut y = cdr(x)
  let ext_lop = symval(q_lop)
  let ext_rop = symval(q_rop)
  if y is Nil {
    mathml_function(x, l, r, t) // this should not happen
  } else if cdr(y) is Nil {
    mathml_function(x, l, r, t) // this should not happen, too
  } else {
    let mut nl : Value = Nil
    let mut l = l
    let mut lop = ext_lop
    let mut rop = op
    while cdr(y).truthy() {
      nl = nconc(nl, mathml(car(y), l, list1(sym_), lop, rop))
      y = cdr(y)
      l = Nil
      lop = op
      rop = if cdr(y) is Nil { ext_rop } else { op }
    }
    nconc(nl, mathml(car(y), l, r, lop, rop))
  }
}

///|
fn mathml_nofix(x : Value, l : Value, r : Value) -> Value raise {
  mathml(caar(x), l, r, caar(x), symval(q_rop))
}

///|
fn mathml_matchfix(x : Value, l : Value, r : Value) -> Value raise {
  // car of mathmlsym of a matchfix operator is the lead op
  let l = append(l, car(mathmlsym(caar(x))))
  // cdr is the trailing op
  let r = append(cdr(mathmlsym(caar(x))), r)
  let x = mathml_list(cdr(x), Nil, r, Str("<mo>,</mo>"))
  append(l, x)
}

///|
fn mathmlsym(x : Value) -> Value raise {
  let v = get(x, q_mathmlsym)
  if v.truthy() {
    return v
  }
  let v = get(x, q_strsym)
  if v.truthy() {
    return v
  }
  let v = get(x, q_dissym)
  if v.truthy() {
    return v
  }
  mathml_stripdollar(x)
}

///|
fn mathmlword(x : Value) -> Value raise {
  let v = get(x, q_mathmlword)
  if v.truthy() {
    return v
  }
  let v = get(x, q_reversealias)
  if v.truthy() {
    return v
  }
  mathml_stripdollar(x)
}

///|
fn mathml_bigfloat(x : Value, l : Value, r : Value) -> Value raise {
  let formatted = fpformat(x)
  let is_b = fn(e : Value) -> Bool raise { eq(e, sym("b")) || eq(e, sym("B")) }
  if find_if(is_b, formatted).truthy() {
    let spell = Collector::new()
    spell.add(Str("<mrow><msub><mn>"))
    for e in formatted.iter() {
      if is_b(e) {
        spell.add(Str("</mn><mi>B</mi></msub>"))
        spell.add(Str("<mo>&times;</mo>"))
        spell.add(Str("<msup><mn>10</mn><mn>"))
      } else {
        spell.add(e)
      }
    }
    spell.add(Str("</mn></msup></mrow>"))
    append(l, append(spell.result(), r))
  } else {
    append(l, append(formatted, r))
  }
}

///|
fn mathml_mlabox(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(
      share_mathml__strs([
        "<mtable><mtr><mtd columnalign=\"center\" style=\"font-size: 0.8em;\">",
      ]),
      append(
        mathml(caddr(x), Nil, Nil, q_mparen, q_mparen),
        append(
          share_mathml__strs([
            "</mtd></mtr><mtr><mtd><menclose notation=\"box\"><menclose notation=\"box\">",
          ]),
          append(
            mathml(cadr(x), Nil, Nil, q_mparen, q_mparen),
            append(
              share_mathml__strs([
                "</menclose></menclose></mtd></mtr></mtable>",
              ]),
              r,
            ),
          ),
        ),
      ),
    ),
  )
}

///|
fn mathml_mqapply(x : Value, l : Value, r : Value) -> Value raise {
  let l = mathml(
    cadr(x),
    l,
    share_mathml__strs(["<mo>(</mo>"]),
    symval(q_lop),
    q_mfunction,
  )
  let r = mathml_list(
    cddr(x),
    Nil,
    cons(Str("<mo>)</mo>"), r),
    Str("<mo>,</mo>"),
  )
  append(l, r)
}

///|
/// insert left-angle-brackets for mncexpt. a^<n> is how a^^n looks.
fn mathml_mexpt(x : Value, l : Value, r : Value) -> Value raise {
  let nc = eq(caar(x), q_mncexpt) // true if a^^b rather than a^b
  let mut l = l
  let mut r = r
  // here is where we have to check for f(x)^b to be displayed as f^b(x),
  // as is the case for sin(x)^2, which should be sin^2 x rather than
  // (sin x)^2 or (sin(x))^2. yet we must not display (a+b)^2 as
  // +^2(a,b)... or (sin(x))^(-1) as sin^(-1)x, which would be arcsine x
  let hack = eq(caar(x), q_mexpt) && // don't do this hack for mncexpt
    {
      let fx = cadr(x) // this is f(x)
      let f = if !atom(fx) && atom(caar(fx)) { caar(fx) } else { Nil } // this is f [or nil]
      let bascdr = if f.truthy() { cdr(fx) } else { Nil } // this is (x) [maybe (x,y..), or nil]
      let expon = caddr(x) // this is the exponent
      let doit = f.truthy() && // there is such a function
        (match get_first_char(f) {
          Char('%') | Char('$') => true
          _ => false
        }) && // insist it is a % or $ function
        memq(
          f,
          list([
            q_p_sum,
            q_p_product,
            q_p_derivative,
            q_p_integrate,
            q_p_at,
            q_p_lsum,
            q_p_limit,
          ]),
        )
        is Nil && // what else? what a hack...
        memq(q_array, cdar(fx)) is Nil && // fix for x[i]^2
        (
          (atom(expon) && !numberp(expon)) || // f(x)^y is ok
          (atom(expon) && numberp(expon) && num_gt(expon, Fix(0L)))
        )
      // f(x)^3 is ok, but not f(x)^-1, which could be the inverse of f,
      // if written f^-1 x
      if doit {
        l = mathml(mk(q_mexpt, [f, expon]), l, Nil, q_mparen, q_mparen)
        if cdr(bascdr) is Nil && eq(get(f, q_mathml), q_mathml_prefix) {
          r = mathml(car(bascdr), Nil, r, f, q_mparen)
        } else {
          r = mathml(cons(list1(q_mprogn), bascdr), Nil, r, q_mparen, q_mparen)
        }
        true
      } else {
        false // won't doit. fall through
      }
    }
  if !hack {
    l = mathml(
      cadr(x),
      append(l, share_mathml__strs(["<msup><mrow>"])),
      Nil,
      symval(q_lop),
      caar(x),
    )
    let x = nformat(caddr(x))
    r = if mmminusp(x).truthy() {
      // the change in base-line makes parens unnecessary
      // exponents are wrapped in 〈〉 (= #x3008 #x3009)
      if nc {
        mathml(
          cadr(x),
          share_mathml__strs([
            "</mrow> <mrow><mo form=\"prefix\">&#x3008;</mo><mo form=\"prefix\">-</mo>",
          ]),
          cons(Str("<mo form=\"postfix\">&#x3009;</mo></mrow></msup> "), r),
          q_mparen,
          q_mparen,
        )
      } else {
        mathml(
          cadr(x),
          share_mathml__strs(["</mrow> <mrow> <mo form=\"prefix\">-</mo>"]),
          cons(Str("</mrow></msup> "), r),
          q_mparen,
          q_mparen,
        )
      }
    } else if nc {
      mathml(
        x,
        share_mathml__strs(["</mrow> <mrow><mo form=\"prefix\">&#x3008;</mo>"]),
        cons(Str("<mo form=\"postfix\">&#x3009;</mo></mrow></msup>"), r),
        q_mparen,
        q_mparen,
      )
    } else if numberp(x) && num_lt(x, Fix(10L)) {
      mathml(
        x,
        share_mathml__strs(["</mrow> "]),
        cons(Str("</msup> "), r),
        q_mparen,
        q_mparen,
      )
    } else {
      mathml(
        x,
        share_mathml__strs(["</mrow> <mrow>"]),
        cons(Str("</mrow></msup> "), r),
        q_mparen,
        q_mparen,
      )
    }
  }
  append(l, r)
}

///|
/// format as \\sqrt { } assuming implicit parens for sqr grouping
fn mathml_sqrt(x : Value, l : Value, r : Value) -> Value raise {
  mathml(
    cadr(x),
    append(l, share_mathml__strs(["<msqrt>"])),
    append(share_mathml__strs(["</msqrt>"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
/// macsyma doesn't know about cube (or nth) roots, but if it did, this is
/// what it would look like.
fn mathml_cubrt(x : Value, l : Value, r : Value) -> Value raise {
  mathml(
    cadr(x),
    append(l, share_mathml__strs(["<mroot><mrow>"])),
    append(share_mathml__strs(["</mrow>3</mroot>"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn mathml_mquotient(x : Value, l : Value, r : Value) -> Value raise {
  if cddr(x) is Nil || cdddr(x).truthy() {
    wna_err(caar(x)) |> ignore
  }
  let l = mathml(
    cadr(x),
    append(l, share_mathml__strs(["<mfrac><mrow>"])),
    Nil,
    q_mparen,
    q_mparen,
  )
  let r = mathml(
    caddr(x),
    share_mathml__strs(["</mrow> <mrow>"]),
    append(share_mathml__strs(["</mrow></mfrac> "]), r),
    q_mparen,
    q_mparen,
  )
  append(l, r)
}

///|
/// matrix looks like ((mmatrix)((mlist) a b) ...)
fn mathml_matrix(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(
      share_mathml__strs(["<mrow><mo form=\"prefix\">(</mo><mtable>"]),
      append(
        mapcan(
          y => mathml_list(
            cdr(y),
            share_mathml__strs(["<mtr><mtd>"]),
            share_mathml__strs(["</mtd></mtr> "]),
            Str("</mtd><mtd>"),
          ),
          cdr(x),
        ),
        append(share_mathml__strs(["</mtable><mo>)</mo></mrow> "]), r),
      ),
    ),
  )
}

///|
fn share_mathml__append_all(parts : Array[Value]) -> Value raise {
  let mut acc : Value = Nil
  for i = parts.length() - 1; i >= 0; i = i - 1 {
    acc = append(parts[i], acc)
  }
  acc
}

///|
fn mathml_lsum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_lsum) {
    Str("<mrow><munder><mo>&sum;</mo> <mrow>")
  } else {
    Nil
  }
  // gotta be one of those above
  let s1 = mathml(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // summand
  // "index = lowerlimit"
  let index = mathml(
    mk_simp(q_min, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  append(
    l,
    append(
      share_mathml__append_all([
        list1(op),
        index,
        share_mathml__strs(["</mrow></munder> <mrow>"]),
        s1,
        share_mathml__strs(["</mrow></mrow> "]),
      ]),
      r,
    ),
  )
}

///|
fn mathml_sum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_sum) {
    Str("<mrow><munderover><mo>&sum;</mo><mrow>")
  } else if eq(caar(x), q_p_product) {
    Str("<mrow><munderover><mo>&prod;</mo><mrow>")
  } else {
    Nil
  }
  // gotta be one of those above
  let s1 = mathml(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // summand
  // "index = lowerlimit"
  let index = mathml(
    mk_simp(q_mequal, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  let toplim = mathml(car(cddddr(x)), Nil, Nil, q_mparen, q_mparen)
  append(
    l,
    append(
      share_mathml__append_all([
        list1(op),
        index,
        share_mathml__strs(["</mrow> <mrow>"]),
        toplim,
        share_mathml__strs(["</mrow></munderover> <mrow>"]),
        s1,
        share_mathml__strs(["</mrow></mrow> "]),
      ]),
      r,
    ),
  )
}

///|
fn mathml_int(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = mathml(cadr(x), Nil, Nil, q_mparen, q_mparen) // integrand delims / & d
  let var_ = mathml(caddr(x), Nil, Nil, q_mparen, symval(q_rop)) // variable
  let ms = share_mathml__space("mediummathspace")
  if length(x) == 3 {
    append(
      l,
      append(
        share_mathml__append_all([
          share_mathml__strs(["<mrow><mo>&int;</mo><mrow>"]),
          s1,
          share_mathml__strs([
            "</mrow> <mspace width=\"", ms, "\"/> <mrow><mo>&DifferentialD;</mo>",
          ]),
          var_,
          share_mathml__strs(["</mrow></mrow> "]),
        ]),
        r,
      ),
    )
  } else {
    // presumably length 5
    let low = mathml(nth(3, x), Nil, Nil, q_mparen, q_mparen)
    // 1st item is 0
    let hi = mathml(nth(4, x), Nil, Nil, q_mparen, q_mparen)
    append(
      l,
      append(
        share_mathml__append_all([
          share_mathml__strs(["<mrow><munderover><mo>&int;</mo> <mrow>"]),
          low,
          share_mathml__strs(["</mrow> <mrow>"]),
          hi,
          share_mathml__strs(["</mrow> </munderover> <mrow>"]),
          s1,
          share_mathml__strs([
            "</mrow> <mspace width=\"", ms, "\"/> <mrow><mo>&DifferentialD;</mo>",
          ]),
          var_,
          share_mathml__strs([" </mrow></mrow> "]),
        ]),
        r,
      ),
    )
  }
}

///|
/// ignoring direction, last optional arg to limit
fn mathml_limit(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = mathml(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // limitfunction
  // the thing underneath "limit"
  let subfun = mathml(
    mk_simp(q_mrarr, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  append(
    l,
    append(
      share_mathml__append_all([
        share_mathml__strs(["<munder><mo>lim</mo><mrow>"]),
        subfun,
        share_mathml__strs(["</mrow> </munder> <mrow>"]),
        s1,
        share_mathml__strs(["</mrow>"]),
      ]),
      r,
    ),
  )
}

///|
/// e.g.  at(diff(f(x)),x=a)
fn mathml_at(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = mathml(cadr(x), Nil, Nil, symval(q_lop), symval(q_rop))
  let sub = mathml(caddr(x), Nil, Nil, q_mparen, q_mparen)
  share_mathml__append_all([
    l,
    share_mathml__strs(["<msub><mrow>"]),
    s1,
    share_mathml__strs(["<mo form=\"postfix\">|</mo></mrow> <mrow>"]),
    sub,
    share_mathml__strs(["</mrow> </msub> "]),
    r,
  ])
}

///|
/// e.g. 'at_difference(f(x), x, a, b)
fn mathml_at_difference(e : Value, l : Value, r : Value) -> Value raise {
  let f = car(cdr(e))
  let x = cadr(cdr(e))
  let a = caddr(cdr(e))
  let b = cadddr(cdr(e))
  let mathml_f = mathml(f, Nil, Nil, symval(q_lop), symval(q_rop))
  let mathml_sub = mathml(mk(q_mequal, [x, a]), Nil, Nil, q_mparen, q_mparen)
  let mathml_sup = mathml(mk(q_mequal, [x, b]), Nil, Nil, q_mparen, q_mparen)
  share_mathml__append_all([
    l,
    share_mathml__strs(["<msubsup>"]),
    share_mathml__strs(["<mrow>"]),
    mathml_f,
    share_mathml__strs(["<mo form=\"postfix\">|</mo></mrow>"]),
    share_mathml__strs(["<mrow>"]),
    mathml_sub,
    share_mathml__strs(["</mrow>"]),
    share_mathml__strs(["<mrow>"]),
    mathml_sup,
    share_mathml__strs(["</mrow>"]),
    share_mathml__strs(["</msubsup> "]),
    r,
  ])
}

///|
/// binomial coefficients
fn mathml_choose(x : Value, l : Value, r : Value) -> Value raise {
  share_mathml__append_all([
    l,
    share_mathml__strs([
      "<mrow><mo form=\"prefix\">(</mo><mtable><mtr><mtd>",
    ]),
    mathml(cadr(x), Nil, Nil, q_mparen, q_mparen),
    share_mathml__strs(["</mtd></mtr> <mtr><mtd>"]),
    mathml(caddr(x), Nil, Nil, q_mparen, q_mparen),
    share_mathml__strs(["</mtd></mtr> </mtable><mo>)</mo></mrow> "]),
    r,
  ])
}

///|
fn mathml_rat(x : Value, l : Value, r : Value) -> Value raise {
  mathml_mquotient(x, l, r)
}

///|
fn mathml_mplus(x : Value, l : Value, r : Value) -> Value raise {
  let mut r = r
  if memq(q_trunc, car(x)).truthy() {
    r = cons(Str("<mo>+</mo><mtext>&ctdot;</mtext> "), r)
  }
  if cddr(x) is Nil {
    if cdr(x) is Nil {
      mathml_function(x, l, r, t)
    } else {
      mathml(cadr(x), cons(Str("<mo>+</mo>"), l), r, q_mplus, symval(q_rop))
    }
  } else {
    let l = mathml(cadr(x), l, Nil, symval(q_lop), q_mplus)
    let mut x = cddr(x)
    let mut nl = l
    while cdr(x).truthy() {
      let (ll, dissym) = if mmminusp(car(x)).truthy() {
        (cadar(x), share_mathml__strs(["<mo>-</mo> "]))
      } else {
        (car(x), share_mathml__strs(["<mo>+</mo> "]))
      }
      nl = append(nl, mathml(ll, dissym, Nil, q_mplus, q_mplus))
      x = cdr(x)
    }
    let (ll, dissym) = if mmminusp(car(x)).truthy() {
      (cadar(x), share_mathml__strs(["<mo>-</mo> "]))
    } else {
      (car(x), share_mathml__strs(["<mo>+</mo> "]))
    }
    r = mathml(ll, dissym, r, q_mplus, symval(q_rop))
    append(nl, r)
  }
}

///|
/// make sin(x) display as sin x , but sin(x+y) as sin(x+y) etc
fn mathml_setup(x : Value) -> Value raise {
  let a = car(x)
  let b = cadr(x)
  putprop(a, q_mathml_prefix, q_mathml) |> ignore
  putprop(a, b, q_mathmlword) |> ignore // This means "sin" will always be roman
  putprop(a, list1(b), q_mathmlsym) |> ignore
  putprop(a, Fix(130L), q_mathml_rbp)
}

///|
fn mathml_derivative(x : Value, l : Value, r : Value) -> Value raise {
  mathml(
    mathml_d(
      x,
      dim_derivative_sym(
        x,
        Str("<mo form=\"prefix\">&DifferentialD;</mo>"),
        Str("<mo form=\"prefix\">&PartialD;</mo>"),
      ),
    ),
    l,
    r,
    symval(q_lop),
    symval(q_rop),
  )
}

///|
/// format the macsyma derivative form so it looks sort of like a quotient
/// times the deriva-dand. dsym should be "&DifferentialD;" or "&PartialD;"
fn mathml_d(x : Value, dsym : Value) -> Value raise {
  let arg_ = cadr(x) // the function being differentiated
  let difflist = cddr(x) // list of derivs e.g. (x 1 y 2)
  let ords = odds(difflist, Fix(0L)) // e.g. (1 2)
  let vars = odds(difflist, Fix(1L)) // e.g. (x y)
  let numer = mk(q_mexpt, [dsym, cons(list1(q_mplus), ords)]) // d^n numerator
  let denom_terms = Collector::new()
  let mut b = vars
  let mut e = ords
  while b is Cons(_) && e is Cons(_) {
    denom_terms.add(dsym)
    denom_terms.add(simplifya(mk(q_mexpt, [car(b), car(e)]), Nil))
    b = cdr(b)
    e = cdr(e)
  }
  let denom = cons(list1(q_mtimes), denom_terms.result())
  mk(q_mtimes, [mk(q_mquotient, [simplifya(numer, Nil), denom]), arg_])
}

///|
fn mathml_mcond(x : Value, l : Value, r : Value) -> Value raise {
  let ms = share_mathml__space("mediummathspace")
  append(
    l,
    append(
      mathml(
        cadr(x),
        share_mathml__strs(["<mi>if</mi> <mspace width=\"", ms, "\"/>"]),
        share_mathml__strs([
          "<mspace width=\"", ms, "\"/> <mi>then</mi><mspace width=\"", ms, "\"/> ",
        ]),
        q_mparen,
        q_mparen,
      ),
      if eql(nth(4, x), q_d_false) {
        mathml(caddr(x), Nil, r, q_mcond, symval(q_rop))
      } else {
        append(
          mathml(caddr(x), Nil, Nil, q_mparen, q_mparen),
          mathml(
            nth(4, x),
            share_mathml__strs([
              "<mspace width=\"", ms, "\"/> <mi>else</mi><mspace width=\"", ms,
              "\"/> ",
            ]),
            r,
            q_mcond,
            symval(q_rop),
          ),
        )
      },
    ),
  )
}

///|
fn mathml_lbp(x : Value) -> Value raise {
  let v = get(x, q_mathml_lbp)
  if v.truthy() {
    v
  } else {
    lbp(x)
  }
}

///|
fn mathml_rbp(x : Value) -> Value raise {
  let v = get(x, q_mathml_rbp)
  if v.truthy() {
    v
  } else {
    lbp(x)
  }
}

// these aren't quite right

///|
fn mathml_mdo(x : Value, l : Value, r : Value) -> Value raise {
  mathml_list(
    mathmlmdo(x),
    l,
    r,
    Str("<mspace width=\"" + share_mathml__space("mediummathspace") + "\"/> "),
  )
}

///|
fn mathml_mdoin(x : Value, l : Value, r : Value) -> Value raise {
  mathml_list(
    mathmlmdoin(x),
    l,
    r,
    Str("<mspace width=\"" + share_mathml__space("mediummathspace") + "\"/> "),
  )
}

///|
fn share_mathml__mdo_tail(x : Value) -> Value raise {
  let seventh = nth(6, x)
  let cond7 : Value = if seventh is Nil {
    Nil
  } else if eq(q_mnot, caar(seventh)) {
    list([Str("<mi>while</mi> "), cadr(seventh)])
  } else {
    list([Str("<mi>unless</mi> "), seventh])
  }
  nconc(cond7, list([Str("<mi>do</mi> "), nth(7, x)]))
}

///|
fn mathmlmdo(x : Value) -> Value raise {
  let c1 : Value = if nth(1, x).truthy() {
    list([Str("<mi>for</mi> "), nth(1, x)])
  } else {
    Nil
  }
  let c2 : Value = if equal(Fix(1L), nth(2, x)) {
    Nil
  } else if nth(2, x).truthy() {
    list([Str("<mi>from</mi> "), nth(2, x)])
  } else {
    Nil
  }
  let c3 : Value = if equal(Fix(1L), nth(3, x)) {
    Nil
  } else if nth(3, x).truthy() {
    list([Str("<mi>step</mi> "), nth(3, x)])
  } else if nth(4, x).truthy() {
    list([Str("<mi>next</mi> "), nth(4, x)])
  } else {
    Nil
  }
  let c4 : Value = if nth(5, x).truthy() {
    list([Str("<mi>thru</mi> "), nth(5, x)])
  } else {
    Nil
  }
  nconc(c1, nconc(c2, nconc(c3, nconc(c4, share_mathml__mdo_tail(x)))))
}

///|
fn mathmlmdoin(x : Value) -> Value raise {
  let c1 = list([Str("<mi>for</mi>"), nth(1, x), Str("<mi>in</mi> "), nth(2, x)])
  let c2 : Value = if nth(5, x).truthy() {
    list([Str("<mi>thru</mi> "), nth(5, x)])
  } else {
    Nil
  }
  nconc(c1, nconc(c2, share_mathml__mdo_tail(x)))
}

///|
fn share_mathml__defprops(
  prop : Value,
  entries : Array[(Value, Value)],
) -> Unit raise {
  for e in entries {
    putprop(e.0, e.1, prop) |> ignore
  }
}

///|
fn init_share_mathml() -> Unit raise {
  register_mspec(q_d_mathml, share_mathml__d_mathml)
  let ms = share_mathml__space("mediummathspace")
  let ths = share_mathml__space("thinmathspace")
  let s = (x : String) => Value::Str(x)
  let ls = (a : Array[String]) => share_mathml__strs(a)
  putprop(q_bigfloat, q_mathml_bigfloat, q_mathml) |> ignore
  share_mathml__defprops(q_mathmlword, [
    (q_mprog, s("<mi>block</mi><mspace width=\"" + ms + "\"/> ")),
    (q_p_erf, s("<mi>erf</mi> ")),
    (q_d_erf, s("<mi>erf</mi> ")), // etc for multicharacter names
    (q_d_true, s("<mi>true</mi> ")),
    (q_d_false, s("<mi>false</mi> ")),
  ])
  putprop(q_mprogn, q_mathml_matchfix, q_mathml) |> ignore // mprogn is (<progstmnt>, ...)
  putprop(
    q_mprogn,
    list([ls(["<mrow><mo>(</mo>"]), s("<mo>)</mo></mrow> ")]),
    q_mathmlsym,
  )
  |> ignore
  putprop(q_mlist, q_mathml_matchfix, q_mathml) |> ignore
  putprop(
    q_mlist,
    list([ls(["<mrow><mo>[</mo>"]), s("<mo>]</mo></mrow> ")]),
    q_mathmlsym,
  )
  |> ignore
  putprop(q_mbox, q_mathml_matchfix, q_mathml) |> ignore
  putprop(
    q_mbox,
    list([
      ls(["<menclose notation=\"box\"><menclose notation=\"box\">"]),
      s("</menclose></menclose>"),
    ]),
    q_mathmlsym,
  )
  |> ignore
  putprop(q_mlabox, q_mathml_mlabox, q_mathml) |> ignore
  // absolute value
  putprop(q_mabs, q_mathml_matchfix, q_mathml) |> ignore
  putprop(
    q_mabs,
    list([
      ls(["<mrow><mo form=\"prefix\">|</mo>"]),
      s("<mo form=\"postfix\">|</mo></mrow> "),
    ]),
    q_mathmlsym,
  )
  |> ignore
  putprop(q_mqapply, q_mathml_mqapply, q_mathml) |> ignore
  share_mathml__defprops(q_mathmlword, [
    (q_d__pcti, s("<mi>&ImaginaryI;</mi> ")),
    (q_d__pctpi, s("<mi>&pi;</mi> ")),
    (q_d__pcte, s("<mi>&ExponentialE;</mi> ")),
    (q_d_inf, s("<mi>&infin;</mi> ")),
    (q_d_minf, s("<mi>-&infin;</mi> ")),
    (q_p_laplace, s("<mo>&Laplacetrf;</mo>")),
    (q_d_alpha, s("<mi>&alpha;</mi> ")),
    (q_d_beta, s("<mi>&beta;</mi> ")),
    (q_d_gamma, s("<mi>&gamma;</mi> ")),
    (q_p_gamma, s("<mi>&Gamma;</mi> ")),
    (q_d_delta, s("<mi>&delta;</mi> ")),
    (q_d_epsilon, s("<mi>&epsilon;</mi> ")),
    (q_d_zeta, s("<mi>&zeta;</mi> ")),
    (q_d_eta, s("<mi>&eta;</mi> ")),
    (q_d_theta, s("<mi>&theta;</mi> ")),
    (q_d_iota, s("<mi>&iota;</mi> ")),
    (q_d_kappa, s("<mi>&kappa;</mi> ")),
    (q_lambda, s("<mi>&lambda;</mi> ")),
    (q_d_mu, s("<mi>&mu;</mi> ")),
    (q_d_nu, s("<mi>&nu;</mi> ")),
    (q_d_xi, s("<mi>&xi;</mi> ")),
    (q_d_pi, s("<mi>&pi;</mi> ")),
    (q_d_rho, s("<mi>&rho;</mi> ")),
    (q_d_sigma, s("<mi>&sigma;</mi> ")),
    (q_d_tau, s("<mi>&tau;</mi> ")),
    (q_d_upsilon, s("<mi>&upsilon;</mi> ")),
    (q_d_phi, s("<mi>&phi;</mi> ")),
    (q_d_chi, s("<mi>&chi;</mi> ")),
    (q_d_psi, s("<mi>&psi;</mi> ")),
    (q_d_omega, s("<mi>&omega;</mi> ")),
  ])
  let infix_ops : Array[(Value, Value, String, Value, Value)] = [
    // (op, mathml handler, mathmlsym, lbp, rbp); Nil means no defprop
    (q_mquote, q_mathml_prefix, "<mo>'</mo>", Nil, Fix(201L)),
    (q_msetq, q_mathml_infix, "<mo>:</mo>", Nil, Fix(180L)),
    (q_mset, q_mathml_infix, "<mo>::</mo>", Fix(180L), Fix(20L)),
    (q_mdefine, q_mathml_infix, "<mo>:=</mo>", Fix(180L), Fix(20L)),
    (q_mdefmacro, q_mathml_infix, "<mo>::=</mo>", Fix(180L), Fix(20L)),
    (q_marrow, q_mathml_infix, "<mo>&rightarrow;</mo>", Fix(25L), Fix(25L)),
    (q_mfactorial, q_mathml_postfix, "<mo>!</mo>", Fix(160L), Nil),
  ]
  for e in infix_ops {
    putprop(e.0, e.1, q_mathml) |> ignore
    putprop(e.0, ls([e.2]), q_mathmlsym) |> ignore
    if e.3.truthy() {
      putprop(e.0, e.3, q_mathml_lbp) |> ignore
    }
    if e.4.truthy() {
      putprop(e.0, e.4, q_mathml_rbp) |> ignore
    }
  }
  // (defprop msetq 20. mathml-rbp) follows (defprop msetq 180. mathml-rbp)
  putprop(q_msetq, Fix(20L), q_mathml_rbp) |> ignore
  putprop(q_mexpt, q_mathml_mexpt, q_mathml) |> ignore
  putprop(q_mexpt, Fix(140L), q_mathml_lbp) |> ignore
  putprop(q_mexpt, Fix(139L), q_mathml_rbp) |> ignore
  putprop(q_p_sum, Fix(110L), q_mathml_rbp) |> ignore // added by BLW, 1 Oct 2001
  putprop(q_p_product, Fix(115L), q_mathml_rbp) |> ignore // added by BLW, 1 Oct 2001
  putprop(q_mncexpt, q_mathml_mexpt, q_mathml) |> ignore
  putprop(q_mncexpt, Fix(135L), q_mathml_lbp) |> ignore
  putprop(q_mncexpt, Fix(134L), q_mathml_rbp) |> ignore
  putprop(q_mnctimes, q_mathml_nary, q_mathml) |> ignore
  putprop(q_mnctimes, s("<mi>&ctdot;</mi> "), q_mathmlsym) |> ignore
  putprop(q_mnctimes, Fix(110L), q_mathml_lbp) |> ignore
  putprop(q_mnctimes, Fix(109L), q_mathml_rbp) |> ignore
  putprop(q_mtimes, q_mathml_nary, q_mathml) |> ignore
  putprop(q_mtimes, s("<mspace width=\"" + ths + "\"/>"), q_mathmlsym) |> ignore // thinmathspace
  putprop(q_mtimes, Fix(120L), q_mathml_lbp) |> ignore
  putprop(q_mtimes, Fix(120L), q_mathml_rbp) |> ignore
  putprop(q_p_sqrt, q_mathml_sqrt, q_mathml) |> ignore
  putprop(q_d_cubrt, q_mathml_cubrt, q_mathml) |> ignore
  putprop(q_mquotient, q_mathml_mquotient, q_mathml) |> ignore
  putprop(q_mquotient, ls(["<mo>/</mo>"]), q_mathmlsym) |> ignore
  putprop(q_mquotient, Fix(122L), q_mathml_lbp) |> ignore // dunno about this
  putprop(q_mquotient, Fix(123L), q_mathml_rbp) |> ignore
  putprop(q_d_matrix, q_mathml_matrix, q_mathml) |> ignore
  putprop(q_p_sum, q_mathml_sum, q_mathml) |> ignore
  putprop(q_p_lsum, q_mathml_lsum, q_mathml) |> ignore
  putprop(q_p_product, q_mathml_sum, q_mathml) |> ignore
  putprop(q_p_integrate, q_mathml_int, q_mathml) |> ignore
  putprop(q_p_limit, q_mathml_limit, q_mathml) |> ignore
  putprop(q_mrarr, q_mathml_infix, q_mathml) |> ignore
  putprop(q_mrarr, ls(["<mo>&rarr;</mo> "]), q_mathmlsym) |> ignore
  putprop(q_mrarr, Fix(80L), q_mathml_lbp) |> ignore
  putprop(q_mrarr, Fix(80L), q_mathml_rbp) |> ignore
  putprop(q_p_at, q_mathml_at, q_mathml) |> ignore
  putprop(q_p_at_difference, q_mathml_at_difference, q_mathml) |> ignore
  putprop(q_p_binomial, q_mathml_choose, q_mathml) |> ignore
  putprop(q_rat, q_mathml_rat, q_mathml) |> ignore
  putprop(q_rat, Fix(120L), q_mathml_lbp) |> ignore
  putprop(q_rat, Fix(121L), q_mathml_rbp) |> ignore
  putprop(q_mplus, q_mathml_mplus, q_mathml) |> ignore
  putprop(q_mplus, Fix(100L), q_mathml_lbp) |> ignore
  putprop(q_mplus, Fix(100L), q_mathml_rbp) |> ignore
  putprop(q_mminus, q_mathml_prefix, q_mathml) |> ignore
  putprop(q_mminus, ls(["<mo>-</mo>"]), q_mathmlsym) |> ignore
  putprop(q_mminus, Fix(100L), q_mathml_rbp) |> ignore
  putprop(q_mminus, Fix(100L), q_mathml_lbp) |> ignore
  let rel_ops : Array[(Value, String?)] = [
    (q_min, Some("<mo>&isin;</mo> ")),
    (q_mequal, Some("<mo>=</mo> ")),
    (q_mnotequal, None),
    (q_mgreaterp, Some("<mo>&gt;</mo> ")),
    (q_mgeqp, Some("<mo>&ge;</mo> ")),
    (q_mlessp, Some("<mo>&lt;</mo> ")),
    (q_mleqp, Some("<mo>&le;</mo> ")),
  ]
  for e in rel_ops {
    putprop(e.0, q_mathml_infix, q_mathml) |> ignore
    if e.1 is Some(sy) {
      putprop(e.0, ls([sy]), q_mathmlsym) |> ignore
    }
    putprop(e.0, Fix(80L), q_mathml_lbp) |> ignore
    putprop(e.0, Fix(80L), q_mathml_rbp) |> ignore
  }
  putprop(q_mnot, q_mathml_prefix, q_mathml) |> ignore
  putprop(q_mnot, ls(["<mo>&not;</mo> "]), q_mathmlsym) |> ignore
  putprop(q_mnot, Fix(70L), q_mathml_rbp) |> ignore
  putprop(q_mand, q_mathml_nary, q_mathml) |> ignore
  putprop(q_mand, ls(["<mo>&and;</mo> "]), q_mathmlsym) |> ignore
  putprop(q_mand, Fix(60L), q_mathml_lbp) |> ignore
  putprop(q_mand, Fix(60L), q_mathml_rbp) |> ignore
  putprop(q_mor, q_mathml_nary, q_mathml) |> ignore
  putprop(q_mor, ls(["<mo>&or;</mo> "]), q_mathmlsym) |> ignore
  let setups : Array[(Value, String)] = [
    (q_p_acos, "<mi>arccos</mi> "),
    (q_p_asin, "<mi>arcsin</mi> "),
    (q_p_atan, "<mi>arctan</mi> "),
    (sym("%arg"), "<mi>arg</mi> "),
    (q_p_cos, "<mi>cos</mi> "),
    (q_p_cosh, "<mi>cosh</mi> "),
    (q_p_cot, "<mi>cot</mi> "),
    (q_p_coth, "<mi>coth</mi> "),
    (q_p_csc, "<mi>cosec</mi> "),
    (sym("%deg"), "<mi>deg</mi> "),
    (q_p_determinant, "<mi>det</mi> "),
    (sym("%dim"), "<mi>dim</mi> "),
    (sym("%exp"), "<mi>exp</mi> "),
    (sym("%gcd"), "<mi>gcd</mi> "),
    (sym("%hom"), "<mi>hom</mi> "),
    (sym("%inf"), "<mi>&infin;</mi> "),
    (sym("%ker"), "<mi>ker</mi> "),
    (sym("%lg"), "<mi>lg</mi> "),
    (sym("%liminf"), "<mi>lim inf</mi> "),
    (sym("%limsup"), "<mi>lim sup</mi> "),
    (sym("%ln"), "<mi>ln</mi> "),
    (q_p_log, "<mi>log</mi> "),
    (sym("%max"), "<mi>max</mi> "),
    (sym("%min"), "<mi>min</mi> "),
    (q_p_sec, "<mi>sec</mi> "),
    (q_p_sech, "<mi>sech</mi> "),
    (q_p_sin, "<mi>sin</mi> "),
    (q_p_sinh, "<mi>sinh</mi> "),
    (sym("%sup"), "<mi>sup</mi> "),
    (q_p_tan, "<mi>tan</mi> "),
    (q_p_tanh, "<mi>tanh</mi> "),
  ]
  for e in setups {
    mathml_setup(list([e.0, s(e.1)])) |> ignore
  }
  putprop(q_mor, q_mathml_nary, q_mathml) |> ignore
  putprop(q_mor, Fix(50L), q_mathml_lbp) |> ignore
  putprop(q_mor, Fix(50L), q_mathml_rbp) |> ignore
  putprop(q_mcond, q_mathml_mcond, q_mathml) |> ignore
  putprop(q_mcond, Fix(25L), q_mathml_lbp) |> ignore
  putprop(q_mcond, Fix(25L), q_mathml_rbp) |> ignore
  putprop(q_p_del, q_mathml_prefix, q_mathml) |> ignore
  putprop(q_p_del, ls(["<mo>&DifferentialD;</mo>"]), q_mathmlsym) |> ignore
  putprop(q_p_del, Fix(125L), q_mathml_rbp) |> ignore
  putprop(q_p_derivative, q_mathml_derivative, q_mathml) |> ignore
  putprop(q_mdo, q_mathml_mdo, q_mathml) |> ignore
  putprop(q_mdo, Fix(30L), q_mathml_lbp) |> ignore
  putprop(q_mdo, Fix(30L), q_mathml_rbp) |> ignore
  putprop(q_mdoin, q_mathml_mdoin, q_mathml) |> ignore
  putprop(q_mdoin, Fix(30L), q_mathml_rbp) |> ignore
}
