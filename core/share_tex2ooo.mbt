// Port of share/contrib/tex2ooo.lisp: modifications of tex properties and
// formatting functions to yield output suitable for the OpenOffice formula
// writer (Dieter Schuster; extracted from mactex.lisp by Robert Dodier).
// Loading it redefines many functions of mactex.lisp.
//
// Usage:
//  load (tex2ooo);
//  tex (expr);

///|
/// DEFUN of a mactex function: install it in the function cell and in
/// mactex's table of redefinitions.
fn share_tex2ooo__redefine(
  name : Value,
  f : (Array[Value]) -> Value raise,
) -> Unit raise {
  defun(name, f, name=symbol_name(name))
  mactex__redefined.set(symbol_name(name), f)
}

///|
fn share_tex2ooo__strs(a : Array[String]) -> Value {
  list(a.map(s => Value::Str(s)))
}

///|
fn share_tex2ooo__string(x : Value) -> String raise {
  match x {
    Str(s) => s
    Char(c) => c.to_string()
    Sym(_) => symbol_name(x)
    _ => princ_to_string(x)
  }
}

///|
fn share_tex2ooo__quote_pct(sym_ : Value) -> Value raise {
  let strsym = share_tex2ooo__string(sym_)
  let chars = string_chars(strsym)
  let mut pos = -1
  for i, c in chars {
    if c == '%' || c == '_' {
      pos = i
      break
    }
  }
  if pos >= 0 {
    Str(
      substring(strsym, 0, end=pos) +
      "" +
      chars[pos].to_string() +
      share_tex2ooo__string(
        share_tex2ooo__quote_pct(Str(substring(strsym, pos + 1))),
      ),
    )
  } else {
    Str(strsym)
  }
}

///|
fn share_tex2ooo__tex1(mexplabel : Value, filename : Value) -> Value raise {
  with_specials([(q_texport, Nil), (q_d_gcprint, Nil), (q_ccol, Nil)], () => {
    let mut mexplabel = mexplabel
    if mexplabel is Nil {
      displa(Str(" No eqn given to TeX")) |> ignore
      return Nil
    }
    // collect the file-name, if any, and open a port if needed
    let texport = if filename is Nil {
      symval(standard_output)
    } else {
      make_string_output_stream()
    }
    set(q_texport, texport) |> ignore
    // do a normal evaluation of the expression in macsyma
    let mut mexp = meval(mexplabel)
    let mut itsalabel = false
    if memq(mexplabel, symval(q_d_labels)).truthy() {
      // leave it if it is a label
      mexplabel = Str(
        "(" + share_tex2ooo__string(print_invert_case(stripdollar(mexplabel))) + ")",
      )
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
    // (string $inchar): the CL name of the symbol, upper case
    let cl_name = (v : Value) => invert_case(share_tex2ooo__string(v))
    let label_str = share_tex2ooo__string(mexplabel)
    let prefix_match = (c : String) => c.length() <= label_str.length() &&
      substring(c, 1, end=c.length()) == substring(label_str, 1, end=c.length())
    if !atom(mexp) && memq(caar(mexp), list([q_mdefine, q_mdefmacro])).truthy() {
      if mexplabel.truthy() {
        mexplabel = share_tex2ooo__quote_pct(mexplabel)
      }
      format(texport, "|~%", []) |> ignore // delimit with |marks
      if mexplabel.truthy() {
        format(texport, "~a ", [mexplabel]) |> ignore
      }
      mgrind(mexp, texport) |> ignore // write expression as string
      format(texport, ";|~%", []) |> ignore
    } else if itsalabel &&
      prefix_match(cl_name(symval(q_d_inchar))) &&
      // Check to make sure it isn't an outchar in disguise
      !prefix_match(cl_name(symval(q_d_outchar))) {
      // aha, this is a C-line: do the grinding:
      format(texport, "~%|~a ", [mexplabel]) |> ignore // delimit with |marks
      mgrind(mexp, texport) |> ignore // write expression as string
      format(texport, ";|~%", []) |> ignore
    } else {
      if mexplabel.truthy() {
        mexplabel = share_tex2ooo__quote_pct(mexplabel)
      }
      // display the expression for TeX now:
      myprinc(Str(""), texport~) |> ignore
      // initially the left and right contexts are empty lists, and there
      // are implicit parens around the whole expression
      for x in tex(mexp, Nil, Nil, q_mparen, q_mparen).iter() {
        myprinc(x, texport~) |> ignore
      }
      if mexplabel.truthy() {
        format(texport, "", [mexplabel]) |> ignore
      }
      format(texport, "", []) |> ignore
    }
    terpri(stream=texport)
    if filename.truthy() {
      // and close port if not terminal
      mactex__append_to_file(
        share_tex2ooo__string(print_invert_case(stripdollar(filename))),
        get_output_stream_string(texport),
      )
    }
    mexplabel
  })
}

///|
fn share_tex2ooo__tex_string(x : Value) -> Value raise {
  if equal(x, Str("")) {
    Str("")
  } else if (match x {
      Str(s) => s.length() > 0 && char_at(s, 0) == '\\'
      _ => false
    }) {
    x
  } else {
    Str("" + share_tex2ooo__string(x) + "")
  }
}

///|
fn share_tex2ooo__tex_char(x : Value) -> Value raise {
  if eql(x, Char('|')) {
    Str("")
  } else {
    Str("" + share_tex2ooo__string(x) + "")
  }
}

///|
fn share_tex2ooo__tex_stripdollar(sym_ : Value) -> Value raise {
  if !symbolp(sym_) {
    return sym_
  }
  let pname_chars = string_chars(
    share_tex2ooo__string(share_tex2ooo__quote_pct(sym_)),
  )
  let l = pname_chars.length()
  let mut begin_sub = -1
  let mut i = l - 1
  while true {
    if i < 0 {
      raise LispError::SimpleError(
        "Invalid index -1 for (SIMPLE-ARRAY CHARACTER)",
      )
    }
    if !(pname_chars[i] >= '0' && pname_chars[i] <= '9') {
      begin_sub = i + 1
      break
    }
    i -= 1
  }
  let tem : Array[Char] = []
  let mut begin_sub_t = false
  for i in 0..<l {
    if !begin_sub_t && i == begin_sub {
      let key = Value::Str(String::from_array(tem))
      // *TEX-TRANSLATIONS* is not defined anywhere: CL signals
      // UNBOUND-VARIABLE here.
      let tt = sym("*tex-translations*")
      if !boundp(tt) {
        raise LispError::SimpleError(
          "The variable *TEX-TRANSLATIONS* is unbound.",
        )
      }
      let a = assoc_equal(key, symval(tt))
      if a.truthy() {
        let a = cdr(a)
        tem.clear()
        for c in string_chars(share_tex2ooo__string(a)) {
          tem.push(c)
        }
      }
      if i != l - 1 {
        tem.push('{')
        begin_sub_t = true
      }
    }
    if !(i == 0 && pname_chars[i] == '$') {
      tem.push(pname_chars[i])
    }
  }
  if begin_sub_t {
    tem.push('}')
  }
  sym(String::from_array(tem))
}

///|
fn share_tex2ooo__texnumformat(atom_ : Value) -> Value raise {
  if integerp(atom_) {
    return atom_
  }
  let r = explode(atom_)
  let is_e = fn(c : Value) -> Bool raise {
    match c {
      Sym(_) => {
        let n = symbol_name(c)
        n == "e" || n == "E"
      }
      _ => false
    }
  }
  // is it ddd.ddde+EE
  let mut exponent = r
  while exponent.truthy() && !is_e(car(exponent)) {
    exponent = cdr(exponent)
  }
  if exponent is Nil {
    // it is not. go with it as given
    atom_
  } else {
    let mut rr = reverse(r)
    while rr.truthy() && !is_e(car(rr)) {
      rr = cdr(rr)
    }
    let firstpart = nreverse(cdr(rr))
    strcat(
      list([
        strcat(firstpart),
        Str(" times 10^{"),
        strcat(cdr(exponent)),
        Str("}"),
      ]),
    )
  }
}

///|
fn share_tex2ooo__tex_paren(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    x,
    append(l, share_tex2ooo__strs([" left( "])),
    cons(Str(" right)"), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn share_tex2ooo__tex_array(x : Value, l : Value, r : Value) -> Value raise {
  let mut x = x
  let mut l = l
  if eq(q_mqapply, caar(x)) {
    let f = cadr(x)
    x = cdr(x)
    l = tex(
      f,
      append(l, share_tex2ooo__strs([" left( "])),
      share_tex2ooo__strs([" right) "]),
      q_mparen,
      q_mparen,
    )
  } else {
    let f = caar(x)
    l = tex(f, l, Nil, symval(q_lop), q_mfunction)
  }
  let r = nconc(
    tex_list(cdr(x), Nil, share_tex2ooo__strs(["}"]), Str(",")),
    r,
  )
  nconc(l, cons(Str("_{"), r))
}

///|
fn share_tex2ooo__tex_mexpt(x : Value, l : Value, r : Value) -> Value raise {
  let nc = eq(caar(x), q_mncexpt) // true if a^^b rather than a^b
  let mut l = l
  let mut r = r
  // here is where we have to check for f(x)^b to be displayed as f^b(x),
  // as is the case for sin(x)^2 . which should be sin^2 x rather than
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
        memq(q_array, cdar(fx)) is Nil && // fix for x[i]^2
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
        (
          (atom(expon) && !numberp(expon)) || // f(x)^y is ok
          (atom(expon) && numberp(expon) && num_gt(expon, Fix(0L)))
        )
      // f(x)^3 is ok, but not f(x)^-1, which could be the inverse of f
      if doit {
        l = tex(mk(q_mexpt, [f, expon]), l, Nil, q_mparen, q_mparen)
        if cdr(bascdr) is Nil && eq(get(f, q_tex), q_tex_prefix) {
          r = tex(car(bascdr), Nil, r, f, q_mparen)
        } else {
          r = tex(cons(list1(q_mprogn), bascdr), Nil, r, q_mparen, q_mparen)
        }
        true
      } else {
        false // won't doit. fall through
      }
    }
  if !hack {
    l = if numberp(cadr(x)) && numneedsparen(cadr(x)).truthy() {
      tex(
        cadr(x),
        cons(Str(" left( "), l),
        share_tex2ooo__strs([" right) "]),
        symval(q_lop),
        caar(x),
      )
    } else {
      tex(cadr(x), l, Nil, symval(q_lop), caar(x))
    }
    let x = nformat(caddr(x))
    r = if mmminusp(x).truthy() {
      // the change in base-line makes parens unnecessary
      if nc {
        tex(
          cadr(x),
          share_tex2ooo__strs(["^ {- langle "]),
          cons(Str(" rangle }"), r),
          q_mparen,
          q_mparen,
        )
      } else {
        tex(
          cadr(x),
          share_tex2ooo__strs(["^ {- "]),
          cons(Str(" }"), r),
          q_mparen,
          q_mparen,
        )
      }
    } else if nc {
      tex(
        x,
        share_tex2ooo__strs(["^{ langle "]),
        cons(Str(" rangle }"), r),
        q_mparen,
        q_mparen,
      )
    } else if integerp(x) && num_lt(x, Fix(10L)) {
      tex(x, share_tex2ooo__strs(["^"]), cons(Str(" "), r), q_mparen, q_mparen)
    } else {
      tex(x, share_tex2ooo__strs(["^{"]), cons(Str("}"), r), q_mparen, q_mparen)
    }
  }
  append(l, r)
}

///|
/// format as \\sqrt { } assuming implicit parens for sqr grouping
fn share_tex2ooo__tex_sqrt(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    cadr(x),
    append(l, share_tex2ooo__strs([" sqrt {"])),
    append(share_tex2ooo__strs(["}"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn share_tex2ooo__tex_cubrt(x : Value, l : Value, r : Value) -> Value raise {
  tex(
    cadr(x),
    append(l, share_tex2ooo__strs([" nroot {3} {"])),
    append(share_tex2ooo__strs(["}"]), r),
    q_mparen,
    q_mparen,
  )
}

///|
fn share_tex2ooo__tex_mquotient(x : Value, l : Value, r : Value) -> Value raise {
  if cddr(x) is Nil || cdddr(x).truthy() {
    wna_err(caar(x)) |> ignore
  }
  let l = tex(
    cadr(x),
    append(l, share_tex2ooo__strs(["{alignc {"])),
    Nil,
    q_mparen,
    q_mparen,
  )
  // the divide bar groups things
  let r = tex(
    caddr(x),
    share_tex2ooo__strs(["} over {"]),
    append(share_tex2ooo__strs(["}}"]), r),
    q_mparen,
    q_mparen,
  )
  append(l, r)
}

///|
/// matrix looks like ((mmatrix)((mlist) a b) ...)
fn share_tex2ooo__tex_matrix(x : Value, l : Value, r : Value) -> Value raise {
  let foo = mapcan(
    y => tex_list(cdr(y), Nil, share_tex2ooo__strs([" ## "]), Str(" # ")),
    cdr(x),
  )
  let lst = last(foo)
  if lst is Nil {
    raise LispError::SimpleError("The value NIL is not of type CONS")
  }
  rplaca(lst, Str(" ")) |> ignore
  append(
    l,
    append(
      share_tex2ooo__strs([" left( matrix {"]),
      append(foo, append(share_tex2ooo__strs(["} right) "]), r)),
    ),
  )
}

///|
fn share_tex2ooo__append_all(parts : Array[Value]) -> Value raise {
  let mut acc : Value = Nil
  for i = parts.length() - 1; i >= 0; i = i - 1 {
    acc = append(parts[i], acc)
  }
  acc
}

///|
fn share_tex2ooo__tex_lsum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_lsum) {
    Str("sum from {")
  } else {
    Nil
  }
  // gotta be one of those above
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // summand
  // "index = lowerlimit"
  let index = tex(
    mk_simp(q_min, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  share_tex2ooo__append_all([
    l,
    list1(op),
    index,
    share_tex2ooo__strs(["}}{"]),
    s1,
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_sum(x : Value, l : Value, r : Value) -> Value raise {
  let op : Value = if eq(caar(x), q_p_sum) {
    Str(" sum from {")
  } else if eq(caar(x), q_p_product) {
    Str(" prod from {")
  } else {
    Nil
  }
  // gotta be one of those above
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // summand
  // "index = lowerlimit"
  let index = tex(
    mk_simp(q_mequal, [caddr(x), cadddr(x)]),
    Nil,
    Nil,
    q_mparen,
    q_mparen,
  )
  let toplim = tex(car(cddddr(x)), Nil, Nil, q_mparen, q_mparen)
  share_tex2ooo__append_all([
    l,
    list1(op),
    index,
    share_tex2ooo__strs(["} to {"]),
    toplim,
    share_tex2ooo__strs(["}{"]),
    s1,
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_int(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, q_mparen) // integrand delims / & d
  let var_ = tex(caddr(x), Nil, Nil, q_mparen, symval(q_rop)) // variable
  if length(x) == 3 {
    share_tex2ooo__append_all([
      l,
      share_tex2ooo__strs([" int {"]),
      s1,
      share_tex2ooo__strs(["}{`d"]),
      var_,
      share_tex2ooo__strs(["}"]),
      r,
    ])
  } else {
    // presumably length 5
    let low = tex(nth(3, x), Nil, Nil, q_mparen, q_mparen)
    // 1st item is 0
    let hi = tex(nth(4, x), Nil, Nil, q_mparen, q_mparen)
    share_tex2ooo__append_all([
      l,
      share_tex2ooo__strs([" int from {"]),
      low,
      share_tex2ooo__strs(["} to {"]),
      hi,
      share_tex2ooo__strs(["}{"]),
      s1,
      share_tex2ooo__strs([" d"]),
      var_,
      share_tex2ooo__strs(["}"]),
      r,
    ])
  }
}

///|
/// ignoring direction, last optional arg to limit
fn share_tex2ooo__tex_limit(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, q_mparen, symval(q_rop)) // limitfunction
  // the thing underneath "limit"
  let subfun = subst(
    Str(" rightarrow "),
    sym("="),
    tex(
      mk_simp(q_mequal, [caddr(x), cadddr(x)]),
      Nil,
      Nil,
      q_mparen,
      q_mparen,
    ),
  )
  share_tex2ooo__append_all([
    l,
    share_tex2ooo__strs([" lim from {"]),
    subfun,
    share_tex2ooo__strs(["}{"]),
    s1,
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_at(x : Value, l : Value, r : Value) -> Value raise {
  let s1 = tex(cadr(x), Nil, Nil, symval(q_lop), symval(q_rop))
  let sub = tex(caddr(x), Nil, Nil, q_mparen, q_mparen)
  share_tex2ooo__append_all([
    l,
    share_tex2ooo__strs([" left ."]),
    s1,
    share_tex2ooo__strs([" right |_{"]),
    sub,
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_mbox(x : Value, l : Value, r : Value) -> Value raise {
  share_tex2ooo__append_all([
    l,
    share_tex2ooo__strs(["{"]),
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_choose(x : Value, l : Value, r : Value) -> Value raise {
  share_tex2ooo__append_all([
    l,
    share_tex2ooo__strs([" matrix {"]),
    tex(cadr(x), Nil, Nil, q_mparen, q_mparen),
    share_tex2ooo__strs([" ## "]),
    tex(caddr(x), Nil, Nil, q_mparen, q_mparen),
    share_tex2ooo__strs(["}"]),
    r,
  ])
}

///|
fn share_tex2ooo__tex_mplus(x : Value, l : Value, r : Value) -> Value raise {
  let mut r = r
  if memq(q_trunc, car(x)).truthy() {
    r = cons(Str(" + dotsaxis "), r)
  }
  if cddr(x) is Nil {
    if cdr(x) is Nil {
      tex_function(x, l, r, t)
    } else {
      tex(cadr(x), cons(Str(" + "), l), r, q_mplus, symval(q_rop))
    }
  } else {
    let l = tex(cadr(x), l, Nil, symval(q_lop), q_mplus)
    let mut x = cddr(x)
    let mut nl = l
    while cdr(x).truthy() {
      let (ll, dissym) = if mmminusp(car(x)).truthy() {
        (cadar(x), share_tex2ooo__strs([" - "]))
      } else {
        (car(x), share_tex2ooo__strs([" + "]))
      }
      nl = append(nl, tex(ll, dissym, Nil, q_mplus, q_mplus))
      x = cdr(x)
    }
    let (ll, dissym) = if mmminusp(car(x)).truthy() {
      (cadar(x), share_tex2ooo__strs([" - "]))
    } else {
      (car(x), share_tex2ooo__strs([" + "]))
    }
    r = tex(ll, dissym, r, q_mplus, symval(q_rop))
    append(nl, r)
  }
}

///|
fn share_tex2ooo__tex_mcond(x : Value, l : Value, r : Value) -> Value raise {
  append(
    l,
    append(
      tex(
        cadr(x),
        share_tex2ooo__strs([" bold if"]),
        share_tex2ooo__strs([" bold then"]),
        q_mparen,
        q_mparen,
      ),
      if eql(nth(4, x), q_d_false) {
        tex(caddr(x), Nil, r, q_mcond, symval(q_rop))
      } else {
        append(
          tex(caddr(x), Nil, Nil, q_mparen, q_mparen),
          tex(
            nth(4, x),
            share_tex2ooo__strs([" bold else"]),
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
fn share_tex2ooo__tex_mdo(x : Value, l : Value, r : Value) -> Value raise {
  tex_list(share_tex2ooo__texmdo(x), l, r, Str("`"))
}

///|
fn share_tex2ooo__tex_mdoin(x : Value, l : Value, r : Value) -> Value raise {
  tex_list(share_tex2ooo__texmdoin(x), l, r, Str("`"))
}

///|
fn share_tex2ooo__mdo_tail(x : Value) -> Value raise {
  let seventh = nth(6, x)
  let c : Value = if seventh is Nil {
    Nil
  } else if eq(q_mnot, caar(seventh)) {
    list([Str(" bold while"), cadr(seventh)])
  } else {
    list([Str(" bold unless"), seventh])
  }
  nconc(c, list([Str(" bold do"), nth(7, x)]))
}

///|
fn share_tex2ooo__texmdo(x : Value) -> Value raise {
  let c1 : Value = if nth(1, x).truthy() {
    list([Str(" bold for"), nth(1, x)])
  } else {
    Nil
  }
  let c2 : Value = if equal(Fix(1L), nth(2, x)) {
    Nil
  } else if nth(2, x).truthy() {
    list([Str(" bold from"), nth(2, x)])
  } else {
    Nil
  }
  let c3 : Value = if equal(Fix(1L), nth(3, x)) {
    Nil
  } else if nth(3, x).truthy() {
    list([Str(" bold step"), nth(3, x)])
  } else if nth(4, x).truthy() {
    list([Str(" bold next"), nth(4, x)])
  } else {
    Nil
  }
  let c4 : Value = if nth(5, x).truthy() {
    list([Str(" bold thru"), nth(5, x)])
  } else {
    Nil
  }
  nconc(c1, nconc(c2, nconc(c3, nconc(c4, share_tex2ooo__mdo_tail(x)))))
}

///|
fn share_tex2ooo__texmdoin(x : Value) -> Value raise {
  let c1 = list([Str(" bold for"), nth(1, x), Str(" bold in"), nth(2, x)])
  let c2 : Value = if nth(5, x).truthy() {
    list([Str(" bold thru"), nth(5, x)])
  } else {
    Nil
  }
  nconc(c1, nconc(c2, share_tex2ooo__mdo_tail(x)))
}

///|
fn share_tex2ooo__tex_mlabel(x : Value, l : Value, r : Value) -> Value raise {
  let lab = if cadr(x).truthy() {
    list1(format(Nil, "", [share_tex2ooo__tex_stripdollar(cadr(x))]))
  } else {
    Nil
  }
  tex(caddr(x), append(l, lab), r, q_mparen, q_mparen)
}

///|
fn share_tex2ooo__tex_spaceout(x : Value, l : Value, r : Value) -> Value raise {
  // The control string "~" is invalid: SBCL compiles this function to
  // signal the FORMAT error.
  raise LispError::SimpleError(
    "error in FORMAT: string ended before directive was found\n  ~\n   ^ for " +
    princ_to_string(num_mul(Fix(3L), cadr(x))) +
    " " +
    princ_to_string(append(l, r)),
  )
}

///|
fn init_share_tex2ooo() -> Unit raise {
  let f3 = (f : (Value, Value, Value) -> Value raise) => (a : Array[Value]) => f(
    arg(a, 0),
    arg(a, 1),
    arg(a, 2),
  )
  share_tex2ooo__redefine(sym("quote-%"), a => share_tex2ooo__quote_pct(
    arg(a, 0),
  ))
  share_tex2ooo__redefine(q_tex1, a => share_tex2ooo__tex1(arg(a, 0), arg(a, 1)))
  share_tex2ooo__redefine(q_tex_string, a => share_tex2ooo__tex_string(
    arg(a, 0),
  ))
  share_tex2ooo__redefine(q_tex_char, a => share_tex2ooo__tex_char(arg(a, 0)))
  share_tex2ooo__redefine(q_tex_stripdollar, a => share_tex2ooo__tex_stripdollar(
    arg(a, 0),
  ))
  share_tex2ooo__redefine(q_texnumformat, a => share_tex2ooo__texnumformat(
    arg(a, 0),
  ))
  share_tex2ooo__redefine(q_tex_paren, f3(share_tex2ooo__tex_paren))
  share_tex2ooo__redefine(q_tex_array, f3(share_tex2ooo__tex_array))
  let s = (x : String) => Value::Str(x)
  let ls = (a : Array[String]) => share_tex2ooo__strs(a)
  let texwords : Array[(Value, String)] = [
    (q_mprog, ""),
    (q_p_erf, " erf "),
    (q_d_erf, " erf "), // etc for multicharacter names
    (q_d_true, " true "),
    (q_d_false, " false "),
  ]
  for e in texwords {
    putprop(e.0, s(e.1), q_texword) |> ignore
  }
  putprop(q_mprogn, list([ls([" left( "]), s(" right) ")]), q_texsym) |> ignore
  putprop(q_mlist, list([ls([" left[ "]), s(" right] ")]), q_texsym) |> ignore
  putprop(q_mabs, list([ls([" left lline "]), s(" right rline ")]), q_texsym)
  |> ignore
  let texwords2 : Array[(String, String)] = [
    ("$%pi", "%pi"),
    ("$inf", " infty "),
    ("$minf", " - infty "),
    ("%laplace", "%DELTA"),
    ("$alpha", "%alpha"),
    ("$beta", "%beta"),
    ("$gamma", "%gamma"),
    ("%gamma", "%GAMMA"),
    ("$%gamma", "%gamma"),
    ("$delta", "%delta"),
    ("$epsilon", "%varepsilon"),
    ("$zeta", "%zeta"),
    ("$eta", "%eta"),
    ("$theta", "%vartheta"),
    ("$iota", "%iota"),
    ("$kappa", "%varkappa"),
    ("$mu", "%my"),
    ("$nu", "%nu"),
    ("$xi", "%xi"),
    ("$pi", "%pi"),
    ("$rho", "%rho"),
    ("$sigma", "%sigma"),
    ("$tau", "%tau"),
    ("$upsilon", "%ypsilon"),
    ("$phi", "%varphi"),
    ("$chi", "%chi"),
    ("$psi", "%psi"),
    ("$omega", "%omega"),
    ("$Gamma", "%GAMMA"),
    ("$Delta", "%DELTA"),
    ("$Theta", "%ThETA"),
    ("$Lambda", "%LAMBDA"),
    ("$Xi", "%XI"),
    ("$Pi", "%PI"),
    ("$Sigma", "%SIGMA"),
    ("$Upsilon", "%YPSILON"),
    ("$Phi", "%PHI"),
    ("$Psi", "%PSI"),
    ("$Omega", "%OMEGA"),
  ]
  for e in texwords2 {
    putprop(sym(e.0), s(e.1), q_texword) |> ignore
  }
  putprop(q_marrow, ls([" rightarrow "]), q_texsym) |> ignore
  share_tex2ooo__redefine(q_tex_mexpt, f3(share_tex2ooo__tex_mexpt))
  putprop(q_mnctimes, ls([" cdot "]), q_texsym) |> ignore
  putprop(q_mtimes, ls([" cdot "]), q_texsym) |> ignore // HMM, SEEMS INADVISABLE
  share_tex2ooo__redefine(q_tex_sqrt, f3(share_tex2ooo__tex_sqrt))
  share_tex2ooo__redefine(q_tex_cubrt, f3(share_tex2ooo__tex_cubrt))
  putprop(q_mquotient, ls([" over "]), q_texsym) |> ignore
  share_tex2ooo__redefine(q_tex_mquotient, f3(share_tex2ooo__tex_mquotient))
  share_tex2ooo__redefine(q_tex_matrix, f3(share_tex2ooo__tex_matrix))
  share_tex2ooo__redefine(q_tex_lsum, f3(share_tex2ooo__tex_lsum))
  share_tex2ooo__redefine(q_tex_sum, f3(share_tex2ooo__tex_sum))
  share_tex2ooo__redefine(q_tex_int, f3(share_tex2ooo__tex_int))
  share_tex2ooo__redefine(q_tex_limit, f3(share_tex2ooo__tex_limit))
  share_tex2ooo__redefine(q_tex_at, f3(share_tex2ooo__tex_at))
  share_tex2ooo__redefine(q_tex_mbox, f3(share_tex2ooo__tex_mbox))
  share_tex2ooo__redefine(q_tex_choose, f3(share_tex2ooo__tex_choose))
  share_tex2ooo__redefine(q_tex_mplus, f3(share_tex2ooo__tex_mplus))
  let texsyms : Array[(Value, String)] = [
    (q_mminus, " `-`"),
    (q_min, " in "),
    (q_mgeqp, " geq "),
    (q_mleqp, " leq "),
    (q_mnot, " not "),
    (q_mand, " and "),
    (q_mor, " or "),
    (q_mnotequal, " neq "),
  ]
  for e in texsyms {
    putprop(e.0, ls([e.1]), q_texsym) |> ignore
  }
  let setups : Array[(Value, String)] = [
    (q_p_acos, " arccos "),
    (q_p_asin, " arcsin "),
    (q_p_atan, " arctan "),
    (q_p_cos, " cos "),
    (q_p_cosh, " cosh "),
    (q_p_cot, " cot "),
    (q_p_coth, " coth "),
    (q_p_csc, " csc "),
    (q_p_determinant, " det "),
    (sym("%dim"), " dim "),
    (sym("%exp"), " exp "),
    (sym("%gcd"), " gcd "),
    (sym("%inf"), " inf "),
    (sym("%ln"), " ln "),
    (q_p_log, " log "),
    (sym("%max"), " max "),
    (sym("%min"), " min "),
    (q_p_sec, " sec "),
    (q_p_sin, " sin "),
    (q_p_sinh, " sinh "),
    (q_p_tan, " tan "),
    (q_p_tanh, " tanh "),
  ]
  for e in setups {
    tex_setup(list([e.0, s(e.1)])) |> ignore
  }
  share_tex2ooo__redefine(q_tex_mcond, f3(share_tex2ooo__tex_mcond))
  share_tex2ooo__redefine(q_tex_mdo, f3(share_tex2ooo__tex_mdo))
  share_tex2ooo__redefine(q_tex_mdoin, f3(share_tex2ooo__tex_mdoin))
  share_tex2ooo__redefine(q_texmdo, a => share_tex2ooo__texmdo(arg(a, 0)))
  share_tex2ooo__redefine(q_texmdoin, a => share_tex2ooo__texmdoin(arg(a, 0)))
  putprop(sym(" --> "), s(" rightarrow "), q_texsym) |> ignore
  putprop(sym(" WHERE "), s("` bold where`"), q_texsym) |> ignore
  share_tex2ooo__redefine(q_tex_mlabel, f3(share_tex2ooo__tex_mlabel))
  share_tex2ooo__redefine(q_tex_spaceout, f3(share_tex2ooo__tex_spaceout))
}
