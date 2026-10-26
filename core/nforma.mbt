// Port of src/nforma.lisp: NFORMAT, converting simplified expressions to the
// form used for display (e.g. a*b^-1 to a/b, negative numbers to (mminus)).

///|
/// `(type-of form)` reduced to what NFORMAT needs: a symbol naming the type
/// of an atom, on which a FORMATTER property may be found.
fn nforma__type_of(form : Value) -> Value {
  match form {
    Ratio(_, _) => q_ratio
    Cplx(_, _) => q_complex
    // The numeric.lisp classes are BIGFLOAT::BIGFLOAT and
    // BIGFLOAT::COMPLEX-BIGFLOAT, not Maxima's BIGFLOAT (which has a
    // formatter for ((bigfloat) m e) forms).
    Struct(s) if s.stype.name == "bigfloat" || s.stype.name == "complex-bigfloat" =>
      sym("bigfloat::" + s.stype.name)
    Struct(s) => Sym(s.stype)
    _ => Nil
  }
}

///|
fn nformat(form : Value) -> Value raise {
  if atom(form) {
    if realp(form) && minusp(form) && float_inf_p(form) is Nil {
      return list2(list1(q_mminus), num_neg(form))
    }
    if eq(t, form) {
      return if symval(q_in_p).truthy() { t } else { q_d_true }
    }
    if form is Nil {
      return if symval(q_in_p).truthy() { Nil } else { q_d_false }
    }
    // Perhaps some object is an atom, maybe a structure: look for a
    // formatter on its type.
    let p = nforma__type_of(form)
    if p.truthy() {
      let f = get(p, q_formatter)
      if f.truthy() {
        let r = funcall(f, [form])
        if r.truthy() {
          return r
        }
      }
    }
    // just display as a lisp symbol, number, or other atom.
    return form
  }
  if atom(car(form)) {
    return form // probably an illegal form; just return it.
  }
  // Process FORM if it is simplified or has some other operator flag (e.g.,
  // TRUNC) (ignoring line number annotations). Otherwise, return FORM
  // unchanged.
  let foo = cdar(form)
  if foo is Nil {
    return form
  }
  if length(foo) == 1 {
    let bar = first(foo)
    if consp(bar) && equal(last(bar), list1(q_src)) {
      return form
    }
  }
  // the ordinary maxima objects that are tagged by their main operator
  if symbolp(caar(form)) {
    let p = get(caar(form), q_formatter)
    if p.truthy() {
      return funcall(p, [form])
    }
  }
  form
}

///|
fn form_mplus(form : Value) -> Value raise {
  let args = mapcar(x => nformat(x), cdr(form))
  let trunc = memq(q_trunc, cdar(form)).truthy()
  let simplified = memq(q_simp, cdar(form)).truthy()
  let head = if trunc { list2(q_mplus, q_trunc) } else { list1(q_mplus) }
  let powerdisp = symval(q_d_powerdisp).truthy()
  let body = if memq(q_ratsimp, cdar(form)).truthy() &&
    memq(q_simp, cdar(form)) is Nil {
    if powerdisp {
      nreverse(args)
    } else {
      args
    }
  } else if trunc && memq(q_simp, cdar(form)) is Nil {
    nreverse(args)
  } else if powerdisp || trunc || memq(q_cf, cdar(form)).truthy() {
    args
  } else if symval(q_d_negsumdispflag).truthy() && cdddr(form) is Nil {
    if mmminusp(car(args)) is Nil && mmminusp(cadr(args)).truthy() {
      args
    } else if simplified {
      nreverse(args)
    } else {
      args
    }
  } else if simplified {
    nreverse(args)
  } else {
    args
  }
  cons(head, body)
}

///|
fn form_mtimes(form : Value) -> Value raise {
  if cdr(form) is Nil {
    return list1(list1(q_mtimes))
  }
  if equal(Fix(-1L), cadr(form)) {
    return list2(list1(q_mminus), form_mtimes(cdr(form)))
  }
  let mut num : Value = Nil
  let mut den : Value = Nil
  let mut minus = false
  let mut flag = false
  let mut l = cdr(form)
  while l.truthy() {
    let dummy = nformat(car(l))
    if atom(dummy) {
      num = cons(dummy, num)
    } else if eq(q_mminus, caar(dummy)) {
      minus = !minus
      l = append(dummy, cdr(l))
    } else if eq(q_mquotient, caar(dummy)) ||
      (symval(q_d_pfeformat) is Nil && eq(q_rat, caar(dummy))) {
      if !equal(Fix(1L), cadr(dummy)) {
        num = cons(cadr(dummy), num)
      }
      den = cons(caddr(dummy), den)
    } else {
      num = cons(dummy, num)
    }
    l = cdr(l)
  }
  num = if num is Nil {
    Fix(1L)
  } else if cdr(num) is Nil {
    car(num)
  } else {
    cons(list1(q_mtimes), nreverse(num))
  }
  den = if den is Nil {
    flag = true
    Nil
  } else if cdr(den) is Nil {
    car(den)
  } else {
    cons(list1(q_mtimes), nreverse(den))
  }
  if !flag {
    num = list3(list1(q_mquotient), num, den)
  }
  if minus {
    list2(list1(q_mminus), num)
  } else {
    num
  }
}

///|
fn form_mexpt(form : Value) -> Value raise {
  if symval(q_d_sqrtdispflag).truthy() &&
    alike1(symval(q_n1_sl_sl2), caddr(form)).truthy() {
    return list2(list1(q_p_sqrt), cadr(form))
  }
  if symval(q_d_sqrtdispflag).truthy() &&
    alike1(symval(q_n_1_sl_sl2), caddr(form)).truthy() {
    return list3(list1(q_mquotient), Fix(1L), list2(list1(q_p_sqrt), cadr(form)))
  }
  if (symval(q_d__pctedispflag).truthy() && eq(q_d__pcte, cadr(form))) ||
    (symval(q_d_exptdispflag).truthy() && !eq(q_d__pcte, cadr(form))) {
    let exp_ = nformat(caddr(form))
    if !atom(exp_) && eq(q_mminus, caar(exp_)) {
      return list3(
        list1(q_mquotient),
        Fix(1L),
        if equal(Fix(1L), cadr(exp_)) {
          cadr(form)
        } else {
          list3(list1(q_mexpt), cadr(form), cadr(exp_))
        },
      )
    }
  }
  cons(list1(q_mexpt), cdr(form))
}

///|
fn form_mrat(form : Value) -> Value raise {
  let trunc = memq(q_trunc, cdar(form)).truthy()
  let mut exact = false
  if trunc && eq(cadr(form), q_ps) {
    exact = car(cadddr(form)) is Nil
  }
  let form = ratdisrepd(form)
  rdis1(form) |> ignore
  if trunc &&
    (
      atom(form) ||
      // A constant, e.g. ((mplus) $a 1)
      !(
        equal(car(form), list2(q_mplus, q_exact)) ||
        equal(car(form), list2(q_mplus, q_trunc))
      )
    ) {
    cons(
      if exact {
        list2(q_mplus, q_exact)
      } else {
        list2(q_mplus, q_trunc)
      },
      ncons(form),
    )
  } else {
    nformat(form)
  }
}

///|
fn rdis1(form : Value) -> Value raise {
  if atom(form) || specrepp(form).truthy() {
    t
  } else if cdar(form) is Nil {
    rplaca(form, list2(caar(form), q_ratsimp))
  } else {
    mapc(x => rdis1(x) |> ignore, cdr(form))
  }
}

///|
fn nformat_all(form : Value) -> Value raise {
  let form = nformat(form)
  if atom(form) || memq(caar(form), list2(q_bigfloat, q_rat)).truthy() {
    // can't recurse over cdrs
    form
  } else {
    cons(
      delsimp(car(form)),
      if memq(caar(form), list2(q_mdo, q_mdoin)).truthy() {
        mapcar(
          u => if u.truthy() {
            nformat_all(u)
          } else {
            Nil
          },
          cdr(form),
        )
      } else {
        mapcar(u => nformat_all(u), cdr(form))
      },
    )
  }
}

///|
fn init_nforma() -> Unit raise {
  set(q_in_p, Nil) |> ignore
  putprop(
    q_rat,
    lfunc("rat-formatter", args => {
      let form = arg(args, 0)
      if minusp(cadr(form)) {
        list2(
          list1(q_mminus),
          list3(list1(q_rat), num_neg(cadr(form)), caddr(form)),
        )
      } else {
        cons(list1(q_rat), cdr(form))
      }
    }),
    q_formatter,
  )
  |> ignore
  putprop(
    q_mmacroexpanded,
    lfunc("mmacroexpanded-formatter", args => nformat(caddr(arg(args, 0)))),
    q_formatter,
  )
  |> ignore
  putprop(q_mplus, q_form_mplus, q_formatter) |> ignore
  putprop(q_mtimes, q_form_mtimes, q_formatter) |> ignore
  putprop(q_mexpt, q_form_mexpt, q_formatter) |> ignore
  putprop(q_mrat, q_form_mrat, q_formatter) |> ignore
  putprop(
    q_mpois,
    lfunc("mpois-formatter", args => nformat(d_outofpois(arg(args, 0)))),
    q_formatter,
  )
  |> ignore
  putprop(
    q_bigfloat,
    lfunc("bigfloat-formatter", args => {
      let form = arg(args, 0)
      if minusp(cadr(form)) {
        list2(
          list1(q_mminus),
          list3(car(form), num_neg(cadr(form)), caddr(form)),
        )
      } else {
        cons(car(form), cdr(form))
      }
    }),
    q_formatter,
  )
  |> ignore
  // in case a common lisp ratio is returned somehow.
  putprop(
    q_ratio,
    lfunc("ratio-formatter", args => {
      let form = arg(args, 0)
      if minusp(form) {
        list2(
          list1(q_mminus),
          list3(list1(q_rat), num_neg(numerator(form)), denominator(form)),
        )
      } else {
        list3(list1(q_rat), numerator(form), denominator(form))
      }
    }),
    q_formatter,
  )
  |> ignore
  // in case a common lisp complex number is returned somehow.
  putprop(
    q_complex,
    lfunc("complex-formatter", args => {
      let form = arg(args, 0)
      if complexp(form) {
        nformat(
          list3(
            list1(q_mplus),
            realpart(form),
            list3(list1(q_mtimes), imagpart(form), q_d__pcti),
          ),
        )
      } else {
        // some random form with caar COMPLEX, not really a CL complex
        form
      }
    }),
    q_formatter,
  )
  |> ignore
}
