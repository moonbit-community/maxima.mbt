// Port of share/algebra/charsets/charsets_powers.lisp: extracting powers,
// finding leading and trailing coefficients, and finding the degree of
// polynomials (Barton Willis).
//
// REQUIRE-SYMBOL, $DEGREE and DEGREE of this file are private
// (charsets_powers__*): the contract names belong to other share files.
// Loading the file installs its $DEGREE in the function cell, as the Lisp
// DEFUN does.

///|
/// posintp(x) returns true iff x is a positive integer or if x has been
/// declared to be an integer and has been assumed to be greater than zero.
fn d_posintp(x : Value) -> Value raise {
  if d_integerp(x).truthy() || d_featurep(x, q_d_integer).truthy() {
    mgrp(x, Fix(0L))
  } else {
    Nil
  }
}

///|
/// Set ratfac to nil, return rat(e,x), and reset ratfac to its previous
/// value.
fn myrat(e : Value, x : Value) -> Value raise {
  let save_ratfac = symval(q_d_ratfac)
  set(q_d_ratfac, Nil) |> ignore
  defer set(q_d_ratfac, save_ratfac) |> ignore
  apply(q_d_rat, cons(e, x))
}

///|
/// If x list a Maxima list of symbols, return true iff the expression p
/// doesn't depend on any member of x. If x is a symbol, return true iff p
/// doesn't depend on x.
fn d_ratfreeof(x : Value, p : Value) -> Value raise {
  let x = require_list_of_symbols(x, Str("$ratfreeof"), Fix(2L))
  let p_vars = cdr(d_showratvars(p))
  if every(z => d_symbolp(z).truthy() || d_subvarp(z).truthy(), p_vars) {
    lbool(every(z => member_if_test(z, p_vars, (a, b) => like(a, b).truthy()) is Nil, x))
  } else {
    let p = d_totaldisrep(p)
    lbool(every(z => d_freeof(list2(d_totaldisrep(z), p)).truthy(), x))
  }
}

///|
/// variablep(e) evaluates to true if and only if e is a non-constant symbol
/// or a subscripted symbol.
fn d_variablep(e : Value) -> Value raise {
  if d_symbolp(e).truthy() || d_subvarp(e).truthy() {
    lbool(d_constantp(e) is Nil)
  } else {
    Nil
  }
}

///|
/// ordinal_string(i) returns the ordinal name of the integer i. When i >
/// 10, i < 1, or i isn't an integer, give up and return i-th.
fn d_ordinal_string(i : Value) -> Value raise {
  let names = [
    "first", "second", "third", "fourth", "fifth", "sixth", "seventh", "eighth",
    "ninth", "tenth",
  ]
  for k in 1..=10 {
    if eql(i, int(k)) {
      return Str(names[k - 1])
    }
  }
  format(Nil, "~A-th", [mfuncall(q_d_string, list1(i))])
}

///|
/// If variablep(v) evaluates to false, signal an error saying that the i-th
/// argument of the function f requires a symbol; otherwise, return true.
fn charsets_powers__require_symbol(v : Value, f : Value, i : Value) -> Value raise {
  if d_variablep(v) is Nil {
    merr("The ~A argument of ~:M must be a symbol, instead found ~:M", [
      d_ordinal_string(i),
      f,
      v,
    ])
  } else {
    t
  }
}

///|
/// If v is a Maxima list and each element of v is a symbol, return the cdr
/// of v. When v isn't a list, but is a symbol, return the Lisp list (list
/// v). Otherwise signal an error.
fn require_list_of_symbols(v : Value, f : Value, i : Value) -> Value raise {
  let x = if d_listp(v).truthy() { cdr(v) } else { list1(v) }
  if every(e => d_variablep(e).truthy(), x) {
    x
  } else {
    merr(
      "The ~A argument of ~:M must be a symbol or a list of symbols, instead found ~:M",
      [d_ordinal_string(i), f, v],
    )
  }
}

///|
fn require_poly(p : Value, v : Value, f : Value, i : Value) -> Value raise {
  let p = myrat(p, list1(v))
  if d_charsets_polynomialp(p, vars=v).truthy() {
    p
  } else {
    merr("The ~A argument of ~:M requires a polynomial, instead found ~:M", [
      d_ordinal_string(i),
      f,
      p,
    ])
  }
}

///|
fn require_nonlist(e : Value, f : Value, i : Value) -> Value raise {
  if d_listp(e).truthy() {
    merr("The ~A argument of ~:M requires a nonlist, instead found ~:M", [
      d_ordinal_string(i),
      f,
      e,
    ])
  } else {
    Nil
  }
}

///|
/// Return a Maxima list of the non-constant rat variables in e.
fn non_constant_ratvars(e : Value) -> Value raise {
  let mut acc : Value = Nil
  for vi in cdr(d_showratvars(e)).iter() {
    if d_constantp(vi) is Nil {
      acc = cons(vi, acc)
    }
  }
  cons(list2(q_mlist, q_simp), acc)
}

///|
/// If e is a list, map $powers over the list. If e is a sum of powers of
/// powers of x, return a list of the exponents.
fn d_powers(e : Value, x : Value) -> Value raise {
  charsets_powers__require_symbol(x, Str("$powers"), Fix(2L)) |> ignore
  if d_listp(e).truthy() {
    cons(list2(q_mlist, q_simp), mapcar(p => d_powers(p, x), cdr(e)))
  } else {
    let e = require_poly(myrat(e, list1(x)), x, Str("$powers"), Fix(1L))
    if d_ratfreeof(x, e).truthy() {
      list2(list2(q_mlist, q_simp), Fix(0L))
    } else {
      cons(list2(q_mlist, q_simp), odds(cadr(e), Fix(0L)))
    }
  }
}

///|
/// Return the highest power of the polynomial e in the variable x.
fn d_hipower(e : Value, x : Value) -> Value raise {
  charsets_powers__require_symbol(x, Str("$hipower"), Fix(2L)) |> ignore
  let e = require_poly(myrat(e, list1(x)), x, Str("$hipower"), Fix(1L))
  if d_constantp(e).truthy() || d_ratfreeof(x, e).truthy() {
    Fix(0L)
  } else {
    cadadr(e)
  }
}

///|
/// Return the lowest power of the polynomial e in the variable x.
fn d_lowpower(e : Value, x : Value) -> Value raise {
  charsets_powers__require_symbol(x, Str("$lowpower"), Fix(2L)) |> ignore
  let e = require_poly(myrat(e, list1(x)), x, Str("$lowpower"), Fix(1L))
  if d_constantp(e).truthy() || d_ratfreeof(x, e).truthy() {
    Fix(0L)
  } else {
    nth(1, reverse(cadr(e)))
  }
}

///|
/// Flatten a Maxima list.
fn flatten_list(e : Value) -> Value raise {
  if d_listp(e).truthy() {
    let mut acc : Value = Nil
    for ei in cdr(e).iter() {
      acc = if d_listp(ei).truthy() {
        nconc(cdr(flatten_list(ei)), acc)
      } else {
        cons(ei, acc)
      }
    }
    cons(list2(q_mlist, q_simp), nreverse(acc))
  } else {
    e
  }
}

///|
/// If e is a sum of powers of x, return a list of the coefficients of
/// powers of x.
fn d_allcoeffs(e : Value, x : Value) -> Value raise {
  flatten_list(allcoeffs(e, x))
}

///|
fn allcoeffs(e : Value, x : Value) -> Value raise {
  if d_listp(e).truthy() {
    cons(list2(q_mlist, q_simp), mapcar(s => allcoeffs(s, x), cdr(e)))
  } else if d_listp(x).truthy() {
    if num_eq(Fix(0L), d_length(x)) {
      e
    } else {
      allcoeffs(allcoeffs(e, d_first(x)), d_rest(x))
    }
  } else {
    charsets_powers__require_symbol(x, Str("$allcoeffs"), Fix(2L)) |> ignore
    let e = myrat(e, list1(x))
    let p = d_powers(e, x)
    cons(list2(q_mlist, q_simp), mapcar(n => d_ratcoef(e, x, n~), cdr(p)))
  }
}

///|
/// Return the coefficient of the term of the polynomial e that contains the
/// highest power of x. When x = [x1,x2,...,xn], return
/// lcoeff(lcoeff( ... (lcoeff(e,x1),x2),...,xn)...)
fn d_lcoeff(e : Value, v? : Value = Nil) -> Value raise {
  require_nonlist(e, Str("$lcoeff"), Fix(1L)) |> ignore
  let v = if v is Nil { non_constant_ratvars(e) } else { v }
  let p = require_poly(myrat(e, Nil), v, Str("$lcoeff"), Fix(1L))
  lcoeff(p, require_list_of_symbols(v, Str("$lcoeff"), Fix(2L)))
}

///|
fn lcoeff(e : Value, x : Value) -> Value raise {
  if x is Nil {
    e
  } else {
    lcoeff(d_ratcoef(e, car(x), n=d_hipower(e, car(x))), cdr(x))
  }
}

///|
/// Return the coefficient of the term of the polynomial e that contains the
/// least power of x.
fn d_tcoeff(e : Value, v? : Value = Nil) -> Value raise {
  require_nonlist(e, Str("$tcoeff"), Fix(1L)) |> ignore
  let v = if v is Nil { non_constant_ratvars(e) } else { v }
  let p = require_poly(myrat(e, Nil), v, Str("$tcoeff"), Fix(1L))
  tcoeff(p, require_list_of_symbols(v, Str("$tcoeff"), Fix(2L)))
}

///|
fn tcoeff(e : Value, x : Value) -> Value raise {
  if x is Nil {
    e
  } else {
    tcoeff(d_ratcoef(e, car(x), n=d_lowpower(e, car(x))), cdr(x))
  }
}

///|
/// Return the degree of the symbol x in the polynomial p. When x is a list,
/// degree(p, [x1,x2,...,xn]) returns
/// degree(p,x1) + degree(lcoeff(p, x1),[x2,...xn]). Finally,
/// degree(p,[]) returns 0.
fn charsets_powers__d_degree(p : Value, x : Value) -> Value raise {
  let p = require_poly(myrat(p, Nil), x, Str("$degree"), Fix(1L))
  charsets_powers__degree(p, require_list_of_symbols(x, Str("$degree"), Fix(2L)))
}

///|
fn charsets_powers__degree(p : Value, x : Value) -> Value raise {
  if x is Nil {
    Fix(0L)
  } else {
    let h = d_hipower(p, car(x))
    add2(h, charsets_powers__degree(lcoeff(p, list1(car(x))), cdr(x)))
  }
}

///|
/// Return the total degree of the polynomial.
fn d_total_degree(p : Value, v? : Value = Nil) -> Value raise {
  let v = if v is Nil { non_constant_ratvars(p) } else { v }
  let v = require_list_of_symbols(v, Str("$total_degree"), Fix(2L))
  total_degree(cadr(myrat(p, v)))
}

///|
fn total_degree(e : Value) -> Value raise {
  if consp(nth(2, e)) {
    num_add(nth(1, e), total_degree(nth(2, e)))
  } else {
    nth(1, e)
  }
}

///|
fn d_lcm(p : Value, q : Value) -> Value raise {
  nth(1, d_divide(mul2(p, q), d_gcd(p, q, Nil), Nil))
}

///|
/// Compute the s-polynomial of f and g. For a definition of the
/// s-polynomial, see Davenport, Siret, and Tournier, "Computer Algebra",
/// 1988, page 100.
fn d_spoly(f : Value, g : Value, v : Value) -> Value raise {
  let v = cons(
    list2(q_mlist, q_simp),
    require_list_of_symbols(v, Str("$spoly"), Fix(3L)),
  )
  let f = myrat(f, Nil)
  let g = myrat(g, Nil)
  let fp = d_lterm(f, v~)
  let gp = d_lterm(g, v~)
  mul2(d_lcm(fp, gp), add2(div(f, fp), mul2(Fix(-1L), div(g, gp))))
}

///|
fn d_lterm(p : Value, v? : Value = Nil) -> Value raise {
  let v = if v is Nil { non_constant_ratvars(p) } else { v }
  let q = require_poly(myrat(p, Nil), v, Str("$lterm"), Fix(1L))
  lterm(q, require_list_of_symbols(v, Str("$lterm"), Fix(2L)))
}

///|
fn lterm(p : Value, v : Value) -> Value raise {
  if v is Nil {
    p
  } else {
    let vo = car(v)
    let n = d_hipower(p, vo)
    lterm(mult(d_ratcoef(p, vo, n~), power(vo, n)), cdr(v))
  }
}

///|
fn d_get_exponents(p : Value, x : Value) -> Value raise {
  let x = require_list_of_symbols(x, Str("$get_exponents"), Fix(2L))
  let mut acc : Value = Nil
  let mut p = myrat(p, Nil)
  require_poly(p, cons(list2(q_mlist, q_simp), x), Str("$get_exponents"), Fix(1L))
  |> ignore
  for xi in x.iter() {
    acc = cons(d_hipower(p, xi), acc)
    p = d_lcoeff(p, v=xi)
  }
  cons(list2(q_mlist, q_simp), nreverse(acc))
}

///|
/// Return true iff and only if e is a polynomial in the variables var.
fn d_charsets_polynomialp(
  e : Value,
  vars? : Value = Nil,
  cp? : Value = Nil,
  ep? : Value = Nil,
) -> Value raise {
  ignore(cp)
  ignore(ep)
  let vars = if vars is Nil { non_constant_ratvars(e) } else { vars }
  let vars = require_list_of_symbols(vars, Str("$charsets_polynomialp"), Fix(2L))
  let vars = cons(list2(q_mlist, q_simp), vars)
  if every(
      x => d_variablep(x).truthy() ||
        d_ratfreeof(vars, x).truthy() ||
        d_constantp(x).truthy(),
      cdr(d_showratvars(e)),
    ) &&
    d_taylorp(e) is Nil {
    d_ratfreeof(vars, d_ratdenom(e))
  } else {
    Nil
  }
}

///|
/// Top-level forms of charsets_powers.lisp.
fn init_share_charsets_powers() -> Unit raise {
  d_put(q_d_powers, Fix(1L), q_d_version) |> ignore
  defun(q_d_degree, args => charsets_powers__d_degree(arg(args, 0), arg(args, 1)))
}
