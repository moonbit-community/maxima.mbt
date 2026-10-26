// Port of src/hayat.lisp, part 1: free predicates, coefficient and exponent
// arithmetic, and power series arithmetic (psplus, pstimes, psexpt, ...).
//
// HAYAT -- Finite Power Series Routines.
// (c) Copyright 1982 Massachusetts Institute of Technology.
//
// See mhayat.mbt for the representation of power series. Exponents are
// pairs (n . d) of CL integers; nil is an infinite exponent.

///|
/// Run F with `least_term?` bound to V.
fn[T] hayat__with_least_term(v : Value, f : () -> T raise) -> T raise {
  with_special(q_least_term_q, v, f)
}

// Subtitle General Macsyma Free Predicates

///|
fn zfree(e : Value, x : Value) -> Value raise {
  if equal(e, x) {
    Nil
  } else if atom(e) {
    t
  } else if eq(caar(e), q_mrat) {
    lbool(member_equal(x, cdr(d_listofvars(e))) is Nil)
  } else {
    let mut l = cdr(e)
    while !(l is Nil) {
      if !zfree(car(l), x).truthy() {
        return Nil
      }
      l = cdr(l)
    }
    t
  }
}

///|
fn mfree(exp_ : Value, varl : Value) -> Value raise {
  if atom(exp_) {
    lbool(memq(exp_, varl) is Nil)
  } else if eq(caar(exp_), q_mrat) {
    let mut l = mrat_varlist(exp_)
    while !(l is Nil) {
      if !mfree(car(l), varl).truthy() {
        return Nil
      }
      l = cdr(l)
    }
    t
  } else if memq(caar(exp_), symval(q_dummy_variable_operators)).truthy() ||
    memq(q_array, cdar(exp_)).truthy() {
    let mut vars = varl
    while !(vars is Nil) {
      if !freeof(car(vars), exp_).truthy() {
        return Nil
      }
      vars = cdr(vars)
    }
    t
  } else if mfree(caar(exp_), varl).truthy() {
    mfreel(cdr(exp_), varl)
  } else {
    Nil
  }
}

///|
fn mfreel(l : Value, varl : Value) -> Value raise {
  if l is Nil {
    t
  } else if mfree(car(l), varl).truthy() {
    mfreel(cdr(l), varl)
  } else {
    Nil
  }
}

// Subtitle Coefficient Arithmetic

///|
fn rcexpt(x : Value, y : Value) -> Value raise {
  let mut y = y
  if equal(x, rcone()) {
    rcone()
  } else if rczerop(y).truthy() {
    rcone()
  } else if equal(cdr(y), Fix(1L)) && fixnump(car(y)) {
    ratexpt(x, car(y))
  } else if symval(q_d_radexpand).truthy() &&
    numberp(car(y)) &&
    numberp(cdr(y)) {
    if floatp(car(y)) {
      y = maxima_rationalize(quot(car(y), cdr(y)))
    }
    ratexpt(rcquo(rcexpt1(car(x), cdr(y)), rcexpt1(cdr(x), cdr(y))), car(y))
  } else {
    with_special(q_d_keepfloat, Nil, () => prep1(
      power_star(rcdisrep(x), rcdisrep(y)),
    ))
  }
}

///|
fn rcexpt1(p : Value, n : Value) -> Value raise {
  if equal(p, Fix(1L)) {
    rcone()
  } else if pcoefp(p).truthy() {
    prep1(power_star(pdis(p), n_starred(Fix(1L), n)))
  } else {
    // psqfr does a square-free decomposition of p yielding
    // (p1 e1 p2 e2 ... pn en) where p = p1^e1 p2^e2 ... pn^en.
    let mut l = psqfr(p)
    let mut ans = rcone()
    while !(l is Nil) {
      if !equal(num_rem(cadr(l), n), Fix(0L)) {
        ans = rctimes(ans, prep1(power_star(pdis(car(l)), n_starred(cadr(l), n))))
      } else {
        // If pi<0, n=2m and n|ei then ei=2e and
        //	    (pi^ei)^(1/(2m)) = (-pi)^(e/m)
        if evenp(n) && eq(d_sign(pdis(car(l))), q_d_neg) {
          rplaca(l, pminus(car(l))) |> ignore
        }
        ans = rctimes(
          ans,
          ratexpt(cons(car(l), Fix(1L)), num_truncate(cadr(l), b=n).0),
        )
      }
      l = cddr(l)
    }
    ans
  }
}

///|
/// A sure check, but expensive.
fn rccoefp(e : Value) -> Value raise {
  if atom(e) {
    return Nil
  }
  let a = if atom(car(e)) { t } else { memq(caar(e), symval(q_genvar)) }
  if a is Nil {
    return Nil
  }
  if atom(cdr(e)) {
    t
  } else {
    memq(cadr(e), symval(q_genvar))
  }
}

// Subtitle Exponent arithmetic

///|
fn ezerop(x : Value) -> Value raise {
  lbool(!(x is Nil) && numberp(car(x)) && zerop(car(x)))
}

///|
fn e_plus(x : Value, y : Value) -> Value raise {
  if x is Nil || y is Nil {
    inf()
  } else if equal(cdr(x), Fix(1L)) && equal(cdr(y), Fix(1L)) {
    cons(num_add(car(x), car(y)), Fix(1L))
  } else {
    ereduce(
      num_add(num_mul(car(x), cdr(y)), num_mul(cdr(x), car(y))),
      num_mul(cdr(x), cdr(y)),
    )
  }
}

///|
fn ediff(x : Value, y : Value) -> Value raise {
  if x is Nil {
    inf()
  } else if equal(cdr(x), Fix(1L)) && equal(cdr(y), Fix(1L)) {
    cons(num_sub(car(x), car(y)), Fix(1L))
  } else {
    ereduce(
      num_sub(num_mul(car(x), cdr(y)), num_mul(cdr(x), car(y))),
      num_mul(cdr(x), cdr(y)),
    )
  }
}

///|
fn emin(x : Value, y : Value) -> Value raise {
  if x is Nil {
    y
  } else if y is Nil {
    x
  } else if equal(cdr(x), cdr(y)) {
    cons(num_min(car(x), car(y)), cdr(x))
  } else if num_lt(num_mul(car(x), cdr(y)), num_mul(cdr(x), car(y))) {
    x
  } else {
    y
  }
}

///|
fn emax(x : Value, y : Value) -> Value raise {
  if x is Nil || y is Nil {
    inf()
  } else if equal(cdr(x), cdr(y)) {
    cons(num_max(car(x), car(y)), cdr(x))
  } else if num_gt(num_mul(car(x), cdr(y)), num_mul(cdr(x), car(y))) {
    x
  } else {
    y
  }
}

///|
fn e_star(x : Value, y : Value) -> Value raise {
  if x is Nil || y is Nil {
    inf()
  } else if equal(cdr(x), Fix(1L)) && equal(cdr(y), Fix(1L)) {
    cons(num_mul(car(x), car(y)), Fix(1L))
  } else {
    ereduce(num_mul(car(x), car(y)), num_mul(cdr(x), cdr(y)))
  }
}

///|
fn erecip(e : Value) -> Value raise {
  if minusp(car(e)) {
    cons(num_neg(cdr(e)), num_neg(car(e)))
  } else {
    cons(cdr(e), car(e))
  }
}

///|
fn equo(x : Value, y : Value) -> Value raise {
  if x is Nil {
    inf()
  } else if y is Nil {
    rczero()
  } else {
    ereduce(num_mul(car(x), cdr(y)), num_mul(cdr(x), car(y)))
  }
}

///|
fn e1_plus(x : Value) -> Value raise {
  if x is Nil {
    inf()
  } else if num_eq(cdr(x), Fix(1L)) {
    cons(one_plus(car(x)), Fix(1L))
  } else {
    cons(num_add(cdr(x), car(x)), cdr(x))
  }
}

///|
fn e1_(x : Value) -> Value raise {
  if x is Nil {
    inf()
  } else if equal(cdr(x), Fix(1L)) {
    cons(one_minus(car(x)), Fix(1L))
  } else {
    cons(num_sub(car(x), cdr(x)), cdr(x))
  }
}

///|
fn e_gt(x : Value, y : Value) -> Value raise {
  if x is Nil {
    t
  } else if y is Nil {
    Nil
  } else if equal(cdr(x), cdr(y)) {
    lbool(num_gt(car(x), car(y)))
  } else {
    lbool(num_gt(num_mul(car(x), cdr(y)), num_mul(car(y), cdr(x))))
  }
}

///|
fn e_eq(e1 : Value, e2 : Value) -> Value raise {
  if eq(e1, e2) {
    t
  } else if e1 is Nil || e2 is Nil {
    Nil
  } else {
    lbool(equal(car(e1), car(e2)) && equal(cdr(e1), cdr(e2)))
  }
}

///|
fn ereduce(n : Value, d : Value) -> Value raise {
  let mut n = n
  let mut d = d
  if numberp(d) && num_lt(d, Fix(0L)) {
    d = num_neg(d)
    n = num_neg(n)
  }
  if zerop(n) {
    rczero()
  } else {
    let gcd = num_gcd(n, d)
    cons(num_div(n, gcd), num_div(d, gcd))
  }
}

///|
fn egcd(x : Value, y : Value) -> Value raise {
  let xn = num_abs(car(x))
  let xd = cdr(x)
  let yn = num_abs(car(y))
  let yd = cdr(y)
  cons(num_gcd(xn, yn), num_mul(xd, num_div(yd, num_gcd(xd, yd))))
}

// Subtitle polynomial arithmetic

///|
fn ord_vector(p : Value) -> Value raise {
  let vs = mapcar(datum => list1(int_gvar(datum)), symval(q_tlist))
  with_special(q_vars, vs, () => if cdr(symval(q_vars)) is Nil {
    list1(ps_le_star(p))
  } else {
    ord_vect1(p) |> ignore
    mapcar(
      x => {
        let v = cdr(x)
        if v.truthy() {
          v
        } else {
          rczero()
        }
      },
      symval(q_vars),
    )
  })
}

///|
fn ord_vect1(p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    return Nil
  }
  let data = assq(gvar(p), symval(q_vars))
  let le = ps_le(p)
  rplacd(data, if cdr(data) is Nil { le } else { emin(cdr(data), le) })
  |> ignore
  let ts = terms(p)
  let mut l = ts
  while !(l is Nil) {
    ord_vect1(lc(l)) |> ignore
    l = cdr(l)
  }
  ts
}

///|
fn trunc_vector(p : Value, min_q : Value) -> Value raise {
  let vs = mapcar(datum => list1(int_gvar(datum)), symval(q_tlist))
  with_special(q_vars, vs, () => if cdr(symval(q_vars)) is Nil {
    list1(if psp(p).truthy() { trunc_lvl(p) } else { Nil })
  } else {
    trunc_vect1(p, min_q) |> ignore
    mapcar(x => cdr(x), symval(q_vars))
  })
}

///|
fn trunc_vect1(p : Value, min_q : Value) -> Value raise {
  if pscoefp(p).truthy() {
    return Nil
  }
  let data = assq(gvar(p), symval(q_vars))
  let trunc = trunc_lvl(p)
  if trunc.truthy() {
    rplacd(
      data,
      if cdr(data) is Nil {
        trunc
      } else if min_q.truthy() {
        emin(cdr(data), trunc)
      } else {
        emax(cdr(data), trunc)
      },
    )
    |> ignore
  }
  for term in terms(p).iter() {
    trunc_vect1(c(term), min_q) |> ignore
  }
  Nil
}

///|
fn psplus(x : Value, y : Value) -> Value raise {
  if pscoefp(x).truthy() {
    if pscoefp(y).truthy() {
      rcplus(x, y)
    } else if rczerop(x).truthy() {
      y
    } else {
      pscplus(x, y)
    }
  } else if pscoefp(y).truthy() {
    if rczerop(y).truthy() {
      x
    } else {
      pscplus(y, x)
    }
  } else if eqgvar(gvar_o(x), gvar_o(y)).truthy() {
    psplus1(x, y)
  } else if pointerp(gvar_o(x), gvar_o(y)).truthy() {
    pscplus(y, x)
  } else {
    pscplus(x, y)
  }
}

///|
fn rcplus_bang(x : Value, y : Value) -> Value raise {
  if !(symval(q_least_term_q).truthy() && symval(q_taylor_simplifier).truthy()) {
    rcplus(x, y)
  } else {
    prep1(
      funcall(symval(q_taylor_simplifier), [
        add2_star(rcdisrep(x), rcdisrep(y)),
      ]),
    )
  }
}

///|
fn psdiff(x : Value, y : Value) -> Value raise {
  if pscoefp(x).truthy() {
    if pscoefp(y).truthy() {
      rcdiff(x, y)
    } else if rczerop(x).truthy() {
      pstimes(rcmone(), y)
    } else {
      pscdiff(x, y, Nil)
    }
  } else if pscoefp(y).truthy() {
    if rczerop(y).truthy() {
      x
    } else {
      pscdiff(y, x, t)
    }
  } else if eqgvar(gvar_o(x), gvar_o(y)).truthy() {
    psdiff1(x, y)
  } else if pointerp(gvar_o(x), gvar_o(y)).truthy() {
    pscdiff(y, x, t)
  } else {
    pscdiff(x, y, Nil)
  }
}

///|
fn rcdiff_bang(x : Value, y : Value) -> Value raise {
  if !(symval(q_least_term_q).truthy() && symval(q_taylor_simplifier).truthy()) {
    rcdiff(x, y)
  } else {
    prep1(
      funcall(symval(q_taylor_simplifier), [
        sub_star(rcdisrep(x), rcdisrep(y)),
      ]),
    )
  }
}

///|
fn psplus1(x : Value, y : Value) -> Value raise {
  let ans = cons(Nil, Nil)
  psplus2(
    gvar_o(x),
    emin(trunc_lvl(x), trunc_lvl(y)),
    cons(Fix(0L), terms(x)),
    cons(Fix(0L), terms(y)),
    ans,
    ans,
  )
}

///|
fn pscplus(c : Value, p : Value) -> Value raise {
  if e_gt(rczero(), trunc_lvl(p)).truthy() {
    p
  } else {
    pscheck(gvar_o(p), poly_data(p), pscplus1(c, terms(p)))
  }
}

///|
fn pscdiff(c : Value, p : Value, fl : Value) -> Value raise {
  if e_gt(rczero(), trunc_lvl(p)).truthy() {
    if fl.truthy() {
      p
    } else {
      psminus(p)
    }
  } else {
    pscheck(
      gvar_o(p),
      poly_data(p),
      if !fl.truthy() {
        pscplus1(c, psminus_terms(terms(p)))
      } else {
        pscplus1(psminus(c), terms(p))
      },
    )
  }
}

///|
fn strip_zeroes(terms : Value, ps_q : Value) -> Value raise {
  if terms is Nil || symval(q_taylor_simplifier) is Nil {
    terms
  } else if ps_q is Nil {
    let mut ts = terms
    while !(ts is Nil) {
      change_lc(ts, strip_zeroes(lc(ts), t)) |> ignore
      if !rczerop(lc(ts)).truthy() {
        return ts
      }
      ts = n__term(ts)
    }
    Nil
  } else if pscoefp(terms).truthy() {
    if symval(q_taylor_simplifier) is Nil {
      terms
    } else {
      let exp_ = rcdisrep(terms)
      // If a pscoeff is not free of tvars then the ps is a multivar series
      // and we can't handle a recursive call to taylor (as opposed to a
      // call to prep1, as below) because this would be circular (e.g. try
      // taylor(x/ (x^2+1),[x],%i,-1) ). Besides, in this case the pscoeff
      // contains a tvar hence should not be 0.
      if !mfree(exp_, symval(q_tvars)).truthy() {
        terms
      } else {
        prep1(funcall(symval(q_taylor_simplifier), [exp_]))
      }
    }
  } else {
    pscheck(
      gvar_o(terms),
      poly_data(terms),
      strip_zeroes(cdddr(terms), Nil),
    )
  }
}

///|
fn pscplus1(c : Value, l : Value) -> Value raise {
  let mut c = c
  if l is Nil {
    list1(term(rczero(), c))
  } else if rczerop(le(l)).truthy() {
    c = psplus(c, lc(l))
    if rczerop(c).truthy() {
      strip_zeroes(n__term(l), Nil)
    } else {
      cons(term(rczero(), c), n__term(l))
    }
  } else if e_gt(le(l), rczero()).truthy() {
    cons(term(rczero(), c), l)
  } else {
    let first = lt(l)
    cons(first, hayat__with_least_term(Nil, () => pscplus1(c, n__term(l))))
  }
}

// Both here and in psdiff2 xx and yy point one before where one might think
// they should point so that extensions will be retained.

///|
fn psplus2(
  varh : Value,
  trunc : Value,
  xx : Value,
  yy : Value,
  ans : Value,
  a : Value,
) -> Value raise {
  let mut xx = xx
  let mut yy = yy
  let mut a = a
  let mut c : Value = Nil
  // state 0 = tag A, 1 = tag NULL
  let mut state = 0
  while true {
    if state == 0 {
      if mono_term_q(xx).truthy() {
        if mono_term_q(yy).truthy() {
          break
        } else {
          state = 1
          continue
        }
      } else if mono_term_q(yy).truthy() {
        yy = xx
        state = 1
        continue
      }
      if equal(le(n__term(xx)), le(n__term(yy))) {
        xx = n__term(xx)
        yy = n__term(yy)
        c = hayat__with_least_term(lbool(n__term(ans) is Nil), () => psplus(
          lc(xx),
          lc(yy),
        ))
        if rczerop(c).truthy() {
          continue
        } else {
          add_term(a, term_or_e=le(xx), c~) |> ignore
        }
      } else if e_gt(le(n__term(xx)), le(n__term(yy))).truthy() {
        yy = n__term(yy)
        add_term(a, term_or_e=lt(yy)) |> ignore
      } else {
        xx = n__term(xx)
        add_term(a, term_or_e=lt(xx)) |> ignore
      }
      a = n__term(a)
    } else if mono_term_q(yy).truthy() ||
      e_gt(le(n__term(yy)), trunc).truthy() {
      break
    } else {
      yy = n__term(yy)
      add_term(a, term_or_e=lt(yy)) |> ignore
      a = n__term(a)
    }
  }
  pscheck(varh, list1(trunc), cdr(ans))
}

///|
fn psdiff1(x : Value, y : Value) -> Value raise {
  let ans = cons(Nil, Nil)
  psdiff2(
    gvar_o(x),
    emin(trunc_lvl(x), trunc_lvl(y)),
    cons(Fix(0L), terms(x)),
    cons(Fix(0L), terms(y)),
    ans,
    ans,
  )
}

///|
fn psdiff2(
  varh : Value,
  trunc : Value,
  xx : Value,
  yy : Value,
  ans : Value,
  a : Value,
) -> Value raise {
  let mut xx = xx
  let mut yy = yy
  let mut a = a
  let mut cc : Value = Nil
  let mut state = 0
  while true {
    if state == 0 {
      if mono_term_q(xx).truthy() {
        if mono_term_q(yy).truthy() {
          break
        } else {
          yy = cons(
            Fix(0L),
            mapcar(q => term(e(q), psminus(c(q))), cdr(yy)),
          )
          state = 1
          continue
        }
      } else if mono_term_q(yy).truthy() {
        yy = xx
        state = 1
        continue
      }
      if equal(le(n__term(xx)), le(n__term(yy))) {
        xx = n__term(xx)
        yy = n__term(yy)
        cc = hayat__with_least_term(lbool(n__term(ans) is Nil), () => psdiff(
          lc(xx),
          lc(yy),
        ))
        if rczerop(cc).truthy() {
          continue
        } else {
          add_term(a, term_or_e=le(xx), c=cc) |> ignore
        }
      } else if e_gt(le(n__term(xx)), le(n__term(yy))).truthy() {
        yy = n__term(yy)
        add_term(a, term_or_e=le(yy), c=psminus(lc(yy))) |> ignore
      } else {
        xx = n__term(xx)
        add_term(a, term_or_e=lt(xx)) |> ignore
      }
      a = n__term(a)
    } else if mono_term_q(yy).truthy() ||
      e_gt(le(n__term(yy)), trunc).truthy() {
      break
    } else {
      yy = n__term(yy)
      add_term(a, term_or_e=le(yy), c=lc(yy)) |> ignore
      a = n__term(a)
    }
  }
  pscheck(varh, list1(trunc), cdr(ans))
}

///|
fn psminus(x : Value) -> Value raise {
  if psp(x).truthy() {
    make_ps(x, psminus_terms(terms(x)))
  } else {
    rcminus(x)
  }
}

///|
fn psminus_terms(terms : Value) -> Value raise {
  let ans = cons(Nil, Nil)
  let mut q = terms
  let mut a = ans
  while !(q is Nil) {
    add_term(a, term_or_e=le(q), c=psminus(lc(q))) |> ignore
    q = n__term(q)
    a = cdr(a)
  }
  cdr(ans)
}

///|
fn pscheck(a : Value, b : Value, terms : Value) -> Value raise {
  if terms is Nil {
    rczero()
  } else if mono_term_q(terms).truthy() && rczerop(le(terms)).truthy() {
    lc(terms)
  } else {
    make_ps(a, b, terms~)
  }
}

///|
fn pstrim_terms(terms : Value, e : Value) -> Value raise {
  let mut terms = terms
  while true {
    if terms is Nil {
      return Nil
    } else if !e_gt(e, le(terms)).truthy() {
      return terms
    } else {
      terms = n__term(terms)
    }
  }
  Nil
}

///|
fn psterm(terms : Value, e : Value) -> Value raise {
  psterm1(pstrim_terms(terms, e), e)
}

///|
fn psterm1(l : Value, e : Value) -> Value raise {
  if l is Nil {
    rczero()
  } else if e_eq(le(l), e).truthy() {
    lc(l)
  } else {
    rczero()
  }
}

///|
/// A is an mrat!
fn pscoeff1(a : Value, b : Value, c : Value) -> Value raise {
  with_special(q_tlist, mrat_tlist(a), () => {
    let tail = {
      let mut l = mrat_tlist(a)
      let mut ans : Value = Nil
      let mut res : Value = Nil
      while !(l is Nil) {
        if alike1(caar(l), b).truthy() {
          res = if ans.truthy() || cdr(l).truthy() {
            list2(nreconc(ans, cdr(l)), q_trunc)
          } else {
            Nil
          }
          break
        }
        let nl = cdr(l)
        ans = cons(car(l), ans)
        l = nl
      }
      if l is Nil {
        ans
      } else {
        res
      }
    }
    let hd = nconc(list([q_mrat, q_simp, mrat_varlist(a), mrat_genvar(a)]), tail)
    cons(hd, pscoef(mrat_ps(a), int_gvar(get_datum(b)), prep1(c)))
  })
}

///|
fn pscoef(a : Value, b : Value, c : Value) -> Value raise {
  if pscoefp(a).truthy() {
    if rczerop(c).truthy() {
      a
    } else {
      rczero()
    }
  } else if eq(b, gvar(a)) {
    psterm(terms(a), c)
  } else {
    let gvo = gvar_o(a)
    let pd = poly_data(a)
    let mut ans = rczero()
    let mut ts = terms(a)
    while !(ts is Nil) {
      let temp = pscoef(lc(ts), b, c)
      if !rczerop(temp).truthy() {
        ans = psplus(ans, make_ps(gvo, pd, terms=list1(term(le(ts), temp))))
      }
      ts = n__term(ts)
    }
    ans
  }
}

///|
fn psdisextend(p : Value) -> Value raise {
  if !psp(p).truthy() {
    p
  } else {
    make_ps(p, mapcar(q => cons(car(q), psdisextend(cdr(q))), terms(p)))
  }
}

///|
fn psfloat(p : Value) -> Value raise {
  if psp(p).truthy() {
    psfloat1(p, trunc_lvl(p), terms(p), list1(Fix(0L)))
  } else {
    rctimes(rcfone(), p)
  }
}

///|
fn psfloat1(p : Value, trunc : Value, l : Value, ans : Value) -> Value raise {
  with_special(q_d_float, t, () => {
    let mut a = last(ans)
    let mut l = l
    while true {
      if l is Nil || e_gt(le(l), trunc).truthy() {
        break
      }
      add_term(a, term_or_e=le(l), c=psfloat(lc(l))) |> ignore
      l = n__term(l)
      a = n__term(a)
    }
    pscheck(gvar_o(p), poly_data(p), cdr(ans))
  })
}

///|
fn pstrunc(p : Value) -> Value raise {
  pstrunc1(
    p,
    mapcar(q => cons(int_gvar(q), current_trunc(q)), symval(q_tlist)),
  )
}

///|
fn pstrunc1(p : Value, trlist : Value) -> Value raise {
  if !psp(p).truthy() {
    p
  } else {
    let trnc = cdr(assq(gvar(p), trlist))
    let mut a : Value = Nil
    let mut l = terms(p)
    while !(l is Nil) {
      if e_gt(le(l), trnc).truthy() {
        return pscheck(gvar_o(p), list1(trnc), nreverse(a))
      }
      let trunc_ps = pstrunc1(lc(l), trlist)
      if !rczerop(trunc_ps).truthy() {
        a = cons(term(le(l), trunc_ps), a)
      }
      l = n__term(l)
    }
    pscheck(gvar_o(p), list1(trunc_lvl(p)), nreverse(a))
  }
}

///|
fn pstimes(x : Value, y : Value) -> Value raise {
  if rczerop(x).truthy() || rczerop(y).truthy() {
    rczero()
  } else if pscoefp(x).truthy() {
    if pscoefp(y).truthy() {
      rctimes(x, y)
    } else if equal(x, rcone()) {
      y
    } else {
      psctimes_star(x, y)
    }
  } else if pscoefp(y).truthy() {
    if equal(y, rcone()) {
      x
    } else {
      psctimes_star(y, x)
    }
  } else if eqgvar(gvar_o(x), gvar_o(y)).truthy() {
    pstimes_star1(x, y)
  } else if pointerp(gvar_o(x), gvar_o(y)).truthy() {
    psctimes_star(y, x)
  } else {
    psctimes_star(x, y)
  }
}

///|
fn psctimes_star(c : Value, p : Value) -> Value raise {
  make_ps(p, maplist(l => term(le(l), pstimes(c, lc(l))), terms(p)))
}

///|
fn pstimes_star1(xa : Value, ya : Value) -> Value raise {
  let ans = cons(Nil, Nil)
  let mut trunc = {
    let lex = ps_le(xa)
    let ley = ps_le(ya)
    e_plus(
      emin(e_(trunc_lvl(xa), e2=lex), e_(trunc_lvl(ya), e2=ley)),
      e_plus(lex, ley),
    )
  }
  if !symval(q_d_maxtayorder).truthy() {
    trunc = emin(trunc, t_o_var(gvar(xa)))
  }
  pstimes_star2(xa, ya, trunc, ans)
}

///|
fn pstimes_star2(xa : Value, ya : Value, trunc : Value, ans : Value) -> Value raise {
  let mut x = terms(xa)
  let yy = terms(ya)
  let mut y = yy
  let mut a = ans
  let mut e : Value = Nil
  let mut c : Value = Nil
  // tags: 0 = A, 1 = B, 2 = C, 3 = D
  let mut state = 0
  while true {
    match state {
      0 => {
        if y is Nil ||
          {
            e = e_plus(le(x), le(y))
            e_gt(e, trunc).truthy()
          } {
          state = 1
          continue
        } else {
          c = pstimes(lc(x), lc(y))
          if !rczerop(c).truthy() {
            add_term(a, term_or_e=e, c~) |> ignore
            a = n__term(a)
          }
        }
        y = n__term(y)
      }
      1 => {
        x = n__term(x)
        if x is Nil {
          return pscheck(gvar_o(xa), list1(trunc), cdr(ans))
        }
        y = yy
        a = ans
        state = 2
      }
      2 => {
        if y is Nil ||
          {
            e = e_plus(le(x), le(y))
            e_gt(e, trunc).truthy()
          } {
          state = 1
          continue
        }
        c = pstimes(lc(x), lc(y))
        state = 3
      }
      _ => {
        if mono_term_q(a).truthy() || e_gt(le(n__term(a)), e).truthy() {
          add_term(a, term_or_e=e, c~) |> ignore
          a = n__term(a)
        } else if e_gt(e, le(n__term(a))).truthy() {
          a = n__term(a)
          continue
        } else {
          c = psplus(c, lc(n__term(a)))
          if rczerop(c).truthy() {
            rplacd(a, n__term(n__term(a))) |> ignore
          } else {
            change_lc(n__term(a), c) |> ignore
            a = n__term(a)
          }
        }
        y = n__term(y)
        state = 2
      }
    }
  }
  Nil
}

///|
fn pscsubst(c : Value, v : Value, p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    p
  } else if eq(v, gvar(p)) {
    pscsubst1(c, p)
  } else if pointerp(v, gvar(p)).truthy() {
    p
  } else {
    make_ps(p, maplist(q => term(le(q), pscsubst(c, v, lc(q))), terms(p)))
  }
}

///|
fn pscsubst1(v : Value, u : Value) -> Value raise {
  let mut a = rczero()
  let mut ul = terms(u)
  while !(ul is Nil) {
    a = psplus(a, pstimes(lc(ul), psexpt(v, le(ul))))
    ul = n__term(ul)
  }
  a
}

///|
fn get_series(
  func : Value,
  trunc : Value,
  var2 : Value,
  e : Value,
  c : Value,
) -> Value raise {
  let pw = e_sl_sl(trunc, e2=e)
  let e = if equal(e, rcone()) && equal(c, rcone()) {
    getexp_fun(func, var2, pw)
  } else {
    psmonsubst(getexp_fun(func, var2, pw), trunc, e, c)
  }
  if symval(q_d_float).truthy() && symval(q_d_keepfloat).truthy() {
    psfloat(e)
  } else {
    e
  }
}

///|
fn psmonsubst(p : Value, trunc : Value, e : Value, c : Value) -> Value raise {
  if psp(p).truthy() {
    psmonsubst1(
      p,
      trunc,
      e,
      c,
      cons(Nil, terms(p)),
      list1(Nil),
      rcone(),
      rczero(),
    )
  } else {
    p
  }
}

///|
fn psmonsubst1(
  p : Value,
  trunc : Value,
  e : Value,
  c : Value,
  l : Value,
  ans : Value,
  cc : Value,
  el : Value,
) -> Value raise {
  // We set $MAXTAYORDER to () here so that the calls to psexpt below won't
  // do needless extra work, e.g. see rwg's complaint of 9/7/82.
  with_special(q_d_maxtayorder, Nil, () => {
    let mut l = l
    let mut cc = cc
    let mut el = el
    let mut a = ans
    let varh = gvar_o(p)
    while true {
      let mut ee : Value = Nil
      if mono_term_q(l).truthy() ||
        {
          ee = e_star(e, le(n__term(l)))
          e_gt(ee, trunc).truthy()
        } {
        break
      }
      l = n__term(l)
      cc = pstimes(cc, psexpt(c, e_(le(l), e2=el)))
      if rczerop(cc).truthy() {
        ()
      } else if mono_term_q(a).truthy() {
        add_term(a, term_or_e=ee, c=pstimes(cc, lc(l))) |> ignore
      }
      a = n__term(a)
      el = le(l)
    }
    pscheck(varh, list1(trunc), cdr(ans))
  })
}

///|
fn psexpon_gcd(terms : Value) -> Value raise {
  let mut gcd = le(terms)
  let mut l = n__term(terms)
  while !(l is Nil) {
    gcd = egcd(le(l), gcd)
    l = n__term(l)
  }
  gcd
}

///|
fn psfind_s(p : Value) -> Value raise {
  if psp(p).truthy() {
    psfind_s(psterm(terms(p), rczero()))
  } else {
    psfind_s1(p)
  }
}

///|
fn psfind_s1(r : Value) -> Value raise {
  if !atom(cdr(r)) {
    rczero()
  } else if atom(car(r)) {
    r
  } else {
    let mut p = ptterm(cdar(r), Fix(0L))
    while !atom(p) {
      p = ptterm(cdr(p), Fix(0L))
    }
    cons(p, cdr(r))
  }
}

///|
fn psexpt(p : Value, n : Value) -> Value raise {
  if rczerop(n).truthy() {
    // p^0
    if rczerop(p).truthy() {
      // 0^0
      merr("taylor: 0^0 is undefined.", [])
    } else {
      rcone()
    }
  } else if equal(n, rcone()) || equal(n, rcfone()) {
    p
  } else if pscoefp(p).truthy() {
    rcexpt(p, n)
  } else if mono_term_q(terms(p)).truthy() {
    // A monomial to a power
    let mut s = psfind_s(n)
    let l = terms(p)
    // s is the numeric part of the exponent
    if floatp(car(s)) {
      s = maxima_rationalize(quot(car(s), cdr(s)))
    }
    let n_s = psdiff(n, s) // the non-numeric part of exponent
    let mut x = e_star(s, le(l)) // the degree of the lowest term
    x = if !symval(q_d_maxtayorder).truthy() &&
      e_gt(x, t_o_var(gvar(p))).truthy() {
      rczero()
    } else {
      pscheck(
        gvar_o(p),
        list1(e_plus(trunc_lvl(p), e_(x, e2=le(l)))),
        list1(term(x, psexpt(lc(l), n))),
      )
    }
    // x is now p^s
    if rczerop(n_s).truthy() || rczerop(x).truthy() {
      x
    } else {
      pstimes(
        x,
        psexpt(
          prep1(power_star(get_inverse(gvar(p)), rcdisrep(n_s))),
          ps_le(p),
        ),
      )
    }
  } else {
    let l = terms(p)
    let lc_ = lc(l)
    let le_ = le(l)
    let lt_ = lt(l)
    let trunc = trunc_lvl(p)
    let inc = psexpon_gcd(l)
    let mut s = psfind_s(n)
    if floatp(car(s)) {
      s = maxima_rationalize(quot(car(s), cdr(s)))
    }
    let lt2 = pscheck(gvar_o(p), list1(trunc), list1(lt_))
    let mut ans = psexpt(lt2, n)
    let lcinv = psexpt(lc_, rcmone())
    let mr = e_plus(inc, e_star(s, le_))
    let mut lim = if trunc is Nil && !e_gt(s, rczero()).truthy() {
      t_o_var(gvar(p))
    } else {
      // See the comment in PSEXPT1 below which tells why we don't allow
      // inf. trunc's here.
      e_plus(
        if trunc is Nil && !rcintegerp(s).truthy() {
          let lim0 = t_o_var(gvar(p))
          if lim0 is Nil {
            infin_ord_err()
          } else {
            lim0
          }
        } else {
          trunc
        },
        e_star(e1_(s), le_),
      )
    }
    ans = if pscoefp(ans).truthy() || !eq(gvar(p), gvar(ans)) {
      list2(Fix(0L), term(rczero(), ans))
    } else {
      cons(Fix(0L), terms(ans))
    }
    if !symval(q_d_maxtayorder).truthy() &&
      (
        !(lim is Nil) ||
        !rcintegerp(s).truthy() ||
        e_gt(e_star(s, le(last(l))), t_o_var(gvar(p))).truthy()
      ) {
      lim = emin(lim, t_o_var(gvar(p)))
    }
    psexpt1(gvar_o(p), lim, l, n, s, inc, Fix(1L), mr, ans, le_, lcinv)
  }
}

///|
fn psexpt1(
  varh : Value,
  trunc : Value,
  l : Value,
  n : Value,
  s : Value,
  inc : Value,
  m : Value,
  mr : Value,
  ans : Value,
  r : Value,
  linv : Value,
) -> Value raise {
  // n is the power we are raising the series to
  // inc is the exponent increment
  // mr is the current exponent
  // tr is the truncation level desired
  // m is the term index
  let mut m = to_int64(m)
  let mut mr = mr
  let mut a = last(ans)
  let mut tr = trunc
  // I don't see what's wrong with truncating exact series when raising them
  // to fractional powers so we'll allow it for now. This is accomplished
  // above in PSEXPT (see the comment). Thus, presumably, this check should
  // never be needed anymore.
  if tr is Nil {
    if rcintegerp(s).truthy() {
      tr = e_star(s, le(last(l)))
    } else {
      merr("taylor: expected an integer, instead found: ~:M", [s]) |> ignore
    }
  }
  if tr is Nil {
    tr = t_o_var(car(varh))
  }
  while true {
    // tag B
    if e_gt(mr, tr).truthy() {
      break
    }
    let mut kr = inc
    let mut ak = l
    let ma0 = pstimes(cons(Fix(1L), Fix(m)), linv)
    let mut k = 1L
    let mut sum = rczero()
    while true {
      // tag A
      if k > m {
        break
      }
      let cm_k = psterm(cdr(ans), e_(mr, e2=kr))
      if cm_k is Nil {
        break
      }
      ak = pstrim_terms(ak, e_plus(kr, r))
      if ak is Nil {
        break
      }
      let c = pstimes(
        psdiff(pstimes(cons(Fix(k), Fix(1L)), n), cons(Fix(m - k), Fix(1L))),
        pstimes(
          if e_eq(e_plus(kr, r), le(ak)).truthy() {
            lc(ak)
          } else {
            rczero()
          },
          cm_k,
        ),
      )
      sum = psplus(sum, c)
      k = k + 1
      kr = e_plus(kr, inc)
    }
    // tag ADD-TERM
    if !rczerop(sum).truthy() {
      add_term(a, term_or_e=mr, c=pstimes(ma0, sum)) |> ignore
      a = n__term(a)
    }
    m = m + 1
    mr = e_plus(mr, inc)
  }
  pscheck(varh, list1(trunc), cdr(ans))
}

///|
fn psderivative(p : Value, v : Value) -> Value raise {
  if pscoefp(p).truthy() {
    rcderiv(p, v)
  } else if eq(v, gvar(p)) {
    let z = rczerop(ps_le(p)).truthy()
    let p = psderiv1(
      gvar_o(p),
      trunc_lvl(p),
      cons(Fix(0L), terms(p)),
      list1(Fix(0L)),
    )
    if z {
      strip_zeroes(p, t)
    } else {
      p
    }
  } else {
    psderiv2(
      gvar_o(p),
      trunc_lvl(p),
      v,
      cons(Fix(0L), terms(p)),
      list1(Fix(0L)),
    )
  }
}

///|
fn psderiv1(varh : Value, trunc : Value, l : Value, ans : Value) -> Value raise {
  let mut a = last(ans)
  let mut l = l
  while true {
    if mono_term_q(l).truthy() || e_gt(le(n__term(l)), trunc).truthy() {
      return pscheck(varh, list1(e1_(trunc)), cdr(ans))
    }
    l = n__term(l)
    if !rczerop(le(l)).truthy() {
      add_term(a, term_or_e=e1_(le(l)), c=pstimes(le(l), lc(l))) |> ignore
      a = n__term(a)
    }
  }
  Nil
}

///|
fn psderiv2(
  varh : Value,
  trunc : Value,
  v : Value,
  l : Value,
  ans : Value,
) -> Value raise {
  let mut a = last(ans)
  let mut l = l
  while true {
    if mono_term_q(l).truthy() || e_gt(le(n__term(l)), trunc).truthy() {
      return pscheck(varh, list1(trunc), cdr(ans))
    }
    l = n__term(l)
    let c = psderivative(lc(l), v)
    if !rczerop(c).truthy() {
      add_term(a, term_or_e=le(l), c~) |> ignore
    }
    a = n__term(a)
  }
  Nil
}

///|
fn psdp(p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    return rcderivx(p)
  }
  let temp = getdiff(gvar_o(p))
  if rczerop(temp).truthy() || eq(car(temp), q_multi) {
    let temp2 = psdp2(
      gvar_o(p),
      trunc_lvl(p),
      cons(Fix(0L), terms(p)),
      list1(Fix(0L)),
    )
    if eq(car(temp), q_multi) {
      pstimes(
        temp2,
        make_ps(gvar_o(p), list1(inf()), terms=list1(term(cdr(temp), rcone()))),
      )
    } else {
      temp2
    }
  } else if temp is Nil {
    // A gvar without DIFF property belongs to an adjoined singular kernel
    // (e.g. log(x) or %e^(-1/x)) whose derivative the DIFF property scheme
    // cannot express. RATDX re-expands such series before calling us, so
    // this is only reachable via TSDIFF.
    merr("taylor: unable to differentiate series in ~:M", [
      getdisrep(gvar_o(p)),
    ])
  } else {
    psdp1(gvar_o(p), trunc_lvl(p), cons(Fix(0L), terms(p)), list1(Fix(0L)), temp)
  }
}

///|
fn psdp1(
  varh : Value,
  trunc : Value,
  l : Value,
  ans : Value,
  dx : Value,
) -> Value raise {
  let mut a = last(ans)
  let mut c = rczero()
  let mut l = l
  while true {
    if mono_term_q(l).truthy() || e_gt(le(n__term(l)), trunc).truthy() {
      return psplus(c, pscheck(varh, list1(e1_(trunc)), cdr(ans)))
    }
    l = n__term(l)
    // Product rule: A term a*v^e contributes PSDP(a)*v^e from the
    // coefficient, on top of the e*dx*a*v^(e-1) kernel part that the
    // ADD-TERM-&-POP below emits for e # 0.
    if !rczerop(le(l)).truthy() {
      let cd = psdp(lc(l))
      if !rczerop(cd).truthy() {
        c = psplus(
          c,
          make_ps(varh, list1(e1_(trunc)), terms=list1(term(le(l), cd))),
        )
      }
    }
    if rczerop(le(l)).truthy() {
      c = psplus(c, psdp(lc(l)))
    } else {
      add_term(a, term_or_e=e1_(le(l)), c=pstimes(le(l), pstimes(dx, lc(l))))
      |> ignore
      a = n__term(a)
    }
  }
  Nil
}

///|
fn psdp2(varh : Value, trunc : Value, l : Value, ans : Value) -> Value raise {
  let mut a = last(ans)
  let mut l = l
  while true {
    if mono_term_q(l).truthy() || e_gt(le(n__term(l)), trunc).truthy() {
      return pscheck(varh, list1(trunc), cdr(ans))
    }
    l = n__term(l)
    let c = psdp(lc(l))
    if !rczerop(c).truthy() {
      add_term(a, term_or_e=le(l), c~) |> ignore
      a = n__term(a)
    }
  }
  Nil
}

///|
fn psexpt_log_ord(p : Value) -> Value raise {
  if !symval(q_d_maxtayorder).truthy() {
    emin(trunc_lvl(p), t_o_var(gvar(p)))
  } else if trunc_lvl(p) is Nil {
    t_o_var(gvar(p))
  } else {
    trunc_lvl(p)
  }
}
