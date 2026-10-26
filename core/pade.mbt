// Port of src/pade.lisp: Pade approximants of truncated Taylor series.

///|
fn red(p : Value) -> Value raise {
  cdr(p)
}

///|
fn p0_q(p : Value) -> Value raise {
  lbool(p is Nil)
}

///|
fn e0_q(expon : Value) -> Value raise {
  lbool(zerop(car(expon)))
}

///|
fn epos_q(expon : Value) -> Value raise {
  let x = car(expon)
  lbool(numberp(x) && num_gt(x, Fix(0L)))
}

///|
fn eneg_q(expon : Value) -> Value raise {
  let x = car(expon)
  lbool(numberp(x) && num_lt(x, Fix(0L)))
}

///|
fn num(r : Value) -> Value raise {
  car(r)
}

///|
fn denom(r : Value) -> Value raise {
  cdr(r)
}

///|
fn eneg(exp_ : Value) -> Value raise {
  cons(num_neg(car(exp_)), cdr(exp_))
}

///|
fn pade_lexp(poly : Value) -> Value raise {
  if poly is Nil {
    ezero()
  } else {
    le(poly)
  }
}

///|
fn eshift(poly : Value, expon : Value) -> Value raise {
  mapcar(tm => term(e_plus(e(tm), expon), c(tm)), poly)
}

///|
fn psmake(p : Value, tpf : Value) -> Value raise {
  make_ps(gvar_o(tpf), poly_data(tpf), terms=reverse(p))
}

///|
fn d_pade(taylor_form : Value, n__bound : Value, d__bound : Value) -> Value raise {
  if !(d_ratp(taylor_form).truthy() && memq(q_trunc, car(taylor_form)).truthy()) {
    merr("pade: first argument must be a Taylor series; found: ~M", [
      taylor_form,
    ])
    |> ignore
  }
  let hd = car(taylor_form)
  with_specials(
    [(q_varlist, third(hd)), (q_genvar, fourth(hd)), (q_tlist, fifth(hd))],
    () => if psp(cdr(taylor_form)).truthy() {
      cons(
        list1(q_mlist),
        pade(
          cdr(taylor_form),
          cons(car(tay_order(n__bound)), car(tay_order(d__bound))),
          orig_trunc(car(mrat_tlist(taylor_form))),
        ),
      )
    } else {
      list2(list1(q_mlist), srdis(cdr(taylor_form)))
    },
  )
}

///|
fn pade(tpf : Value, bounds : Value, trunc : Value) -> Value raise {
  let ord = le(terms(tpf))
  let mut poly = terms(tpf)
  let mut trunc = e_plus(trunc, egcd(trunc, psexpon_gcd(poly)))
  if !e0_q(ord).truthy() {
    poly = eshift(poly, eneg(ord))
    trunc = e_(trunc, e2=ord)
    if epos_q(ord).truthy() {
      rplaca(bounds, e_(car(bounds), e2=ord)) |> ignore
    } else {
      rplacd(bounds, e_plus(cdr(bounds), ord)) |> ignore
    }
  }
  let mut r1 = cons(list1(term(trunc, rcone())), Nil)
  let mut r2 = pade_monize(reverse(poly), list1(term(ezero(), rcone())))
  let mut ans : Value = if e_gt(le(last(poly)), num(bounds)).truthy() ||
    eneg_q(denom(bounds)).truthy() {
    Nil
  } else {
    list1(r2)
  }
  while !(e0_q(pade_lexp(num(r2))).truthy() ||
      e_gt_eq(pade_lexp(denom(r2)), denom(bounds)).truthy()) {
    r1 = pade1(r1, r2)
    let tmp = r1
    r1 = r2
    r2 = tmp
    ans = if e_gt(le(num(r2)), num(bounds)).truthy() ||
      e_gt(le(denom(r2)), denom(bounds)).truthy() {
      ans
    } else if epos_q(le(last(num(r2)))).truthy() {
      // not a true approximate
      ans
    } else {
      cons(r2, ans)
    }
  }
  mapcar(
    r => d_ratsimp(
      div_star(
        srdis(psmake(eshift(num(r), ord), tpf)),
        srdis(psmake(denom(r), tpf)),
      ),
      Nil,
    ),
    ans,
  )
}

///|
fn pade1(r1 : Value, r2 : Value) -> Value raise {
  let lcoef = lc(num(r2))
  let expon = le(num(r2))
  let p2 = red(num(r2))
  let q2 = denom(r2)
  let mut p1 = num(r1)
  let mut q1 = denom(r1)
  while !(p1 is Nil || e_gt(expon, le(p1)).truthy()) {
    let quoterm = term(e_(le(p1), e2=expon), rcminus(rcquo(lc(p1), lcoef)))
    p1 = upoly_plus(red(p1), term_star(quoterm, p2))
    q1 = upoly_plus(q1, term_star(quoterm, q2))
  }
  pade_monize(p1, q1)
}

///|
fn term_star(term : Value, p : Value) -> Value raise {
  let mut p1 : Value = Nil
  let coef = c(term)
  let expon = e(term)
  for term1 in p.iter() {
    let coef1 = rctimes(coef, c(term1))
    if !rczerop(coef1).truthy() {
      p1 = cons(cons(e_plus(expon, e(term1)), coef1), p1)
    }
  }
  nreverse(p1)
}

///|
/// Monicize numerator.
fn pade_monize(num : Value, den : Value) -> Value raise {
  let mult = term(ezero(), rcinv(lc(num)))
  cons(term_star(mult, num), term_star(mult, den))
}

///|
fn upoly_plus(p1 : Value, p2 : Value) -> Value raise {
  let mut p1 = p1
  let mut p2 = p2
  let mut p : Value = Nil
  while true {
    if p1 is Nil {
      return nreconc(p, p2)
    } else if p2 is Nil {
      return nreconc(p, p1)
    } else if e_gt(le(p2), le(p1)).truthy() {
      p = cons(car(p2), p)
      p2 = cdr(p2)
    } else if e_gt(le(p1), le(p2)).truthy() {
      p = cons(car(p1), p)
      p1 = cdr(p1)
    } else {
      let c = rcplus(lc(p1), lc(p2))
      if !rczerop(c).truthy() {
        p = cons(term(le(p1), c), p)
      }
      p1 = red(p1)
      p2 = red(p2)
    }
  }
  Nil
}
