// Port of src/sinint.lisp: integration of rational functions (Hermite
// reduction, partial fractions, logarithmic parts) used by the SIN
// integrator.

///|
/// `(r+ r . l)`: sum of rational expressions, right-associated with RATPL.
fn sinint__rplus(xs : Array[Value]) -> Value raise {
  let mut r = xs[xs.length() - 1]
  for i = xs.length() - 2; i >= 0; i = i - 1 {
    r = ratpl(xs[i], r)
  }
  r
}

///|
/// `(r* r . l)`: product of rational expressions, right-associated with RATTI.
fn sinint__rtimes(xs : Array[Value]) -> Value raise {
  let mut r = xs[xs.length() - 1]
  for i = xs.length() - 2; i >= 0; i = i - 1 {
    r = ratti(xs[i], r, t)
  }
  r
}

///|
/// Divides P by Q. Under $ALGEBRAIC, PGCD normalizes its output via
/// ALGNORMAL, meaning Q might only divide P up to a constant factor rather
/// than perfectly. We return this scaled quotient and let CPROG handle the
/// final rescaling.
fn rootfac_quotient(p : Value, q : Value) -> Value raise {
  if symval(q_d_algebraic).truthy() {
    let r = rquotient(p, q)
    if equal(cdr(r), Fix(1L)) {
      car(r)
    } else {
      cadr(oldcontent(car(r)))
    }
  } else {
    pquotient(p, q)
  }
}

///|
fn rootfac(q : Value, sinint_var : Value) -> Value raise {
  let mut nthdq = pgcd(q, pderivative(q, sinint_var))
  let simproots = rootfac_quotient(q, nthdq)
  let mut ans = list1(rootfac_quotient(simproots, pgcd(nthdq, simproots)))
  let mut n_loops = 0
  while true {
    if num_eq(int(n_loops), symval(q_d_factor_max_degree)) {
      return list1(q)
    } else if pcoefp(nthdq).truthy() ||
      pointergp(sinint_var, car(nthdq)).truthy() {
      return reverse(ans)
    }
    let nthdq1 = pgcd(pderivative(nthdq, sinint_var), nthdq)
    ans = cons(
      rootfac_quotient(pgcd(nthdq, simproots), pgcd(nthdq1, simproots)),
      ans,
    )
    nthdq = nthdq1
    n_loops += 1
  }
  Nil
}

///|
fn aprog(q : Value, sinint_var : Value) -> (Value, Value) raise {
  let q = oldcontent(q)
  let rf0 = rootfac(cadr(q), sinint_var)
  let sinint_rootfactor = cons(ptimes(car(q), car(rf0)), cdr(rf0))
  let mut pd = list1(car(sinint_rootfactor))
  let mut rf = cdr(sinint_rootfactor)
  let mut n = 2
  while !(rf is Nil) {
    pd = cons(pexpt(car(rf), int(n)), pd)
    rf = cdr(rf)
    n += 1
  }
  let sinint_pardenom = reverse(pd)
  (sinint_rootfactor, sinint_pardenom)
}

///|
fn cprog(
  top : Value,
  bottom : Value,
  sinint_var : Value,
  sinint_pardenom : Value,
) -> (Value, Value) raise {
  let frpart0 = pdivide(top, bottom)
  let sinint_wholepart = car(frpart0)
  let mut frpart = cadr(frpart0)
  // With algebraic coefficients, the factors from ROOTFAC can multiply to a
  // constant multiple of BOTTOM.
  if symval(q_d_algebraic).truthy() {
    let prod = reduce((a, b) => ptimes(a, b), sinint_pardenom)
    if !equal(prod, bottom) {
      frpart = ratti(frpart, rquotient(prod, bottom), t)
    }
  }
  if length(sinint_pardenom) == 1 {
    return (list1(frpart), sinint_wholepart)
  }
  let mut pardenomc = cdr(sinint_pardenom)
  let mut ppdenom = list1(car(sinint_pardenom))
  while length(pardenomc) != 1 {
    ppdenom = cons(ptimes(car(ppdenom), car(pardenomc)), ppdenom)
    pardenomc = cdr(pardenomc)
  }
  pardenomc = reverse(sinint_pardenom)
  let mut sinint_parnumer : Value = Nil
  while true {
    let thebpg = bprog(car(pardenomc), car(ppdenom), sinint_var)
    sinint_parnumer = cons(
      cdr(ratdivide(ratti(frpart, cdr(thebpg), t), car(pardenomc))),
      sinint_parnumer,
    )
    frpart = cdr(ratdivide(ratti(frpart, car(thebpg), t), car(ppdenom)))
    pardenomc = cdr(pardenomc)
    ppdenom = cdr(ppdenom)
    if ppdenom is Nil {
      return (cons(frpart, sinint_parnumer), sinint_wholepart)
    }
  }
  (Nil, Nil)
}

///|
fn sinint__polyint1(p : Value, sinint_var : Value) -> Value raise {
  if p is Nil || equal(p, Fix(0L)) {
    cons(Fix(0L), Fix(1L))
  } else if atom(p) {
    list3(sinint_var, Fix(1L), p)
  } else if !numberp(car(p)) {
    if pointergp(sinint_var, car(p)).truthy() {
      list3(sinint_var, Fix(1L), p)
    } else {
      sinint__polyint1(cdr(p), sinint_var)
    }
  } else {
    ratplus(
      sinint__polyint2(p, sinint_var),
      sinint__polyint1(cddr(p), sinint_var),
    )
  }
}

///|
fn sinint__polyint2(p : Value, sinint_var : Value) -> Value raise {
  cons(list3(sinint_var, one_plus(car(p)), cadr(p)), one_plus(car(p)))
}

///|
fn polyint(p : Value, sinint_var : Value) -> Value raise {
  ratqu(sinint__polyint1(ratnumerator(p), sinint_var), ratdenominator(p))
}

///|
fn dprog(
  ratarg : Value,
  sinint_ratform : Value,
  sinint_var : Value,
) -> (Value, Value) raise {
  let mut ans = cons(Fix(0L), Fix(1L))
  let mut sinint_logptdx : Value = Nil
  if pcoefp(cdr(ratarg)).truthy() ||
    pointergp(sinint_var, cadr(ratarg)).truthy() {
    return (
      disrep(polyint(ratarg, sinint_var), sinint_ratform),
      sinint_logptdx,
    )
  }
  let (rootfactor0, sinint_pardenom) = aprog(
    ratdenominator(ratarg),
    sinint_var,
  )
  let (parnumer0, sinint_wholepart) = cprog(
    ratnumerator(ratarg),
    ratdenominator(ratarg),
    sinint_var,
    sinint_pardenom,
  )
  let mut sinint_rootfactor = reverse(rootfactor0)
  let mut sinint_parnumer = reverse(parnumer0)
  let mut klth = length(sinint_rootfactor)
  // intg
  while klth != 1 {
    let arootf = car(sinint_rootfactor)
    if !zerop(pdegree(arootf, sinint_var)) {
      let deriv = pderivative(arootf, sinint_var)
      let thebpg = bprog(arootf, deriv, sinint_var)
      let mut kx = klth - 1
      let mut thetop = car(sinint_parnumer)
      // iter
      while true {
        let prod1 = ratti(thetop, car(thebpg), t)
        let prod2 = ratti(thetop, cdr(thebpg), t)
        let thebot = pexpt(arootf, int(kx))
        ans = ratplus(ans, ratqu(ratminus(prod2), ratti(int(kx), thebot, t)))
        thetop = ratplus(
          prod1,
          ratqu(
            ratreduce(pderivative(car(prod2), sinint_var), cdr(prod2)),
            int(kx),
          ),
        )
        thetop = cdr(ratdivide(thetop, thebot))
        if kx == 1 {
          sinint_logptdx = cons(ratqu(thetop, arootf), sinint_logptdx)
          break
        }
        kx = kx - 1
      }
    }
    // reset
    sinint_rootfactor = cdr(sinint_rootfactor)
    sinint_parnumer = cdr(sinint_parnumer)
    klth = klth - 1
  }
  // simp
  sinint_logptdx = cons(
    ratqu(car(sinint_parnumer), car(sinint_rootfactor)),
    sinint_logptdx,
  )
  if equal(ans, Fix(0L)) {
    return (
      disrep(polyint(sinint_wholepart, sinint_var), sinint_ratform),
      sinint_logptdx,
    )
  }
  let thetop = cadr(pdivide(ratnumerator(ans), ratdenominator(ans)))
  (
    mk(q_mplus, [
      disrep(polyint(sinint_wholepart, sinint_var), sinint_ratform),
      disrep(ratqu(thetop, ratdenominator(ans)), sinint_ratform),
    ]),
    sinint_logptdx,
  )
}

///|
fn logmabs(x : Value) -> Value raise {
  let x = if symval(q_d_logabs).truthy() &&
    memq(
      d_csign(simplify(x)),
      list([q_d_complex, q_d_imaginary]),
    ).is_nil() {
    ftake(q_mabs, [x])
  } else {
    x
  }
  mk(q_p_log, [x])
}

///|
fn npask(npask_exp : Value) -> Value raise {
  if freeof(q_d__pcti, npask_exp).truthy() &&
    memq(d_csign(npask_exp), list([q_d_complex, q_d_imaginary])).is_nil() {
    learn(mk(q_mnotequal, [npask_exp, Fix(0L)]), t) |> ignore
    asksign(npask_exp)
  } else {
    q_d_positive
  }
}

///|
fn integrate_use_rootsof(
  f : Value,
  q : Value,
  variable : Value,
  sinint_ratform : Value,
) -> Value raise {
  let dummy = make_param()
  let qprime = disrep(pderivative(q, p__var(q)), sinint_ratform)
  let ff = disrep(f, sinint_ratform)
  let qq = disrep(q, sinint_ratform)
  // This basically does a partial fraction expansion and integrates
  // the result.  Let r be one (simple) root of the denominator
  // polynomial q.  Then the partial fraction expansion is
  //
  //   f(x)/q(x) = A/(x-r) + similar terms.
  //
  // Then
  //
  //   f(x) = A*q(x)/(x-r) + others
  //
  // Take the limit as x -> r.
  //
  //   f(r) = A*limit(q(x)/(x-r),x,r) + others
  //        = A*at(diff(q(x),r), [x=r])
  //
  // Hence, A = f(r)/at(diff(q(x),x),[x=r])
  //
  // Then it follows that the integral is
  //
  //    A*log(x-r)
  //
  // Note that we don't express the polynomial in terms of the
  // variable of integration, but in our dummy variable instead.
  // Using the variable of integration results in a wrong answer
  // when a substitution was done previously, since when the
  // substitution is finally undone, that modifies the polynomial.
  let quo = div_star(subst(dummy, variable, ff), subst(dummy, variable, qprime))
  let lg = mk(q_p_log, [sub_star(variable, dummy)])
  mk(q_p_lsum, [
    mk(q_mtimes, [quo, lg]),
    dummy,
    mk(q_d_rootsof, [subst(dummy, variable, qq), dummy]),
  ])
}

///|
fn eprog(
  p : Value,
  sinint_ratform : Value,
  sinint_var : Value,
  sinint_switch1 : Value,
) -> Value raise {
  let mut sinint_switch1 = sinint_switch1
  if equal(p, Fix(0L)) || equal(car(p), Fix(0L)) {
    return Fix(0L)
  }
  let mut p1e = ratnumerator(p)
  let mut p2e = ratdenominator(p)
  let mut xx : Value = Nil
  let mut deg : Value = Nil
  let mut a1e : Value = Nil
  let go_efac = sinint_switch1.truthy() ||
    (
      !atom(p2e) &&
      {
        xx = cadr(oldcontent(p2e))
        eq(car(xx), sinint_var)
      } &&
      {
        deg = pdegree(xx, sinint_var)
        member_equal(deg, list([Fix(5L), Fix(6L)])).truthy()
      } &&
      zerocoefl(xx, deg, sinint_var).truthy() &&
      (equal(deg, Fix(5L)) || !pminusp(car(last(xx))).truthy())
    )
  if !go_efac {
    a1e = intfactor(p2e)
    if length(a1e) > 1 {
      // e40
      let sinint_pardenom = a1e
      sinint_switch1 = t
      let sinint_parnumer = cprog(p1e, p2e, sinint_var, sinint_pardenom).0
      let sw = sinint_switch1
      let a2e = mapcar2(
        (j, k) => eprog(ratqu(j, k), sinint_ratform, sinint_var, sw),
        sinint_parnumer,
        sinint_pardenom,
      )
      return cons(list1(q_mplus), a2e)
    }
  }
  // efac
  let ncc = oldcontent(p1e)
  p1e = cadr(ncc)
  let dcc = oldcontent(p2e)
  p2e = cadr(dcc)
  let allcc = ratqu(car(ncc), car(dcc))
  deg = pdegree(p2e, sinint_var)
  a1e = pderivative(p2e, sinint_var)
  let mut a2e = ratqu(
    polcoef(p1e, pdegree(p1e, sinint_var), sinint_var),
    polcoef(a1e, pdegree(a1e, sinint_var), sinint_var),
  )
  if equal(ratti(a2e, a1e, t), cons(p1e, Fix(1L))) {
    return mk(q_mtimes, [
      disrep(ratti(allcc, a2e, t), sinint_ratform),
      logmabs(disrep(p2e, sinint_ratform)),
    ])
  }
  if equal(deg, Fix(1L)) {
    // e10
    return mk(q_mtimes, [
      disrep(
        ratti(
          allcc,
          ratqu(
            polcoef(p1e, pdegree(p1e, sinint_var), sinint_var),
            polcoef(p2e, Fix(1L), sinint_var),
          ),
          t,
        ),
        sinint_ratform,
      ),
      logmabs(disrep(p2e, sinint_ratform)),
    ])
  } else if equal(deg, Fix(2L)) {
    // e20
    let discrim = ratdifference(
      cons(pexpt(polcoef(p2e, Fix(1L), sinint_var), Fix(2L)), Fix(1L)),
      ratti(
        Fix(4L),
        ratti(
          polcoef(p2e, Fix(2L), sinint_var),
          polcoef(p2e, Fix(0L), sinint_var),
          t,
        ),
        t,
      ),
    )
    a2e = ratti(polcoef(p2e, pdegree(p2e, sinint_var), sinint_var), Fix(2L), t)
    xx = simplify(disrep(discrim, sinint_ratform))
    let mut goto_e30 = false
    let mut goto_zip = false
    if equal(d_imagpart(xx), Fix(0L)) {
      let sign = npask(xx)
      if eq(sign, q_d_negative) {
        goto_e30 = true
      } else if eq(sign, q_d_zero) {
        goto_zip = true
      }
    }
    if goto_e30 {
      // e30
      a1e = ratsqrt(ratminus(discrim), sinint_ratform)
      let repart = ratqu(
        if zerop(pdegree(p1e, sinint_var)) {
          ratti(a2e, polcoef(p1e, Fix(0L), sinint_var), t)
        } else {
          eprogratd(a2e, p1e, p2e, sinint_var)
        },
        polcoef(p2e, pdegree(p2e, sinint_var), sinint_var),
      )
      let a3e : Value = if equal(Fix(0L), car(repart)) {
        Fix(0L)
      } else {
        let q1 = mk(q_mquotient, [
          disrep(ratti(allcc, repart, t), sinint_ratform),
          a1e,
        ])
        mk(q_mtimes, [
          q1,
          mk(q_p_atan, [
            mk(q_mquotient, [
              disrep(pderivative(p2e, sinint_var), sinint_ratform),
              a1e,
            ]),
          ]),
        ])
      }
      if zerop(pdegree(p1e, sinint_var)) {
        return a3e
      }
      return mk(q_mplus, [
        mk(q_mtimes, [
          disrep(
            ratti(
              allcc,
              ratqu(polcoef(p1e, pdegree(p1e, sinint_var), sinint_var), a2e),
              t,
            ),
            sinint_ratform,
          ),
          logmabs(disrep(p2e, sinint_ratform)),
        ]),
        a3e,
      ])
    }
    if goto_zip {
      // zip
      p2e = ratqu(
        psimp(
          p__var(p2e),
          pcoefadd(
            Fix(2L),
            pexpt(ptimes(Fix(2L), polcoef(p2e, Fix(2L), sinint_var)), Fix(2L)),
            pcoefadd(
              Fix(1L),
              ptimes(
                Fix(4L),
                ptimes(
                  polcoef(p2e, Fix(2L), sinint_var),
                  polcoef(p2e, Fix(1L), sinint_var),
                ),
              ),
              pcoefadd(
                Fix(0L),
                pexpt(polcoef(p2e, Fix(1L), sinint_var), Fix(2L)),
                Nil,
              ),
            ),
          ),
        ),
        ptimes(Fix(4L), polcoef(p2e, Fix(2L), sinint_var)),
      )
      return fprog(ratti(allcc, ratqu(p1e, p2e), t), sinint_ratform, sinint_var)
    }
    a1e = ratsqrt(discrim, sinint_ratform)
    let num_ = mk(q_mplus, [
      mk(q_mtimes, [
        disrep(a2e, sinint_ratform),
        disrep(list3(sinint_var, Fix(1L), Fix(1L)), sinint_ratform),
      ]),
      disrep(polcoef(p2e, Fix(1L), sinint_var), sinint_ratform),
      mk(q_mminus, [a1e]),
    ])
    let den_ = mk(q_mplus, [
      mk(q_mtimes, [
        disrep(a2e, sinint_ratform),
        disrep(list3(sinint_var, Fix(1L), Fix(1L)), sinint_ratform),
      ]),
      disrep(polcoef(p2e, Fix(1L), sinint_var), sinint_ratform),
      a1e,
    ])
    let a3e = logmabs(mk(q_mquotient, [num_, den_]))
    if zerop(pdegree(p1e, sinint_var)) {
      return mk(q_mtimes, [
        disrep(allcc, sinint_ratform),
        mk(q_mquotient, [
          disrep(polcoef(p1e, Fix(0L), sinint_var), sinint_ratform),
          a1e,
        ]),
        a3e,
      ])
    }
    let t1 = mk(q_mtimes, [
      disrep(
        ratti(
          allcc,
          ratqu(polcoef(p1e, pdegree(p1e, sinint_var), sinint_var), a2e),
          t,
        ),
        sinint_ratform,
      ),
      logmabs(disrep(p2e, sinint_ratform)),
    ])
    let t2 = mk(q_mtimes, [
      mk(q_mquotient, [
        disrep(
          ratti(allcc, ratqu(eprogratd(a2e, p1e, p2e, sinint_var), a2e), t),
          sinint_ratform,
        ),
        a1e,
      ]),
      a3e,
    ])
    return mk(q_mplus, [t1, t2])
  } else if equal(deg, Fix(3L)) &&
    equal(polcoef(p2e, Fix(2L), sinint_var), Fix(0L)) &&
    equal(polcoef(p2e, Fix(1L), sinint_var), Fix(0L)) {
    return e3prog(p1e, p2e, allcc, sinint_ratform, sinint_var, sinint_switch1)
  } else if member_equal(deg, list([Fix(4L), Fix(5L), Fix(6L)])).truthy() &&
    zerocoefl(p2e, deg, sinint_var).truthy() {
    return enprog(p1e, p2e, allcc, deg, sinint_ratform, sinint_var)
  }
  if symval(q_d_integrate_use_rootsof).truthy() &&
    equal(car(psqfr(p2e)), p2e) {
    return mk(q_mtimes, [
      disrep(allcc, sinint_ratform),
      integrate_use_rootsof(
        p1e,
        p2e,
        car(last(symval(q_varlist))),
        sinint_ratform,
      ),
    ])
  }
  mk(q_mtimes, [
    disrep(allcc, sinint_ratform),
    mk(q_p_integrate, [
      mk(q_mquotient, [
        disrep(p1e, sinint_ratform),
        disrep(p2e, sinint_ratform),
      ]),
      car(last(symval(q_varlist))),
    ]),
  ])
}

///|
fn e3prog(
  num : Value,
  denom : Value,
  cont : Value,
  sinint_ratform : Value,
  sinint_var : Value,
  sinint_switch1 : Value,
) -> Value raise {
  let a = polcoef(num, Fix(2L), sinint_var)
  let b = polcoef(num, Fix(1L), sinint_var)
  let c = polcoef(num, Fix(0L), sinint_var)
  let d = polcoef(denom, Fix(3L), sinint_var)
  let e = polcoef(denom, Fix(0L), sinint_var)
  let r = if eq(
      npask(simplify(disrep(ratqu(e, d), sinint_ratform))),
      q_d_negative,
    ) {
    simpnrt(disrep(ratqu(ratti(Fix(-1L), e, t), d), sinint_ratform), Fix(3L))
  } else {
    neg(simpnrt(disrep(ratqu(e, d), sinint_ratform), Fix(3L)))
  }
  let var_star = list3(sinint_var, Fix(1L), Fix(1L))
  newvar(r) |> ignore
  orderpointer(symval(q_varlist)) |> ignore
  let x = ratf(r)
  let sinint_ratform = car(x)
  let ratr = cdr(x)
  let rp = sinint__rplus
  let rt = sinint__rtimes
  let t1 = mk(q_mtimes, [
    disrep(
      ratqu(
        rt([cont, rp([rt([a, ratr, ratr]), rt([b, ratr]), c])]),
        rt([ratr, ratr, Fix(3L), d]),
      ),
      sinint_ratform,
    ),
    logmabs(disrep(ratpl(ratti(Fix(-1L), ratr, t), var_star), sinint_ratform)),
  ])
  let t2 = eprog(
    rt([
      cont,
      ratqu(
        rp([
          rt([
            rp([
              rt([Fix(2L), a, ratr, ratr]),
              rt([Fix(-1L), b, ratr]),
              rt([Fix(-1L), c]),
            ]),
            var_star,
          ]),
          rp([
            ratqu(rt([Fix(-1L), a, e]), d),
            rt([b, ratr, ratr]),
            rt([Fix(-1L), Fix(2L), c, ratr]),
          ]),
        ]),
        rt([
          Fix(3L),
          d,
          ratr,
          ratr,
          rp([
            ratti(var_star, var_star, t),
            ratti(ratr, var_star, t),
            ratti(ratr, ratr, t),
          ]),
        ]),
      ),
    ]),
    sinint_ratform,
    sinint_var,
    sinint_switch1,
  )
  simplify(mk(q_mplus, [t1, t2]))
}

///|
fn eprogratd(
  a2e : Value,
  p1e : Value,
  p2e : Value,
  sinint_var : Value,
) -> Value raise {
  ratdifference(
    ratti(
      a2e,
      polcoef(p1e, one_minus(pdegree(p1e, sinint_var)), sinint_var),
      t,
    ),
    ratti(
      polcoef(p2e, one_minus(pdegree(p2e, sinint_var)), sinint_var),
      polcoef(p1e, pdegree(p1e, sinint_var), sinint_var),
      t,
    ),
  )
}

///|
/// `((rat simp) n d)`
fn sinint__rat(n : Int, d : Int) -> Value {
  mk_simp(q_rat, [int(n), int(d)])
}

///|
fn enprog(
  num : Value,
  denom : Value,
  cont : Value,
  deg : Value,
  sinint_ratform : Value,
  sinint_var : Value,
) -> Value raise {
  // Denominator is (A*VAR^4+B) =
  //   if B<0 then (SQRT(A)*VAR^2 - SQRT(-B)) (SQRT(A)*VAR^2 + SQRT(-B))
  //	     else
  //	(SQRT(A)*VAR^2 - SQRT(2)*A^(1/4)*B^(1/4)*VAR + SQRT(B)) *
  //	(SQRT(A)*VAR^2 + SQRT(2)*A^(1/4)*B^(1/4)*VAR + SQRT(B))
  // or (A*VAR^5+B) =
  //	(1/4) * (A^(1/5)*VAR + B^(1/5)) *
  //	(2*A^(2/5)*VAR^2 + (-SQRT(5)-1)*A^(1/5)*B^(1/5)*VAR + 2*B^(2/5)) *
  //	(2*A^(2/5)*VAR^2 + (+SQRT(5)-1)*A^(1/5)*B^(1/5)*VAR + 2*B^(2/5))
  // or (A*VAR^6+B) =
  //   if B<0 then (SQRT(A)*VAR^3 - SQRT(-B)) (SQRT(A)*VAR^3 + SQRT(-B))
  //	     else
  //	(A^(1/3)*VAR^2 + B^(1/3)) *
  //	(A^(1/3)*VAR^2 - SQRT(3)*A^(1/6)*B^(1/6)*VAR + B^(1/3)) *
  //	(A^(1/3)*VAR^2 + SQRT(3)*A^(1/6)*B^(1/6)*VAR + B^(1/3))
  with_specials(
    [(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L)), (q_d_algebraic, Nil)],
    () => {
      let a = simplify(disrep(polcoef(denom, deg, sinint_var), sinint_ratform))
      let b = simplify(disrep(polcoef(denom, Fix(0L), sinint_var), sinint_ratform))
      let disvar = simplify(get(sinint_var, q_disrep))
      let num = simplify(disrep(num, sinint_ratform))
      let cont = simplify(disrep(cont, sinint_ratform))
      let mut denom = denom
      let mut term : Value = Nil
      if num_eq(deg, Fix(4L)) {
        if eql(d_imagpart(b), Fix(0L)) && eq(q_d_neg, d_asksign(b)) {
          denom = mul2(
            add2(
              mul2(power(a, sinint__rat(1, 2)), power(disvar, Fix(2L))),
              power(mul2(Fix(-1L), b), sinint__rat(1, 2)),
            ),
            add2(
              mul2(power(a, sinint__rat(1, 2)), power(disvar, Fix(2L))),
              mul2(Fix(-1L), power(mul2(Fix(-1L), b), sinint__rat(1, 2))),
            ),
          )
        } else {
          denom = add2(
            mul2(power(a, sinint__rat(1, 2)), power(disvar, Fix(2L))),
            power(b, sinint__rat(1, 2)),
          )
          term = muln(
            list([
              power(Fix(2L), sinint__rat(1, 2)),
              power(a, sinint__rat(1, 4)),
              power(b, sinint__rat(1, 4)),
              disvar,
            ]),
            t,
          )
          denom = mul2(add2(denom, term), sub(denom, term))
        }
      } else if num_eq(deg, Fix(5L)) {
        term = mul3(power(a, sinint__rat(1, 5)), power(b, sinint__rat(1, 5)), disvar)
        denom = add2(
          mul3(Fix(2L), power(a, sinint__rat(2, 5)), power(disvar, Fix(2L))),
          sub(mul2(Fix(2L), power(b, sinint__rat(2, 5))), term),
        )
        term = mul2(power(Fix(5L), sinint__rat(1, 2)), term)
        denom = muln(
          list([
            sinint__rat(1, 4),
            add2(
              mul2(power(a, sinint__rat(1, 5)), disvar),
              power(b, sinint__rat(1, 5)),
            ),
            add2(denom, term),
            sub(denom, term),
          ]),
          t,
        )
      } else if eql(d_imagpart(b), Fix(0L)) && eq(q_d_neg, d_asksign(b)) {
        denom = mul2(
          add2(
            mul2(power(a, sinint__rat(1, 2)), power(disvar, Fix(3L))),
            power(mul2(Fix(-1L), b), sinint__rat(1, 2)),
          ),
          add2(
            mul2(power(a, sinint__rat(1, 2)), power(disvar, Fix(3L))),
            mul2(Fix(-1L), power(mul2(Fix(-1L), b), sinint__rat(1, 2))),
          ),
        )
      } else {
        denom = add2(
          mul2(power(a, sinint__rat(1, 3)), power(disvar, Fix(2L))),
          power(b, sinint__rat(1, 3)),
        )
        term = muln(
          list([
            power(Fix(3L), sinint__rat(1, 2)),
            power(a, sinint__rat(1, 6)),
            power(b, sinint__rat(1, 6)),
            disvar,
          ]),
          t,
        )
        denom = mul3(denom, add2(denom, term), sub(denom, term))
      }
      // Needs $ALGEBRAIC NIL so next call to RATF will preserve factorization.
      mul2(cont, ratint(div(num, denom), disvar))
    },
  )
}

///|
fn zerocoefl(e : Value, n : Value, sinint_var : Value) -> Value raise {
  let mut i = 1
  while !num_eq(int(i), n) {
    if !equal(polcoef(e, int(i), sinint_var), Fix(0L)) {
      return Nil
    }
    i += 1
  }
  t
}

///|
fn ratsqrt(a : Value, sinint_ratform : Value) -> Value raise {
  with_special(q_varlist, Nil, () => simpnrt(
    disrep(a, sinint_ratform),
    Fix(2L),
  ))
}

///|
fn fprog(
  rat_star : Value,
  sinint_ratform : Value,
  sinint_var : Value,
) -> Value raise {
  let (dprog_ret, sinint_logptdx) = dprog(rat_star, sinint_ratform, sinint_var)
  addn(
    cons(
      dprog_ret,
      mapcar(p => eprog(p, sinint_ratform, sinint_var, Nil), sinint_logptdx),
    ),
    Nil,
  )
}

///|
fn ratint(sinint_exp : Value, sinint_var : Value) -> Value raise {
  with_specials(
    [
      (q_genvar, Nil),
      (q_ear_checkfactors, Nil),
      (q_varlist, Nil),
      (q_d_keepfloat, Nil),
    ],
    () => {
      set(q_varlist, list1(sinint_var)) |> ignore
      let ratarg = ratf(sinint_exp)
      let sinint_ratform = car(ratarg)
      let sinint_var = caadr(ratf(sinint_var))
      fprog(cdr(ratarg), sinint_ratform, sinint_var)
    },
  )
}

///|
fn sinint__everysecond(a : Value) -> Value raise {
  if a.truthy() {
    cons(
      if numberp(car(a)) {
        pexpt(car(a), cadr(a))
      } else {
        car(a)
      },
      sinint__everysecond(cddr(a)),
    )
  } else {
    Nil
  }
}

///|
fn intfactor(l : Value) -> Value raise {
  with_special(q_d_factorflag, Nil, () => {
    let a = oldcontent(l)
    let b = sinint__everysecond(pfactor(cadr(a)))
    if equal(car(a), Fix(1L)) {
      b
    } else {
      cons(car(a), b)
    }
  })
}

///|
fn init_sinint() -> Unit raise {
  // (defmvar $integrate_use_rootsof nil ... :setting-list (nil t))
  let possible_values = list([Nil, t])
  putprop(
    q_d_integrate_use_rootsof,
    lfunc("integrate_use_rootsof-assign", args => {
      let var_ = arg(args, 0)
      let val = arg(args, 1)
      if member(val, possible_values) is Nil {
        mseterr(
          var_,
          val,
          reason=Str(
            format_to_string("must be one of: ~{~A~^, ~}", [
              mapcar(x => stripdollar(x), possible_values),
            ]),
          ),
        )
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
}
