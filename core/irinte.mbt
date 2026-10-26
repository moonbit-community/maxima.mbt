// Port of src/irinte.lisp: integrals of irrational expressions, i.e. of
// products of polynomials and powers of quadratics whose exponents are
// half an odd integer.

///|
/// `1//2` (the special holding ((rat simp) 1 2)).
fn irinte__half() -> Value {
  symval(q_n1_sl_sl2)
}

///|
/// `-1//2`
fn irinte__mhalf() -> Value {
  symval(q_n_1_sl_sl2)
}

///|
fn irinte__i(n : Int) -> Value {
  int(n)
}

///|
/// The patterns below hold this symbol in their `,var2` slots.
fn irinte__pat(text : String) -> Value {
  try! lread(text)
}

///|
let irinte__root_pat : Value = irinte__pat(
  "((mplus) ((coeffpt) (c nonzerp) ((mexpt) (u hasvar2 irinte-var2) (v integerpfr))) ((coeffpp) (c true)))",
)

///|
let irinte__jmaug_pat : Value = irinte__pat(
  "((mtimes) ((coefftt) (d freevar2 irinte-var2)) ((coefftt) (p polyp-var irinte-var2)) ((mexpt) ((mplus) ((coeffpt) (f freevar2 irinte-var2) (x varp2 irinte-var2)) ((coeffpp) (e freevar2 irinte-var2))) (m maxima-integerp)) ((mexpt) ((mplus) ((coeffpt) (a freevar2 irinte-var2) ((mexpt) (x varp2 irinte-var2) 2)) ((coeffpt) (b freevar2 irinte-var2) (x varp2 irinte-var2)) ((coeffpp) (c freevar2 irinte-var2))) (n integerp1)))",
)

///|
let irinte__factpow_pat : Value = irinte__pat(
  "((mtimes) ((coefftt) (d freevar2 irinte-var2)) ((coefftt) (p polyp-var irinte-var2)) ((mexpt) (r1 hasvar2 irinte-var2) (e1 integerpfr)) ((mexpt) (r2 hasvar2 irinte-var2) (e2 integerpfr)) ((mexpt) (r0 hasvar2 irinte-var2) (e0 maxima-integerp)))",
)

///|
let irinte__elliptquad_pat : Value = irinte__pat(
  "((mtimes) ((coefftt) (d freevar2 irinte-var2)) ((coefftt) (p polyp-var irinte-var2)) ((mexpt) ((mplus) ((coeffpt) (e freevnz2 irinte-var2) ((mexpt) (x varp2 irinte-var2) 2)) ((coeffpt) (f freevar2 irinte-var2) (x varp2 irinte-var2)) ((coeffpp) (g freevar2 irinte-var2))) -1) ((mexpt) (r0 hasvar2 irinte-var2) (e0 integerpfr)))",
)

///|
/// Instantiate a pattern template with the variable of integration.
fn irinte__inst(template : Value, var2 : Value) -> Value {
  subst(var2, sym("irinte-var2"), template)
}

///|
/// T if A is half an odd integer. The INTEGERP2 test excludes an
/// integral float such as 2.0, which MAXIMA-INTEGERP does not accept.
fn integerpfr(a : Value) -> Value raise {
  if !(maxima_integerp(a).truthy() || integerp2(a).truthy()) {
    integerp1(a)
  } else {
    Nil
  }
}

///|
fn hasvar2(exp_ : Value, var2 : Value) -> Value raise {
  lbool(!freevar2(exp_, var2).truthy())
}

///|
fn freevnz2(a : Value, var2 : Value) -> Value raise {
  if freevar2(a, var2).truthy() {
    lbool(!equal(a, Fix(0L)))
  } else {
    Nil
  }
}

///|
fn inte(funct : Value, x : Value) -> Value raise {
  with_specials(
    [
      (q_ear_checkcoefsignlist, Nil),
      (q_ear_globalcareflag, Nil),
      (q_d_radexpand, t),
    ],
    () => intir_ref(funct, x),
  )
}

///|
fn intir_ref(fun : Value, x : Value) -> Value raise {
  let a = intir1(fun, x)
  if a.truthy() {
    return a
  }
  let a = intir2(fun, x)
  if a.truthy() {
    return a
  }
  intir3(fun, x)
}

///|
fn intir1(fun : Value, x : Value) -> Value raise {
  let assoclist = factpow(specrepcheck(fun), x)
  let mut e1 = cdras(q_e1, assoclist)
  let mut e2 = cdras(q_e2, assoclist)
  if assoclist is Nil {
    return Nil
  }
  let d = cdras(q_d, assoclist)
  let p = cdras(q_p, assoclist)
  let mut e0 = cdras(q_e0, assoclist)
  let r0 = cdras(q_r0, assoclist)
  let r1 = cdras(q_r1, assoclist)
  let r2 = cdras(q_r2, assoclist)
  if floatp(e0) {
    e0 = rdis(ration1(e0))
  }
  if floatp(e1) {
    e1 = rdis(ration1(e1))
  }
  if floatp(e2) {
    e2 = rdis(ration1(e2))
  }
  intir1_ref(d, p, r0, e0, r1, e1, r2, e2, x)
}

///|
fn intir2(funct : Value, x : Value) -> Value raise {
  let res = intir(funct, x)
  if res.truthy() {
    res
  } else {
    intirfactoroot(funct, x)
  }
}

///|
fn intir3(exp_ : Value, x : Value) -> Value raise {
  let assoclist = elliptquad(exp_, x)
  if assoclist.truthy() {
    let e = cdras(q_e, assoclist)
    let f = cdras(q_f, assoclist)
    let g = cdras(q_g, assoclist)
    let r0 = cdras(q_r0, assoclist)
    assume(mk(q_d_notequal, [e, Fix(0L)])) |> ignore
    return intir3_r0test(assoclist, x, e, f, g, r0)
  }
  Nil
}

///|
fn intir3_r0test(
  assoclist : Value,
  x : Value,
  e : Value,
  f : Value,
  g : Value,
  r0 : Value,
) -> Value raise {
  if root_plusanything(r0, x).truthy() {
    Nil
  } else {
    intir3_ref(assoclist, x, e, f, g, r0)
  }
}

///|
/// Handle integrals of the form d*p(x)*r1(x)^e1*r2(x)^e2*r0(x)^e0,
/// where p(x) is a polynomial, e1 and e2 are both half an odd integer,
/// and e0 is an integer.
fn intir1_ref(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  r1 : Value,
  e1 : Value,
  r2 : Value,
  e2 : Value,
  x : Value,
) -> Value raise {
  let nume1 = cadr(e1)
  let nume2 = cadr(e2)
  if plusp(nume1) && plusp(nume2) {
    pp_intir1(d, p, r0, e0, r1, e1, r2, e2, x)
  } else if minusp(nume1) && minusp(nume2) {
    mm_intir1(d, p, r0, e0, r1, e1, r2, e2, x)
  } else if plusp(nume1) {
    pm_intir1(d, p, r0, e0, r1, e1, r2, e2, x)
  } else {
    pm_intir1(d, p, r0, e0, r2, e2, r1, e1, x)
  }
}

///|
fn pp_intir1(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  r1 : Value,
  e1 : Value,
  r2 : Value,
  e2 : Value,
  x : Value,
) -> Value raise {
  if num_gt(cadr(e1), cadr(e2)) {
    pp_intir1_exec(d, p, r0, e0, r1, e1, r2, e2, x)
  } else {
    pp_intir1_exec(d, p, r0, e0, r2, e2, r1, e1, x)
  }
}

///|
fn mm_intir1(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  r1 : Value,
  e1 : Value,
  r2 : Value,
  e2 : Value,
  x : Value,
) -> Value raise {
  if num_gt(cadr(e1), cadr(e2)) {
    mm_intir1_exec(d, p, r0, e0, r1, e1, r2, e2, x)
  } else {
    mm_intir1_exec(d, p, r0, e0, r2, e2, r1, e1, x)
  }
}

///|
fn pm_intir1(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  rofpos : Value,
  epos : Value,
  rofneg : Value,
  eneg : Value,
  x : Value,
) -> Value raise {
  let numepos = cadr(epos)
  let numul_1eneg = muln_([Fix(-1L), cadr(eneg)])
  if num_gt(numepos, numul_1eneg) {
    mm_intir1(
      d,
      muln_([p, power(rofpos, sub(epos, eneg))]),
      r0,
      e0,
      rofpos,
      eneg,
      rofneg,
      eneg,
      x,
    )
  } else if equal(e0, Fix(0L)) || plusp(e0) {
    pp_intir1(
      d,
      muln_([p, power(rofneg, sub(eneg, epos))]),
      r0,
      e0,
      rofpos,
      epos,
      rofneg,
      epos,
      x,
    )
  } else {
    mm_intir1(
      d,
      muln_([p, power(rofpos, sub(epos, eneg))]),
      r0,
      e0,
      rofpos,
      eneg,
      rofneg,
      eneg,
      x,
    )
  }
}

///|
fn pp_intir1_exec(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  rofmax : Value,
  emax : Value,
  rofmin : Value,
  emin : Value,
  x : Value,
) -> Value raise {
  intir1_exec(d, p, r0, e0, rofmax, emax, rofmin, emin, x)
}

///|
fn mm_intir1_exec(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  rofmin : Value,
  emin : Value,
  rofmax : Value,
  emax : Value,
  x : Value,
) -> Value raise {
  intir1_exec(d, p, r0, e0, rofmax, emax, rofmin, emin, x)
}

///|
/// Integrate d*p*r0^e0*rofmax^emax*rofmin^emin as
/// d*p*r0^e0*rofmax^(emax-emin)*q^emin with q = rofmax*rofmin. The two
/// differ by the factor u = rofmax^emin*rofmin^emin/q^emin, which is 1 or
/// -1 and constant wherever neither rofmax nor rofmin crosses a branch cut.
/// Terms of the result with powers of q are written in rofmax and rofmin
/// again, and the other terms that depend on x are multiplied by u. If u
/// is 1 for every real x, the result is returned as it is.
fn intir1_exec(
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
  rofmax : Value,
  emax : Value,
  rofmin : Value,
  emin : Value,
  x : Value,
) -> Value raise {
  let q = d_expand(muln_([rofmax, rofmin]))
  let res = intir(
    muln_([
      d,
      p,
      if equal(e0, Fix(0L)) {
        Fix(1L)
      } else {
        power(r0, e0)
      },
      power(rofmax, addn_([emax, muln_([Fix(-1L), emin])])),
      power(q, emin),
    ]),
    x,
  )
  if res.truthy() && intir1_merge_exact_p(rofmax, rofmin, x).truthy() {
    return res
  }
  if res.truthy() {
    addn(
      mapcar(
        term => {
          let new_ = intir1_unsplit(term, q, rofmax, rofmin)
          if !alike1(new_, term).truthy() {
            new_
          } else if freeof(x, term).truthy() {
            term
          } else {
            muln_([
              power(rofmax, emin),
              power(rofmin, emin),
              power(q, neg(emin)),
              term,
            ])
          }
        },
        if mplusp(res).truthy() {
          cdr(res)
        } else {
          list1(res)
        },
      ),
      t,
    )
  } else {
    Nil
  }
}

///|
/// Return T if sqrt(r1)*sqrt(r2) equals sqrt(r1*r2) for every real x,
/// which holds for r1 = a1*x+b1 and r2 = a2*x+b2 with real numbers
/// a1*a2 < 0 and abs(a2)*b1+abs(a1)*b2 >= 0.
fn intir1_merge_exact_p(r1 : Value, r2 : Value, x : Value) -> Value raise {
  fn coeffs(r : Value) -> Value raise {
    let r = d_expand(r)
    let a = d_coeff(r, x, n=Fix(1L))
    let b = d_coeff(r, x, n=Fix(0L))
    if freeof(x, a).truthy() &&
      freeof(x, b).truthy() &&
      alike1(d_expand(addn_([muln_([a, x]), b])), r).truthy() &&
      zerop1(d_imagpart(a)).truthy() {
      list2(a, b)
    } else {
      Nil
    }
  }

  let c1 = coeffs(r1)
  let c2 = coeffs(r2)
  lbool(
    c1.truthy() &&
    c2.truthy() &&
    eq(t, mgrp(Fix(0L), muln_([first(c1), first(c2)]))) &&
    eq(
      t,
      mgqp(
        addn_([
          muln_([ftake(q_mabs, [first(c2)]), second(c1)]),
          muln_([ftake(q_mabs, [first(c1)]), second(c2)]),
        ]),
        Fix(0L),
      ),
    ),
  )
}

///|
/// Replace q^k in E by r1^k*r2^k for k not an integer.
fn intir1_unsplit(e : Value, q : Value, r1 : Value, r2 : Value) -> Value raise {
  if atom(e) {
    e
  } else if mexptp(e).truthy() &&
    alike1(cadr(e), q).truthy() &&
    !integerp(caddr(e)) {
    muln_([power(r1, caddr(e)), power(r2, caddr(e))])
  } else {
    recur_apply(
      lfunc("intir1-unsplit", args => intir1_unsplit(args[0], q, r1, r2)),
      e,
    )
  }
}

///|
/// Integrating the form (e*x^2+f*x+g)^m*r0(x)^e0.
fn intir3_ref(
  assoclist : Value,
  x : Value,
  e : Value,
  f : Value,
  g : Value,
  r0 : Value,
) -> Value raise {
  let signdisc = signdiscr(e, f, g)
  let d = cdras(q_d, assoclist)
  let p = cdras(q_p, assoclist)
  let e0 = cdras(q_e0, assoclist)
  if eq(signdisc, q_d_positive) {
    pns_intir3(x, e, f, g, d, p, r0, e0)
  } else if eq(signdisc, q_d_negative) {
    ns_intir3(x, e, f, g, d, p, r0, e0)
  } else {
    zs_intir3(x, e, f, d, p, r0, e0)
  }
}

///|
fn root_plusanything(exp_ : Value, var2 : Value) -> Value raise {
  m2(exp_, irinte__inst(irinte__root_pat, var2))
}

///|
/// Handle d*p(x)/(e*x^2+f*x+g)*r0(x)^e0 when the quadratic has two
/// distinct real roots, by splitting into partial fractions.
fn pns_intir3(
  x : Value,
  e : Value,
  f : Value,
  g : Value,
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
) -> Value raise {
  let discr = power(
    sub(muln_([f, f]), muln_([Fix(4L), e, g])),
    irinte__half(),
  )
  let p_r0_e0 = muln_([p, power(r0, e0)])
  let two_e_x_f = addn_([muln_([Fix(2L), e, x]), f])
  let two_e_d_invdisc = muln_([Fix(2L), e, d, inv(discr)])
  let i1 = intir2(muln_([inv(sub(two_e_x_f, discr)), p_r0_e0]), x)
  let i2 = if i1.truthy() {
    intir2(muln_([inv(addn_([two_e_x_f, discr])), p_r0_e0]), x)
  } else {
    Nil
  }
  if i2.truthy() {
    muln_([two_e_d_invdisc, sub(i1, i2)])
  } else {
    Nil
  }
}

///|
/// Handle d*p(x)/(e*x^2+f*x+g)*r0(x)^e0 when the quadratic has a
/// repeated root: it is e*(x+f/(2*e))^2.
fn zs_intir3(
  x : Value,
  e : Value,
  f : Value,
  d : Value,
  p : Value,
  r0 : Value,
  e0 : Value,
) -> Value raise {
  intir2(
    muln_([
      d,
      p,
      inv(e),
      power(addn_([x, div(f, addn_([e, e]))]), Fix(-2L)),
      power(r0, e0),
    ]),
    x,
  )
}

///|
/// The quadratic has no real roots: not handled (G&R 2.252).
fn ns_intir3(
  xx : Value,
  ee : Value,
  fff : Value,
  gg : Value,
  dd : Value,
  pp : Value,
  r0 : Value,
  e0 : Value,
) -> Value raise {
  ignore((xx, ee, fff, gg, dd, pp, r0, e0))
  Nil
}

///|
fn intir(funct : Value, x : Value) -> Value raise {
  inti(funct, x, jmaug(specrepcheck(funct), x))
}

///|
/// Integrate d*p(x)*(f*x+e)^m*(a*x^2+b*x+c)^n.  p(x) is a polynomial,
/// m is an integer, n is a number.  a, b, c, e, and f are expressions
/// independent of x.
fn inti(funct : Value, x : Value, assoclist : Value) -> Value raise {
  let n = cdras(q_n, assoclist)
  if assoclist is Nil || maxima_integerp(n).truthy() {
    return Nil
  }
  let f = cdras(q_f, assoclist)
  let e = cdras(q_e, assoclist)
  // If e is 0 (or not given), we don't have to do the transformation.
  if equal(e, Fix(0L)) || e is Nil {
    return intira(funct, x)
  }
  // Apply the linear substitution y = f*x+e.  That is x = (y-e)/f.
  let invf = inv(f)
  let met = make_symbol("yannis")
  let sum = addn_([met, muln_([Fix(-1L), e])])
  let mutable_expr = intira(
    distrexpandroot(cdr(d_substitute(muln_([invf, sum]), x, expr=funct))),
    met,
  )
  let expr = if mutable_expr.truthy() {
    muln_([inv(f), mutable_expr])
  } else {
    Nil
  }
  d_expand(d_substitute(addn_([muln_([f, x]), e]), met, expr~))
}

///|
fn distrexpandroot(expr : Value) -> Value raise {
  if expr is Nil {
    Fix(1L)
  } else {
    muln_([expandroot(car(expr)), distrexpandroot(cdr(expr))])
  }
}

///|
fn expandroot(expr : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if eq(caar(expr), q_mexpt) && integerpfr(caddr(expr)).truthy() {
    d_expand(expr)
  } else {
    expr
  }
}

///|
fn intirfactoroot(expr : Value, x : Value) -> Value raise {
  let factors = timestest(expr)
  fn try_inti() -> Value raise {
    let e = distrfactor(factors, x)
    let alist = jmaug(e, x)
    if alist.truthy() {
      inti(e, x, alist)
    } else {
      Nil
    }
  }

  let r = try_inti()
  if r.truthy() {
    r
  } else {
    with_special(q_ear_globalcareflag, t, () => try_inti())
  }
}

///|
/// Apply FACTOROOT to each element of FACTORS and multiply the results,
/// associating to the right.
fn distrfactor(factors : Value, x : Value) -> Value raise {
  if factors is Nil {
    Fix(1L)
  } else {
    muln_([factoroot(first(factors), x), distrfactor(rest(factors), x)])
  }
}

///|
/// If EXPR is of the form A^B and is not free of VAR2, use CAREFULFACTOR
/// to try to factor it. Otherwise just return EXPR.
fn factoroot(expr : Value, var2 : Value) -> Value raise {
  if mexptp(expr).truthy() &&
    hasvar2(expr, var2).truthy() &&
    integerpfr(caddr(expr)).truthy() {
    carefulfactor(expr, var2)
  } else {
    expr
  }
}

///|
/// Factor A^B. If *GLOBALCAREFLAG* is NIL, this is $FACTOR. Otherwise use
/// $FACTOR on (A/x)^B and restore the missing x^B with RESTOREX.
fn carefulfactor(expr : Value, x : Value) -> Value raise {
  if symval(q_ear_globalcareflag) is Nil {
    d_factor(expr)
  } else {
    restorex(
      d_factor(power(div(cadr(expr), x), caddr(expr))),
      x,
      caddr(expr),
    )
  }
}

///|
/// Multiply EXPR by VAR2^EXPT, trying to insert the factor of VAR2 inside
/// terms in a product if possible.
fn restorex(expr : Value, var2 : Value, expt_ : Value) -> Value raise {
  if mexptp(expr).truthy() && equal(expt_, caddr(expr)) {
    power(restorex(cadr(expr), var2, Fix(1L)), caddr(expr))
  } else if mtimesp(expr).truthy() {
    distrestorex(cdr(expr), var2, expt_)
  } else {
    muln_([power(var2, expt_), expr])
  }
}

///|
fn distrestorex(factors : Value, var2 : Value, expt_ : Value) -> Value raise {
  if factors is Nil {
    power(var2, expt_)
  } else {
    let start = first(factors)
    if mexptp(start).truthy() && equal(expt_, caddr(start)) {
      lmul(
        cons(
          power(d_expand(muln_([var2, cadr(start)])), caddr(start)),
          rest(factors),
        ),
      )
    } else {
      muln_([start, distrestorex(rest(factors), var2, expt_)])
    }
  }
}

///|
fn timestest(expr : Value) -> Value raise {
  if mtimesp(expr).truthy() {
    cdr(expr)
  } else {
    list1(expr)
  }
}

///|
/// Integrate a function of the form d*p(y)*y^m*(a*y^2+b*x+c)^n.
/// n is half of an integer.
fn intira(funct : Value, x : Value) -> Value raise {
  let assoclist = jmaug(specrepcheck(funct), x)
  let mut n = cdras(q_n, assoclist)
  if floatp(n) {
    n = rdis(ration1(n))
  }
  if assoclist is Nil || maxima_integerp(n).truthy() {
    return Nil
  }
  let d = cdras(q_d, assoclist)
  if equal(d, Fix(0L)) {
    return Fix(0L)
  }
  let c = cdras(q_a, assoclist)
  if equal(c, Fix(0L)) {
    return Nil
  }
  let m = cdras(q_m, assoclist)
  let polfact = cdras(q_p, assoclist)
  // n is of the form s/2; make n = s.
  n = cadr(n)
  let signn = checksigntm(n)
  let ec_1 = power(c, Fix(-1L))
  let b = cdras(q_b, assoclist)
  let a = cdras(q_c, assoclist)
  // pluspowfo1 = 1/2*(n-1), the original exponent - 1/2.
  let pluspowfo1 = muln_([irinte__half(), num_add(n, Fix(-1L))])
  // minuspowfo = 1/2*(n+1), the original exponent + 1/2.
  let minuspowfo = muln_([irinte__half(), num_add(n, Fix(1L))])
  // pluspowfo2 = -1/2*(n+1).
  let pluspowfo2 = num_mul(Fix(-1L), minuspowfo)
  let pcl = powercoeflist(polfact, m, x)
  let poszpowlist = car(pcl)
  let negpowlist = cadr(pcl)
  if negpowlist is Nil && poszpowlist is Cons(_) {
    // Only polynomial parts.
    if eq(signn, q_d_positive) {
      return augmult(
        muln_([
          d,
          nummnumn(poszpowlist, pluspowfo1, minuspowfo, c, b, a, x, ec_1),
        ]),
      )
    }
    return augmult(
      muln_([d, nummdenn(poszpowlist, pluspowfo2, c, b, a, x, ec_1)]),
    )
  }
  if poszpowlist is Nil && negpowlist is Cons(_) {
    // No polynomial parts.
    if eq(signn, q_d_positive) {
      return augmult(
        muln_([d, denmnumn(negpowlist, minuspowfo, c, b, a, x, ec_1)]),
      )
    }
    return augmult(
      muln_([d, denmdenn(negpowlist, pluspowfo2, c, b, a, x, ec_1)]),
    )
  }
  if negpowlist is Cons(_) && poszpowlist is Cons(_) {
    // Positive and negative powers.
    if eq(signn, q_d_positive) {
      return addn_([
        augmult(
          muln_([
            d,
            nummnumn(poszpowlist, pluspowfo1, minuspowfo, c, b, a, x, ec_1),
          ]),
        ),
        augmult(
          muln_([d, denmnumn(negpowlist, minuspowfo, c, b, a, x, ec_1)]),
        ),
      ])
    }
    return addn_([
      augmult(muln_([d, nummdenn(poszpowlist, pluspowfo2, c, b, a, x, ec_1)])),
      augmult(muln_([d, denmdenn(negpowlist, pluspowfo2, c, b, a, x, ec_1)])),
    ])
  }
  Nil
}

///|
/// Match d*p(x)*(f*x+e)^m*(a*x^2+b*x+c)^n.
fn jmaug(exp_ : Value, var2 : Value) -> Value raise {
  m2(exp_, irinte__inst(irinte__jmaug_pat, var2))
}

///|
/// Match d*p(x)*r1(x)^e1*r2(x)^e2*r0(x)^e0.
fn factpow(exp_ : Value, var2 : Value) -> Value raise {
  m2(exp_, irinte__inst(irinte__factpow_pat, var2))
}

///|
/// Match d*p/(e*x^2+f*x+g)*r0(x)^e0.
fn elliptquad(exp_ : Value, var2 : Value) -> Value raise {
  m2(exp_, irinte__inst(irinte__elliptquad_pat, var2))
}

///|
/// From the set of coefficients, generate the polynomial c*x^2+b*x+a.
fn polfoo(c : Value, b : Value, a : Value, x : Value) -> Value raise {
  addn_([muln_([c, x, x]), muln_([b, x]), a])
}

///|
/// The coefficients of fun(x)*x^m as a Laurent polynomial: a list of the
/// polynomial part and of the principal part, each a list of
/// (power coefficient) pairs.
fn powercoeflist(fun : Value, m : Value, var2 : Value) -> Value raise {
  let expanfun = unquote(
    d_expand(muln_([prevconstexpan(fun, var2), power(var2, m)])),
  )
  let mut poszpowlist : Value = Nil
  let mut negpowlist : Value = Nil
  if equal(fun, Fix(1L)) && plusp(m) {
    return cons(Nil, list1(list1(cons(m, list1(Fix(1L))))))
  }
  if equal(fun, Fix(1L)) && minusp(m) {
    return cons(Nil, list1(list1(cons(num_neg(m), list1(Fix(1L))))))
  }
  if equal(expanfun, Fix(1L)) {
    return cons(list1(cons(Fix(0L), list1(Fix(1L)))), list1(Nil))
  }
  let maxpowfun = funcall(q_d_hipow, [expanfun, var2])
  let mut powfun = funcall(q_d_lopow, [expanfun, var2])
  while true {
    let coef = d_coeff(expanfun, power(var2, powfun))
    let skip = numberp(coef) && !zerop(powfun) && zerop(coef)
    if !skip {
      if plusp(powfun) {
        poszpowlist = append(poszpowlist, list1(cons(powfun, list1(coef))))
      }
      if zerop(powfun) {
        poszpowlist = append(
          poszpowlist,
          list1(cons(Fix(0L), list1(d_coeff(expanfun, var2, n=Fix(0L))))),
        )
      }
      if minusp(powfun) {
        negpowlist = append(
          negpowlist,
          list1(cons(num_neg(powfun), list1(coef))),
        )
      }
      if num_eq(powfun, maxpowfun) {
        return list2(poszpowlist, reverse(negpowlist))
      }
    }
    powfun = one_plus(powfun)
  }
  Nil
}

///|
fn consterm(fun : Value, var2 : Value) -> Value raise {
  if fun is Nil {
    Fix(0L)
  } else if freeof(var2, car(fun)).truthy() {
    addn_([car(fun), consterm(cdr(fun), var2)])
  } else {
    consterm(cdr(fun), var2)
  }
}

///|
fn prevconstexpan(fun : Value, var2 : Value) -> Value raise {
  if atom(fun) {
    fun
  } else if eq(caar(fun), q_mplus) {
    if freeof(var2, fun).truthy() && !inside(fun, q_mexpt).truthy() {
      list2(list1(q_mquote), fun)
    } else if freeof(var2, fun).truthy() && inside(fun, q_mexpt).truthy() {
      list2(list1(q_mquote), distrinplusprev(cdr(fun), var2))
    } else if inside(fun, q_mexpt).truthy() {
      distrinplusprev(cdr(fun), var2)
    } else {
      fun
    }
  } else if eq(caar(fun), q_mtimes) {
    distrintimesprev(cdr(fun), var2)
  } else if !inside(cdr(fun), var2).truthy() && eq(caar(fun), q_mexpt) {
    power(prevconstexpan(cadr(fun), var2), caddr(fun))
  } else {
    fun
  }
}

///|
fn distrinplusprev(fun : Value, var2 : Value) -> Value raise {
  if fun is Nil {
    Fix(0L)
  } else {
    addn_([prevconstexpan(car(fun), var2), distrinplusprev(cdr(fun), var2)])
  }
}

///|
fn distrintimesprev(fun : Value, var2 : Value) -> Value raise {
  if fun is Nil {
    Fix(1L)
  } else {
    muln_([prevconstexpan(car(fun), var2), distrintimesprev(cdr(fun), var2)])
  }
}

///|
fn inside(fun : Value, arg : Value) -> Value raise {
  if atom(fun) {
    lbool(equal(fun, arg))
  } else if inside(car(fun), arg).truthy() {
    t
  } else {
    inside(cdr(fun), arg)
  }
}

///|
fn unquote(fun : Value) -> Value raise {
  if !inside(fun, q_mquote).truthy() {
    fun
  } else {
    unquote(meval(fun))
  }
}

// CHECKSIGNTM, CHECKFLAGANDACT and FINDSIGNOFACTORS share two closure
// variables in the Lisp source (a top-level LET).

///|
let irinte__zerosigntest : Ref[Value] = Ref(Nil)

///|
let irinte__productcase : Ref[Value] = Ref(Nil)

///|
/// The sign of EXPR, remembered in *CHECKCOEFSIGNLIST*.
fn checksigntm(expr : Value) -> Value raise {
  irinte__zerosigntest.val = Nil
  irinte__productcase.val = Nil
  let mut aslist = symval(q_ear_checkcoefsignlist)
  if !atom(expr) && eq(caar(expr), q_mtimes) {
    irinte__productcase.val = t
  }
  while true {
    if aslist is Nil {
      let old = symval(q_ear_checkcoefsignlist)
      let quest = checkflagandact(expr)
      set(
        q_ear_checkcoefsignlist,
        append(old, list1(cons(expr, list1(quest)))),
      )
      |> ignore
      return quest
    }
    if equal(caar(aslist), expr) {
      return cadar(aslist)
    }
    aslist = cdr(aslist)
  }
  Nil
}

///|
fn checkflagandact(expr : Value) -> Value raise {
  if irinte__productcase.val.truthy() {
    irinte__productcase.val = Nil
    findsignoftheirproduct(findsignofactors(cdr(expr)))
  } else {
    asksign(d_realpart(expr))
  }
}

///|
fn findsignofactors(listofactors : Value) -> Value raise {
  if listofactors is Nil {
    Nil
  } else if eq(irinte__zerosigntest.val, q_d_zero) {
    q_d_zero
  } else {
    let s = checksigntm(car(listofactors))
    irinte__zerosigntest.val = s
    append(list1(s), findsignofactors(cdr(listofactors)))
  }
}

///|
fn findsignoftheirproduct(llist : Value) -> Value raise {
  if eq(llist, q_d_zero) {
    return q_d_zero
  }
  let mut sign = q_d_positive
  let mut l = llist
  while true {
    if l is Nil {
      return sign
    }
    if eq(car(l), q_d_positive) {
      l = cdr(l)
      continue
    }
    if eq(car(l), q_d_negative) {
      sign = changesign(sign)
      l = cdr(l)
      continue
    }
    return q_d_zero
  }
  Nil
}

///|
fn changesign(sign : Value) -> Value raise {
  if eq(sign, q_d_positive) {
    q_d_negative
  } else {
    q_d_positive
  }
}

///|
/// Integrate 1/sqrt(c*x^2+b*x+a) (G&R 2.261).
fn den1(c : Value, b : Value, a : Value, x : Value) -> Value raise {
  let expr = addn_([muln_([Fix(2L), c, x]), b])
  let signc = checksigntm(power(c, Fix(-1L)))
  let signb = checksigntm(power(b, Fix(2L)))
  let signdiscrim = signdis2(c, b, a, signc, signb)
  if eq(signc, q_d_positive) && eq(signdiscrim, q_d_negative) {
    // c > 0, D > 0
    return augmult(
      mul_star(
        list([
          power(c, irinte__mhalf()),
          mk(q_p_asinh, [
            muln_([
              expr,
              power(
                addn_([muln_([Fix(4L), c, a]), muln_([Fix(-1L), b, b])]),
                irinte__mhalf(),
              ),
            ]),
          ]),
        ]),
      ),
    )
  }
  if eq(signc, q_d_positive) && eq(signdiscrim, q_d_zero) {
    // c > 0, D = 0
    return augmult(
      mul_star(
        list([
          div(ftake(q_mabs, [expr]), expr),
          power(c, irinte__mhalf()),
          mk(q_p_log, [expr]),
        ]),
      ),
    )
  }
  if eq(signc, q_d_positive) {
    // c > 0
    return augmult(
      mul_star(
        list([
          power(c, irinte__mhalf()),
          mk(q_p_log, [
            addn_([
              muln_([
                Fix(2L),
                power(c, irinte__half()),
                power(polfoo(c, b, a, x), irinte__half()),
              ]),
              expr,
            ]),
          ]),
        ]),
      ),
    )
  }
  if eq(signc, q_d_negative) && eq(signdiscrim, q_d_positive) {
    // c < 0, D > 0
    return augmult(
      mul_star(
        list([
          Fix(-1L),
          power(muln_([Fix(-1L), c]), irinte__mhalf()),
          mk(q_p_asin, [
            muln_([
              expr,
              power(
                addn_([muln_([b, b]), muln_([Fix(-4L), c, a])]),
                irinte__mhalf(),
              ),
            ]),
          ]),
        ]),
      ),
    )
  }
  if eq(signc, q_d_negative) {
    // c < 0.  Flip the sign of the polynomial, and multiply by -%i.
    return augmult(
      muln_([
        power(Fix(-1L), irinte__mhalf()),
        den1(
          muln_([Fix(-1L), c]),
          muln_([Fix(-1L), b]),
          muln_([Fix(-1L), a]),
          x,
        ),
      ]),
    )
  }
  Nil
}

///|
/// Sign of the discriminant b^2-4*c*a of c*x^2+b*x+a.
fn signdiscr(c : Value, b : Value, a : Value) -> Value raise {
  checksigntm(
    simplifya(
      addn_([power(b, Fix(2L)), muln_([Fix(-4L), c, a])]),
      Nil,
    ),
  )
}

///|
fn askinver(a : Value) -> Value raise {
  checksigntm(inv(a))
}

///|
fn signdis1(c : Value, b : Value, a : Value) -> Value raise {
  if equal(muln_([b, a]), Fix(0L)) {
    if equal(b, Fix(0L)) && equal(a, Fix(0L)) {
      q_d_zero
    } else {
      q_d_nonzero
    }
  } else {
    checksigntm(
      power(addn_([muln_([b, b]), muln_([Fix(-4L), c, a])]), Fix(2L)),
    )
  }
}

///|
/// Sign of the discriminant of c*x^2+b*x+a, also taking into account the
/// signs of c and b.
fn signdis2(
  c : Value,
  b : Value,
  a : Value,
  signc : Value,
  signb : Value,
) -> Value raise {
  if equal(signb, q_d_zero) {
    if equal(a, Fix(0L)) {
      q_d_zero
    } else {
      let askinv = askinver(a)
      if (eq(signc, q_d_positive) && eq(askinv, q_d_negative)) ||
        (eq(signc, q_d_negative) && eq(askinv, q_d_positive)) {
        q_d_positive
      } else {
        q_d_negative
      }
    }
  } else if equal(a, Fix(0L)) {
    q_d_positive
  } else {
    signdiscr(c, b, a)
  }
}

///|
fn signdis3(
  c : Value,
  b : Value,
  a : Value,
  signa : Value,
  ec_1 : Value,
) -> Value raise {
  if equal(b, Fix(0L)) {
    if equal(checksigntm(ec_1), signa) {
      q_d_negative
    } else {
      q_d_positive
    }
  } else {
    signdiscr(c, b, a)
  }
}

///|
/// Integrate things like x^m*R^(p-1/2), p > 0, m > 0 (G&R 2.260).
fn nummnumn(
  poszpowlist : Value,
  pluspowfo1 : Value,
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let expr = power(polfoo(c, b, a, x), addn_([p, irinte__half()]))
  let expo = ec_1
  let ex = power(c, Fix(-2L))
  let mut lst = poszpowlist
  let mut result : Value = Fix(0L)
  let mut controlpow = caar(lst)
  let mut coef = cadar(lst)
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  // states: 0 start, 1 jump1, 2 jump2, 3 jump3, 4 jump, 5 jump4, 6 loop
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          // Integrate R^(p-1/2)
          result = augmult(
            muln_([coef, numn(pluspowfo1, c, b, a, x, ec_1)]),
          )
          count = Fix(1L)
          st = 6
          continue
        }
        st = 1
      }
      1 => {
        // x*R^(p-1/2), G&R 2.260, m = 1
        res1 = addn_([
          augmult(
            muln_([
              expr,
              expo,
              power(num_sum([p, p, Fix(1L)]), Fix(-1L)),
            ]),
          ),
          augmult(
            muln_([
              Fix(-1L),
              b,
              irinte__half(),
              expo,
              numn(pluspowfo1, c, b, a, x, ec_1),
            ]),
          ),
        ])
        if equal(controlpow, Fix(1L)) {
          result = addn_([result, augmult(muln_([coef, res1]))])
          count = Fix(2L)
          st = 6
          continue
        }
        st = 2
      }
      2 => {
        // x^2*R^(p-1/2), G&R 2.260, m = 2
        res2 = addn_([
          augmult(
            mul_star(list([x, expr, expo, inv(num_sum([p, p, Fix(2L)]))])),
          ),
          augmult(
            mul_star(
              list([
                b,
                num_sum([p, p, Fix(3L)]),
                mk(q_rat, [Fix(-1L), Fix(4L)]),
                ex,
                inv(num_sum([p, p, p, Fix(1L), num_mul(p, p), num_mul(p, p)])),
                expr,
              ]),
            ),
          ),
          augmult(
            muln_([
              inv(one_plus(p)),
              ex,
              mk_simp(q_rat, [Fix(1L), Fix(8L)]),
              addn_([
                muln_([power(b, Fix(2L)), num_sum([p, p, Fix(3L)])]),
                muln_([Fix(-4L), a, c]),
              ]),
              numn(pluspowfo1, c, b, a, x, ec_1),
            ]),
          ),
        ])
        if equal(controlpow, Fix(2L)) {
          result = addn_([result, augmult(muln_([coef, res2]))])
          count = Fix(3L)
          st = 6
          continue
        }
        st = 3
      }
      3 => {
        count = Fix(4L)
        m = Fix(3L)
        st = 4
      }
      4 => {
        // The general case:  x^m*R^(p-1/2)
        let pro = inv(num_sum([m, p, p]))
        partres = addn_([
          augmult(muln_([power(x, one_minus(m)), expr, expo, pro])),
          augmult(
            muln_([
              Fix(-1L),
              b,
              num_sum([p, p, m, m, Fix(-1L)]),
              irinte__half(),
              expo,
              pro,
              res2,
            ]),
          ),
          augmult(muln_([Fix(-1L), a, one_minus(m), expo, pro, res1])),
        ])
        m = one_plus(m)
        if num_gt(m, controlpow) {
          result = addn_([result, augmult(muln_([coef, partres]))])
          st = 6
          continue
        }
        st = 5
      }
      5 => {
        res1 = res2
        res2 = partres
        st = 4
      }
      _ => {
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        st = if equal(count, Fix(4L)) {
          5
        } else if equal(count, Fix(1L)) {
          1
        } else if equal(count, Fix(2L)) {
          2
        } else {
          3
        }
      }
    }
  }
  Nil
}

///|
/// Integrate R^(p+1/2)
fn numn(
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = ec_1
  let exp2 = addn_([b, muln_([Fix(2L), c, x])])
  let exp4 = addn_([muln_([Fix(4L), a, c]), muln_([Fix(-1L), b, b])])
  let exp5 = div(Fix(1L), one_plus(p))
  if zerop(p) {
    // G&R 2.262
    addn_([
      augmult(
        muln_([
          mk_simp(q_rat, [Fix(1L), Fix(4L)]),
          exp1,
          exp2,
          power(polfoo(c, b, a, x), irinte__half()),
        ]),
      ),
      augmult(
        muln_([
          mk_simp(q_rat, [Fix(1L), Fix(8L)]),
          exp1,
          exp4,
          den1(c, b, a, x),
        ]),
      ),
    ])
  } else {
    // G&R 2.260, eq. 2
    addn_([
      augmult(
        muln_([
          mk_simp(q_rat, [Fix(1L), Fix(4L)]),
          exp1,
          exp5,
          exp2,
          power(polfoo(c, b, a, x), addn_([p, irinte__half()])),
        ]),
      ),
      augmult(
        muln_([
          mk_simp(q_rat, [Fix(1L), Fix(8L)]),
          exp1,
          exp5,
          num_sum([p, p, Fix(1L)]),
          exp4,
          numn(one_minus(p), c, b, a, x, ec_1),
        ]),
      ),
    ])
  }
}

///|
fn augmult(x : Value) -> Value raise {
  d_multthru(simplifya(x, Nil))
}

///|
/// Integrate things like 1/x^m/R^(p+1/2), p > 0 (G&R 2.268).
fn denmdenn(
  negpowlist : Value,
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = power(polfoo(c, b, a, x), addn_([irinte__half(), num_neg(p)]))
  let mut lst = negpowlist
  let mut result : Value = Nil
  let mut controlpow : Value = Nil
  let mut coef : Value = Nil
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  let signa = checksigntm(simplifya(a, Nil))
  if eq(signa, q_d_zero) {
    return noconstquad(lst, p, c, b, x)
  }
  result = Fix(0L)
  controlpow = caar(lst)
  let ea_1 = power(a, Fix(-1L))
  coef = cadar(lst)
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          result = augmult(muln_([coef, denn(p, c, b, a, x)]))
          count = Fix(1L)
          st = 6
          continue
        }
        st = 1
      }
      1 => {
        // 1/x/R^(p+1/2)
        res1 = den1denn(p, c, b, a, x, ec_1)
        if equal(controlpow, Fix(1L)) {
          result = addn_([result, augmult(muln_([coef, res1]))])
          count = Fix(2L)
          st = 6
          continue
        }
        st = 2
      }
      2 => {
        // 1/x^2/R^(p+1/2), G&R 2.268, m = 2
        res2 = addn_([
          augmult(muln_([Fix(-1L), ea_1, power(x, Fix(-1L)), exp1])),
          augmult(
            muln_([
              Fix(-1L),
              b,
              num_sum([Fix(1L), p, p]),
              irinte__half(),
              ea_1,
              den1denn(p, c, b, a, x, ec_1),
            ]),
          ),
          augmult(muln_([Fix(-2L), p, c, ea_1, denn(p, c, b, a, x)])),
        ])
        if equal(controlpow, Fix(2L)) {
          result = addn_([result, augmult(muln_([coef, res2]))])
          count = Fix(3L)
          st = 6
          continue
        }
        st = 3
      }
      3 => {
        count = Fix(4L)
        m = Fix(3L)
        st = 4
      }
      4 => {
        // General case 1/x^m/R^(p+1/2), G&R 2.268
        let exp2 = div(Fix(-1L), one_minus(m))
        partres = addn_([
          augmult(
            muln_([exp2, ea_1, power(x, one_plus(num_neg(m))), exp1]),
          ),
          augmult(
            muln_([
              b,
              num_sum([p, p, m, m, Fix(-3L)]),
              irinte__half(),
              ea_1,
              exp2,
              res2,
            ]),
          ),
          augmult(
            muln_([c, ea_1, exp2, num_sum([p, p, m, Fix(-2L)]), res1]),
          ),
        ])
        m = one_plus(m)
        if num_gt(m, controlpow) {
          result = addn_([result, augmult(muln_([coef, partres]))])
          st = 6
          continue
        }
        st = 5
      }
      5 => {
        res1 = res2
        res2 = partres
        st = 4
      }
      _ => {
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        st = if equal(count, Fix(4L)) {
          5
        } else if equal(count, Fix(1L)) {
          1
        } else if equal(count, Fix(2L)) {
          2
        } else {
          3
        }
      }
    }
  }
  Nil
}

///|
/// Integral of 1/(c*x^2+b*x+a)^(n), n > 0.  p = n + 1/2 (G&R 2.263).
fn denn(p : Value, c : Value, b : Value, a : Value, x : Value) -> Value raise {
  let signdisc = signdis1(c, b, a)
  let exp1 = addn_([b, muln_([Fix(2L), c, x])])
  let exp2 = addn_([muln_([Fix(4L), a, c]), muln_([b, b, Fix(-1L)])])
  let exp3 = inv(num_sum([p, p, Fix(-1L)]))
  let ec_1 = inv(c)
  if eq(signdisc, q_d_zero) && zerop(p) {
    // 1/sqrt(R), repeated roots: sqrt(c*(x+b/2/c)^2).
    let exp4 = addn_([x, muln_([b, irinte__half(), ec_1])])
    let r_factored = muln_([c, power(exp4, Fix(2L))])
    augmult(
      muln_([
        exp4,
        power(r_factored, irinte__mhalf()),
        mk(q_p_log, [power(power(exp4, Fix(2L)), irinte__half())]),
      ]),
    )
  } else if eq(signdisc, q_d_zero) && plusp(p) {
    // 1/sqrt(R^(2*p+1)), repeated roots
    let exp4 = addn_([x, muln_([b, irinte__half(), ec_1])])
    let r_factored = muln_([c, power(exp4, Fix(2L))])
    augmult(
      muln_([
        exp4,
        div(Fix(-1L), num_add(p, p)),
        power(r_factored, addn_([irinte__mhalf(), num_neg(p)])),
      ]),
    )
  } else if zerop(p) {
    // 1/sqrt(R)
    den1(c, b, a, x)
  } else if equal(p, Fix(1L)) {
    // 1/sqrt(R^3), G&R 2.264 eq. 5
    augmult(
      muln_([
        Fix(2L),
        exp1,
        inv(exp2),
        power(polfoo(c, b, a, x), irinte__mhalf()),
      ]),
    )
  } else {
    // The general case.  G&R 2.263 eq. 3.
    addn_([
      augmult(
        muln_([
          Fix(2L),
          exp1,
          exp3,
          inv(exp2),
          power(polfoo(c, b, a, x), addn_([irinte__half(), num_neg(p)])),
        ]),
      ),
      augmult(
        muln_([
          Fix(8L),
          c,
          one_minus(p),
          exp3,
          inv(exp2),
          denn(one_minus(p), c, b, a, x),
        ]),
      ),
    ])
  }
}

///|
/// Integral of 1/x/(c*x^2+b*x+a)^(p+1/2), p > 0.
fn den1denn(
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let signa = checksigntm(power(a, Fix(2L)))
  let ea_1 = inv(a)
  if eq(signa, q_d_zero) {
    noconstquad(Fix(1L), p, c, b, x)
  } else if zerop(p) {
    den1den1(c, b, a, x, ec_1)
  } else {
    // G&R 2.268
    addn_([
      augmult(
        muln_([
          inv(num_sum([p, p, Fix(-1L)])),
          ea_1,
          power(polfoo(c, b, a, x), addn_([irinte__half(), num_neg(p)])),
        ]),
      ),
      augmult(muln_([ea_1, den1denn(one_minus(p), c, b, a, x, ec_1)])),
      augmult(
        muln_([Fix(-1L), irinte__half(), ea_1, b, denn(p, c, b, a, x)]),
      ),
    ])
  }
}

///|
/// Integral of 1/x/sqrt(c*x^2+b*x+a) (G&R 2.266).
fn den1den1(
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp2 = addn_([muln_([b, x]), a, a])
  let mut exp3 = inv(simplify(list2(list1(q_mabs), x)))
  let signa = checksigntm(simplifya(a, Nil))
  if eq(signa, q_d_zero) {
    return noconstquad(list1(list2(Fix(1L), Fix(1L))), Fix(0L), c, b, x)
  }
  let signdiscrim = signdis3(c, b, a, signa, ec_1)
  let exp1 = power(a, inv(Fix(-2L)))
  if eq(signa, q_d_positive) && eq(signdiscrim, q_d_negative) {
    // a > 0, del > 0
    return mul_star(
      list([
        Fix(-1L),
        exp1,
        mk(q_p_asinh, [
          augmult(
            muln_([
              exp2,
              exp3,
              power(
                addn_([muln_([Fix(4L), a, c]), muln_([Fix(-1L), b, b])]),
                irinte__mhalf(),
              ),
            ]),
          ),
        ]),
      ]),
    )
  }
  if eq(signdiscrim, q_d_zero) && eq(signa, q_d_positive) {
    // del = 0, a > 0
    return mul_star(
      list([
        div(ftake(q_mabs, [exp2]), exp2),
        Fix(-1L),
        exp1,
        mk(q_p_log, [augmult(muln_([exp3, exp2]))]),
      ]),
    )
  }
  if eq(signa, q_d_positive) {
    // a > 0.  For real x, dividing by abs(x) instead of x keeps the
    // result real. For complex x, that would make it wrong.
    if decl_complexp(x).truthy() {
      exp3 = inv(x)
    }
    return mul_star(
      list([
        Fix(-1L),
        exp1,
        mk(q_p_log, [
          addn_([
            muln_([b, x, exp3]),
            muln_([Fix(2L), a, exp3]),
            muln_([
              Fix(2L),
              exp3,
              power(a, irinte__half()),
              power(polfoo(c, b, a, x), irinte__half()),
            ]),
          ]),
        ]),
      ]),
    )
  }
  if eq(signa, q_d_negative) && eq(signdiscrim, q_d_positive) {
    // a < 0, del < 0
    return mul_star(
      list([
        power(muln_([Fix(-1L), a]), irinte__mhalf()),
        mk(q_p_asin, [
          augmult(
            muln_([
              exp2,
              exp3,
              power(
                addn_([muln_([b, b]), muln_([Fix(-4L), a, c])]),
                irinte__mhalf(),
              ),
            ]),
          ),
        ]),
      ]),
    )
  }
  // a < 0: flip the signs of the coefficients and multiply by 1/%i.
  muln_([
    Fix(-1L),
    power(Fix(-1L), irinte__half()),
    den1den1(
      muln_([Fix(-1L), c]),
      muln_([Fix(-1L), b]),
      muln_([Fix(-1L), a]),
      x,
      ec_1,
    ),
  ])
}

///|
/// Integral of d/x^m/(c*x^2+b*x)^(p+1/2), p > 0.  The values of m and d
/// are in NEGPOWLIST.
fn noconstquad(
  negpowlist : Value,
  p : Value,
  c : Value,
  b : Value,
  x : Value,
) -> Value raise {
  let exp1 = inv(num_sum([p, p, Fix(1L)]))
  let exp2 = inv(x)
  let exp3 = num_neg(p)
  let mut lst = negpowlist
  let mut result : Value = Nil
  let mut controlpow : Value = Nil
  let mut coef : Value = Nil
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  let signb = checksigntm(power(b, Fix(2L)))
  if eq(signb, q_d_zero) {
    return trivial1(lst, p, c, x)
  }
  result = Fix(0L)
  controlpow = caar(lst)
  coef = cadar(lst)
  let eb_1 = inv(b)
  // states: 0 start, 1 jump1, 2 jump2, 3 jump, 4 jump3, 5 loop
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          result = augmult(muln_([coef, denn(p, c, b, Fix(0L), x)]))
          count = Fix(1L)
          st = 5
          continue
        }
        st = 1
      }
      1 => {
        // 1/x/R^(p+1/2), G&R 2.268, a = 0, m = 1
        res1 = addn_([
          augmult(
            muln_([
              Fix(-2L),
              exp1,
              eb_1,
              exp2,
              power(
                polfoo(c, b, Fix(0L), x),
                addn_([irinte__half(), exp3]),
              ),
            ]),
          ),
          augmult(
            muln_([
              Fix(-4L),
              p,
              c,
              exp1,
              eb_1,
              denn(p, c, b, Fix(0L), x),
            ]),
          ),
        ])
        if equal(controlpow, Fix(1L)) {
          result = addn_([result, augmult(muln_([coef, res1]))])
          count = Fix(2L)
          st = 5
          continue
        }
        st = 2
      }
      2 => {
        count = Fix(3L)
        m = Fix(2L)
        st = 3
      }
      3 => {
        // General case 1/x^m/R^(p+1/2), G&R 2.268, a = 0
        partres = addn_([
          augmult(
            muln_([
              Fix(-2L),
              inv(num_sum([p, p, m, m, Fix(-1L)])),
              eb_1,
              power(x, muln_([Fix(-1L), m])),
              power(
                polfoo(c, b, Fix(0L), x),
                addn_([irinte__half(), exp3]),
              ),
            ]),
          ),
          augmult(
            muln_([
              Fix(-2L),
              c,
              num_sum([p, p, m, Fix(-1L)]),
              eb_1,
              inv(num_sum([p, p, m, m, Fix(-1L)])),
              res1,
            ]),
          ),
        ])
        m = one_plus(m)
        if num_gt(m, controlpow) {
          result = addn_([result, augmult(muln_([coef, partres]))])
          st = 5
          continue
        }
        st = 4
      }
      4 => {
        res1 = partres
        st = 3
      }
      _ => {
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        st = if num_eq(count, Fix(3L)) {
          4
        } else if num_eq(count, Fix(1L)) {
          1
        } else {
          2
        }
      }
    }
  }
  Nil
}

///|
/// The trivial case of d/x^m/(c*x^2+b*x+a)^(p+1/2), p > 0, and a=b=0.
fn trivial1(negpowlist : Value, p : Value, c : Value, x : Value) -> Value raise {
  if negpowlist is Nil {
    Fix(0L)
  } else {
    // The integral is -d/c^(p+1/2)/x^(m+2*p)/(m+2*p)
    addn_([
      augmult(
        muln_([
          power(
            x,
            addn_([
              num_mul(Fix(-2L), p),
              muln_([Fix(-1L), caar(negpowlist)]),
            ]),
          ),
          cadar(negpowlist),
          power(c, addn_([num_neg(p), irinte__mhalf()])),
          inv(
            addn_([
              num_mul(Fix(-2L), p),
              muln_([Fix(-1L), caar(negpowlist)]),
            ]),
          ),
        ]),
      ),
      trivial1(cdr(negpowlist), p, c, x),
    ])
  }
}

///|
/// Integrate pl(x)/(c*x^2+b*x+a)^(p+1/2) where pl(x) is a polynomial and
/// p > 0.  The polynomial is given in POSZPOWLIST (G&R 2.263, eq.1).
fn nummdenn(
  poszpowlist : Value,
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = inv(num_sum([p, p, Fix(-1L)]))
  let exp2 = power(polfoo(c, b, a, x), addn_([irinte__half(), num_neg(p)]))
  let exp3 = addn_([muln_([Fix(4L), a, c]), muln_([Fix(-1L), b, b])])
  let exp4 = addn_([x, muln_([b, irinte__half(), ec_1])])
  let exp5 = power(c, Fix(-2L))
  let exp6 = num_add(Fix(2L), num_mul(Fix(-2L), p))
  let exp7 = one_plus(num_mul(Fix(-2L), p))
  let mut lst = poszpowlist
  let mut result : Value = Fix(0L)
  let mut controlpow = caar(lst)
  let mut coef = cadar(lst)
  let signdiscrim = signdis1(c, b, a)
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  // states: 0 start, 1 jump1, 2 jump2, 3 jump3, 4 jump, 5 on, 6 jump4,
  // 7 loop
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          result = augmult(muln_([coef, denn(p, c, b, a, x)]))
          count = Fix(1L)
          st = 7
          continue
        }
        st = 1
      }
      1 => {
        // coef*x/R^(p+1/2)
        res1 = addn_([
          augmult(muln_([Fix(-1L), ec_1, exp1, exp2])),
          augmult(
            muln_([b, irinte__mhalf(), ec_1, denn(p, c, b, a, x)]),
          ),
        ])
        if num_eq(controlpow, Fix(1L)) {
          result = addn_([result, augmult(muln_([coef, res1]))])
          count = Fix(2L)
          st = 7
          continue
        }
        st = 2
      }
      2 => {
        // coef*x^2/R^(p+1/2)
        if plusp(p) && !eq(signdiscrim, q_d_zero) {
          // p > 0, no repeated roots
          res2 = addn_([
            augmult(
              muln_([
                ec_1,
                exp1,
                inv(exp3),
                exp2,
                addn_([
                  muln_([Fix(2L), a, b]),
                  muln_([Fix(2L), b, b, x]),
                  muln_([Fix(-4L), a, c, x]),
                ]),
              ]),
            ),
            augmult(
              muln_([
                ec_1,
                inv(exp3),
                exp1,
                addn_([
                  muln_([Fix(4L), a, c]),
                  muln_([Fix(2L), b, b, p]),
                  muln_([Fix(-3L), b, b]),
                ]),
                denn(num_add(p, Fix(-1L)), c, b, a, x),
              ]),
            ),
          ])
        }
        if zerop(p) && !eq(signdiscrim, q_d_zero) {
          // x^2/sqrt(R), no repeated roots.  G&R 2.264, eq. 3
          res2 = addn_([
            augmult(
              muln_([
                mk_simp(q_rat, [Fix(1L), Fix(4L)]),
                exp5,
                addn_([muln_([Fix(2L), c, x]), muln_([Fix(-3L), b])]),
                power(polfoo(c, b, a, x), irinte__half()),
              ]),
            ),
            augmult(
              muln_([
                mk_simp(q_rat, [Fix(1L), Fix(8L)]),
                exp5,
                addn_([muln_([Fix(3L), b, b]), muln_([Fix(-4L), a, c])]),
                den1(c, b, a, x),
              ]),
            ),
          ])
        }
        if zerop(p) && eq(signdiscrim, q_d_zero) {
          // x^2/sqrt(R), repeated roots
          let r_factored = muln_([c, power(exp4, Fix(2L))])
          let s = power(r_factored, irinte__half())
          res2 = muln_([
            exp4,
            inv(s),
            addn_([
              augmult(
                mul_star(
                  list([
                    b,
                    b,
                    mk(q_rat, [Fix(1L), Fix(4L)]),
                    power(c, Fix(-2L)),
                    mk(q_p_log, [
                      power(power(exp4, Fix(2L)), irinte__half()),
                    ]),
                  ]),
                ),
              ),
              augmult(muln_([irinte__half(), power(x, Fix(2L))])),
              augmult(muln_([irinte__mhalf(), b, x, ec_1])),
            ]),
          ])
        }
        if num_eq(p, Fix(1L)) && eq(signdiscrim, q_d_zero) {
          // x^2/sqrt(R^3), repeated roots
          let r_factored = muln_([c, power(exp4, Fix(2L))])
          let s = power(r_factored, irinte__half())
          res2 = muln_([
            exp4,
            ec_1,
            inv(s),
            addn_([
              augmult(
                mk(q_p_log, [power(power(exp4, Fix(2L)), irinte__half())]),
              ),
              augmult(muln_([b, x, ec_1, power(exp4, Fix(-2L))])),
              augmult(
                muln_([
                  div(Fix(3L), Fix(8L)),
                  power(c, Fix(-2L)),
                  b,
                  b,
                  power(exp4, Fix(-2L)),
                ]),
              ),
            ]),
          ])
        }
        if eq(signdiscrim, q_d_zero) && num_gt(p, Fix(1L)) {
          // x^2/R^(p+1/2), repeated roots, p > 1
          let r_factored = muln_([c, power(exp4, Fix(2L))])
          let s = power(r_factored, irinte__half())
          res2 = muln_([
            exp4,
            power(c, num_neg(p)),
            inv(s),
            addn_([
              augmult(muln_([power(exp4, exp6), inv(exp6)])),
              augmult(
                muln_([Fix(-1L), b, ec_1, inv(exp7), power(exp4, exp7)]),
              ),
              augmult(
                muln_([
                  b,
                  b,
                  mk_simp(q_rat, [Fix(-1L), Fix(8L)]),
                  power(c, Fix(-2L)),
                  inv(p),
                  power(exp4, num_mul(Fix(-2L), p)),
                ]),
              ),
            ]),
          ])
        }
        if num_eq(controlpow, Fix(2L)) {
          result = addn_([result, augmult(muln_([coef, res2]))])
          count = Fix(3L)
          st = 7
          continue
        }
        st = 3
      }
      3 => {
        count = Fix(4L)
        m = Fix(3L)
        st = 4
      }
      4 => {
        // coef*x^m/R^(p+1/2).  m >= 3.  G&R 2.263, eq 1
        let denom = num_sum([p, p, num_neg(m)])
        partres = addn_([
          augmult(
            mul_star(
              list([
                power(x, one_minus(m)),
                ec_1,
                div(Fix(-1L), denom),
                power(
                  polfoo(c, b, a, x),
                  addn_([irinte__half(), num_neg(p)]),
                ),
              ]),
            ),
          ),
          augmult(
            muln_([
              b,
              num_sum([p, p, Fix(1L), num_mul(Fix(-2L), m)]),
              irinte__mhalf(),
              ec_1,
              inv(denom),
              res2,
            ]),
          ),
          augmult(muln_([a, one_minus(m), ec_1, inv(denom), res1])),
        ])
        st = 5
      }
      5 => {
        // Move on to next higher power
        m = one_plus(m)
        if num_gt(m, controlpow) {
          result = addn_([result, augmult(muln_([coef, partres]))])
          st = 7
          continue
        }
        st = 6
      }
      6 => {
        res1 = res2
        res2 = partres
        if num_eq(m, num_add(p, p)) {
          let expr = nummdenn(
            list1(list2(one_minus(m), Fix(1L))),
            p,
            c,
            b,
            a,
            x,
            ec_1,
          )
          partres = addn_([
            muln_([x, expr]),
            muln_([Fix(-1L), distrint(cdr(d_expand(expr)), x)]),
          ])
          st = 5
          continue
        }
        st = 4
      }
      _ => {
        // Done with first term of polynomial.  Exit if we're done.
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        st = if num_eq(count, Fix(4L)) {
          6
        } else if num_eq(count, Fix(1L)) {
          1
        } else if num_eq(count, Fix(2L)) {
          2
        } else {
          3
        }
      }
    }
  }
  Nil
}

///|
/// Integrate functions of the form coef*R^(pow-1/2)/x^m.  NEGPOWLIST
/// contains the list of coef's and m's.
fn denmnumn(
  negpowlist : Value,
  pow : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = inv(x)
  let exp2 = num_sum([pow, pow, Fix(-1L)])
  let mut lst = negpowlist
  let mut result : Value = Nil
  let mut controlpow : Value = Nil
  let mut coef : Value = Nil
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  let mut ea_1 : Value = Nil
  // p = 2*pow-1.  NOTE: p is not the same here as in other routines!
  let p = num_sum([pow, pow, Fix(-1L)])
  // CASE1 calls this with a leading T in NEGPOWLIST.
  if eq(car(lst), t) {
    lst = cdr(lst)
  } else {
    let signa = checksigntm(power(a, Fix(2L)))
    if eq(signa, q_d_zero) {
      return nonconstquadenum(lst, p, c, b, x, ec_1)
    }
    ea_1 = inv(a)
  }
  // there
  result = Fix(0L)
  controlpow = caar(lst)
  coef = cadar(lst)
  // states: 0 start, 1 jump1, 2 jump2, 3 jump3, 4 jump, 5 jump4, 6 loop
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          // integrate(sqrt(R)).
          result = augmult(
            muln_([
              coef,
              numn(
                addn_([muln_([p, irinte__half()]), irinte__half()]),
                c,
                b,
                a,
                x,
                ec_1,
              ),
            ]),
          )
          count = Fix(1L)
          st = 6
          continue
        }
        st = 1
      }
      1 => {
        // integrate(sqrt(R^(2*pow-1))/x),x
        res1 = den1numn(pow, c, b, a, x, ec_1)
        if equal(controlpow, Fix(1L)) {
          result = addn_([result, augmult(muln_([coef, res1]))])
          count = Fix(2L)
          st = 6
          continue
        }
        st = 2
      }
      2 => {
        // integrate(sqrt(R^(2*pow-1))/x^2,x)
        if !num_eq(p, Fix(1L)) {
          res2 = addn_([
            augmult(
              muln_([
                Fix(-1L),
                exp1,
                power(polfoo(c, b, a, x), addn_([pow, irinte__mhalf()])),
              ]),
            ),
            augmult(
              muln_([
                b,
                div(exp2, Fix(2L)),
                den1numn(one_minus(pow), c, b, a, x, ec_1),
              ]),
            ),
            augmult(
              muln_([
                c,
                exp2,
                numn(num_sub(pow, Fix(2L)), c, b, a, x, ec_1),
              ]),
            ),
          ])
        }
        if num_eq(p, Fix(1L)) {
          // integrate(sqrt(R)/x^2,x), G&R 2.267, eq. 2
          res2 = addn_([
            augmult(
              muln_([
                Fix(-1L),
                power(polfoo(c, b, a, x), irinte__half()),
                exp1,
              ]),
            ),
            augmult(muln_([b, irinte__half(), den1den1(c, b, a, x, ec_1)])),
            augmult(muln_([c, den1(c, b, a, x)])),
          ])
        }
        if equal(controlpow, Fix(2L)) {
          result = addn_([result, augmult(muln_([coef, res2]))])
          count = Fix(3L)
          st = 6
          continue
        }
        st = 3
      }
      3 => {
        count = Fix(4L)
        m = Fix(3L)
        st = 4
      }
      4 => {
        // The general case sqrt(R^(2*p-1))/x^m, G&R 2.265
        partres = addn_([
          augmult(
            muln_([
              div(Fix(-1L), one_minus(m)),
              ea_1,
              power(x, one_plus(num_neg(m))),
              power(
                polfoo(c, b, a, x),
                addn_([div(p, Fix(2L)), Fix(1L)]),
              ),
            ]),
          ),
          augmult(
            muln_([
              inv(num_sum([m, m, Fix(-2L)])),
              ea_1,
              b,
              num_sum([p, Fix(4L), num_mul(Fix(-2L), m)]),
              res2,
            ]),
          ),
          augmult(
            muln_([
              c,
              ea_1,
              num_sum([p, Fix(3L), num_neg(m)]),
              inv(one_minus(m)),
              res1,
            ]),
          ),
        ])
        m = one_plus(m)
        if num_gt(m, controlpow) {
          result = addn_([result, augmult(muln_([coef, partres]))])
          st = 6
          continue
        }
        st = 5
      }
      5 => {
        res1 = res2
        res2 = partres
        st = 4
      }
      _ => {
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        st = if num_eq(count, Fix(4L)) {
          5
        } else if num_eq(count, Fix(1L)) {
          1
        } else if num_eq(count, Fix(2L)) {
          2
        } else {
          3
        }
      }
    }
  }
  Nil
}

///|
/// Like denmnumn, but a = 0.
fn nonconstquadenum(
  negpowlist : Value,
  p : Value,
  c : Value,
  b : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  if equal(p, Fix(1L)) {
    return case1(negpowlist, c, b, x, ec_1)
  }
  let mut result : Value = Fix(0L)
  let mut lst = negpowlist
  while true {
    let m = caar(lst)
    let coef = cadar(lst)
    result = addn_([result, augmult(muln_([coef, casegen(m, p, c, b, x, ec_1)]))])
    lst = cdr(lst)
    if lst is Nil {
      return result
    }
  }
  Nil
}

///|
/// Integrate (c*x^2+b*x)^(p-1/2)/x^m
fn casegen(
  m : Value,
  p : Value,
  c : Value,
  b : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = power(polfoo(c, b, Fix(0L), x), div(p, Fix(2L)))
  let exp3 = power(x, one_plus(num_neg(m)))
  if num_eq(p, Fix(1L)) {
    // sqrt(c*x^2+b*x)/x^m
    case1(list1(list2(m, Fix(1L))), c, b, x, ec_1)
  } else if zerop(m) {
    // (c*x^2+b*x)^(p-1/2)
    case0(p, c, b, x, ec_1)
  } else if num_eq(m, one_plus(p)) {
    // (c*x^2+b*x)^(p-1/2)/x^(p+1)
    addn_([
      augmult(muln_([Fix(-1L), exp1, inv(one_minus(m)), exp3])),
      augmult(
        muln_([
          b,
          irinte__half(),
          casegen(one_minus(m), num_sub(p, Fix(2L)), c, b, x, ec_1),
        ]),
      ),
      augmult(
        muln_([
          c,
          casegen(num_sub(m, Fix(2L)), num_sub(p, Fix(2L)), c, b, x, ec_1),
        ]),
      ),
    ])
  } else if num_eq(m, Fix(1L)) {
    // (c*x^2+b*x)^(p-1/2)/x
    addn_([
      augmult(muln_([inv(p), exp1])),
      augmult(
        muln_([b, irinte__half(), case0(num_sub(p, Fix(2L)), c, b, x, ec_1)]),
      ),
    ])
  } else {
    // (c*x^2+b*x)^(p-1/2)/x^m
    addn_([
      augmult(
        muln_([Fix(-1L), exp1, inv(num_sub(m, one_plus(p))), exp3]),
      ),
      augmult(
        muln_([
          Fix(-1L),
          p,
          b,
          irinte__half(),
          inv(num_sub(m, one_plus(p))),
          casegen(one_minus(m), num_sub(p, Fix(2L)), c, b, x, ec_1),
        ]),
      ),
    ])
  }
}

///|
/// Integrate things like sqrt(c*x^2+b*x))/x^m.
fn case1(
  negpowlist : Value,
  c : Value,
  b : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  if eql(b, Fix(0L)) {
    // don't handle degenerate case (would divide by zero)
    return Nil
  }
  let exp1 = power(c, irinte__mhalf())
  let eb_1 = inv(b)
  let mut lst = negpowlist
  let mut result : Value = Fix(0L)
  let mut controlpow = caar(lst)
  let mut coef = cadar(lst)
  let mut count : Value = Nil
  let mut res1 : Value = Nil
  let mut res2 : Value = Nil
  let mut m : Value = Nil
  let mut partres : Value = Nil
  let mut res : Value = Nil
  let mut m1 = num_sub(controlpow, Fix(2L))
  // states: 0 start, 1 jump1, 2 jump2, 3 jump3, 4 jump4, 5 jump5, 6 on,
  // 7 loop
  let mut st = 0
  while true {
    match st {
      0 => {
        if zerop(controlpow) {
          result = augmult(muln_([coef, case0(Fix(1L), c, b, x, ec_1)]))
          count = Fix(1L)
          st = 7
          continue
        }
        st = 1
      }
      1 => {
        // sqrt(R)/x
        if num_eq(controlpow, Fix(1L)) {
          result = addn_([
            result,
            augmult(muln_([coef, den1numn(Fix(1L), c, b, Fix(0L), x, ec_1)])),
          ])
          count = Fix(2L)
          st = 7
          continue
        }
        st = 2
      }
      2 => {
        // sqrt(R)/x^2
        if num_eq(controlpow, Fix(2L)) {
          result = addn_([
            result,
            augmult(
              muln_([
                coef,
                denmnumn(
                  list2(t, list2(Fix(2L), Fix(1L))),
                  Fix(1L),
                  c,
                  b,
                  Fix(0L),
                  x,
                  ec_1,
                ),
              ]),
            ),
          ])
          count = Fix(3L)
          st = 7
          continue
        }
        st = 3
      }
      3 => {
        let signb = checksigntm(power(b, Fix(2L)))
        if eq(signb, q_d_zero) {
          count = Fix(5L)
          st = 5
          continue
        }
        count = Fix(4L)
        m = Fix(0L)
        let signc = checksigntm(ec_1)
        if eq(signc, q_d_positive) {
          res = augmult(
            mul_star(
              list([
                Fix(2L),
                exp1,
                mk(q_p_log, [
                  addn_([
                    power(muln_([c, x]), irinte__half()),
                    power(addn_([b, muln_([c, x])]), irinte__half()),
                  ]),
                ]),
              ]),
            ),
          )
          st = 4
          continue
        }
        res = augmult(
          mul_star(
            list([
              Fix(2L),
              exp1,
              mk(q_p_atan, [
                power(
                  muln_([c, x, inv(addn_([b, muln_([Fix(-1L), c, x])]))]),
                  irinte__half(),
                ),
              ]),
            ]),
          ),
        )
        st = 4
      }
      4 => {
        m = one_plus(m)
        res = addn_([
          augmult(
            muln_([
              Fix(-2L),
              power(polfoo(c, b, Fix(0L), x), irinte__half()),
              eb_1,
              inv(num_sum([m, m, Fix(-1L)])),
              power(x, num_neg(m)),
            ]),
          ),
          augmult(
            muln_([
              div(Fix(-2L), num_sum([m, m, Fix(-1L)])),
              c,
              one_minus(m),
              eb_1,
              res,
            ]),
          ),
        ])
        if num_eq(m, m1) {
          res2 = res
          st = 4
          continue
        }
        if num_eq(one_minus(m), m1) {
          if res2 is Nil {
            return Nil
          }
          res1 = res
          partres = addn_([
            augmult(
              muln_([
                Fix(-1L),
                power(polfoo(c, b, Fix(0L), x), irinte__half()),
                r1m(m),
                power(x, num_neg(m)),
              ]),
            ),
            augmult(muln_([b, irinte__half(), r1m(m), res1])),
            augmult(muln_([c, r1m(m), res2])),
          ])
          st = 6
          continue
        }
        st = 4
      }
      5 => {
        m = controlpow
        if zerop(m) {
          partres = mul_star(list([exp1, mk(q_p_log, [x])]))
          st = 6
          continue
        }
        partres = muln_([Fix(-1L), exp1, power(x, num_neg(m)), r1m(m)])
        st = 6
      }
      6 => {
        result = addn_([result, augmult(muln_([coef, partres]))])
        st = 7
      }
      _ => {
        lst = cdr(lst)
        if lst is Nil {
          return result
        }
        coef = cadar(lst)
        controlpow = caar(lst)
        if num_eq(count, Fix(5L)) {
          st = 5
          continue
        }
        if num_eq(count, Fix(1L)) {
          st = 1
          continue
        }
        if num_eq(count, Fix(2L)) {
          st = 2
          continue
        }
        if num_eq(count, Fix(3L)) {
          st = 3
          continue
        }
        m1 = num_sub(controlpow, Fix(2L))
        if num_eq(m1, m) {
          res2 = res1
        }
        st = 4
      }
    }
  }
  Nil
}

///|
fn r1m(m : Value) -> Value raise {
  div(Fix(1L), m)
}

///|
/// Integrate (c*x^2+b*x)^(p-1/2)
fn case0(
  power_ : Value,
  c : Value,
  b : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  let exp1 = mk_simp(q_rat, [Fix(1L), Fix(4L)])
  let exp2 = addn_([b, muln_([Fix(2L), c, x])])
  let exp3 = power(c, mk_simp(q_rat, [Fix(-3L), Fix(2L)]))
  let signc = checksigntm(ec_1)
  let mut p : Value = Fix(1L)
  let mut result : Value = Nil
  // sqrt(c*x^2+b*x)
  if eq(signc, q_d_positive) {
    result = addn_([
      augmult(
        muln_([
          exp1,
          ec_1,
          exp2,
          power(polfoo(c, b, Fix(0L), x), irinte__half()),
        ]),
      ),
      augmult(
        mul_star(
          list([
            b,
            b,
            mk(q_rat, [Fix(-1L), Fix(8L)]),
            exp3,
            mk(q_p_log, [
              addn_([
                exp2,
                muln_([
                  Fix(2L),
                  power(c, irinte__half()),
                  power(polfoo(c, b, Fix(0L), x), irinte__half()),
                ]),
              ]),
            ]),
          ]),
        ),
      ),
    ])
  }
  if eq(signc, q_d_negative) {
    result = addn_([
      augmult(
        muln_([
          exp1,
          ec_1,
          exp2,
          power(polfoo(c, b, Fix(0L), x), irinte__half()),
        ]),
      ),
      augmult(
        mul_star(
          list([
            b,
            b,
            mk(q_rat, [Fix(-1L), Fix(8L)]),
            ec_1,
            power(muln_([Fix(-1L), c]), irinte__mhalf()),
            mk(q_p_asin, [muln_([Fix(-1L), inv(b), exp2])]),
          ]),
        ),
      ),
    ])
  }
  while true {
    if equal(power_, p) {
      return result
    }
    p = num_add(p, Fix(2L))
    result = addn_([
      augmult(
        muln_([
          irinte__half(),
          ec_1,
          inv(one_plus(p)),
          exp2,
          power(polfoo(c, b, Fix(0L), x), div(p, Fix(2L))),
        ]),
      ),
      augmult(
        muln_([
          p,
          b,
          b,
          mk_simp(q_rat, [Fix(-1L), Fix(4L)]),
          ec_1,
          inv(one_plus(p)),
          result,
        ]),
      ),
    ])
  }
  Nil
}

///|
/// Integrate R^(p-1/2)/x, p >= 1 (G&R 2.265, 2.267).
fn den1numn(
  p : Value,
  c : Value,
  b : Value,
  a : Value,
  x : Value,
  ec_1 : Value,
) -> Value raise {
  if num_eq(p, Fix(1L)) {
    addn_([
      power(polfoo(c, b, a, x), irinte__half()),
      augmult(muln_([a, den1den1(c, b, a, x, ec_1)])),
      augmult(muln_([b, irinte__half(), den1(c, b, a, x)])),
    ])
  } else {
    addn_([
      augmult(
        muln_([
          power(polfoo(c, b, a, x), addn_([p, irinte__mhalf()])),
          inv(num_sum([p, p, Fix(-1L)])),
        ]),
      ),
      augmult(muln_([a, den1numn(num_add(p, Fix(-1L)), c, b, a, x, ec_1)])),
      augmult(
        muln_([
          b,
          irinte__half(),
          numn(num_add(p, Fix(-2L)), c, b, a, x, ec_1),
        ]),
      ),
    ])
  }
}

///|
/// Sum up the results of applying INTIRA to each expression in L.
fn distrint(l : Value, x : Value) -> Value raise {
  addn(
    mapcar(
      e => {
        let ie = intira(e, x)
        if ie.truthy() {
          ie
        } else {
          cons(list2(q_p_integrate, q_simp), list2(e, x))
        }
      },
      l,
    ),
    t,
  )
}

///|
fn init_irinte() -> Unit raise {
  ()
}
