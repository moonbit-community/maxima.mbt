// Port of src/rat3b.lisp: the new Rational Function Package, part 2.
// Rational functions (pairs (num . denom) of CRE polynomials).

///|
fn ralgp(r : Value) -> Value raise {
  let v = palgp(car(r))
  if v.truthy() {
    v
  } else {
    palgp(cdr(r))
  }
}

///|
fn palgp(poly : Value) -> Value raise {
  if atom(poly) {
    Nil
  } else if alg(poly).truthy() {
    t
  } else {
    let mut p = cdr(poly)
    while !(p is Nil) {
      if palgp(cadr(p)).truthy() {
        return t
      }
      p = cddr(p)
    }
    Nil
  }
}

///|
/// RATDX: derivative of the CRE (or general) expression E with respect to
/// *X*, using DIFF properties on the gensyms.
fn ratdx(e : Value, ear_x : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_x, ear_x),
    (q_varlist, Nil),
    (q_flag, Nil),
    (q_v_star, Nil),
    (q_genvar, Nil),
    (q_n_stara, Nil),
    (q_trunclist, Nil),
  ])
  defer unbind_all(bs)
  let mut e = e
  if memq(q_trunc, car(e)).truthy() {
    set(q_trunclist, cadddr(cdar(e))) |> ignore
  }
  if !eq(caar(e), q_mrat) {
    e = ratf(e)
  }
  // A tlist with non-atomic kernels means the series contains adjoined
  // singular kernels; differentiate the disrep'd expression and re-expand.
  let trunclist = symval(q_trunclist)
  if trunclist.truthy() &&
    find_if(x => !tvar_q(car(x)).truthy(), trunclist).truthy() {
    return with_special(q_exact_poly, Nil, () => taylor1(
      sdiff(d_ratdisrep(e), symval(q_ear_x)),
      list1(mapcar(x => copy_tree(x), symval(q_trunclist))),
    ))
  }
  set(q_varlist, caddar(e)) |> ignore
  set(q_genvar, car(cdr(cddar(e)))) |> ignore
  if length(symval(q_genvar)) > length(symval(q_varlist)) {
    set(
      q_genvar,
      mapcar2((_a, b) => b, symval(q_varlist), symval(q_genvar)),
    )
    |> ignore
  }
  set(q_ear_x, fullratsimp(symval(q_ear_x))) |> ignore
  newvar(symval(q_ear_x)) |> ignore
  let a = mapcan(
    z => {
      let ff = fullratsimp(sdiff(z, symval(q_ear_x)))
      newvar(ff) |> ignore
      orderpointer(symval(q_varlist)) |> ignore
      list2(z, ff)
    },
    symval(q_varlist),
  )
  set(q_n_stara, cons(Nil, a)) |> ignore
  let mut vl = symval(q_varlist)
  let mut gl = symval(q_genvar)
  while vl is Cons(_) && gl is Cons(_) {
    let z = car(vl)
    let b = car(gl)
    if old_get(symval(q_n_stara), z) is Nil {
      putprop(b, rzero(), q_diff) |> ignore
    } else if putprop(b, cdr(ratf(old_get(symval(q_n_stara), z))), q_diff).truthy() &&
      alike1(z, symval(q_ear_x)).truthy() {
      set(q_v_star, b) |> ignore
    } else {
      set(q_flag, t) |> ignore
    }
    vl = cdr(vl)
    gl = cdr(gl)
  }
  let flag = symval(q_flag).truthy()
  if symval(q_trunclist).truthy() {
    return cons(
      list([
        q_mrat,
        q_simp,
        symval(q_varlist),
        symval(q_genvar),
        symval(q_trunclist),
        q_trunc,
      ]),
      if flag {
        psdp(cdr(e))
      } else {
        psderivative(cdr(e), symval(q_v_star))
      },
    )
  }
  cons(
    list4(q_mrat, q_simp, symval(q_varlist), symval(q_genvar)),
    if flag {
      ratdx1(cadr(e), cddr(e))
    } else {
      ratderivative(cdr(e), symval(q_v_star))
    },
  )
}

///|
fn ratdx1(u : Value, v : Value) -> Value raise {
  ratquotient(
    ratdif(
      rattimes(cons(v, Fix(1L)), ratdp(u), t),
      rattimes(cons(u, Fix(1L)), ratdp(v), t),
    ),
    cons(pexpt(v, Fix(2L)), Fix(1L)),
  )
}

///|
fn ratdp(p : Value) -> Value raise {
  if atom(p) {
    rzero()
  } else if rzerop(get(car(p), q_diff)).truthy() {
    ratdp1(cons(list3(car(p), q_foo, Fix(1L)), Fix(1L)), cdr(p))
  } else {
    ratdp2(
      cons(list3(car(p), q_foo, Fix(1L)), Fix(1L)),
      get(car(p), q_diff),
      cdr(p),
    )
  }
}

///|
fn ratdp1(x : Value, v : Value) -> Value raise {
  if v is Nil {
    rzero()
  } else if equal(car(v), Fix(0L)) {
    ratdp(cadr(v))
  } else {
    ratplus(
      rattimes(subst(car(v), q_foo, x), ratdp(cadr(v)), t),
      ratdp1(x, cddr(v)),
    )
  }
}

///|
fn ratdp2(x : Value, dx : Value, v : Value) -> Value raise {
  if v is Nil {
    rzero()
  } else if equal(car(v), Fix(0L)) {
    ratdp(cadr(v))
  } else if equal(car(v), Fix(1L)) {
    ratplus(
      ratdp2(x, dx, cddr(v)),
      ratplus(
        rattimes(dx, cons(cadr(v), Fix(1L)), t),
        rattimes(subst(Fix(1L), q_foo, x), ratdp(cadr(v)), t),
      ),
    )
  } else {
    ratplus(
      ratdp2(x, dx, cddr(v)),
      ratplus(
        rattimes(
          dx,
          rattimes(
            subst(num_sub(car(v), Fix(1L)), q_foo, x),
            cons(ptimes(car(v), cadr(v)), Fix(1L)),
            t,
          ),
          t,
        ),
        rattimes(ratdp(cadr(v)), subst(car(v), q_foo, x), t),
      ),
    )
  }
}

///|
fn ratderivative(rat : Value, var2 : Value) -> Value raise {
  let mut num = car(rat)
  let mut denom = cdr(rat)
  if equal(Fix(1L), denom) {
    cons(pderivative(num, var2), Fix(1L))
  } else {
    denom = pgcdcofacts(denom, pderivative(denom, var2))
    // RATREDUCE ONLY NEEDS TO BE DONE WITH CONTENT OF GCD WRT VAR2.
    num = ratreduce(
      pdifference(
        ptimes(cadr(denom), pderivative(num, var2)),
        ptimes(num, caddr(denom)),
      ),
      car(denom),
    )
    if ratmac__pz(car(num)) {
      num
    } else {
      rplacd(num, ptimes(cdr(num), pexpt(cadr(denom), Fix(2L))))
    }
  }
}

///|
fn ratdif(x : Value, y : Value) -> Value raise {
  ratplus(x, ratminus(y))
}

///|
fn ratfact(x : Value, fn_ : Value) -> Value raise {
  let mut fn_ = fn_
  if symval(q_d_keepfloat).truthy() &&
    (pfloatp(car(x)).truthy() || pfloatp(cdr(x)).truthy()) {
    fn_ = q_floatfact
  }
  if !onep1(cdr(x)).truthy() {
    nconc(
      funcall(fn_, [car(x)]),
      fixmult(funcall(fn_, [cdr(x)]), Fix(-1L)),
    )
  } else {
    funcall(fn_, [car(x)])
  }
}

///|
fn floatfact(p : Value) -> Value raise {
  let r = ptermcont(p)
  let cont = monom__gtfacl(car(r))
  let primp = cadr(r)
  if equal(primp, Fix(1L)) {
    cont
  } else {
    append(cont, list2(primp, Fix(1L)))
  }
}

///|
fn ratinvert(y : Value) -> Value raise {
  ratalgdenom(
    if ratmac__pz(car(y)) {
      ratmac__rat_error("`quotient' by `zero'")
    } else if symval(q_modulus).truthy() && atom(car(y)) {
      cons(pctimes(crecip(car(y)), cdr(y)), Fix(1L))
    } else if symval(q_d_keepfloat).truthy() && floatp(car(y)) {
      cons(pctimes(num_div(Fix(1L), car(y)), cdr(y)), Fix(1L))
    } else if rat3a__pminusp(car(y)) {
      cons(pminus(cdr(y)), pminus(car(y)))
    } else {
      cons(cdr(y), car(y))
    },
  )
}

///|
fn ratminus(x : Value) -> Value raise {
  cons(pminus(car(x)), cdr(x))
}

///|
fn ratalgdenom(x : Value) -> Value raise {
  if !symval(q_d_ratalgdenom).truthy() {
    x
  } else if atom(cdr(x)) {
    x
  } else if alg(cdr(x)).truthy() {
    let v = ratmac__ignore_rat_err(() => rattimes(
      cons(car(x), Fix(1L)),
      rainv(cdr(x)),
      t,
    ))
    if v.truthy() {
      v
    } else {
      x
    }
  } else {
    x
  }
}

///|
fn ratreduce(x : Value, y : Value) -> Value raise {
  if ratmac__pz(y) {
    ratmac__rat_error("`quotient' by `zero'")
  } else if ratmac__pz(x) {
    rzero()
  } else if equal(y, Fix(1L)) {
    cons(x, Fix(1L))
  } else if symval(q_d_keepfloat).truthy() &&
    atom(y) &&
    (symval(q_d_float).truthy() || floatp(y) || pfloatp(x).truthy()) {
    cons(pctimes(quot(Flo(1.0), y), x), Fix(1L))
  } else {
    let b = pgcdcofacts(x, y)
    let b = ratalgdenom(rplacd(cdr(b), caddr(b)))
    if symval(q_modulus).truthy() && atom(cdr(b)) {
      cons(pctimes(crecip(cdr(b)), car(b)), Fix(1L))
    } else if rat3a__pminusp(cdr(b)) {
      cons(pminus(car(b)), pminus(cdr(b)))
    } else {
      b
    }
  }
}

///|
fn ptimes_star(p : Value, q : Value) -> Value raise {
  if symval(q_d_ratwtlvl).truthy() {
    wtptimes(p, q, Fix(0L))
  } else {
    ptimes(p, q)
  }
}

///|
fn rattimes(x : Value, y : Value, gcdsw : Value) -> Value raise {
  if symval(q_d_ratfac).truthy() {
    facrtimes(x, y, gcdsw)
  } else if symval(q_d_algebraic).truthy() &&
    gcdsw.truthy() &&
    ralgp(x).truthy() &&
    ralgp(y).truthy() {
    let w = rattimes(x, y, Nil)
    ratreduce(car(w), cdr(w))
  } else if equal(Fix(1L), cdr(x)) {
    if equal(Fix(1L), cdr(y)) {
      cons(ptimes_star(car(x), car(y)), Fix(1L))
    } else if gcdsw.truthy() {
      rattimes(ratreduce(car(x), cdr(y)), cons(car(y), Fix(1L)), Nil)
    } else {
      cons(ptimes_star(car(x), car(y)), cdr(y))
    }
  } else if equal(Fix(1L), cdr(y)) {
    rattimes(y, x, gcdsw)
  } else if gcdsw.truthy() {
    rattimes(ratreduce(car(x), cdr(y)), ratreduce(car(y), cdr(x)), Nil)
  } else {
    cons(ptimes_star(car(x), car(y)), ptimes_star(cdr(x), cdr(y)))
  }
}

///|
fn ratexpt(x : Value, n : Value) -> Value raise {
  if equal(n, Fix(0L)) {
    cons(Fix(1L), Fix(1L))
  } else if equal(n, Fix(1L)) {
    x
  } else if minusp(n) {
    ratinvert(ratexpt(x, num_neg(n)))
  } else if symval(q_d_ratwtlvl).truthy() {
    ratreduce(wtpexpt(car(x), n), wtpexpt(cdr(x), n))
  } else if symval(q_d_algebraic).truthy() {
    ratreduce(pexpt(car(x), n), pexpt(cdr(x), n))
  } else {
    cons(pexpt(car(x), n), pexpt(cdr(x), n))
  }
}

///|
fn ratplus(x : Value, y : Value) -> Value raise {
  if symval(q_d_ratfac).truthy() {
    facrplus(x, y)
  } else if symval(q_d_ratwtlvl).truthy() {
    ratreduce(
      pplus(
        wtptimes(car(x), cdr(y), Fix(0L)),
        wtptimes(car(y), cdr(x), Fix(0L)),
      ),
      wtptimes(cdr(x), cdr(y), Fix(0L)),
    )
  } else if symval(q_d_algebraic).truthy() &&
    ralgp(x).truthy() &&
    ralgp(y).truthy() {
    ratreduce(
      pplus(ptimeschk(car(x), cdr(y)), ptimeschk(car(y), cdr(x))),
      ptimeschk(cdr(x), cdr(y)),
    )
  } else if equal(Fix(1L), cdr(x)) {
    if equal(Fix(0L), car(x)) {
      y
    } else if equal(Fix(1L), cdr(y)) {
      cons(pplus(car(x), car(y)), Fix(1L))
    } else {
      cons(pplus(ptimes(car(x), cdr(y)), car(y)), cdr(y))
    }
  } else if equal(Fix(1L), cdr(y)) {
    if equal(Fix(0L), car(y)) {
      x
    } else {
      cons(pplus(ptimes(car(y), cdr(x)), car(x)), cdr(x))
    }
  } else {
    let q = pgcdcofacts(cdr(x), cdr(y))
    let mut n = pplus(ptimes(car(x), caddr(q)), ptimes(car(y), cadr(q)))
    if cadddr(q).truthy() {
      // denom factor from algebraic gcd
      n = ptimes(n, cadddr(q))
    }
    ratreduce(n, ptimes(car(q), ptimes(cadr(q), caddr(q))))
  }
}

///|
fn ratquotient(x : Value, y : Value) -> Value raise {
  rattimes(x, ratinvert(y), t)
}
