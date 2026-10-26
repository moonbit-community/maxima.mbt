// Port of src/nrat4.lisp: ratcoef, ratsubst, bothcoef, freeof and radcan.

///|
fn pdis(x : Value) -> Value raise {
  d_ratdisrep(pdis_star(x))
}

///|
fn pdis_star(x : Value) -> Value raise {
  cons(
    list4(q_mrat, q_simp, symval(q_varlist), symval(q_genvar)),
    cons(x, Fix(1L)),
  )
}

///|
fn rdis(x : Value) -> Value raise {
  d_ratdisrep(rdis_star(x))
}

///|
fn rdis_star(x : Value) -> Value raise {
  cons(list4(q_mrat, q_simp, symval(q_varlist), symval(q_genvar)), x)
}

///|
fn rform(x : Value) -> Value raise {
  cdr(ratf(x))
}

///|
/// The spelling "ratcoeff" is nicer.
fn d_ratcoef(e : Value, x : Value, n? : Value = Fix(1L)) -> Value raise {
  ratcoeff(e, x, n)
}

///|
fn ratcoeff(a : Value, b : Value, c : Value) -> Value raise {
  let formflag = d_ratp(a).truthy()
  let taylorform = formflag && memq(q_trunc, cdar(a)).truthy()
  if zerop1(b).truthy() {
    improper_arg_err(b, q_d_ratcoeff)
  } else if mbagp(a).truthy() {
    cons(car(a), mapcar(a => ratcoeff(a, b, c), cdr(a)))
  } else if taylorform &&
    mnump(c).truthy() &&
    assolike(b, cadddr(cdar(a))).truthy() {
    pscoeff1(a, b, c)
  } else if taylorform &&
    mexptp(b).truthy() &&
    mnump(c).truthy() &&
    mnump(caddr(b)).truthy() &&
    assolike(cadr(b), cadddr(cdar(a))).truthy() {
    pscoeff1(a, cadr(b), mul2(c, caddr(b)))
  } else if taylorform &&
    equal(c, Fix(0L)) &&
    freeof(d_ratdisrep(b), d_ratdisrep(a)).truthy() {
    a
  } else {
    let mut a = a
    if taylorform {
      a = ratdisrep(a)
    }
    let a0 = a
    a = with_special(q_d_ratwtlvl, Nil, () => if equal(c, Fix(0L)) {
      ratcoef(mul2_star(a0, b), b)
    } else {
      ratcoef(
        a0,
        if equal(c, Fix(1L)) {
          b
        } else {
          list3(list1(q_mexpt), b, c)
        },
      )
    })
    if formflag && !taylorform {
      minimize_varlist(a)
    } else {
      ratdisrep(a)
    }
  }
}

///|
fn minimize_varlist(ratfun : Value) -> Value raise {
  let ratfun = if !d_ratp(ratfun).truthy() { ratf(ratfun) } else { ratfun }
  minvarlist_mrat(caddr(car(ratfun)), cadddr(car(ratfun)), cdr(ratfun))
}

///|
fn minvarlist_mrat(vars : Value, gens : Value, ratform : Value) -> Value raise {
  let newgens = union_star(listovars(car(ratform)), listovars(cdr(ratform)))
  let mut lv = vars
  let mut lg = gens
  let mut nlv : Value = Nil
  let mut nlg : Value = Nil
  while !(lg is Nil) {
    if memq(car(lg), newgens).truthy() {
      nlg = cons(car(lg), nlg)
      nlv = cons(car(lv), nlv)
    }
    lv = cdr(lv)
    lg = cdr(lg)
  }
  cons(list4(q_mrat, q_simp, nreverse(nlv), nreverse(nlg)), ratform)
}

///|
fn ratcoef(exp_ : Value, var_ : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_d_ratfac, Nil),
    (q_d_algebraic, Nil),
    (q_d_ratwtlvl, Nil),
    (q_bas, Nil),
  ])
  defer unbind_all(bs)
  let mut exp_ = exp_
  let mut var_ = ratdisrep(var_)
  set(
    q_bas,
    if mexptp(var_).truthy() && mnump(caddr(var_)).truthy() {
      cadr(var_)
    } else {
      var_
    },
  )
  |> ignore
  newvar(var_) |> ignore
  newvar(symval(q_bas)) |> ignore
  let mut minvar = car(symval(q_varlist))
  newvar(exp_) |> ignore
  exp_ = cdr(ratrep_star(exp_))
  var_ = cdr(ratrep_star(var_))
  set(q_bas, cadr(ratrep_star(symval(q_bas)))) |> ignore
  // PRODCOEF truncates numeric quotients, so only take this shortcut when
  // the monomial VAR has coefficient 1 or -1.
  if onep1(cdr(exp_)).truthy() &&
    onep1(cdr(var_)).truthy() &&
    pureprod(car(var_)).truthy() &&
    member(leadcoefficient(car(var_)), list2(Fix(1L), Fix(-1L))).truthy() {
    return pdis_star(prodcoef(car(var_), car(exp_)))
  }
  exp_ = ratquotient(exp_, var_)
  if minvar is Nil {
    return pdis_star(prodcoef(cdr(exp_), car(exp_)))
  }
  minvar = caadr(ratrep_star(minvar))
  while true {
    if atom(cdr(exp_)) || ratmac__pgp(minvar, cadr(exp_)) {
      return rdis_star(cdr(ratdivide(exp_, symval(q_bas))))
    }
    exp_ = ratcoef1(car(exp_), cdr(exp_))
  }
  Nil
}

///|
fn ratcoef1(num : Value, den : Value) -> Value raise {
  if atom(num) {
    rzero()
  } else if eq(car(num), car(den)) {
    car(pdivide(num, den))
  } else if ratmac__pgp(car(den), car(num)) {
    rzero()
  } else {
    ratcoef1(constcoef(cdr(num)), den)
  }
}

///|
fn constcoef(p : Value) -> Value raise {
  let mut p = p
  while !(p is Nil) {
    if zerop(car(p)) {
      return cadr(p)
    }
    p = cddr(p)
  }
  Fix(0L)
}

///|
/// NEEDS CODE FOR FAC. FORM
fn d_ratsubst(a : Value, b : Value, c : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, Nil),
    (q_d_ratfac, Nil),
    (q_genvar, Nil),
    (q_d_keepfloat, Nil),
    (q_d_float, Nil),
    (q_d_numer, Nil),
  ])
  defer unbind_all(bs)
  let mut a = a
  let mut b = b
  let mut c = c
  // hard to maintain user ordering info.
  let dontdisrepit = d_ratp(c).truthy()
  if symval(q_d_radsubstflag).truthy() &&
    {
      newvar(b) |> ignore
      some(v => mexptp(v).truthy(), symval(q_varlist))
    } {
    let bs2 = bind_all([
      (q_d_factorflag, t),
      (q_n_starexp, Nil),
      (q_n_starexp2, Nil),
      (q_n_starradsubst, Nil),
    ])
    defer unbind_all(bs2)
    a = fullratsimp(a)
    b = fullratsimp(b)
    c = fullratsimp(c)
    set(q_varlist, Nil) |> ignore
    fnewvar(b) |> ignore
    fnewvar(c) |> ignore
    set(q_n_starexp, cdr(ratrep_star(b))) |> ignore
    set(q_n_starexp2, cdr(ratrep_star(c))) |> ignore
    // since *radsubst is t, both *exp and *exp2 will be radcan simplified
    set(q_n_starradsubst, t) |> ignore
    spc0(symval(q_n_starvar)) |> ignore
    b = rdis(symval(q_n_starexp))
    c = rdis(symval(q_n_starexp2))
    set(q_varlist, Nil) |> ignore
  } else {
    a = d_rat(a, Nil)
    b = d_rat(b, Nil)
    c = d_rat(c, Nil)
    set(q_varlist, Nil) |> ignore
  }
  a = d_ratdisrep(a)
  b = d_ratdisrep(b)
  c = d_ratdisrep(c)
  if integerp(b) {
    c = ratf(maxima_substitute(a, b, c))
    return if dontdisrepit { c } else { d_ratdisrep(c) }
  }
  newvar(c) |> ignore
  let a1 = a
  let b1 = b
  let mut newvarlist = mapcar(
    z => if atom(z) {
      z
    } else {
      resimplify(
        cons(
          car(z),
          mapcar(
            zz => if alike1(zz, b1).truthy() {
              a1
            } else if atom(zz) {
              zz
            } else {
              d_ratdisrep(d_ratsubst(a1, b1, zz))
            },
            cdr(z),
          ),
        ),
      )
    },
    symval(q_varlist),
  )
  newvar(a) |> ignore
  newvar(b) |> ignore
  newvarlist = reverse(
    pairoff(reverse(symval(q_varlist)), reverse(newvarlist)),
  )
  a = cdr(ratrep_star(a))
  b = cdr(ratrep_star(b))
  c = cdr(ratrep_star(c))
  if rat3a__pminusp(car(b)) {
    b = ratminus(b)
    a = ratminus(a)
  }
  if equal(Fix(1L), car(b)) &&
    !equal(Fix(1L), cdr(b)) &&
    !equal(Fix(0L), car(a)) {
    a = ratinvert(a)
    b = ratinvert(b)
  }
  if !equal(Fix(1L), cdr(b)) {
    a = rattimes(a, cons(cdr(b), Fix(1L)), t)
    b = cons(car(b), Fix(1L))
  }
  c = if member_equal(car(b), list2(Fix(0L), Fix(1L))).truthy() {
    ratf(maxima_substitute(rdis(a), rdis(b), rdis(c)))
  } else {
    let head = list4(q_mrat, q_simp, symval(q_varlist), symval(q_genvar))
    cons(
      head,
      if equal(cdr(a), Fix(1L)) {
        ratreduce(
          everysubst0(car(a), car(b), car(c)),
          everysubst0(car(a), car(b), cdr(c)),
        )
      } else {
        allsubst00(a, b, c)
      },
    )
  }
  if !alike(newvarlist, symval(q_varlist)).truthy() {
    set(q_varlist, newvarlist) |> ignore
    c = rdis(cdr(c))
    set(q_varlist, Nil) |> ignore
    c = ratf(c)
  }
  if dontdisrepit {
    c
  } else {
    d_ratdisrep(c)
  }
}

///|
fn xptimes(x : Value, y : Value) -> Value raise {
  if symval(q_d_ratwtlvl).truthy() {
    wtptimes(x, y, Fix(0L))
  } else {
    ptimes(x, y)
  }
}

///|
fn allsubst00(a : Value, b : Value, c : Value) -> Value raise {
  if equal(a, b) {
    c
  } else if !equal(cdr(b), Fix(1L)) {
    c
  } else {
    let n = everysubst00(a, car(b), car(c))
    ratquotient(n, everysubst00(a, car(b), cdr(c)))
  }
}

///|
fn everysubst00(x : Value, i : Value, z : Value) -> Value raise {
  let mut ans = rzero()
  let mut l = everysubst(i, z, symval(q_n_staralpha))
  while l is Cons(_) {
    let e = car(l)
    let coef = cadr(l)
    ans = ratplus(ans, rattimes(cons(coef, Fix(1L)), ratexpt(x, e), t))
    l = cddr(l)
  }
  ans
}

///|
fn everysubst0(x : Value, i : Value, z : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut l = everysubst(i, z, symval(q_n_staralpha))
  while l is Cons(_) {
    let e = car(l)
    let coef = cadr(l)
    ans = pplus(ans, xptimes(coef, pexpt(x, e)))
    l = cddr(l)
  }
  ans
}

///|
fn everysubst1(a : Value, b : Value, maxpow : Value) -> Value raise {
  let acc = Collector::new()
  let mut l = cdr(b)
  while l is Cons(_) {
    let e = car(l)
    let coef = cadr(l)
    let part = everysubst(a, coef, maxpow)
    acc.append_list(
      if ratmac__eqn(Fix(0L), e) {
        part
      } else {
        everysubst2(part, list3(car(b), e, Fix(1L)))
      },
    )
    l = cddr(l)
  }
  acc.result()
}

///|
fn everysubst2(l : Value, h : Value) -> Value raise {
  let mut ptr = l
  while !(ptr is Nil) {
    rplaca(cdr(ptr), ptimes(h, cadr(ptr))) |> ignore
    ptr = cddr(ptr)
  }
  l
}

///|
fn pairoff(l : Value, m : Value) -> Value raise {
  if m is Nil {
    l
  } else {
    cons(car(m), pairoff(cdr(l), cdr(m)))
  }
}

///|
fn everysubst(a : Value, b : Value, maxpow : Value) -> Value raise {
  if atom(a) {
    if equal(a, Fix(1L)) {
      list2(maxpow, b)
    } else if atom(b) {
      let mut bb = b
      let mut ans : Value = Fix(0L)
      while !(ratmac__gt(num_abs(a), num_abs(bb)) || equal(maxpow, ans)) {
        bb = quot(bb, a)
        ans = num_add(ans, Fix(1L))
      }
      let maxpow1 = ans
      let maxpow2 = expt(a, maxpow1)
      let q = quot(b, maxpow2)
      list4(maxpow1, q, Fix(0L), num_rem(b, maxpow2))
    } else {
      everysubst1(a, b, maxpow)
    }
  } else if atom(b) || ratmac__pgp(car(a), car(b)) {
    list2(Fix(0L), b)
  } else if eq(car(a), car(b)) {
    if cdddr(a) is Nil {
      everypterms(b, caddr(a), cadr(a), maxpow)
    } else {
      substforsum(a, b, maxpow)
    }
  } else {
    everysubst1(a, b, maxpow)
  }
}

///|
fn everypterms(x : Value, p : Value, n : Value, maxpow : Value) -> Value raise {
  if ratmac__lt(cadr(x), n) {
    return list2(Fix(0L), x)
  }
  let k = car(x)
  let mut x = cdr(x)
  let mut ans : Value = Nil
  let mut q = num_min(maxpow, quot(car(x), n))
  while true {
    // m
    if equal(q, Fix(0L)) {
      return if x is Nil { ans } else { cons(Fix(0L), cons(psimp(k, x), ans)) }
    }
    let part = everysubst(p, cadr(x), q)
    ans = nconc(everypterms1(part, k, n, car(x)), ans)
    x = cddr(x)
    if x is Nil {
      q = Fix(0L)
      continue
    }
    // l
    q = num_min(maxpow, quot(car(x), n))
  }
  Nil
}

///|
fn everypterms1(l : Value, k : Value, n : Value, j : Value) -> Value raise {
  let mut ptr = l
  while !(ptr is Nil) {
    rplaca(
      cdr(ptr),
      ptimes(
        psimp(k, list2(num_sub(j, num_mul(n, car(ptr))), Fix(1L))),
        cadr(ptr),
      ),
    )
    |> ignore
    ptr = cddr(ptr)
  }
  l
}

///|
fn substforsum(a : Value, b : Value, maxpow : Value) -> Value raise {
  let mut b = b
  let mut pow : Value = Fix(0L)
  let mut ans : Value = Nil
  while ratmac__lt(pow, maxpow) {
    let r = pdivide(b, a)
    let quot_ = car(r)
    let zl_rem = cadr(r)
    if !(equal(cdr(quot_), Fix(1L)) &&
      !ratmac__pz(car(quot_)) &&
      equal(cdr(zl_rem), Fix(1L))) {
      return cons(pow, cons(b, ans))
    }
    if !ratmac__pz(car(zl_rem)) {
      ans = cons(pow, cons(car(zl_rem), ans))
    }
    b = car(quot_)
    pow = num_add(pow, Fix(1L))
  }
  cons(maxpow, cons(b, ans))
}

///|
fn prodcoef(a : Value, b : Value) -> Value raise {
  if atom(a) {
    if atom(b) {
      quot(b, a)
    } else {
      prodcoef1(a, b)
    }
  } else if atom(b) {
    Fix(0L)
  } else if ratmac__pgp(car(a), car(b)) {
    Fix(0L)
  } else if eq(car(a), car(b)) {
    if cdddr(a) is Nil {
      prodcoef(caddr(a), ptterm(cdr(b), cadr(a)))
    } else {
      sumcoef(a, b)
    }
  } else {
    prodcoef1(a, b)
  }
}

///|
fn sumcoef(a : Value, b : Value) -> Value raise {
  let r = pdivide(b, a)
  let a = car(r)
  let b = cadr(r)
  if equal(cdr(a), Fix(1L)) && equal(cdr(b), Fix(1L)) {
    car(a)
  } else {
    Fix(0L)
  }
}

///|
fn prodcoef1(a : Value, b : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  let mut l = cdr(b)
  while l is Cons(_) {
    let bexp = car(l)
    let bcoef = cadr(l)
    let part = prodcoef(a, bcoef)
    if !ratmac__pz(part) {
      ans = pplus(ans, psimp(car(b), list2(bexp, part)))
    }
    l = cddr(l)
  }
  ans
}

///|
fn pureprod(x : Value) -> Value raise {
  let mut x = x
  while !atom(x) {
    if atom(cdr(x)) || !(cdddr(x) is Nil) {
      return Nil
    }
    x = caddr(x)
  }
  t
}

///|
fn d_bothcoef(r : Value, var_ : Value) -> Value raise {
  let bs = bind_all([
    (q_n_starvar, Nil),
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_d_ratfac, Nil),
  ])
  defer unbind_all(bs)
  let mut r = r
  let mut var_ = var_
  if !d_ratp(r).truthy() {
    let h = coeff(r, var_, Fix(1L))
    return list3(
      list1(q_mlist),
      h,
      list3(list1(q_mplus), r, list4(list1(q_mtimes), Fix(-1L), h, var_)),
    )
  }
  newvar(var_) |> ignore
  let mut h = {
    let vl = symval(q_varlist)
    if vl.truthy() {
      car(vl)
    } else {
      Nil
    }
  }
  newvar(r) |> ignore
  var_ = cdr(ratrep_star(var_))
  r = cdr(ratrep_star(r))
  if h.truthy() {
    h = caadr(ratrep_star(h))
  }
  if h.truthy() &&
    (atom(cdr(r)) || ratmac__pgp(h, cadr(r))) &&
    equal(Fix(1L), cdr(var_)) {
    var_ = bothprodcoef(car(var_), car(r))
    list3(
      list1(q_mlist),
      rdis_star(ratreduce(car(var_), cdr(r))),
      rdis_star(ratreduce(cdr(var_), cdr(r))),
    )
  } else {
    // CAN'T TELL WHAT BROUGHT US TO THIS POINT, SORRY
    merr("bothcoef: invalid arguments.", [])
  }
}

///|
/// COEFF OF A IN B
fn bothprodcoef(a : Value, b : Value) -> Value raise {
  let c = prodcoef(a, b)
  if ratmac__pz(c) {
    cons(Fix(0L), b)
  } else {
    cons(c, pdifference(b, ptimes(c, a)))
  }
}

///|
fn argsfreeof(var_ : Value, e : Value) -> Value raise {
  with_special(q_argsfreeofp, t, () => freeof(var_, e))
}

///|
/// This is a version of freeof for a list first argument
fn d_lfreeof(l : Value, e : Value) -> Value raise {
  if !d_listp(l).truthy() {
    merr("lfreeof: first argument must be a list; found: ~M", [l]) |> ignore
  }
  let exp_ = d_totaldisrep(e)
  for v in margs(l).iter() {
    if !freeof(d_totaldisrep(v), exp_).truthy() {
      return Nil
    }
  }
  t
}

///|
fn d_freeof(args : Value) -> Value raise {
  let mut l = mapcar(x => d_totaldisrep(x), nreverse(args))
  let e = car(l)
  while true {
    l = cdr(l)
    if l is Nil {
      return t
    }
    if freeof(getopr(car(l)), e).truthy() {
      continue
    }
    return Nil
  }
  Nil
}

///|
fn freeof(var2 : Value, e : Value) -> Value raise {
  if alike1(var2, e).truthy() {
    return Nil
  }
  if atom(e) {
    return t
  }
  let argsfreeofp = symval(q_argsfreeofp).truthy()
  let op = caar(e)
  if !argsfreeofp &&
    (alike1(var2, d_verbify(op)).truthy() ||
    alike1(var2, d_nounify(op)).truthy()) {
    Nil
  } else if (memq(op, list([q_p_product, q_p_sum, q_p_laplace])).truthy() ||
    (eq(op, q_p_integrate) && cdddr(e).truthy()) ||
    (eq(op, q_p_limit) && cddr(e).truthy())) &&
    alike1(var2, caddr(e)).truthy() {
    freeofl(var2, cdddr(e))
  } else if eq(op, q_p_at) {
    if !freeofl(var2, hand_side(caddr(e), q_r)).truthy() {
      Nil
    } else if !freeofl(var2, hand_side(caddr(e), q_l)).truthy() {
      t
    } else {
      freeof(var2, cadr(e))
    }
  } else if eq(op, q_lambda) &&
    !memq(q_array, cdar(e)).truthy() &&
    d_listp(cadr(e)).truthy() &&
    // Check if var2 appears in the lambda list in any of the following
    // ways: var2, 'var2, [var2] or ['var2].
    some(
      v => eq(v, var2) ||
        alike1(v, list2(list1(q_mquote), var2)).truthy() ||
        alike1(v, list2(list1(q_mlist), var2)).truthy() ||
        alike1(v, list2(list1(q_mlist), list2(list1(q_mquote), var2))).truthy(),
      cdadr(e),
    ) {
    t
  } else if eq(op, q_mprog) &&
    d_listp(cadr(e)).truthy() &&
    // Check for a local variable in a block: var2 appears in the variable
    // list alone or in an assignment.
    some(
      v => eq(v, var2) || (msetqp(v).truthy() && eq(cadr(v), var2)),
      cdadr(e),
    ) {
    t
  } else if memq(op, list2(q_mdo, q_mdoin)).truthy() &&
    alike1(var2, cadr(e)).truthy() {
    // Check for a loop variable.
    t
  } else if argsfreeofp {
    freeofl(var2, margs(e))
  } else {
    freeofl(var2, cdr(e))
  }
}

///|
fn freeofl(var2 : Value, l : Value) -> Value raise {
  for x in l.iter() {
    if !freeof(var2, x).truthy() {
      return Nil
    }
  }
  t
}

///|
fn hand_side(e : Value, flag : Value) -> Value raise {
  let e = if eq(caar(e), q_mequal) { list1(e) } else { cdr(e) }
  mapcar(u => if eq(flag, q_l) { cadr(u) } else { caddr(u) }, e)
}

// subtitle radcan

///|
fn d_radcan(exp_ : Value) -> Value raise {
  if mbagp(exp_).truthy() {
    cons(car(exp_), mapcar(x => d_radcan(x), cdr(exp_)))
  } else {
    with_specials([(q_d_ratsimpexpons, t), (q_modulus, Nil)], () => simplify(
      with_specials([(q_d_expop, Fix(0L)), (q_d_expon, Fix(0L))], () => {
        let f = fr1(exp_, Nil)
        radcan1(f, symval(q_n_starvar))
      }),
    ))
  }
}

///|
fn radcan1(n_starexp : Value, n_starvar : Value) -> Value raise {
  let bs = bind_all([(q_n_starexp, n_starexp), (q_n_starvar, n_starvar)])
  defer unbind_all(bs)
  if atom(symval(q_n_starexp)) {
    return symval(q_n_starexp)
  }
  let gcdv = {
    let g = symval(q_d_gcd)
    if g.truthy() {
      g
    } else {
      car(symval(q_ear_gcdl))
    }
  }
  let bs2 = bind_all([
    (q_d_factorflag, t),
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_d_ratfac, Nil),
    (q_d_norepeat, Nil),
    (q_d_gcd, gcdv),
    (q_radcanp, t),
  ])
  defer unbind_all(bs2)
  newvar(symval(q_n_starexp)) |> ignore
  set(q_n_starexp, cdr(ratrep_star(symval(q_n_starexp)))) |> ignore
  set(
    q_varlist,
    mapcar(
      x => if atom(x) {
        x
      } else {
        cons(car(x), mapcar(e => radcan1(e, symval(q_n_starvar)), cdr(x)))
      },
      symval(q_varlist),
    ),
  )
  |> ignore
  // A logarithm whose argument simplified to zero is log(0).
  for x in symval(q_varlist).iter() {
    if mlogp(x).truthy() && zerop1(cadr(x)).truthy() {
      merr("log: encountered log(0).", []) |> ignore
    }
  }
  spc0(symval(q_n_starvar)) |> ignore
  fr1(rdis(symval(q_n_starexp)), Nil)
}

///|
fn spc0(n_starvar : Value) -> Value raise {
  let bs = bind_all([
    (q_n_starvar, n_starvar),
    (q_n_starv, Nil),
    (q_n_starloglist, Nil),
  ])
  defer unbind_all(bs)
  if allatoms(symval(q_varlist)).truthy() {
    return Nil
  }
  // make list of logs
  set(q_varlist, mapcar(x => spc1(x), symval(q_varlist))) |> ignore
  set(q_n_starloglist, factorlogs(symval(q_n_starloglist))) |> ignore
  // subst log factorizations
  mapc(x => spc2(x) |> ignore, symval(q_n_starloglist)) |> ignore
  // expand exponents
  {
    let mut vl = symval(q_varlist)
    let mut gl = symval(q_genvar)
    while vl is Cons(_) && gl is Cons(_) {
      spc3(car(vl), car(gl)) |> ignore
      vl = cdr(vl)
      gl = cdr(gl)
    }
  }
  // make exponent list
  mapc(x => spc4(x) |> ignore, symval(q_varlist)) |> ignore
  // find expon dependencies
  let r = spc5(symval(q_n_starv), symval(q_varlist), symval(q_genvar))
  set(q_varlist, car(r)) |> ignore
  set(q_genvar, cdr(r)) |> ignore
  // restore radicals
  set(
    q_varlist,
    mapcar(x => rjfsimp(x, symval(q_n_starvar)), symval(q_varlist)),
  )
  |> ignore
  // simplify radicals
  mapc(x => spc7(x) |> ignore, symval(q_varlist))
}

///|
fn allatoms(l : Value) -> Value raise {
  for x in l.iter() {
    if !atom(x) {
      return Nil
    }
  }
  t
}

///|
fn rjfsimp(x : Value, n_starvar : Value) -> Value raise {
  let b = bind(q_n_starvar, n_starvar)
  defer unbind(b)
  if symval(q_n_starradsubst).truthy() && symval(q_d_radsubstflag).truthy() {
    return x
  }
  let x = with_special(q_d_logsimp, Nil, () => resimplify(x))
  if !m_dolexp_q(x).truthy() {
    return x
  }
  let expon = caddr(x)
  if mlogp(expon).truthy() {
    return cadr(expon)
  }
  let var_ = symval(q_n_starvar)
  if !(mtimesp(expon).truthy() && (symval(q_d_logsimp).truthy() || var_.truthy())) {
    return x
  }
  let rischflag = var_.truthy() &&
    !symval(q_d_logsimp).truthy() &&
    !freeof(var_, x).truthy()
  // POWER IS A PRODUCT
  let mut power = cdr(expon)
  while !(power is Nil) {
    let f = car(power)
    if numberp(f) {
      ()
    } else if mlogp(f).truthy() {
      if rischflag && cdr(power).truthy() {
        return x
      }
      return list3(
        list1(q_mexpt),
        cadar(power),
        muln(nrat4__remove_first_equal(f, cdr(expon)), Nil),
      )
    } else if rischflag {
      return x
    }
    power = cdr(power)
  }
  x
}

///|
/// `(remove item list :count 1 :test #'equal)`
fn nrat4__remove_first_equal(item : Value, l : Value) -> Value {
  let acc = Collector::new()
  let mut p = l
  while p is Cons(_) {
    if equal(car(p), item) {
      acc.append_list(cdr(p))
      return acc.result()
    }
    acc.add(car(p))
    p = cdr(p)
  }
  acc.result()
}

///|
/// Destructive `(delete item list :test #'equal)`.
fn nrat4__delete_equal(item : Value, l : Value) -> Value {
  let mut l = l
  while l is Cons(_) && equal(car(l), item) {
    l = cdr(l)
  }
  if l is Nil {
    return Nil
  }
  let mut p = l
  while cdr(p) is Cons(_) {
    if equal(cadr(p), item) {
      rplacd(p, cddr(p)) |> ignore
    } else {
      p = cdr(p)
    }
  }
  l
}

///|
fn dsubsta(x : Value, y : Value, zl : Value) -> Value raise {
  if zl is Nil {
    zl
  } else {
    if alike1(y, car(zl)).truthy() {
      rplaca(zl, x) |> ignore
    } else if !atom(car(zl)) {
      dsubsta(x, y, cdar(zl)) |> ignore
    }
    dsubsta(x, y, cdr(zl)) |> ignore
    zl
  }
}

///|
fn radsubst(a : Value, b : Value) -> Value raise {
  set(q_n_starexp, allsubst00(a, b, symval(q_n_starexp))) |> ignore
  if symval(q_n_starradsubst).truthy() {
    set(q_n_starexp2, allsubst00(a, b, symval(q_n_starexp2)))
  } else {
    Nil
  }
}

///|
fn spc1(x : Value) -> Value raise {
  if mlogp(x).truthy() {
    putonloglist(x)
  } else if mexptp(x).truthy() && !eq(cadr(x), q_d__pcte) {
    d_exp_form(
      mul2(
        caddr(x),
        putonloglist(list2(list3(q_p_log, q_simp, q_ratsimp), cadr(x))),
      ),
    )
  } else {
    x
  }
}

///|
fn putonloglist(l : Value) -> Value raise {
  if !memalike(l, symval(q_n_starloglist)).truthy() {
    set(q_n_starloglist, cons(l, symval(q_n_starloglist))) |> ignore
  }
  l
}

///|
fn spc2(p : Value) -> Value raise {
  radsubst(rform(cdr(p)), rform(car(p))) |> ignore
  dsubsta(cdr(p), car(p), symval(q_varlist))
}

///|
/// CONVERTS FACTORED RFORM LOGAND TO SUM OF LOGS
fn spc2a(x : Value) -> Value raise {
  let sum = mapcar(y => spc2b(y), x)
  if cdr(sum).truthy() {
    cons(list1(q_mplus), sum)
  } else {
    car(sum)
  }
}

///|
fn spc2b(x : Value) -> Value raise {
  let log = list2(
    list([q_p_log, q_simp, q_ratsimp, q_irreducible]),
    pdis(car(x)),
  )
  if equal(Fix(1L), cdr(x)) {
    log
  } else {
    list3(list1(q_mtimes), cdr(x), log)
  }
}

///|
fn spc3(x : Value, v : Value) -> Value raise {
  if !m_dolexp_q(x).truthy() {
    return Nil
  }
  let y = caddr(x)
  if atom(y) {
    return Nil
  }
  let var_ = symval(q_n_starvar)
  let y = expand1(
    if var_.truthy() {
      d_partfrac(y, var_)
    } else {
      y
    },
    Fix(10L),
    Fix(10L),
  )
  if !mplusp(y).truthy() {
    return Nil
  }
  let y = cons(
    list1(q_mtimes),
    mapcar(z => d_ratsimp(d_exp_form(z), Nil), cdr(y)),
  )
  radsubst(rform(y), rget(v)) |> ignore
  dsubsta(y, x, symval(q_varlist))
}

///|
fn spc4(x : Value) -> Value raise {
  if m_dolexp_q(x).truthy() &&
    !memalike(caddr(x), symval(q_n_starv)).truthy() {
    set(q_n_starv, cons(caddr(x), symval(q_n_starv)))
  } else {
    Nil
  }
}

///|
fn rzcontent(r : Value) -> Value raise {
  let a = pcontent(car(r))
  let mut c1 = car(a)
  let mut p = cadr(a)
  let b = pcontent(cdr(r))
  let c2 = car(b)
  let q = cadr(b)
  if rat3a__pminusp(p) {
    p = pminus(p)
    c1 = num_neg(c1)
  }
  cons(cons(c1, c2), cons(p, q))
}

// The GCDLIST looks like ((GCM1pair occurrencepair11 occurrencepair12 ...)
// ... (GCMnpair occurrencepairn1 occurrencepairn2 ...)) where GCMpairs are
// lists of ratforms and prefix forms for the greatest common multiple of
// the occurrencepairs. Each of these pairs is a list of a ratform and a
// prefix form. The prefix form is a pointer into the varlist. The
// occurrences are exponents of the base %E.

///|
fn spc5(vl : Value, oldvarlist : Value, oldgenvar : Value) -> Value raise {
  let bs = bind_all([(q_varlist, Nil), (q_genvar, Nil)])
  defer unbind_all(bs)
  let mut gcdlist : Value = Nil
  for v in vl.iter() {
    let rz = rzcontent(rform(v))
    let c1 = caar(rz)
    let c = cdar(rz)
    let r = cdr(rz)
    let g = assoc_equal(r, gcdlist)
    if ratmac__pz(c1) {
      ()
    } else if g.truthy() {
      rplaca(cdr(g), plcm(c, cadr(g))) |> ignore
      rplacd(cdr(g), cons(list2(d_exp_form(div_star(v, c1)), c), cddr(g)))
      |> ignore
    } else {
      gcdlist = cons(
        list3(r, c, list2(d_exp_form(div_star(v, c1)), c)),
        gcdlist,
      )
    }
  }
  for g in gcdlist.iter() {
    let rd = rdis(car(g))
    if mlogp(rd).truthy() && memalike(cadr(rd), oldvarlist).truthy() {
      rplacd(cdr(g), cons(list2(cadr(rd), Fix(1L)), cddr(g))) |> ignore
    }
    rplaca(g, d_exp_form(div(rd, cadr(g)))) |> ignore
  }
  spc5b(gcdlist, oldvarlist, oldgenvar)
}

///|
fn spc5b(v : Value, varlist : Value, genvar : Value) -> Value raise {
  let bs = bind_all([(q_varlist, varlist), (q_genvar, genvar)])
  defer unbind_all(bs)
  for l in v.iter() {
    for x in cddr(l).iter() {
      if !equal(cadr(l), cadr(x)) {
        radsubst(
          ratexpt(rform(car(l)), quot(cadr(l), cadr(x))),
          rform(car(x)),
        )
        |> ignore
      }
    }
  }
  cons(symval(q_varlist), symval(q_genvar))
}

///|
fn spc7(x : Value) -> Value raise {
  let x = if eq(x, q_d__pcti) {
    list3(list1(q_mexpt), Fix(-1L), list3(list1(q_rat), Fix(1L), Fix(2L)))
  } else {
    x
  }
  if mexptp(x).truthy() && ratnump(caddr(x)).truthy() {
    let rad = rform(x)
    let rbase = rform(cadr(x))
    let expon = caddr(x)
    radsubst(ratexpt(rbase, cadr(expon)), ratexpt(rad, caddr(expon)))
  } else {
    Nil
  }
}

///|
/// bad -> good
fn goodform(l : Value) -> Value raise {
  let acc = Collector::new()
  let mut p = l
  while p is Cons(_) {
    acc.add(cons(car(p), cadr(p)))
    p = cddr(p)
  }
  acc.result()
}

///|
fn factorlogs(l : Value) -> Value raise {
  let mut l = l
  let mut negl : Value = Nil
  let mut posl : Value = Nil
  let mut maxpl : Value = Nil
  let mut maxnl : Value = Nil
  let mut maxn : Value = Nil
  for log in l.iter() {
    let log = cons(
      log,
      goodform(
        ratfact(rform(radcan1(cadr(log), symval(q_n_starvar))), q_pfactor),
      ),
    )
    if equal(caadr(log), Fix(-1L)) {
      negl = cons(log, negl)
    } else {
      posl = cons(log, posl)
    }
  }
  negl = flsort(negl)
  posl = flsort(posl)
  l = append(negl, posl)
  negl = mapcar(x => cdr(x), negl)
  posl = mapcar(x => cdr(x), posl)
  let minus_one = list1(cons(Fix(-1L), Fix(1L)))
  // label 0 = a, 1 = b
  let mut lbl = 0
  while true {
    if lbl == 0 {
      negl = nrat4__delete_equal(minus_one, negl)
      if negl is Nil {
        return mapc(x => rplacd(x, spc2a(cdr(x))) |> ignore, l)
      }
      maxnl = flmaxl(negl)
      maxn = caaar(maxnl)
      lbl = 1
    }
    // b
    maxpl = flmaxl(posl)
    if maxpl.truthy() && flgreat(caaar(maxpl), maxn).truthy() {
      posl = flred(posl, caaar(maxpl))
      continue
    } else if maxpl.truthy() && !equal(caaar(maxpl), maxn) {
      maxpl = Nil
    }
    if flevenp(maxpl).truthy() && !flevenp(maxnl).truthy() {
      for fp in maxnl.iter() {
        let mut fp = fp
        rplaca(car(fp), pminus(caar(fp))) |> ignore
        if oddp(cdar(fp)) {
          fp = nrat4__delete_equal(cons(Fix(-1L), Fix(1L)), fp)
          negl = nrat4__delete_equal(fp, negl)
          if cdr(fp).truthy() {
            posl = cons(cdr(fp), posl)
          }
        }
      }
    } else {
      posl = flred(posl, maxn)
      negl = flred(negl, maxn)
    }
    lbl = 0
  }
  Nil
}

///|
fn flevenp(pl : Value) -> Value raise {
  for l in pl.iter() {
    if oddp(cdar(l)) {
      return Nil
    }
  }
  t
}

///|
fn flred(pl : Value, p : Value) -> Value raise {
  let mut x = pl
  while x is Cons(_) {
    if equal(p, caaar(x)) {
      rplaca(x, cdar(x)) |> ignore
    }
    x = cdr(x)
  }
  nrat4__delete_equal(Nil, pl)
}

///|
/// Lists of factored polys.
fn flmaxl(fpl : Value) -> Value raise {
  if fpl is Nil {
    Nil
  } else {
    let mut maxl = list1(car(fpl))
    let mut ll = cdr(fpl)
    while !(ll is Nil) {
      maxl = if equal(caaar(maxl), caaar(ll)) {
        cons(car(ll), maxl)
      } else if flgreat(caaar(maxl), caaar(ll)).truthy() {
        maxl
      } else {
        list1(car(ll))
      }
      ll = cdr(ll)
    }
    maxl
  }
}

///|
fn flsort(fpl : Value) -> Value raise {
  mapc(
    x => rplacd(
      x,
      sort_list(cdr(x), (a, b) => flgreat(car(a), car(b)).truthy()),
    )
    |> ignore,
    fpl,
  )
}

///|
fn nmt(p : Value, any : Value) -> Value raise {
  if atom(p) {
    if any.truthy() || minusp(p) {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else {
    let mut s : Value = Fix(0L)
    let mut lp = cdr(p)
    while lp is Cons(_) {
      s = num_add(s, nmt(cadr(lp), any))
      lp = cddr(lp)
    }
    s
  }
}

///|
fn nmterms(p : Value) -> Value raise {
  if equal(p, Fix(-1L)) {
    cons(Fix(0L), Fix(0L))
  } else {
    cons(nmt(p, Nil), nmt(p, t))
  }
}

///|
fn flgreat(p : Value, q : Value) -> Value raise {
  let pn = nmterms(p)
  let qn = nmterms(q)
  if ratmac__gt(car(pn), car(qn)) {
    t
  } else if ratmac__lt(car(pn), car(qn)) {
    Nil
  } else if ratmac__gt(cdr(pn), cdr(qn)) {
    t
  } else if ratmac__lt(cdr(pn), cdr(qn)) {
    Nil
  } else {
    flgreat1(p, q)
  }
}

///|
fn flgreat1(p : Value, q : Value) -> Value raise {
  if numberp(p) {
    if numberp(q) {
      lbool(num_gt(p, q))
    } else {
      Nil
    }
  } else if numberp(q) {
    t
  } else if ratmac__pgp(car(p), car(q)) {
    t
  } else if ratmac__pgp(car(q), car(p)) {
    Nil
  } else if ratmac__gt(cadr(p), cadr(q)) {
    t
  } else if ratmac__lt(cadr(p), cadr(q)) {
    Nil
  } else {
    flgreat1(caddr(p), caddr(q))
  }
}

///|
fn init_nrat4() -> Unit raise {
  set(q_n_starradsubst, Nil) |> ignore
  set(q_n_starvar, Nil) |> ignore
  putprop(q_d_radcan, t, q_evfun) |> ignore
}
