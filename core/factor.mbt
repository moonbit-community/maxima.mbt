// Port of src/factor.lisp (part 1): the FACTOR package.
//
// THIS IS THE NEW FACTORING PACKAGE.  The function FACTOR72 takes a
// primitive square-free poly as input; the output is a list of factors.
// The function FACTOR1972 is above FACTOR72 and it takes care of repeated
// factors over the Gaussian integers before calling FACTOR72.  The function
// Z1 takes two factors in one variable and one poly in several variables as
// input; Z1 takes these factors in one variable and builds out of them two
// factors of the given poly in several variables.
//
// Specials of this file (declare-top): *stop* trl* *xn sharpcont subvar1
// anotype invc fctc subval1 var mcflag alcinv *ab* monic* intbs* *prime *g*
// modulu* plim listelm many* *inl3 *sharpa *sharpb limk split* alc ind *odr*
// *i* elm ne res fact1 fact2 subvar subval ovarlist valist dlp df1 df2 fcs*
// uu* *p*, plus the defvars *afixn* *fctcfixn* *invcfixn* *negflag*.

///|
/// `(ignore-rat-err body)`: the value of BODY, or NIL if it throws to
/// RAT-ERR.
fn factor__ignore_rat_err(f : () -> Value raise) -> Value raise {
  let mut ok = false
  let r = catch_tag(q_rat_err, () => {
    let v = f()
    ok = true
    v
  })
  if ok {
    r
  } else {
    Nil
  }
}

///|
fn primcyclo(n : Value) -> Value raise {
  let g = gensym(prefix="PRIMCYCLO-")
  let c = Collector::new()
  let mut l = cfactorw(n)
  while !(l is Nil) {
    let cc = car(l)
    let e = to_int(cadr(l))
    for _ in 0..<e {
      c.add(cc)
    }
    l = cddr(l)
  }
  let nl = c.result()
  let b = bind(q_ear_g, g)
  defer unbind(b)
  set(g, Fix(0L)) |> ignore
  let res = cyclotomic(list2(n, nl))
  if consp(res) {
    p__terms(res)
  } else if eql(Fix(0L), res) {
    Nil
  } else {
    list2(Fix(0L), res)
  }
}

///|
fn factxn_plus_1(p : Value) -> Value raise {
  let bs = bind_all([(q_ear_g, car(p)), (q_d_factorflag, t)])
  defer unbind_all(bs)
  if equal(Fix(1L), cadr(p)) {
    list1(p)
  } else if equal(cddr(p), list3(Fix(1L), Fix(0L), Fix(1L))) {
    factxn_plus1(cadr(p))
  } else if equal(cddr(p), list3(Fix(1L), Fix(0L), Fix(-1L))) {
    factxn_1(cadr(p))
  } else {
    Nil
  }
}

///|
fn cfactorw(n : Value) -> Value raise {
  with_special(q_d_factorflag, t, () => cfactor(n))
}

///|
fn factxn_1(n : Value) -> Value raise {
  if evenp(n) {
    let a = factxn_1(ash(n, -1))
    append(a, factxn_plus1(ash(n, -1)))
  } else {
    mapcar(x => cyclotomic(x), divisors(cfactor(n)))
  }
}

///|
fn factxn_plus1(n : Value) -> Value raise {
  if symval(q_gauss).truthy() {
    let b = bind(q_gauss, Nil)
    defer unbind(b)
    let facl = factxn_plus1(n)
    if oddp(n) {
      facl
    } else {
      let b2 = bind(q_d_gcd, q_d_subres)
      defer unbind(b2)
      let pfac = list([
        symval(q_ear_g),
        ash(n, -1),
        Fix(1L),
        Fix(0L),
        symval(q_ear_alpha),
      ])
      mapcan(q => subseq(pgcdcofacts(q, pfac), 0, end=2), facl)
    }
  } else {
    let mut m : Value = Fix(1L)
    let mut nl = reverse(cfactor(n))
    if equal(Fix(2L), cadr(nl)) {
      m = expt(Fix(2L), car(nl))
      nl = cddr(nl)
    }
    let m = list3(symval(q_ear_g), m, Fix(-1L))
    if nl is Nil {
      list1(list([symval(q_ear_g), n, Fix(1L), Fix(0L), Fix(1L)]))
    } else {
      mapcar(
        p => pabs(pcsubst(p, m, car(p))),
        mapcar(x => cyclotomic(x), divisors(reverse(nl))),
      )
    }
  }
}

///|
fn cyclp(n : Value, ind : Value) -> Value raise {
  let c = Collector::new()
  let mut i = one_minus(n)
  while !num_lt(i, Fix(0L)) {
    c.add(num_mul(ind, i))
    c.add(Fix(1L))
    i = one_minus(i)
  }
  c.result()
}

///|
fn csf(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    cons(car(l), cons(Fix(1L), csf(cdr(l))))
  }
}

///|
fn condense(l : Value) -> Value raise {
  if cdr(l) is Nil {
    l
  } else if eq(car(l), cadr(l)) {
    condense(cdr(l))
  } else {
    cons(car(l), condense(cdr(l)))
  }
}

///|
fn cyclotomic(nl : Value) -> Value raise {
  let g = symval(q_ear_g)
  if equal(Fix(1L), car(nl)) {
    return list([g, Fix(1L), Fix(1L), Fix(0L), Fix(-1L)])
  }
  let p = condense(cadr(nl))
  if cdr(p) is Nil {
    return cons(g, cyclp(car(p), expt(car(p), int(length(cadr(nl)) - 1))))
  }
  let mut num : Value = Fix(1L)
  let mut den : Value = Fix(1L)
  let n = car(nl)
  let mut dpl = divisors(csf(p))
  while !(dpl is Nil) {
    let dp = car(dpl)
    dpl = cdr(dpl)
    let p = list([g, quot(n, car(dp)), Fix(1L), Fix(0L), Fix(-1L)])
    if length(cadr(dp)) % 2 == 0 || equal(car(dp), Fix(1L)) {
      num = ptimes(p, num)
    } else {
      den = ptimes(p, den)
    }
  }
  pquotient(num, den)
}

///|
fn divisors(l : Value) -> Value raise {
  let mut l = l
  if equal(l, list2(Fix(1L), Fix(1L))) {
    l = Nil
  }
  let ans = list1(list2(Fix(1L), Nil))
  while !(l is Nil) {
    let mut u = ans
    let factor = car(l)
    let mut mult = cadr(l)
    while !zerop(mult) {
      u = mapcar(q => list2(num_mul(factor, car(q)), cons(factor, cadr(q))), u)
      nconc(ans, u) |> ignore
      mult = one_minus(mult)
    }
    l = cddr(l)
  }
  ans
}

///|
fn estcheck2(d : Value, lc : Value, c : Value) -> Value raise {
  let mut d = d
  while !(d is Nil) {
    let p = car(d)
    d = cdr(d)
    let pp = num_mul(p, p)
    if (!equal(num_rem(c, p), Fix(0L)) && !equal(num_rem(lc, pp), Fix(0L))) ||
      (!equal(num_rem(lc, p), Fix(0L)) && !equal(num_rem(c, pp), Fix(0L))) {
      return t
    }
  }
  Nil
}

///|
fn estcheck(p : Value) -> Value raise {
  if atom(p) || cddr(p) is Nil || equal(ptterm(p, Fix(0L)), Fix(0L)) {
    return Nil
  }
  let lc = cadr(p)
  let p = nreverse(cdr(oddelm(cdr(p))))
  let c = car(p)
  let d = cgcdlist(p)
  if equal(Fix(1L), d) {
    return Nil
  }
  let d = oddelm(cfactorw(d))
  estcheck2(d, lc, c)
}

///|
fn cgcdlist(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if cdr(l) is Nil {
    num_abs(car(l))
  } else if member(Fix(1L), l).truthy() || member(Fix(-1L), l).truthy() {
    Fix(1L)
  } else if cddr(l) is Nil {
    num_gcd(car(l), cadr(l))
  } else {
    cgcdlist(cons(num_gcd(car(l), cadr(l)), cddr(l)))
  }
}

///|
fn dropterms(p : Value) -> Value raise {
  if atom(p) {
    return p
  } else if !eq(car(p), symval(q_var)) {
    return kterms(p, symval(q_dlp))
  }
  let mut ans = cons(car(p), Nil)
  let mut p = cdr(p)
  while !(p is Nil) {
    let c = kterms(cadr(p), symval(q_dlp))
    if !equal(c, Fix(0L)) {
      ans = cons(c, cons(car(p), ans))
    }
    p = cddr(p)
  }
  if cdr(ans).truthy() {
    nreverse(ans)
  } else {
    Fix(0L)
  }
}

///|
fn factor__intbase_case() -> Bool {
  !symval(q_many_star).truthy() &&
  symval(q_algfac_star).truthy() &&
  !equal(symval(q_intbs_star), Fix(1L))
}

///|
fn restorelc(l : Value, lc : Value) -> Value raise {
  let bv = bind(q_var, Nil)
  defer unbind(bv)
  if equal(Fix(1L), lc) {
    if factor__intbase_case() {
      return mapcar(x => intbasehk(x), l)
    } else {
      return reverse(l)
    }
  }
  let mut r = lcprodl(l)
  let mut h : Value = Fix(1L)
  let mut l = l
  let mut ans : Value = Nil
  while !(l is Nil) {
    let d0 = car(l)
    l = cdr(l)
    set(q_var, car(d0)) |> ignore
    let deg = cadr(d0)
    let c = caddr(d0)
    let mut d = ptimes(ptimes(h, car(r)), psimp(symval(q_var), cdddr(d0)))
    if symval(q_many_star).truthy() {
      d = dropterms(d)
    }
    d = pplus(list3(symval(q_var), deg, lc), d)
    if factor__intbase_case() {
      d = intbasehk(d)
    }
    let dd = d
    ans = cons(with_special(q_modulus, Nil, () => cadr(oldcontent(dd))), ans)
    h = ptimes(h, c)
    r = cdr(r)
  }
  ans
}

///|
fn iredup(p : Value) -> Value raise {
  let bs = bind_all([(q_mm_star, Fix(1L)), (q_algfac_star, Nil)])
  defer unbind_all(bs)
  if sqfrp(p, car(p)).truthy() {
    let p = catch_tag(q_splt, () => cpber1(p))
    lbool(car(p) is Nil && cdadr(p) is Nil)
  } else {
    Nil
  }
}

///|
fn zerolp(a : Value) -> Value raise {
  lbool(every(x => zerop1(x).truthy(), a))
}

///|
/// Check if y divides x, assuming that x and y are polynomials in the same
/// variable.
fn testdivide(x : Value, y : Value) -> Value raise {
  if symval(q_algfac_star).truthy() {
    algtestd(x, y)
  } else {
    eztestdivide(x, y)
  }
}

///|
/// Check if y divides x, for general polynomials x and y (not necessarily in
/// the same variable).
fn testdivide_star(x : Value, y : Value) -> Value raise {
  if symval(q_algfac_star).truthy() {
    algtestd(x, y)
  } else {
    factor__ignore_rat_err(() => pquotient(x, y))
  }
}

///|
fn algtestd(x : Value, y : Value) -> Value raise {
  let xl = nreverse(pdegreevector(x))
  let yl = nreverse(pdegreevector(y))
  if !div_deg_chk(xl, yl, reverse(symval(q_genvar))).truthy() {
    return Nil
  }
  let x = factor__ignore_rat_err(() => rquotient(x, y))
  if x.truthy() {
    set(q_adn_star, num_mul(symval(q_adn_star), cdr(x))) |> ignore
    car(x)
  } else {
    Nil
  }
}

///|
fn div_deg_chk(xl : Value, yl : Value, gl : Value) -> Value raise {
  if gl is Nil || algv(car(gl)).truthy() {
    t
  } else if num_gt(car(yl), car(xl)) {
    Nil
  } else {
    div_deg_chk(cdr(xl), cdr(yl), cdr(gl))
  }
}

///|
/// FUU is used by systems programmers such as BMT and PAULW while debugging.
fn fuu() -> Value raise {
  set(q_tellratlist, Nil) |> ignore
  set(q_varlist, Nil) |> ignore
  set(q_genvar, Nil) |> ignore
  set(q_genpairs, Nil)
}

///|
fn linout(u : Value) -> Value raise {
  let mut u = u
  let x = car(u)
  let y = list3(x, Fix(1L), Fix(1L))
  let mut m = symval(q_modulus)
  let mut linfac : Value = Nil
  while true {
    m = one_minus(m)
    if num_lt(m, Fix(0L)) {
      return list2(u, linfac)
    } else if equal(cadr(u), Fix(1L)) {
      return list2(Fix(1L), cons(u, linfac))
    } else if zerop(pcsubsty(cmod(m), x, u)) {
      linfac = cons(
        append(
          y,
          if zerop(m) {
            Nil
          } else {
            list2(Fix(0L), cmod(num_neg(m)))
          },
        ),
        linfac,
      )
      u = car(pmodquo(u, car(linfac)))
    }
  }
  Nil
}

///|
fn onevarp(p : Value) -> Value raise {
  if symval(q_algfac_star).truthy() {
    lbool(every(x => pacoefp(x).truthy(), cdr(p)))
  } else {
    lbool(every(x => numberp(x), cdr(p)))
  }
}

///|
fn putodr(l : Value) -> Value raise {
  let mut l = l
  let mut i = 1
  let mut ans : Value = Nil
  while !(l is Nil) {
    ans = cons(cons(car(l), int(i)), ans)
    l = cdr(l)
    i += 1
  }
  ans
}

///|
fn kterms(p : Value, k : Value) -> Value raise {
  if pacoefp(p).truthy() {
    p
  } else if num_eq(k, Fix(0L)) {
    consta(p)
  } else {
    let v = car(p)
    let mut p = cdr(p)
    let mut ans : Value = Nil
    while true {
      if p is Nil {
        return Fix(0L)
      } else if num_gt(car(p), k) {
        p = cddr(p)
      } else {
        break
      }
    }
    while !(p is Nil) {
      let w = kterms(cadr(p), num_sub(k, car(p)))
      if !pzerop(w).truthy() {
        ans = nconc(ans, list2(car(p), w))
      }
      p = cddr(p)
    }
    psimp(v, ans)
  }
}

///|
fn consta(p : Value) -> Value raise {
  if pcoefp(p).truthy() || alg(p).truthy() {
    p
  } else {
    consta(ptterm(cdr(p), Fix(0L)))
  }
}

///|
/// NO LONGER USED?
fn constacl(p : Value) -> Value raise {
  if atom(p) {
    if equal(p, Fix(1L)) {
      throw_tag(q_cnt, Fix(1L))
    } else {
      list1(p)
    }
  } else if every(x => numberp(x), cdr(p)) {
    let p = oddelm(p)
    if member(Fix(1L), p).truthy() {
      throw_tag(q_cnt, Fix(1L))
    } else {
      cdr(p)
    }
  } else {
    let parts = mapcar(x => constacl(x), cdr(oddelm(p)))
    append_n(list_to_array(parts))
  }
}

///|
fn z1(poly : Value, fact1 : Value, fact2 : Value) -> Value raise {
  let bs = bind_all([
    (q_fact1, fact1),
    (q_fact2, fact2),
    (q_res, Nil),
    (q_ear_ab, Nil),
    (q_df1, Nil),
    (q_df2, Nil),
    (q_n_starsharpa, Nil),
    (q_n_starsharpb, Nil),
  ])
  defer unbind_all(bs)
  set(
    q_n_starsharpb,
    with_special(q_modulus, Nil, () => {
      set_modulus(symval(q_n_starprime)) |> ignore
      fact20(fact1, fact2, symval(q_limk))
    }),
  )
  |> ignore
  set(q_n_starsharpa, car(symval(q_n_starsharpb))) |> ignore
  set(q_n_starsharpb, cadr(symval(q_n_starsharpb))) |> ignore
  set(
    q_ear_ab,
    list1(list3(Fix(0L), symval(q_n_starsharpa), symval(q_n_starsharpb))),
  )
  |> ignore
  let steps = symval(q_dlp)
  let hsteps = ash(steps, -1)
  set(
    q_res,
    pdifference(ptimes(pmod(fact1), pmod(fact2)), pmod(poly)),
  )
  |> ignore
  let mut step : Value = Fix(0L)
  set(q_df1, fact1) |> ignore
  set(q_df2, fact2) |> ignore
  let var_ = symval(q_var)
  while true {
    // loop
    let res = symval(q_res)
    if equal(res, Fix(0L)) {
      break
    }
    step = one_plus(step)
    if num_gt(step, steps) {
      break
    }
    let mut c = if eq(car(res), var_) { cdr(res) } else { list2(Fix(0L), res) }
    let mut a : Value = Fix(0L)
    let mut b : Value = Fix(0L)
    // nextm
    while !(c is Nil) {
      let m = car(c)
      let dlr = cadr(c)
      c = cddr(c)
      let kterm = kterms(dlr, step)
      if equal(Fix(0L), kterm) {
        continue
      }
      let d = obtainabm(m)
      b = pplus(b, ptimes(car(d), kterm))
      a = pplus(a, ptimes(cadr(d), kterm))
    }
    z2(a, b, step, hsteps) |> ignore
  }
  list2(symval(q_df1), symval(q_df2))
}

///|
fn z2(a : Value, b : Value, step : Value, hsteps : Value) -> Value raise {
  if equal(a, Fix(0L)) && equal(b, Fix(0L)) {
    return Nil
  }
  let late = !num_lt(step, hsteps)
  let t1 = if late { dropterms(ptimes(a, b)) } else { ptimes(a, b) }
  let t2 = if late {
    dropterms(ptimes(symval(q_df1), b))
  } else {
    ptimes(symval(q_df1), b)
  }
  let d1 = pdifference(t1, t2)
  let t3 = if late {
    dropterms(ptimes(symval(q_df2), a))
  } else {
    ptimes(symval(q_df2), a)
  }
  let step = pdifference(d1, t3)
  set(q_res, pplus(symval(q_res), step)) |> ignore
  set(q_df1, pdifference(symval(q_df1), a)) |> ignore
  set(q_df2, pdifference(symval(q_df2), b))
}

///|
fn obtainabm(m : Value) -> Value raise {
  let ans = cdr(assoc_equal(m, symval(q_ear_ab)))
  if ans.truthy() {
    return ans
  }
  let ans = obtainab(list3(symval(q_var), m, Fix(1L)))
  set(q_ear_ab, cons(cons(m, ans), symval(q_ear_ab))) |> ignore
  ans
}

///|
fn fact20(f1 : Value, g1 : Value, limk : Value) -> Value raise {
  let bl = bind(q_limk, limk)
  defer unbind(bl)
  let mut k : Value = Fix(0L)
  let reml = ppprog(pmod(f1), pmod(g1))
  let mut a = car(reml)
  let mut b = cadr(reml)
  while true {
    // sharp
    if num_gt(k, symval(q_limk)) {
      return list2(a, b)
    }
    let pk = symval(q_modulus)
    set_modulus(num_mul(symval(q_modulus), symval(q_modulus))) |> ignore
    let f = pmod(f1)
    let g = pmod(g1)
    let h = pquo(
      pmod(pdifference(pplus(ptimes(a, f), ptimes(b, g)), Fix(1L))),
      pk,
    )
    let qlp = pmodquo(ptimes(a, h), g)
    let b1 = pplus(ptimes(b, h), ptimes(car(qlp), f))
    a = pdifference(a, pmod(pctimes(pk, cdr(qlp))))
    b = pdifference(b, pmod(pctimes(pk, b1)))
    k = one_plus(k)
  }
  Nil
}

///|
fn baselist(n : Value) -> Value raise {
  set(q_ear_i, n) |> ignore
  completevector(Nil, Fix(0L), n, symval(q_elm))
}

///|
fn inlist3(l : Value) -> Value raise {
  if l is Nil {
    set(q_n_starinl3, Nil)
  } else if zerop(car(l)) {
    cons(Fix(1L), cdr(l))
  } else if equal(car(l), Fix(1L)) {
    cons(Fix(-1L), cdr(l))
  } else {
    cons(Fix(0L), inlist3(cdr(l)))
  }
}

///|
fn newrep(p : Value) -> Value raise {
  let b = bind(q_modulus, Nil)
  defer unbind(b)
  let subvar = symval(q_subvar)
  if subvar.truthy() {
    pcsubsty(
      mapcar2(
        (a, b) => list([a, Fix(1L), Fix(1L), Fix(0L), b]),
        subvar,
        symval(q_subval),
      ),
      subvar,
      p,
    )
  } else {
    p
  }
}

///|
fn oldrep(p : Value) -> Value raise {
  let b = bind(q_modulus, Nil)
  defer unbind(b)
  let subvar = symval(q_subvar)
  if subvar.truthy() {
    pcsubsty(
      mapcar2(
        (a, b) => list([a, Fix(1L), Fix(1L), Fix(0L), num_neg(b)]),
        subvar,
        symval(q_subval),
      ),
      subvar,
      p,
    )
  } else {
    p
  }
}

///|
fn completevector(l : Value, n : Value, m : Value, v : Value) -> Value raise {
  let mut l = l
  let mut i = m
  while !num_eq(i, n) {
    l = cons(v, l)
    i = one_minus(i)
  }
  l
}

///|
/// Special variable *ODR* contains order of nesting of variables in c.
fn degvector(l : Value, n : Value, c : Value) -> Value raise {
  let mut c = c
  let mut j : Value = Nil
  while true {
    // bk
    if numberp(c) {
      return list1(completevector(l, n, symval(q_nn_star), Fix(0L)))
    }
    j = cdr(assoc_equal(car(c), symval(q_ear_odr)))
    // IN CASE (CAR C) IS ALGEBRAIC
    if j is Nil {
      c = Fix(0L)
      continue
    }
    break
  }
  c = cdr(c)
  let lf = completevector(l, n, j, Fix(0L))
  let mut ans : Value = Nil
  while !(c is Nil) {
    ans = nconc(degvector(cons(car(c), lf), one_plus(j), cadr(c)), ans)
    if symval(q_ear_mx).truthy() {
      ans = list1(rat3d__maxlist_in_place(ans))
    } else if symval(q_ear_min).truthy() {
      ans = list1(rat3d__minlist_in_place(ans))
    }
    c = cddr(c)
  }
  ans
}

///|
fn union1(a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut ans = b
  while !(a is Nil) {
    if member_equal(car(a), ans) is Nil {
      ans = cons(car(a), ans)
    }
    a = cdr(a)
  }
  ans
}

///|
fn obtainab(u : Value) -> Value raise {
  let c = pmod(u)
  let ql = pmodquo(ptimes(symval(q_n_starsharpa), c), symval(q_fact2))
  list2(
    cdr(ql),
    pmod(
      pplus(
        ptimes(car(ql), symval(q_fact1)),
        ptimes(symval(q_n_starsharpb), c),
      ),
    ),
  )
}

///|
fn pcdifconc(v : Value, j : Value) -> Value raise {
  let mut l = v
  while !(cdr(l) is Nil) {
    if num_eq(cadr(l), Fix(0L)) {
      if num_eq(j, Fix(0L)) {
        rplacd(l, Nil) |> ignore
      } else {
        rplaca(cddr(l), j) |> ignore
      }
      return v
    }
    l = cddr(l)
  }
  if !num_eq(j, Fix(0L)) {
    rplacd(l, list2(Fix(0L), j)) |> ignore
  }
  v
}

///|
fn orde(a : Value, l : Value) -> Value raise {
  if l is Nil {
    list1(a)
  } else if num_lt(a, car(l)) {
    cons(a, l)
  } else {
    cons(car(l), orde(a, cdr(l)))
  }
}

///|
fn pquo(x : Value, y : Value) -> Value raise {
  with_special(q_modulus, Nil, () => pquotient(x, y))
}

///|
/// Maintains order of list x.
fn intersect(x : Value, y : Value) -> Value raise {
  if x is Nil {
    Nil
  } else if member_equal(car(x), y).truthy() {
    cons(car(x), intersect(cdr(x), y))
  } else {
    intersect(cdr(x), y)
  }
}

///|
/// Like APL IOTA function.
fn index_star(k : Value) -> Value raise {
  if num_lt(k, Fix(2L)) {
    list1(Fix(1L))
  } else {
    cons(k, index_star(one_minus(k)))
  }
}

///|
/// Sets plim to a power of p1 likely to be a large enough modulus for
/// polynomial u; returns limk, where plim = p1^(2^(limk+1)).
fn klim(u : Value, p1 : Value) -> Value raise {
  let mut p1 = p1
  let mut bcoef = num_mul(Fix(5L), maxcoefficient(u))
  if symval(q_algfac_star).truthy() {
    bcoef = num_mul(bcoef, symval(q_intbs_star))
  }
  if num_lt(bcoef, Fix(10000L)) {
    bcoef = Fix(20000L)
  }
  set(q_limk, Fix(0L)) |> ignore
  while true {
    p1 = num_mul(p1, p1)
    if num_gt(p1, bcoef) {
      set(q_plim, p1) |> ignore
      return symval(q_limk)
    }
    set(q_limk, one_plus(symval(q_limk))) |> ignore
  }
  Nil
}

///|
fn cpberl(u : Value) -> Value raise {
  let ql = catch_tag(q_splt, () => cpber1(u))
  let u = caddr(ql)
  let d = car(ql)
  let ql = cadr(ql)
  if ql is Nil {
    d
  } else if cdr(ql) is Nil {
    cons(u, d)
  } else {
    append(
      d,
      if symval(q_ear_alpha).truthy() ||
        num_gt(symval(q_modulus), Fix(70L)) {
        cpbgzass(ql, pmod(u), int(length(ql)))
      } else {
        cpbg(ql, pmod(u), int(length(ql)))
      },
    )
  }
}

///|
/// Returns a list of monomials in G of degree less than N.
fn powrs(g : Value, n : Value) -> Value raise {
  let mut ans = list1(Fix(1L))
  let n = to_int(n)
  for i in 1..<n {
    ans = cons(list3(g, int(i), Fix(1L)), ans)
  }
  ans
}

///|
/// Finds polynomials A and B such that A*F+B*G=1 when MODULUS is non-NIL.
/// Same algorithm as INVMOD.
fn ppprog(f : Value, g : Value) -> Value raise {
  let (g1, f1, s) = if num_gt(cadr(g), cadr(f)) {
    (g, f, false)
  } else {
    (f, g, true)
  }
  let mut ql = pmodquo(g1, f1)
  let mut a1 : Value = Fix(1L)
  let mut b1 : Value = Fix(0L)
  let mut a2 = pminus(car(ql))
  let mut b2 : Value = Fix(1L)
  let mut r1 = f1
  let mut r2 = cdr(ql)
  while !(numberp(r2) ||
    (symval(q_ear_alpha).truthy() && alg(r2).truthy())) {
    ql = pmodquo(r1, r2)
    let ap = pdifference(a1, ptimes(car(ql), a2))
    let bp = pdifference(b1, ptimes(car(ql), b2))
    r1 = r2
    r2 = cdr(ql)
    a1 = a2
    b1 = b2
    a2 = ap
    b2 = bp
  }
  // end
  let ans = if pzerop(r2).truthy() {
    let lc = caddr(r1)
    if equal(Fix(1L), lc) {
      list2(b1, a1)
    } else {
      list2(car(pmodquo(b1, lc)), car(pmodquo(a1, lc)))
    }
  } else {
    list2(car(pmodquo(b2, r2)), car(pmodquo(a2, r2)))
  }
  if !s {
    reverse(ans)
  } else {
    ans
  }
}

///|
fn zff(v : Value, f : Value, g : Value) -> Value raise {
  if symval(q_many_star).truthy() {
    z1(v, f, g)
  } else {
    fact2z(v, f, g, symval(q_limk))
  }
}

///|
fn zfact(u : Value, fl : Value, limk : Value, many_star : Value) -> Value raise {
  let bs = bind_all([(q_limk, limk), (q_many_star, many_star), (q_fcs_star, Nil)])
  defer unbind_all(bs)
  if many_star.truthy() {
    set_modulus(symval(q_plim)) |> ignore
    let degs = mapcar(x => multideg(x), cdr(oddelm(u)))
    set(q_dlp, reduce((a, b) => num_max(a, b), degs)) |> ignore
  }
  if length(fl) == 1 {
    return list1(u)
  }
  let prodl = fsplit(fl, q_v)
  zfactsplit(prodl, u) |> ignore
  symval(q_fcs_star)
}

///|
fn zfactsplit(fl : Value, v : Value) -> Value raise {
  if cdr(fl) is Nil {
    set(q_fcs_star, cons(v, symval(q_fcs_star)))
  } else if cddr(fl) is Nil {
    let fl = cadr(fl)
    let z = zff(v, car(fl), cadr(fl))
    set(q_fcs_star, nconc(z, symval(q_fcs_star)))
  } else {
    let fl = cdr(fl)
    let d = zff(v, caar(fl), caadr(fl))
    zfactsplit(car(fl), car(d)) |> ignore
    zfactsplit(cadr(fl), cadr(d))
  }
}

///|
fn split2(l : Value) -> Value raise {
  let s = nthcdr(to_int(ash(int(length(l)), -1)) - 1, l)
  set(q_dn_star, copy_list(cdr(s))) |> ignore
  rplacd(s, Nil) |> ignore
  set(q_nn_star, l)
}

///|
fn fsplit(l : Value, ind : Value) -> Value raise {
  let bs = bind_all([(q_nn_star, Nil), (q_dn_star, Nil)])
  defer unbind_all(bs)
  if cdr(l) is Nil {
    return l
  } else if cddr(l) is Nil {
    return list2(apply(q_ptimes, l), l)
  }
  split2(l) |> ignore
  set(q_nn_star, fsplit(symval(q_nn_star), Nil)) |> ignore
  set(q_dn_star, fsplit(symval(q_dn_star), Nil)) |> ignore
  let nn = symval(q_nn_star)
  let dn = symval(q_dn_star)
  list3(if ind.truthy() { ind } else { ptimes(car(nn), car(dn)) }, nn, dn)
}

// This page contains routines changed for non-monic hack.

///|
fn pexptmod(p : Value, n : Value, q : Value) -> Value raise {
  if pcoefp(p).truthy() {
    return cexpt(p, n)
  }
  let mut n = n
  let q = cdr(q)
  let x = car(p)
  let mut p = p
  let mut u : Value = Nil
  let mut skip_a = false
  if oddp(n) {
    u = pgcd1(cdr(p), q)
    p = u
    skip_a = true
  } else {
    u = list2(Fix(0L), Fix(1L))
    p = cdr(p)
  }
  while true {
    if !skip_a {
      // a
      p = pgcd1(p, q)
    }
    skip_a = false
    // b
    n = ash(n, -1)
    if zerop(n) {
      return cons(x, u)
    }
    p = ptimes1(p, p)
    if oddp(n) {
      u = pgcd1(ptimes1(u, p), q)
    }
  }
  Nil
}

///|
fn sqfrp(u : Value, var_ : Value) -> Value raise {
  let bv = bind(q_var, var_)
  defer unbind(bv)
  if equal(Fix(0L), ptterm(cdr(u), Fix(0L))) &&
    equal(Fix(0L), ptterm(cdr(u), Fix(1L))) {
    Nil
  } else if onevarp(u).truthy() {
    let u = pgcd(u, pderivative(u, var_))
    if numberp(u) {
      t
    } else {
      alg(u)
    }
  } else {
    quick_sqfr_check(u, var_)
  }
}
