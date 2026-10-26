// Port of src/rat3c.lisp: the new Rational Function Package, part 3.
// The GCD routines and their supporting functions.

///|
fn cgcd(a : Value, b : Value) -> Value raise {
  if symval(q_modulus).truthy() {
    Fix(1L)
  } else if symval(q_d_keepfloat).truthy() && (floatp(a) || floatp(b)) {
    Fix(1L)
  } else {
    num_gcd(a, b)
  }
}

///|
fn pquotientchk(a : Value, b : Value) -> Value raise {
  if equal(b, Fix(1L)) {
    a
  } else {
    pquotient(a, b)
  }
}

///|
/// Divides polynomial X by polynomial Y, returning NIL instead of raising
/// "quotient by polynomial of higher degree".
fn pquotientchk_safe(x : Value, y : Value) -> Value raise {
  ratmac__ignore_rat_err(() => pquotientchk(x, y))
}

///|
fn ptimeschk(a : Value, b : Value) -> Value raise {
  if equal(a, Fix(1L)) {
    b
  } else if equal(b, Fix(1L)) {
    a
  } else {
    ptimes(a, b)
  }
}

///|
fn pfloatp(x : Value) -> Value raise {
  catch_tag(q_float, () => if atom(x) { lbool(floatp(x)) } else { pfloatp1(x) })
}

///|
fn pfloatp1(x : Value) -> Value raise {
  let mut l = cdr(x)
  while l is Cons(_) {
    let q = car(l)
    if atom(q) {
      if floatp(q) {
        throw_tag(q_float, t) |> ignore
      }
    } else {
      pfloatp1(q) |> ignore
    }
    l = cdr(l)
  }
  Nil
}

///|
fn pgcd(x : Value, y : Value) -> Value raise {
  let x = car(pgcda(x, y, Nil))
  if rat3a__pminusp(x) {
    pminus(x)
  } else if symval(q_modulus).truthy() {
    monize(x)
  } else {
    x
  }
}

///|
fn plcm(x : Value, y : Value) -> Value raise {
  let x = pgcdcofacts(x, y)
  ptimes(car(x), ptimes(cadr(x), caddr(x)))
}

///|
fn plcmcofacts(x : Value, y : Value) -> Value raise {
  let x = pgcdcofacts(x, y)
  list3(ptimes(car(x), ptimes(cadr(x), caddr(x))), caddr(x), cadr(x))
}

///|
/// Returns the list (gcd xx yy alg) where x * y = gcd^2 * xx * yy / alg^2
/// and alg is non-nil only when $algebraic is true.
fn pgcdcofacts(x : Value, y : Value) -> Value raise {
  let mut a = pgcda(x, y, t)
  if cdr(a).truthy() {
    return a
  }
  a = car(a)
  if equal(a, Fix(1L)) {
    list3(Fix(1L), x, y)
  } else if symval(q_d_algebraic).truthy() && !atom(a) {
    let g = a
    let x = rquotient(x, a)
    let y = rquotient(y, a)
    let a = pgcdcofacts(cdr(x), cdr(y))
    cons(
      g,
      list3(
        ptimes(car(x), caddr(a)),
        ptimes(car(y), cadr(a)),
        ptimes(cadr(a), cdr(y)),
      ),
    )
  } else if eq(a, x) {
    list3(x, Fix(1L), pquotient(y, x))
  } else if eq(a, y) {
    list3(a, pquotient(x, y), Fix(1L))
  } else {
    list3(a, pquotient(x, a), pquotient(y, a))
  }
}

///|
fn rat3c__oldgcd_with(gcd_ : Value, x : Value, y : Value) -> Value raise {
  with_special(q_d_gcd, gcd_, () => list1(oldgcd(x, y)))
}

///|
fn pgcda(x : Value, y : Value, cofac_q : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let gcdv = symval(q_d_gcd)
  if !gcdv.truthy() {
    return list3(Fix(1L), x, y)
  }
  if symval(q_d_keepfloat).truthy() &&
    (pfloatp(x).truthy() || pfloatp(y).truthy()) {
    if atom(x) || atom(y) {
      return list3(Fix(1L), x, y)
    }
    let mut a = car(ptermcont(x))
    if atom(a) {
      return list3(Fix(1L), x, y)
    }
    a = pgcd(a, car(ptermcont(y)))
    if atom(a) {
      return list3(Fix(1L), x, y)
    }
    return list1(a)
  }
  if atom(x) {
    if atom(y) {
      let a = cgcd(x, y)
      // (CQUOTIENT 0 0) = 0
      return cons(
        a,
        if cofac_q.truthy() {
          list2(cquotient(x, a), cquotient(y, a))
        } else {
          Nil
        },
      )
    } else if zerop(x) {
      return list3(y, x, Fix(1L))
    } else {
      return list1(pcontent1(cdr(y), x))
    }
  }
  if atom(y) {
    if zerop(y) {
      return list3(x, Fix(1L), y)
    } else {
      return list1(pcontent1(cdr(x), y))
    }
  }
  if equal(x, y) {
    return list3(x, Fix(1L), Fix(1L))
  }
  if symval(q_d_ratfac).truthy() {
    let (a, b, c) = fpgcdco(x, y)
    return list3(a, b, c)
  }
  if !eq(car(x), car(y)) {
    return list1(
      if ratmac__pgp(car(x), car(y)) {
        oldcontent1(cdr(x), y)
      } else {
        oldcontent1(cdr(y), x)
      },
    )
  }
  {
    let r1 = ptermcont(x)
    let a = car(r1)
    x = cadr(r1)
    let r2 = ptermcont(y)
    let c = car(r2)
    y = cadr(r2)
    if !(equal(a, Fix(1L)) && equal(c, Fix(1L))) {
      return mapcar2(
        (p, q) => ptimes(p, q),
        monomgcdco(a, c, cofac_q),
        pgcda(x, y, cofac_q),
      )
    }
  }
  if !symval(q_d_algebraic).truthy() && !symval(q_modulus).truthy() {
    let lvf = lin_var_find(
      nreverse(pdegreevector(x)),
      nreverse(pdegreevector(y)),
      reverse(symval(q_genvar)),
    )
    if lvf.truthy() {
      let a = car(lvf)
      let c = cdr(lvf)
      if ratmac__eqn(a, Fix(1L)) {
        return linhack(x, y, car(c), cadr(c), cofac_q)
      } else {
        let a = linhack(y, x, a, cadr(c), cofac_q)
        if cdr(a).truthy() {
          rplacd(a, nreverse(cdr(a))) |> ignore
        }
        return a
      }
    }
  }
  if eq(gcdv, q_d_spmod) {
    if !cofac_q.truthy() && (palgp(x).truthy() || palgp(y).truthy()) {
      rat3c__oldgcd_with(q_d_subres, x, y)
    } else {
      list1(zgcd(x, y))
    }
  } else if eq(gcdv, q_d_subres) {
    list1(oldgcd(x, y))
  } else if eq(gcdv, q_d_algebraic) {
    if palgp(x).truthy() || palgp(y).truthy() {
      rat3c__oldgcd_with(q_d_subres, x, y)
    } else {
      with_special(q_d_gcd, q_d_spmod, () => list1(zgcd(x, y)))
    }
  } else if eq(gcdv, q_d_ez) {
    if palgp(x).truthy() || palgp(y).truthy() {
      // EZGCD2 may loop infinitely on algebraic variables - switch to OLDGCD.
      rat3c__oldgcd_with(q_d_subres, x, y)
    } else {
      ezgcd2(x, y)
    }
  } else if eq(gcdv, q_d_red) {
    list1(oldgcd(x, y))
  } else if eq(gcdv, q_d_mod) {
    if palgp(x).truthy() || palgp(y).truthy() {
      // NEWGCD gcd may loop infinitely on algebraic variables - switch to OLDGCD.
      rat3c__oldgcd_with(q_d_subres, x, y)
    } else {
      newgcd(x, y, symval(q_modulus))
    }
  } else if memq(gcdv, symval(q_ear_gcdl)) is Nil {
    merr("gcd: 'gcd' variable must be one of ~M; found: ~M", [
      symval(q_ear_gcdl),
      gcdv,
    ])
  } else {
    list3(Fix(1L), x, y)
  }
}

///|
fn monomgcdco(p : Value, q : Value, cofac_q : Value) -> Value raise {
  let gcd_ = monomgcd(p, q)
  cons(
    gcd_,
    if cofac_q.truthy() {
      list2(pquotient(p, gcd_), pquotient(q, gcd_))
    } else {
      Nil
    },
  )
}

///|
fn monomgcd(p : Value, q : Value) -> Value raise {
  if atom(p) || atom(q) {
    Fix(1L)
  } else if eq(car(p), car(q)) {
    list3(car(p), num_min(cadr(p), cadr(q)), monomgcd(caddr(p), caddr(q)))
  } else if ratmac__pgp(car(p), car(q)) {
    monomgcd(caddr(p), q)
  } else {
    monomgcd(p, caddr(q))
  }
}

///|
fn linhack(
  pol1 : Value,
  pol2 : Value,
  nonlindeg : Value,
  var2 : Value,
  cofac_q : Value,
) -> Value raise {
  let bp = bothprodcoef(make_poly(var2), pol1)
  let mut coeff11 = car(bp)
  let mut coeff12 = cdr(bp)
  let gcdab = if ratmac__pz(coeff12) { coeff11 } else { pgcd(coeff11, coeff12) }
  if equal(gcdab, Fix(1L)) {
    coeff11 = testdivide(pol2, pol1)
    if coeff11.truthy() {
      return list3(pol1, Fix(1L), coeff11)
    } else {
      return list3(Fix(1L), pol1, pol2)
    }
  }
  let rpol1 = pquotient(pol1, gcdab)
  let lc = linhackcontent(var2, pol2, nonlindeg)
  let mut gcdcd = car(lc)
  let rpol2 = cadr(lc)
  if equal(gcdcd, Fix(1L)) {
    coeff12 = testdivide_star(rpol2, rpol1)
    if coeff12.truthy() {
      return list3(rpol1, gcdab, coeff12)
    } else {
      return list3(Fix(1L), pol1, pol2)
    }
  }
  if cofac_q.truthy() {
    let co = pgcdcofacts(gcdab, gcdcd)
    let gcdcoef = car(co)
    coeff11 = cadr(co)
    coeff12 = caddr(co)
    gcdcd = testdivide_star(rpol2, rpol1)
    if gcdcd.truthy() {
      list3(ptimes(gcdcoef, rpol1), coeff11, ptimes(coeff12, gcdcd))
    } else {
      list3(gcdcoef, ptimes(coeff11, rpol1), ptimes(coeff12, rpol2))
    }
  } else {
    let gcdcoef = pgcd(gcdcd, gcdab)
    if testdivide_star(rpol2, rpol1).truthy() {
      list1(ptimes(gcdcoef, rpol1))
    } else {
      list1(gcdcoef)
    }
  }
}

///|
fn lin_var_find(a : Value, b : Value, c : Value) -> Value raise {
  let mut varl = c
  let mut degl1 = a
  let mut degl2 = b
  while !(degl1 is Nil || degl2 is Nil) {
    if equal(num_min(car(degl1), car(degl2)), Fix(1L)) {
      return list3(car(degl1), car(degl2), car(varl))
    }
    varl = cdr(varl)
    degl1 = cdr(degl1)
    degl2 = cdr(degl2)
  }
  Nil
}

///|
fn linhackcontent(var2 : Value, pol : Value, nonlindeg : Value) -> Value raise {
  let mut npol = pol
  let mut gcd_ : Value = Nil
  let mut i = nonlindeg
  while !ratmac__eqn(i, Fix(0L)) {
    let r = bothprodcoef(list3(var2, i, Fix(1L)), npol)
    let coef = car(r)
    npol = cdr(r)
    if !ratmac__pz(coef) {
      gcd_ = if gcd_ is Nil { coef } else { pgcd(coef, gcd_) }
      if equal(gcd_, Fix(1L)) {
        return list2(Fix(1L), pol)
      }
    }
    i = num_sub(i, Fix(1L))
  }
  gcd_ = pgcd(gcd_, npol)
  list2(gcd_, pquotient(pol, gcd_))
}

// THIS IS THE REDUCED POLYNOMIAL REMAINDER SEQUENCE GCD (COLLINS')

///|
/// Only called from PGCDA.
fn oldgcd(x : Value, y : Value) -> Value raise {
  let r = oldcontent(x)
  let x = car(r)
  let mut u = cadr(r)
  let r = oldcontent(y)
  let y = car(r)
  let mut v = cadr(r)
  let egcd = num_gcd(pgcdexpon(u), pgcdexpon(v))
  if ratmac__gt(egcd, Fix(1L)) {
    u = pexpon_star_sl_sl(u, egcd, Nil)
    v = pexpon_star_sl_sl(v, egcd, Nil)
  }
  if ratmac__gt(cadr(v), cadr(u)) {
    let tmp = u
    u = v
    v = tmp
  }
  let gcdv = symval(q_d_gcd)
  let mut s = if eq(gcdv, q_d_red) {
    redgcd(u, v)
  } else if eq(gcdv, q_d_subres) {
    subresgcd(u, v)
  } else {
    merr("OLDGCD: found gcd = ~M; how did that happen?", [gcdv])
  }
  // Check for gcd that simplifies to 0. SourceForge bugs 831445 and 1313987
  if !ratmac__ignore_rat_err(() => rainv(s)).truthy() {
    s = Fix(1L)
  }
  if !equal(s, Fix(1L)) {
    s = pexpon_star_sl_sl(
      primpart(
        if symval(q_d_algebraic).truthy() {
          s
        } else {
          pquotient(s, pquotient(caddr(s), pgcd(caddr(u), caddr(v))))
        },
      ),
      egcd,
      t,
    )
  }
  s = ptimeschk(s, pgcd(x, y))
  if symval(q_d_algebraic).truthy() {
    u = leadalgcoef(s)
    if !atom(u) && !equal(u, s) {
      s = algnormal(s)
    }
  }
  if symval(q_modulus).truthy() {
    monize(s)
  } else if rat3a__pminusp(s) {
    pminus(s)
  } else {
    s
  }
}

///|
fn pgcdexpon(p : Value) -> Value raise {
  if atom(p) {
    Fix(0L)
  } else {
    let mut d = cadr(p)
    let mut l = cdddr(p)
    while !(l is Nil || ratmac__eqn(d, Fix(1L))) {
      let nd = num_gcd(d, car(l))
      l = cddr(l)
      d = nd
    }
    d
  }
}

///|
fn pexpon_star_sl_sl(p : Value, n : Value, op_star_q : Value) -> Value raise {
  if atom(p) || ratmac__eqn(n, Fix(1L)) {
    p
  } else {
    let mut ans = list1(car(p))
    let mut l = cdr(p)
    while !(l is Nil) {
      ans = cons(
        cadr(l),
        cons(
          if op_star_q.truthy() {
            num_mul(car(l), n)
          } else {
            num_truncate(car(l), b=n).0
          },
          ans,
        ),
      )
      l = cddr(l)
    }
    nreverse(ans)
  }
}

///|
/// Polynomial gcd using reduced prs.
fn redgcd(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut d : Value = Fix(0L)
  while !zerop(pdegree(q, car(p))) {
    let np = q
    let nq = pquotientchk_safe(prem(p, q), pexpt(caddr(p), d))
    let nd = num_sub(num_add(cadr(p), Fix(1L)), cadr(q))
    p = np
    q = nq
    d = nd
    if ratmac__lt(d, Fix(1L)) {
      return Fix(1L)
    }
  }
  if ratmac__pz(q) {
    p
  } else {
    Fix(1L)
  }
}

///|
/// Computes gcd's using subresultant prs (ACM TOMS Sept. 1978).
fn subresgcd(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut g : Value = Fix(1L)
  let mut h : Value = Fix(1L)
  let mut d = num_sub(cadr(p), cadr(q))
  let mut h1d : Value = Fix(1L)
  while true {
    let np = q
    let nq = pquotientchk_safe(prem(p, q), ptimes(g, ptimes(h, h1d)))
    p = np
    q = nq
    if zerop(pdegree(q, car(p))) {
      return if ratmac__pz(q) { p } else { Fix(1L) }
    }
    g = caddr(p)
    h = pquotientchk_safe(pexpt(g, d), h1d)
    d = num_sub(cadr(p), cadr(q))
    if ratmac__lt(d, Fix(1L)) {
      return Fix(1L)
    }
    h1d = pexpt(h, num_sub(d, Fix(1L)))
  }
  Nil
}

// THIS COMPUTES PSEUDO REMAINDERS

///|
fn psquorem1(u : Value, v : Value, quop : Value) -> Value raise {
  let bs = bind_all([(q_lcu, Nil), (q_lcv, Nil)])
  defer unbind_all(bs)
  let mut u = u
  let mut m : Value = Fix(0L)
  let mut quo : Value = Nil
  let mut lc : Value = Nil
  set(q_lcv, cadr(v)) |> ignore
  let mut k = num_sub(car(u), car(v))
  if minusp(k) {
    return list3(Fix(1L), list2(Fix(0L), Fix(0L)), u)
  }
  if quop.truthy() {
    lc = pexpt(cadr(v), num_add(k, Fix(1L)))
  }
  while true {
    set(q_lcu, pminus(cadr(u))) |> ignore
    if quop.truthy() {
      quo = cons(ptimes(cadr(u), pexpt(cadr(v), k)), cons(k, quo))
    }
    u = pgcd2(cddr(u), cddr(v), k)
    if u is Nil {
      return list3(lc, nreverse(quo), list2(Fix(0L), Fix(0L)))
    }
    m = num_sub(car(u), car(v))
    if minusp(m) {
      u = if zerop(k) { u } else { pctimes1(pexpt(symval(q_lcv), k), u) }
      return list3(lc, nreverse(quo), u)
    } else if ratmac__gt(num_sub(k, Fix(1L)), m) {
      u = pctimes1(
        pexpt(symval(q_lcv), num_sub(num_sub(k, Fix(1L)), m)),
        u,
      )
    }
    k = m
  }
  Nil
}

///|
fn prem(p : Value, q : Value) -> Value raise {
  if atom(p) {
    if atom(q) {
      if symval(q_modulus).truthy() || floatp(p) || floatp(q) {
        Fix(0L)
      } else {
        num_rem(p, q)
      }
    } else {
      p
    }
  } else if atom(q) {
    Fix(0L)
  } else {
    psimp(car(p), pgcd1(cdr(p), cdr(q)))
  }
}

///|
fn pgcd1(u : Value, v : Value) -> Value raise {
  caddr(psquorem1(u, v, Nil))
}

///|
fn pgcd2(u : Value, v : Value, k : Value) -> Value raise {
  let lcu = symval(q_lcu)
  let lcv = symval(q_lcv)
  if u is Nil {
    pcetimes1(v, k, lcu)
  } else if v is Nil {
    pctimes1(lcv, u)
  } else {
    let i = num_sub(num_sub(car(u), k), car(v))
    if zerop(i) {
      pcoefadd(
        car(u),
        pplus(ptimes(lcv, cadr(u)), ptimes(lcu, cadr(v))),
        pgcd2(cddr(u), cddr(v), k),
      )
    } else if minusp(i) {
      cons(num_add(car(v), k), cons(ptimes(lcu, cadr(v)), pgcd2(u, cddr(v), k)))
    } else {
      cons(car(u), cons(ptimes(lcv, cadr(u)), pgcd2(cddr(u), v, k)))
    }
  }
}

// OLDCONTENT REMOVES ALL BUT MAIN VARIABLE AND PUTS THAT IN CONTENT
// OLDCONTENT OF 3*A*X IS 3*A (WITH MAINVAR=X)

///|
/// Returns rat-forms.
fn rcontent(p : Value) -> Value raise {
  let q = oldcontenta(p)
  list2(
    cons(q, Fix(1L)),
    if symval(q_d_algebraic).truthy() {
      rquotient(p, q)
    } else {
      cons(pquotient(p, q), Fix(1L))
    },
  )
}

///|
fn oldcontenta(x : Value) -> Value raise {
  if atom(x) {
    x
  } else {
    let x = contsort(cdr(x))
    oldcontent2(cdr(x), car(x))
  }
}

///|
fn oldcontent(x : Value) -> Value raise {
  if atom(x) {
    list2(x, Fix(1L))
  } else if cdddr(x) is Nil {
    list2(caddr(x), list3(car(x), cadr(x), Fix(1L)))
  } else {
    let u0 = contsort(cdr(x))
    let mut u = oldcontent2(cdr(u0), car(u0))
    let mut v = if symval(q_d_algebraic).truthy() {
      rquotient(x, u)
    } else {
      cons(pcquotient(x, u), Fix(1L))
    }
    // With algebraic numbers, U can be a multiple of the content and X/U a
    // fraction. Then U is divided by the denominator if that is exact, else
    // X is kept whole.
    if equal(cdr(v), Fix(1L)) {
      v = car(v)
    } else {
      let w = pquotientchk_safe(u, cdr(v))
      if w.truthy() {
        u = w
        v = car(v)
      } else {
        u = Fix(1L)
        v = x
      }
    }
    if rat3a__pminusp(v) {
      list2(pminus(u), pminus(v))
    } else {
      list2(u, v)
    }
  }
}

///|
fn oldcontent1(x : Value, gcd_ : Value) -> Value raise {
  if equal(gcd_, Fix(1L)) {
    Fix(1L)
  } else if x is Nil {
    gcd_
  } else {
    oldcontent2(contsort(x), gcd_)
  }
}

///|
fn oldcontent2(x : Value, gcd_ : Value) -> Value raise {
  let mut x = x
  let mut gcd_ = gcd_
  while !(x is Nil || equal(gcd_, Fix(1L))) {
    let ng = pgcd(car(x), gcd_)
    x = cdr(x)
    gcd_ = ng
  }
  gcd_
}

///|
fn contsort(x : Value) -> Value raise {
  let x = coefl(x)
  if member(Fix(1L), x).truthy() {
    list1(Fix(1L))
  } else if cdr(x) is Nil {
    x
  } else {
    sort_list(x, (a, b) => contodr(a, b).truthy())
  }
}

///|
fn coefl(x : Value) -> Value raise {
  let mut x = x
  let mut ans : Value = Nil
  while !(x is Nil) {
    ans = cons(cadr(x), ans)
    x = cddr(x)
  }
  ans
}

///|
/// CONTODR orders the coefficients for OLDCONTENT2: numbers first, then
/// lower main variables, lower degrees and fewer terms, so that cheap gcds
/// come first. It is a strict order and CONTSORT sorts stably.
fn contodr(a : Value, b : Value) -> Value raise {
  if atom(a) {
    lbool(!atom(b))
  } else if atom(b) {
    Nil
  } else if eq(car(a), car(b)) {
    if ratmac__eqn(cadr(a), cadr(b)) {
      lbool(ratmac__lt(pnterms(a), pnterms(b)))
    } else {
      lbool(ratmac__lt(cadr(a), cadr(b)))
    }
  } else {
    pointergp(car(b), car(a))
  }
}

///|
/// Number of monomials in the polynomial P.
fn pnterms(p : Value) -> Value raise {
  if atom(p) {
    Fix(1L)
  } else {
    let mut l = cdr(p)
    let mut n : Value = Fix(0L)
    while !(l is Nil) {
      n = num_add(n, pnterms(cadr(l)))
      l = cddr(l)
    }
    n
  }
}

// PCONTENT COMPUTES INTEGER CONTENT
// PCONTENT OF 3*A*X IS 3 IF MODULUS = NIL  1 OTHERWISE

///|
fn pcontent(x : Value) -> Value raise {
  if atom(x) {
    list2(x, Fix(1L))
  } else {
    let u = pcontentz(x)
    if equal(u, Fix(1L)) {
      list2(Fix(1L), x)
    } else {
      list2(u, pcquotient(x, u))
    }
  }
}

///|
fn pcontent1(x : Value, gcd_ : Value) -> Value raise {
  let mut x = x
  let mut gcd_ = gcd_
  while !(x is Nil || equal(gcd_, Fix(1L))) {
    let ng = cgcd(gcd_, pcontentz(cadr(x)))
    x = cddr(x)
    gcd_ = ng
  }
  gcd_
}

///|
fn pcontentz(p : Value) -> Value raise {
  if atom(p) {
    p
  } else {
    pcontent1(cdddr(p), pcontentz(caddr(p)))
  }
}

///|
/// Content of a univariate polynomial.
fn ucontent(p : Value) -> Value raise {
  if atom(p) {
    num_abs(p)
  } else {
    let p = mapcar(x => num_abs(x), coefl(cdr(p)))
    let m = reduce((a, b) => num_min(a, b), p)
    oldcontent2(remove_equal(m, p), m)
  }
}

// PGCDU CORRESPONDS TO BROWN'S ALGORITHM U

///|
fn pgcdu(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  while !ratmac__pz(q) {
    let np = q
    let nq = pmodrem(p, q)
    p = np
    q = nq
  }
  monize(p)
}

///|
fn pmodrem(x : Value, y : Value) -> Value raise {
  if symval(q_modulus) is Nil {
    merr("PMODREM: null modulus; how did that happen?", [])
  } else if rat3a__pacoefp(y) {
    if ratmac__pz(y) {
      x
    } else {
      Fix(0L)
    }
  } else if rat3a__pacoefp(x) {
    x
  } else if eq(car(x), car(y)) {
    psimp(car(x), pgcdu1(cdr(x), cdr(y), Nil))
  } else {
    merr("PMODREM: I can't handle this; x = ~M, y = ~M", [x, y])
  }
}

///|
fn pmodquo(u : Value, v : Value) -> Value raise {
  with_special(q_quo, Nil, () => {
    if symval(q_modulus) is Nil {
      merr("PMODQUO: null modulus; how did that happen?", [])
    } else if atom(v) {
      cons(ptimes(crecip(v), u), Fix(0L))
    } else if alg(v).truthy() {
      cons(ptimes(painvmod(v), u), Fix(0L))
    } else if rat3a__pacoefp(u) {
      cons(Fix(0L), u)
    } else if !eq(car(u), car(v)) {
      merr(
        "PMODQUO: arguments have different variables; how did that happen?",
        [],
      )
    } else {
      let a = psimp(car(u), pgcdu1(cdr(u), cdr(v), t))
      let b = psimp(car(u), symval(q_quo))
      cons(b, a)
    }
  })
}

///|
fn pgcdu1(u : Value, v : Value, pquo_star : Value) -> Value raise {
  let invv = painvmod(cadr(v))
  let bs = bind_all([(q_k, Fix(0L)), (q_q_star, Nil)])
  defer unbind_all(bs)
  let mut u = u
  while true {
    set(q_k, num_sub(car(u), car(v))) |> ignore
    if minusp(symval(q_k)) {
      break
    }
    set(q_q_star, ptimes(invv, cadr(u))) |> ignore
    if pquo_star.truthy() {
      set(
        q_quo,
        nconc(symval(q_quo), list2(symval(q_k), symval(q_q_star))),
      )
      |> ignore
    }
    u = ptpt_subtract_powered_product(
      cddr(u),
      cddr(v),
      symval(q_q_star),
      symval(q_k),
    )
    if u is Nil {
      return Nil
    }
  }
  u
}

///|
fn newprime(p : Value) -> Value raise {
  let mut pl = symval(q_ear_bigprimes)
  while !(pl is Nil) {
    if ratmac__lt(car(pl), p) {
      return car(pl)
    }
    pl = cdr(pl)
  }
  let p = next_prime(num_sub(p, Fix(1L)), Fix(-1L))
  set(q_ear_bigprimes, nconc(symval(q_ear_bigprimes), list1(p))) |> ignore
  p
}

///|
fn leadcoefficient(p : Value) -> Value raise {
  let mut p = p
  while !atom(p) {
    p = caddr(p)
  }
  p
}

///|
fn maxcoefficient(p : Value) -> Value raise {
  if atom(p) {
    num_abs(p)
  } else {
    maxcoef1(cdr(p))
  }
}

///|
fn maxcoef1(p : Value) -> Value raise {
  if p is Nil {
    Fix(0L)
  } else {
    num_max(maxcoefficient(cadr(p)), maxcoef1(cddr(p)))
  }
}

///|
fn maxnorm(poly : Value) -> Value raise {
  if poly is Nil {
    Fix(0L)
  } else {
    num_max(norm(cadr(poly)), maxnorm(cddr(poly)))
  }
}

///|
fn norm(poly : Value) -> Value raise {
  if poly is Nil {
    Fix(0L)
  } else if atom(poly) {
    num_abs(poly)
  } else {
    num_add(norm(caddr(poly)), norm1(cdddr(poly)))
  }
}

///|
fn norm1(poly : Value) -> Value raise {
  if poly is Nil {
    Fix(0L)
  } else {
    num_add(norm(cadr(poly)), norm1(cddr(poly)))
  }
}

///|
fn pdegree(p : Value, var2 : Value) -> Value raise {
  if atom(p) {
    Fix(0L)
  } else if eq(var2, car(p)) {
    cadr(p)
  } else if ratmac__pgp(var2, car(p)) {
    Fix(0L)
  } else {
    let mut l = cdddr(p)
    let mut e = pdegree(caddr(p), var2)
    while !(l is Nil) {
      e = num_max(e, pdegree(cadr(l), var2))
      l = cddr(l)
    }
    e
  }
}

///|
fn poly_in_var(p : Value, v : Value) -> Value raise {
  if atom(p) || ratmac__pgp(v, car(p)) {
    list2(Fix(0L), p)
  } else if eq(car(p), v) {
    cdr(p)
  } else {
    let mut ans : Value = Nil
    let mut l = cdr(p)
    while l is Cons(_) {
      let e = car(l)
      let coef = cadr(l)
      ans = ptptplus(
        ans,
        everysubst2(poly_in_var(coef, v), list3(car(p), e, Fix(1L))),
      )
      l = cddr(l)
    }
    ans
  }
}

///|
fn univar(x : Value) -> Value raise {
  let mut x = x
  while !(x is Nil) {
    if !atom(cadr(x)) {
      return Nil
    }
    x = cddr(x)
  }
  t
}

// THE CHINESE REMAINDER ALGORITHM IS A SPECIAL CASE OF LAGRANGE INTERPOLATION

///|
fn lagrange3(u : Value, uk : Value, p : Value, qk : Value) -> Value raise {
  set_modulus(p) |> ignore
  let uk = pdifference(uk, pmod(u))
  if ratmac__pz(uk) {
    set(q_modulus, Nil) |> ignore
    u
  } else {
    let uk = pctimes(crecip(cmod(qk)), uk)
    set(q_modulus, Nil) |> ignore
    pplus(u, pctimes(qk, uk))
  }
}

///|
fn lagrange33(u : Value, uk : Value, qk : Value, xk : Value) -> Value raise {
  let xv = symval(q_xv)
  let uk = pdifference(uk, pcsubst(u, xk, xv))
  if ratmac__pz(uk) {
    u
  } else {
    pplus(u, ptimes(pctimes(crecip(pcsubst(qk, xk, symval(q_xv))), uk), qk))
  }
}
