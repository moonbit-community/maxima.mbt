// Port of src/ratout.lisp: the out-of-core segment of the rational function
// package (Brown's modular gcd algorithms, Kronecker factoring, fast
// multiplication, ratweight truncation, horner, partfrac, ratdiff, pfet).

///|
/// NEWGCD (X,Y) RETURNS A LIST OF THREE ITEMS, (GCD, X/GCD, Y/GCD)
fn newgcd(ratout_x : Value, ratout_y : Value, modulus : Value) -> Value raise {
  let b = bind(q_modulus, modulus)
  defer unbind(b)
  set_modulus(symval(q_modulus)) |> ignore
  let x = ratout_x
  let y = ratout_y
  let a = if atom(x) {
    if zerop(x) {
      y
    } else if atom(y) {
      cgcd(x, y)
    } else {
      pcontent1(cdr(y), x)
    }
  } else if atom(y) {
    if zerop(y) {
      x
    } else {
      pcontent1(cdr(x), y)
    }
  } else if ratmac__pgp(car(x), car(y)) {
    oldcontent1(cdr(x), y)
  } else if ratmac__pgp(car(y), car(x)) {
    oldcontent1(cdr(y), x)
  } else {
    Nil
  }
  if a.truthy() {
    list3(a, pquotient(x, a), pquotient(y, a))
  } else if symval(q_modulus).truthy() {
    pgcdp(x, y, symval(q_modulus))
  } else {
    pgcdm(x, y)
  }
}

///|
fn pgathercoef(
  p : Value,
  ratout__starchk : Value,
  ratout__starres : Value,
) -> Value raise {
  if atom(p) || !eq(car(p), ratout__starchk) {
    return Fix(1L)
  }
  let chk = ratout__starchk
  let mut res = ratout__starres
  // pgath2
  let mut p = cdr(p)
  let mut vmax : Value = Nil
  while true {
    let mut v2 : Value = Nil
    if p is Nil {
      return res
    } else if atom(cadr(p)) {
      ()
    } else if vgreat(
        {
          v2 = pdegreer(cadr(p))
          v2
        },
        vmax,
      ).truthy() {
      res = psimp(chk, list2(car(p), leadcoefficient(cadr(p))))
      vmax = v2
    } else if equal(vmax, v2) {
      res = pplus(res, psimp(chk, list2(car(p), leadcoefficient(cadr(p)))))
    }
    p = cddr(p)
  }
  Nil
}

///|
fn pgath1(
  p : Value,
  ratout__starmax : Value,
  ratout__starvar : Value,
) -> Value raise {
  let mut p = p
  let mut mx = ratout__starmax
  while !(p is Nil) {
    if atom(cadr(p)) {
      ()
    } else if eq(caadr(p), ratout__starvar) {
      mx = num_max(mx, cadadr(p))
    }
    p = cddr(p)
  }
  mx
}

///|
fn pnext(ratout_x : Value, ratout__starl : Value) -> Value raise {
  let mut l = ratout__starl
  let mut x = ratout_x
  while !(x is Nil) {
    if atom(cadr(x)) || memq(caadr(x), l).truthy() {
      ()
    } else {
      l = cons(caadr(x), l)
    }
    x = cddr(x)
  }
  if l is Nil {
    Nil
  } else {
    car(sort_list(l, (a, b) => ratmac__pgp(a, b)))
  }
}

///|
fn vgreat(ratout_x : Value, ratout_y : Value) -> Value raise {
  let mut x = ratout_x
  let mut y = ratout_y
  while true {
    if x is Nil {
      return Nil
    } else if y is Nil {
      return t
    } else if ratmac__pgp(car(x), car(y)) {
      return t
    } else if !eq(car(x), car(y)) {
      return Nil
    } else if ratmac__gt(cadr(x), cadr(y)) {
      return t
    } else if equal(cadr(x), cadr(y)) {
      x = cddr(x)
      y = cddr(y)
    } else {
      return Nil
    }
  }
  Nil
}

///|
fn pdegreer(ratout_x : Value) -> Value raise {
  if atom(ratout_x) {
    Nil
  } else {
    cons(car(ratout_x), cons(cadr(ratout_x), pdegreer(caddr(ratout_x))))
  }
}

///|
/// PMODCONTENT computes the content of P in Z_p[X_v][X_1, ..., X_(v-1)];
/// PMODCONTENT OF 3*A*X IS A, IF MAINVAR IS X (=X_v).
fn ratout__pmodcontent(p : Value, xv : Value) -> Value raise {
  let chk = car(p)
  let mut mx : Value = Fix(0L)
  let var_ = pnext(cdr(p), Nil)
  let mut res : Value = Nil
  let mut gcd_ : Value = Nil
  if ratmac__pgp(xv, chk) {
    return list2(Fix(1L), p)
  } else if var_ is Nil {
    return list2(p, Fix(1L))
  }
  // The result is discarded (the original special *MAX was renamed).
  pgath1(cdr(p), mx, var_) |> ignore
  while true {
    // a
    res = Fix(0L)
    // pgath3
    let mut q = cdr(p)
    while !(q is Nil) {
      let mut zz : Value = Nil
      let mut add = false
      if atom(cadr(q)) {
        if equal(mx, Fix(0L)) {
          zz = cadr(q)
          add = true
        }
      } else if eq(caadr(q), var_) {
        zz = ptterm(cdadr(q), mx)
        add = true
      } else if equal(mx, Fix(0L)) {
        zz = cadr(q)
        add = true
      }
      if add && !equal(zz, Fix(0L)) {
        res = pplus(res, psimp(chk, list2(car(q), zz)))
      }
      q = cddr(q)
    }
    // a2
    while true {
      if atom(res) {
        if ratmac__pz(res) {
          break
        } else {
          return list2(Fix(1L), p)
        }
      } else if !eq(car(res), chk) {
        return list2(Fix(1L), p)
      } else if !univar(cdr(res)).truthy() {
        res = car(ratout__pmodcontent(res, xv))
        continue
      } else if gcd_.truthy() {
        gcd_ = pgcdu(gcd_, res)
      } else {
        gcd_ = res
      }
      break
    }
    if atom(gcd_) {
      return list2(Fix(1L), p)
    }
    mx = num_sub(mx, Fix(1L))
    if minusp(mx) {
      return list2(gcd_, pquotient(p, gcd_))
    }
  }
  Nil
}

///|
/// PGCDP CORRESPONDS TO BROWN'S ALGORITHM P
fn pgcdp(
  ratout_bigf1 : Value,
  ratout_bigf2 : Value,
  modulus : Value,
) -> Value raise {
  let bnd = bind(q_modulus, modulus)
  defer unbind(bnd)
  let mut bigf1 = ratout_bigf1
  let mut bigf2 = ratout_bigf2
  set_modulus(symval(q_modulus)) |> ignore
  if univar(cdr(bigf1)).truthy() && univar(cdr(bigf2)).truthy() {
    let q = pgcdu(bigf1, bigf2)
    return list3(q, pquotient(bigf1, q), pquotient(bigf2, q))
  }
  let xv = car(bigf1)
  bigf1 = ratout__pmodcontent(bigf1, xv)
  bigf2 = ratout__pmodcontent(bigf2, xv)
  let c1 = car(bigf1)
  let c2 = car(bigf2)
  let c = pgcdu(c1, c2)
  bigf1 = cadr(bigf1)
  bigf2 = cadr(bigf2)
  let mut n = 0
  let mut e = pdegreer(bigf2)
  let mut degree = pdegreer(bigf1)
  if vgreat(e, degree).truthy() {
    e = degree
  }
  let mut b = ash(symval(q_modulus), -1)
  let f1 = pgathercoef(bigf1, xv, Fix(0L))
  let mut f1f2 = pgathercoef(bigf2, xv, Fix(0L))
  let gbar = pgcdu(f1, f1f2)
  let step15a = () => list3(
    c,
    ptimeschk(pquotient(c1, c), bigf1),
    ptimeschk(pquotient(c2, c), bigf2),
  )
  if equal(Fix(0L), f1f2) {
    return step15a()
  }
  let mut nubar = pdegree(gbar, xv)
  let nu1bar = num_add(nubar, pdegree(bigf1, xv))
  let nu2bar = num_add(nubar, pdegree(bigf2, xv))
  f1f2 = ptimes(f1, f1f2)
  nubar = num_max(nu1bar, nu2bar)
  let mut q : Value = Nil
  let mut gstar : Value = Nil
  let mut h1star : Value = Nil
  let mut h2star : Value = Nil
  while true {
    // step6
    b = cplus(b, Fix(1L))
    if equal(pcsubst(f1f2, b, xv), Fix(0L)) {
      continue
    }
    // Step 7
    let gtilde = pcsubst(gbar, b, xv)
    let f1tilde = pcsubst(bigf1, b, xv)
    let f2tilde = pcsubst(bigf2, b, xv)
    let mut h2tilde = newgcd(f1tilde, f2tilde, symval(q_modulus))
    let biggtilde = ptimeschk(gtilde, car(h2tilde))
    if atom(biggtilde) {
      return step15a()
    }
    let h1tilde = cadr(h2tilde)
    h2tilde = caddr(h2tilde)
    degree = pdegreer(biggtilde)
    if vgreat(degree, e).truthy() {
      continue
    } else if vgreat(e, degree).truthy() {
      n = 0
      e = degree
    }
    n = n + 1
    if n == 1 {
      q = list([xv, Fix(1L), Fix(1L), Fix(0L), num_neg(b)])
      gstar = biggtilde
      h1star = h1tilde
      h2star = h2tilde
    } else {
      gstar = lagrange33(gstar, biggtilde, q, b)
      h1star = lagrange33(h1star, h1tilde, q, b)
      h2star = lagrange33(h2star, h2tilde, q, b)
      q = ptimes(q, list([xv, Fix(1L), Fix(1L), Fix(0L), num_neg(b)]))
    }
    // Step 12
    if !ratmac__gt(int(n), nubar) {
      continue
    }
    // Step 13
    let deg = pdegree(gstar, xv)
    if !ratmac__eqn(nu1bar, num_add(deg, pdegree(h1star, xv))) ||
      !ratmac__eqn(nu2bar, num_add(deg, pdegree(h2star, xv))) {
      n = 0
      continue
    }
    gstar = cadr(ratout__pmodcontent(gstar, xv))
    // Step 15
    q = pgathercoef(gstar, xv, Fix(0L))
    return monicgcd(
      ptimeschk(c, gstar),
      ptimeschk(pquotient(c1, c), pquotientchk(h1star, q)),
      ptimeschk(pquotient(c2, c), pquotientchk(h2star, q)),
      leadcoefficient(gstar),
    )
  }
  Nil
}

///|
fn monicgcd(
  ratout_gcd : Value,
  ratout_x : Value,
  ratout_y : Value,
  lcf : Value,
) -> Value raise {
  if equal(lcf, Fix(1L)) {
    list3(ratout_gcd, ratout_x, ratout_y)
  } else {
    list3(
      ptimes(crecip(lcf), ratout_gcd),
      ptimes(lcf, ratout_x),
      ptimes(lcf, ratout_y),
    )
  }
}

///|
/// PGCDM CORRESPONDS TO BROWN'S ALGORITHM M
fn pgcdm(ratout_bigf1 : Value, ratout_bigf2 : Value) -> Value raise {
  let bnd = bind(q_modulus, Nil)
  defer unbind(bnd)
  let mut bigf1 = ratout_bigf1
  let mut bigf2 = ratout_bigf2
  let mut p = symval(q_n_staralpha)
  // Step 1
  let f1c = pcontent(bigf1)
  let f2c = pcontent(bigf2)
  let c1 = car(f1c)
  let c2 = car(f2c)
  let c = cgcd(c1, c2)
  bigf1 = cadr(f1c)
  bigf2 = cadr(f2c)
  // Step 3
  let f1 = leadcoefficient(bigf1)
  let f2 = leadcoefficient(bigf2)
  let gbar = cgcd(f1, f2)
  // Step 4
  let mut n = 0
  let mut degree = pdegreer(bigf1)
  let mut e = pdegreer(bigf2)
  if vgreat(e, degree).truthy() {
    e = degree
  }
  // Step 5
  let mubar = num_mul(
    num_mul(Fix(2L), gbar),
    num_max(maxcoefficient(bigf1), maxcoefficient(bigf2)),
  )
  let mut q : Value = Nil
  let mut gstar : Value = Nil
  let mut h1star : Value = Nil
  let mut h2star : Value = Nil
  let mut first = true
  let mut done = false
  while !done {
    // step6
    if !first {
      p = newprime(p)
    }
    first = false
    // step6a
    if zerop(num_rem(f1, p)) || zerop(num_rem(f2, p)) {
      continue
    }
    set_modulus(p) |> ignore
    // Step 7
    let mut gtilde = pmod(gbar)
    // Step 8
    let mut h2tilde = newgcd(pmod(bigf1), pmod(bigf2), symval(q_modulus))
    let biggtilde = ptimeschk(gtilde, car(h2tilde))
    if atom(biggtilde) {
      set(q_modulus, Nil) |> ignore
      gstar = Fix(1L)
      h1star = bigf1
      h2star = bigf2
      break
    }
    let mut h1tilde : Value = Nil
    if cdr(h2tilde) is Nil {
      h1tilde = pquotient(pmod(bigf1), car(h2tilde))
      h2tilde = pquotient(pmod(bigf2), car(h2tilde))
    } else {
      h1tilde = cadr(h2tilde)
      h2tilde = caddr(h2tilde)
    }
    degree = pdegreer(biggtilde)
    if vgreat(degree, e).truthy() {
      continue
    } else if vgreat(e, degree).truthy() {
      n = 0
      e = degree
    }
    n = n + 1
    // Step 11
    set_modulus(Nil) |> ignore
    if n == 1 {
      q = p
      gstar = biggtilde
      h1star = h1tilde
      h2star = h2tilde
    } else {
      gstar = lagrange3(gstar, biggtilde, p, q)
      h1star = lagrange3(h1star, h1tilde, p, q)
      h2star = lagrange3(h2star, h2tilde, p, q)
      q = num_mul(p, q)
    }
    // Step 12
    if ratmac__gt(mubar, q) {
      continue
    }
    gtilde = norm(gstar)
    if ratmac__gt(
        num_mul(
          Fix(2L),
          num_max(
            num_mul(gtilde, maxcoefficient(h1star)),
            num_mul(gtilde, maxcoefficient(h2star)),
          ),
        ),
        q,
      ) {
      continue
    }
    set_modulus(Nil) |> ignore
    gstar = cadr(pcontent(gstar))
    done = true
  }
  // step15
  q = leadcoefficient(gstar)
  list3(
    ptimeschk(c, gstar),
    ptimeschk(cquotient(c1, c), pquotientchk(h1star, q)),
    ptimeschk(cquotient(c2, c), pquotientchk(h2star, q)),
  )
}

// THE FUNCTIONS ON THIS PAGE ARE USED BY KRONECKER FACTORING

///|
/// Maxima's ERRSET macro: (list value) on success, NIL when an error is
/// signalled (re-signalled when the special ERRSET is true).
fn ratout__errset(f : () -> Value raise) -> Value raise {
  f() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    e => if symval(q_errset).truthy() { raise e } else { Nil }
  } noraise {
    v => list1(v)
  }
}

///|
fn pkroneck(p : Value) -> Value raise {
  let mut p = p
  let mut maxexp = quot(cadr(p), Fix(2L))
  let mut i : Value = Fix(1L)
  let mut factors : Value = Nil
  let mut factor : Value = Nil
  while true {
    // a
    if ratmac__gt(i, maxexp) {
      return cons(p, factors)
    }
    let p0 = p
    let i0 = i
    let mut l = p1(
      reverse(with_special(q_d_factorflag, t, () => pfactor2(p0, i0))),
    )
    let mut found = false
    // b
    while !(l is Nil) {
      let rl = car(l)
      let rp = car(p)
      ratmac__ignore_rat_err(() => {
        factor = ratout__errset(() => pinterpolate(rl, rp))
        factor
      })
      |> ignore
      l = cdr(l)
      if atom(factor) {
        continue
      } else {
        factor = car(factor)
      }
      if atom(factor) ||
        !equal(car(p), car(factor)) ||
        !ratmac__pz(prem(p, factor)) {
        continue
      }
      if symval(q_modulus).truthy() {
        pmonicize(cdr(factor)) |> ignore
      } else if rat3a__pminusp(factor) {
        factor = pminus(factor)
      }
      p = pquotient(p, factor)
      maxexp = quot(cadr(p), Fix(2L))
      factors = cons(factor, factors)
      found = true
      break
    }
    if !found {
      // d
      i = num_add(i, Fix(1L))
    }
  }
  Nil
}

///|
fn pfactor2(p : Value, i : Value) -> Value raise {
  if minusp(i) {
    Nil
  } else {
    let f = pfactor(pcsubst(p, i, car(p)))
    cons(f, pfactor2(p, num_sub(i, Fix(1L))))
  }
}

///|
fn rpowerset(ratout_x : Value, ratout_n : Value) -> Value raise {
  if ratout_x is Nil {
    list2(Fix(1L), Nil)
  } else if equal(ratout_x, Fix(1L)) {
    list1(Fix(1L))
  } else {
    cons(Fix(1L), ptts1(ratout_x, ratout_n, ratout_x))
  }
}

///|
fn allprods(ratout_x : Value, ratout_y : Value) -> Value raise {
  if ratout_x is Nil {
    Nil
  } else if ratout_y is Nil {
    Nil
  } else {
    let a = ap1(car(ratout_x), ratout_y)
    nconc(a, allprods(cdr(ratout_x), ratout_y))
  }
}

///|
/// Probably never called from the testsuite (see the note in ratout.lisp).
fn al1(ratout_f : Value, r : Value, len : Value) -> Value raise {
  if equal(len, Fix(1L)) {
    mapcar(y => cons(y, Nil), ratout_f)
  } else if r is Nil {
    Nil
  } else {
    let mut ss : Value = Nil
    mapc(
      y => ss = nconc(ss, mapcar(z => cons(z, y), ratout_f)),
      al1(car(r), cdr(r), num_sub(len, Fix(1L))),
    )
    |> ignore
    ss
  }
}

///|
fn ap1(ratout_x : Value, l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else {
    cons(ptimes(ratout_x, car(l)), ap1(ratout_x, cdr(l)))
  }
}

///|
fn ptts1(ratout_x : Value, ratout_n : Value, ratout_y : Value) -> Value raise {
  if equal(ratout_n, Fix(1L)) {
    list1(ratout_y)
  } else {
    cons(
      ratout_y,
      ptts1(ratout_x, num_sub(ratout_n, Fix(1L)), ptimes(ratout_x, ratout_y)),
    )
  }
}

///|
fn p1(l : Value) -> Value raise {
  let a = mapcar(x => p11(x), l)
  if l is Nil {
    Nil
  } else {
    cdr(al1(car(a), cdr(a), int(length(a))))
  }
}

///|
fn p11(ele : Value) -> Value raise {
  if cddr(ele) is Nil {
    rpowerset(car(ele), cadr(ele))
  } else {
    allprods(rpowerset(car(ele), cadr(ele)), p11(cddr(ele)))
  }
}

///|
fn pinterpolate(l : Value, var_ : Value) -> Value raise {
  psimp(
    var_,
    pinterpolate1(pinterpolate2(l, Fix(1L)), int(length(l) - 2)),
  )
}

///|
fn pinterpolate1(ratout_x : Value, ratout_n : Value) -> Value raise {
  pinterpolate4(
    pinterpolate5(reverse(ratout_x), Fix(1L), ratout_n, ratout_n),
    num_add(ratout_n, Fix(1L)),
  )
}

///|
fn pinterpolate2(ratout_x : Value, ratout_n : Value) -> Value raise {
  if cdr(ratout_x) is Nil {
    ratout_x
  } else {
    cons(
      car(ratout_x),
      pinterpolate2(
        pinterpolate3(ratout_x, ratout_n),
        num_add(ratout_n, Fix(1L)),
      ),
    )
  }
}

///|
fn pinterpolate3(ratout_x : Value, ratout_n : Value) -> Value raise {
  if cdr(ratout_x) is Nil {
    Nil
  } else {
    cons(
      pquotient(pdifference(cadr(ratout_x), car(ratout_x)), ratout_n),
      pinterpolate3(cdr(ratout_x), ratout_n),
    )
  }
}

///|
fn pinterpolate4(ratout_x : Value, ratout_n : Value) -> Value raise {
  if ratout_x is Nil {
    Nil
  } else if ratmac__pz(car(ratout_x)) {
    pinterpolate4(cdr(ratout_x), num_sub(ratout_n, Fix(1L)))
  } else {
    cons(
      ratout_n,
      cons(
        car(ratout_x),
        pinterpolate4(cdr(ratout_x), num_sub(ratout_n, Fix(1L))),
      ),
    )
  }
}

///|
fn pinterpolate5(
  ratout_x : Value,
  i : Value,
  j : Value,
  ratout_n : Value,
) -> Value raise {
  if ratmac__gt(i, ratout_n) {
    ratout_x
  } else {
    pinterpolate5(
      cons(car(ratout_x), pinterpolate6(ratout_x, i, j)),
      num_add(i, Fix(1L)),
      num_sub(j, Fix(1L)),
      ratout_n,
    )
  }
}

///|
fn pinterpolate6(ratout_x : Value, i : Value, j : Value) -> Value raise {
  if zerop(i) {
    cdr(ratout_x)
  } else {
    cons(
      pdifference(cadr(ratout_x), pctimes(j, car(ratout_x))),
      pinterpolate6(cdr(ratout_x), num_sub(i, Fix(1L)), j),
    )
  }
}

// THE N**(1.585) MULTIPLICATION SCHEME FOLLOWS. IT SHOULD BE USED ONLY WHEN
// BOTH INPUTS ARE MULTIVARIATE, DENSE, AND OF NEARLY THE SAME SIZE. OR
// ABSOLUTELY TREMENDOUS. (THE CLASSICAL MULTIPLICATION SCHEME IS N**2 WHERE
// N IS SIZE OF POLYNOMIAL (OR N*M FOR DIFFERENT SIZES). FOR THIS CASE, N IS
// APPX. THE SIZE OF LARGER.

///|
fn d_fasttimes(ratout_x : Value, ratout_y : Value) -> Value raise {
  let x = ratout_x
  let y = ratout_y
  if !atom(x) &&
    !atom(y) &&
    equal(car(x), car(y)) &&
    equal(caar(x), q_mrat) &&
    equal(cddr(x), Fix(1L)) &&
    equal(cddr(y), Fix(1L)) {
    cons(car(x), cons(fptimes(cadr(x), cadr(y)), Fix(1L)))
  } else {
    merr(
      "fasttimes: arguments must be CRE polynomials with same variables.",
      [],
    )
  }
}

///|
fn fptimes(ratout_x : Value, ratout_y : Value) -> Value raise {
  let x = ratout_x
  let y = ratout_y
  if ratmac__pz(x) || ratmac__pz(y) {
    Fix(0L)
  } else if atom(x) {
    pctimes(x, y)
  } else if atom(y) {
    pctimes(y, x)
  } else if eq(car(x), car(y)) {
    if univar(cdr(x)).truthy() || univar(cdr(y)).truthy() {
      cons(car(x), ptimes1(cdr(x), cdr(y)))
    } else {
      cons(car(x), fptimes1(cdr(x), cdr(y)))
    }
  } else if ratmac__pgp(car(x), car(y)) {
    cons(car(x), pctimes1(y, cdr(x)))
  } else {
    cons(car(y), pctimes1(x, cdr(y)))
  }
}

///|
fn fptimes1(ratout_f : Value, g : Value) -> Value raise {
  let mut f = ratout_f
  let mut g = g
  if f is Nil || g is Nil {
    return Nil
  } else if cddr(f) is Nil {
    return lsft(pctimes1(cadr(f), g), car(f))
  } else if cddr(g) is Nil {
    return lsft(pctimes1(cadr(g), f), car(g))
  }
  let d = ash(num_add(Fix(1L), num_max(car(f), car(g))), -1)
  f = halfsplit(f, d)
  g = halfsplit(g, d)
  let a = fptimes1(car(f), car(g))
  let mut b = fptimes1(ptptplus(car(f), cdr(f)), ptptplus(car(g), cdr(g)))
  let c = fptimes1(cdr(f), cdr(g))
  b = ptptdiffer(ptptdiffer(b, a), c)
  ptptplus(lsft(a, ash(d, 1)), ptptplus(lsft(b, d), c))
}

///|
fn halfsplit(p : Value, d : Value) -> Value raise {
  let mut a : Value = Nil
  let mut p = p
  while !(p is Nil || ratmac__lt(car(p), d)) {
    a = cons(cadr(p), cons(num_sub(car(p), d), a))
    p = cddr(p)
  }
  cons(nreverse(a), p)
}

///|
fn lsft(p : Value, ratout_n : Value) -> Value raise {
  let mut q = p
  while !(q is Nil) {
    rplaca(q, num_add(car(q), ratout_n)) |> ignore
    q = cddr(q)
  }
  p
}

// TO TRUNCATE ON E, DO RATWEIGHT(E,1);
// THEN DO RATWTLVL:N.  ALL POWERS >N GO TO 0.

///|
fn d_ratweight(args : Value) -> Value raise {
  if (length(args) & 1) == 1 {
    merr("ratweight: number of arguments must be a multiple of 2.", [])
    |> ignore
  }
  let mut l = args
  while !(l is Nil) {
    let cell = {
      let c = assoc_equal(first(l), symval(q_n_starratweights))
      if c.truthy() {
        c
      } else {
        set(
          q_n_starratweights,
          cons(list1(first(l)), symval(q_n_starratweights)),
        )
        |> ignore
        car(symval(q_n_starratweights))
      }
    }
    rplacd(cell, second(l)) |> ignore
    l = cddr(l)
  }
  set(
    q_d_ratweights,
    cons(list2(q_mlist, q_simp), dot2l(symval(q_n_starratweights))),
  )
  |> ignore
  if args is Nil {
    symval(q_d_ratweights)
  } else {
    cons(list1(q_mlist), args)
  }
}

///|
fn pweight(ratout_x : Value) -> Value raise {
  let w = get(ratout_x, q_d_ratweight)
  if w.truthy() {
    w
  } else {
    Fix(0L)
  }
}

///|
fn wtptimes(ratout_x : Value, ratout_y : Value, ratout_wtsofar : Value) -> Value raise {
  let x = ratout_x
  let y = ratout_y
  if ratmac__pz(x) ||
    ratmac__pz(y) ||
    ratmac__gt(ratout_wtsofar, symval(q_d_ratwtlvl)) {
    Fix(0L)
  } else if atom(x) {
    wtpctimes(x, y, ratout_wtsofar)
  } else if atom(y) {
    wtpctimes(y, x, ratout_wtsofar)
  } else if eq(car(x), car(y)) {
    palgsimp(
      car(x),
      wtptimes1(cdr(x), cdr(y), pweight(car(x)), ratout_wtsofar),
      alg(x),
    )
  } else if ratmac__pgp(car(x), car(y)) {
    psimp(car(x), wtpctimes1(y, cdr(x), pweight(car(x)), ratout_wtsofar))
  } else {
    psimp(car(y), wtpctimes1(x, cdr(y), pweight(car(y)), ratout_wtsofar))
  }
}

///|
fn ratout__wtptimes2(
  x : Value,
  y : Value,
  xweight : Value,
  wtsofar : Value,
) -> Value raise {
  if y is Nil {
    Nil
  } else {
    let ii = num_add(num_mul(xweight, num_add(car(x), car(y))), wtsofar)
    if ratmac__gt(ii, symval(q_d_ratwtlvl)) {
      ratout__wtptimes2(x, cddr(y), xweight, wtsofar)
    } else {
      pcoefadd(
        num_add(car(x), car(y)),
        wtptimes(cadr(x), cadr(y), ii),
        ratout__wtptimes2(x, cddr(y), xweight, wtsofar),
      )
    }
  }
}

///|
fn wtptimes1(
  ratout_x : Value,
  ratout_y : Value,
  ratout_xweight : Value,
  ratout_wtsofar : Value,
) -> Value raise {
  let xweight = ratout_xweight
  let wtsofar = ratout_wtsofar
  let mut x = ratout_x
  let mut v = ratout__wtptimes2(x, ratout_y, xweight, wtsofar)
  let mut ustar = v
  while true {
    x = cddr(x)
    if x is Nil {
      return ustar
    }
    // wtptimes3
    let mut y = ratout_y
    let mut e : Value = Fix(0L)
    let mut u : Value = Nil
    let mut c : Value = Nil
    // labels: 0=a1 1=a 2=b 3=e 4=d 5=c 6=return
    let mut lbl = 0
    while lbl != 6 {
      match lbl {
        0 => {
          if y is Nil {
            lbl = 6
            continue
          }
          e = num_add(car(x), car(y))
          c = wtptimes(cadr(y), cadr(x), num_add(wtsofar, num_mul(xweight, e)))
          if ratmac__pz(c) {
            y = cddr(y)
            continue
          } else if v is Nil || ratmac__gt(e, car(v)) {
            v = ptptplus(ustar, list2(e, c))
            ustar = v
            y = cddr(y)
            continue
          } else if equal(e, car(v)) {
            c = pplus(c, cadr(v))
            if ratmac__pz(c) {
              v = ptptdiffer(ustar, list2(car(v), cadr(v)))
              ustar = v
            } else {
              rplaca(cdr(v), c) |> ignore
            }
            y = cddr(y)
            continue
          }
          lbl = 1
        }
        1 => {
          if !(cddr(v) is Nil) && ratmac__gt(caddr(v), e) {
            v = cddr(v)
            continue
          }
          u = cdr(v)
          lbl = 2
        }
        2 => {
          if cdr(u) is Nil || ratmac__lt(cadr(u), e) {
            rplacd(u, cons(e, cons(c, cdr(u)))) |> ignore
            lbl = 3
            continue
          }
          c = pplus(caddr(u), c)
          if ratmac__pz(c) {
            rplacd(u, cdddr(u)) |> ignore
            lbl = 4
            continue
          } else {
            rplaca(cddr(u), c) |> ignore
          }
          lbl = 3
        }
        3 => {
          u = cddr(u)
          lbl = 4
        }
        4 => {
          y = cddr(y)
          if y is Nil {
            lbl = 6
            continue
          }
          e = num_add(car(x), car(y))
          c = wtptimes(cadr(x), cadr(y), num_add(wtsofar, num_mul(xweight, e)))
          if ratmac__pz(c) {
            continue
          }
          lbl = 5
        }
        5 => {
          if !(cdr(u) is Nil) && ratmac__gt(cadr(u), e) {
            u = cddr(u)
            continue
          }
          lbl = 2
        }
        _ => lbl = 6
      }
    }
  }
  Nil
}

///|
fn wtpctimes(c : Value, p : Value, ratout_wtsofar : Value) -> Value raise {
  if atom(p) {
    ctimes(c, p)
  } else {
    psimp(car(p), wtpctimes1(c, cdr(p), pweight(car(p)), ratout_wtsofar))
  }
}

///|
fn wtpctimes1(
  c : Value,
  ratout_x : Value,
  xwt : Value,
  ratout_wtsofar : Value,
) -> Value raise {
  if ratout_x is Nil {
    Nil
  } else {
    let cc = wtptimes(
      c,
      cadr(ratout_x),
      num_add(ratout_wtsofar, num_mul(xwt, car(ratout_x))),
    )
    if ratmac__pz(cc) {
      wtpctimes1(c, cddr(ratout_x), xwt, ratout_wtsofar)
    } else {
      cons(
        car(ratout_x),
        cons(cc, wtpctimes1(c, cddr(ratout_x), xwt, ratout_wtsofar)),
      )
    }
  }
}

///|
fn wtpexpt(ratout_x : Value, ratout_n : Value) -> Value raise {
  if ratmac__eqn(ratout_n, Fix(0L)) {
    Fix(1L)
  } else if ratmac__eqn(ratout_n, Fix(1L)) {
    ratout_x
  } else if evenp(ratout_n) {
    let xn2 = wtpexpt(ratout_x, num_div(ratout_n, Fix(2L)))
    wtptimes(xn2, xn2, Fix(0L))
  } else {
    wtptimes(
      ratout_x,
      wtpexpt(ratout_x, num_sub(ratout_n, Fix(1L))),
      Fix(0L),
    )
  }
}

///|
fn d_horner(e : Value, l : Value) -> Value raise {
  let arg1 = taychk2rat(e)
  with_specials(
    [
      (q_d_ratfac, Nil),
      (q_varlist, cdr(symval(q_d_ratvars))),
      (q_genvar, Nil),
    ],
    () => {
      if mbagp(arg1).truthy() {
        cons(car(arg1), mapcar(u => apply(q_d_horner, cons(u, l)), cdr(arg1)))
      } else {
        let x = d_rat(arg1, l)
        let mut gl = cadddr(car(x))
        let mut vl = caddar(x)
        while gl is Cons(_) && vl is Cons(_) {
          putprop(car(gl), car(vl), q_disrep) |> ignore
          gl = cdr(gl)
          vl = cdr(vl)
        }
        div_star(hornrep(cadr(x)), hornrep(cddr(x)))
      }
    },
  )
}

///|
fn hornrep(p : Value) -> Value raise {
  if atom(p) {
    p
  } else {
    horn_plus(cdr(p), get(car(p), q_disrep))
  }
}

///|
fn horn_plus(l : Value, var_ : Value) -> Value raise {
  let mut l = l
  let mut ans = hornrep(cadr(l))
  while true {
    let last = car(l)
    l = cddr(l)
    if l is Nil {
      return if equal(last, Fix(0L)) {
        ans
      } else {
        list3(list1(q_mtimes), list3(list1(q_mexpt), var_, last), ans)
      }
    } else {
      ans = list3(
        list1(q_mplus),
        hornrep(cadr(l)),
        list3(
          list1(q_mtimes),
          list3(list1(q_mexpt), var_, num_sub(last, car(l))),
          ans,
        ),
      )
    }
  }
  Nil
}

///|
fn d_partfrac(ratout_exp : Value, ratout_var : Value) -> Value raise {
  if mbagp(ratout_exp).truthy() {
    return cons(
      car(ratout_exp),
      mapcar(u => d_partfrac(u, ratout_var), cdr(ratout_exp)),
    )
  }
  if atom(ratout_var) && !among(ratout_var, ratout_exp).truthy() {
    return ratout_exp
  }
  let bs = bind_all([
    (q_d_savefactors, t),
    (q_ear_checkfactors, Nil),
    (q_varlist, list1(ratout_var)),
    (q_d_ratfac, Nil),
    (q_d_algebraic, Nil),
    (q_d_keepfloat, Nil),
    (q_genvar, Nil),
  ])
  defer unbind_all(bs)
  let r = taychk2rat(ratout_exp)
  let ratform = car(r)
  let mut exp_ = cdr(r)
  let var_ = caadr(ratf(ratout_var))
  exp_ = partfrac(exp_, var_)
  // FULL DECOMP?
  exp_ = cons(car(exp_), mapcan(x => partfraca(x), cdr(exp_)))
  add2_star(
    disrep(car(exp_), ratform),
    cons(
      list1(q_mplus),
      mapcar(
        l => {
          let coef = car(l)
          let poly = cadr(l)
          let e = caddr(l)
          list3(
            list1(q_mtimes),
            disrep(coef, ratform),
            list3(list1(q_mexpt), disrep(poly, ratform), num_neg(e)),
          )
        },
        cdr(exp_),
      ),
    ),
  )
}

///|
fn partfraca(llist : Value) -> Value raise {
  let coef = car(llist)
  let poly = cadr(llist)
  let mut nc = ratdivide(coef, poly)
  let mut n = caddr(llist)
  let mut ans : Value = Nil
  while !rzerop(car(nc)).truthy() {
    ans = cons(list3(cdr(nc), poly, n), ans)
    nc = ratdivide(car(nc), poly)
    n = num_sub(n, Fix(1L))
  }
  cons(list3(cdr(nc), poly, n), ans)
}

///|
/// Make the factors in L = (f1 m1 f2 m2 ...) pairwise coprime in VAR, keeping
/// their product. PFACTOR factors over the rationals, treating %i and
/// radicals as variables, so with $ALGEBRAIC, two of its factors can still
/// have a common factor, as x^2+1 and x+%i do. Two factors without algebraic
/// numbers stay coprime, so only pairs with an algebraic factor are checked.
fn coprime_factors(l : Value, var_ : Value) -> Value raise {
  let mut facs = {
    let acc = Collector::new()
    let mut p = l
    while p is Cons(_) {
      acc.add(list2(car(p), cadr(p)))
      p = cddr(p)
    }
    acc.result()
  }
  while true {
    let mut found = false
    let mut xs = facs
    while xs is Cons(_) && !found {
      let x = car(xs)
      let rest = cdr(xs)
      for y in rest.iter() {
        let g = if (palgp(car(x)).truthy() || palgp(car(y)).truthy()) &&
          plusp(pdegree(car(x), var_)) &&
          plusp(pdegree(car(y), var_)) {
          pgcd(car(x), car(y))
        } else {
          Nil
        }
        let fx = if g.truthy() && plusp(pdegree(g, var_)) {
          pquotientchk_safe(car(x), g)
        } else {
          Nil
        }
        let fy = if fx.truthy() { pquotientchk_safe(car(y), g) } else { Nil }
        if fy.truthy() {
          rplaca(x, fx) |> ignore
          rplaca(y, fy) |> ignore
          facs = cons(list2(g, num_add(cadr(x), cadr(y))), facs)
          found = true
          break
        }
      }
      xs = cdr(xs)
    }
    if !found {
      break
    }
  }
  let acc = Collector::new()
  for fm in facs.iter() {
    acc.add(car(fm))
    acc.add(cadr(fm))
  }
  acc.result()
}

///|
fn partfrac(rat : Value, ratout_var : Value) -> Value raise {
  let d = pdivide(car(rat), cdr(rat))
  let wholepart = car(d)
  let mut frpart = cadr(d)
  let nd = ratqu(frpart, cdr(rat))
  let mut num = car(nd)
  let denom = cdr(nd)
  if ratmac__pz(num) {
    cons(wholepart, Nil)
  } else if atom(denom) || ratmac__pgp(ratout_var, car(denom)) {
    cons(rat, Nil)
  } else {
    let oc = oldcontent(denom)
    let mut content = car(oc)
    let mut bpart = cadr(oc)
    let mut parnumer : Value = Nil
    let facl = if symval(q_d_algebraic).truthy() {
      coprime_factors(pfactor(bpart), ratout_var)
    } else {
      pfactor(bpart)
    }
    let mut fl = facl
    while fl is Cons(_) {
      let factor = car(fl)
      let multiplicity = cadr(fl)
      if !zerop(pdegree(factor, ratout_var)) {
        let apart = pexpt(factor, multiplicity)
        bpart = pquotient(bpart, apart)
        let y = bprog(apart, bpart, ratout_var)
        frpart = cdr(ratdivide(ratti(num, cdr(y), t), apart))
        parnumer = cons(
          list3(ratqu(frpart, content), factor, multiplicity),
          parnumer,
        )
        let nc = cdr(ratdivide(ratqu(ratti(num, car(y), t), content), bpart))
        num = car(nc)
        content = cdr(nc)
      }
      fl = cddr(fl)
    }
    cons(wholepart, parnumer)
  }
}

// $RATDIFF TAKES DERIVATIVES FAST. IT ASSUMES THAT THE ONLY ENTITY WHICH
// DEPENDS ON X IS X ITSELF. THAT IS, DEPENDENCIES DECLARED EXPLICITLY OR
// IMPLICITLY ARE TOTALLY IGNORED. RATDIFF(F(X),X) IS 0. RATDIFF(Y,X) IS 0.
// ANY OTHER USAGE MUST GO THROUGH $DIFF. FURTHERMORE, X IS ASSUMED TO BE AN
// ATOM OR A SINGLE ITEM ON VARLIST. E.G. X MIGHT BE SIN(U), BUT NOT
// 2*SIN(U).

///|
fn d_ratdiff(p : Value, ratout_x : Value) -> Value raise {
  let mut p = p
  if d_ratp(p).truthy() {
    p = minimize_varlist(
      if memq(q_trunc, cdar(p)).truthy() {
        d_taytorat(p)
      } else {
        p
      },
    )
  }
  let formflag = d_ratp(p).truthy()
  let bs = bind_all([(q_varlist, Nil), (q_genvar, Nil)])
  defer unbind_all(bs)
  let x = ratout_x
  newvar(x) |> ignore
  newvar(p) |> ignore
  if !every(
      ex => alike1(x, ex).truthy() || free(ex, x).truthy(),
      symval(q_varlist),
    ) {
    merr("ratdiff: first argument must be a polynomial in ~M; found: ~M", [
      x, p,
    ])
    |> ignore
  }
  p = ratf(p)
  let xv = caadr(ratf(x))
  p = cons(car(p), ratderivative(cdr(p), xv))
  if formflag {
    p
  } else {
    d_ratdisrep(p)
  }
}

///|
fn ratout__pfet1(m : Value, v : Value) -> Value raise {
  if atom(m) {
    m
  } else if eq(caar(m), q_mplus) {
    cons(list1(q_mplus), mapcar(s => d_partfrac(s, v), cdr(m)))
  } else {
    d_partfrac(m, v)
  }
}

///|
fn ratout__sssqfr(x : Value) -> Value raise {
  with_special(q_dosimp, t, () => simplify(d_sqfr(x)))
}

///|
fn d_pfet(m : Value) -> Value raise {
  let bs = bind_all([
    (q_d_pfeformat, Nil),
    (q_varlist, Nil),
    (q_d_factorflag, Nil),
  ])
  defer unbind_all(bs)
  let mut m = m
  set(q_d_pfeformat, t) |> ignore
  newvar(m) |> ignore
  let listov = symval(q_varlist)
  for r in listov.iter() {
    m = ratout__pfet1(m, r)
  }
  m = simplify(m)
  m = if atom(m) {
    m
  } else if eq(caar(m), q_mplus) {
    cons(list1(q_mplus), mapcar(x => d_ratexpand(x), cdr(m)))
  } else {
    d_ratexpand(m)
  }
  if atom(m) {
    m
  } else if eq(caar(m), q_mplus) {
    cons(list1(q_mplus), mapcar(x => ratout__sssqfr(x), cdr(m)))
  } else {
    ratout__sssqfr(m)
  }
}
