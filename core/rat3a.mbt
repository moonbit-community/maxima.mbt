// Port of src/rat3a.lisp: the new Rational Function Package, part 1.
// Coefficient and polynomial routines (CRE polynomials; see ratmac.mbt for
// the representation) required by the rest of the package.

///|
/// CQUOTIENT: quotient of two coefficients. With MODULUS, multiply by the
/// modular reciprocal; otherwise exact integer division (RAT-ERROR if not
/// exact) or float division.
fn cquotient(a : Value, b : Value) -> Value raise {
  if eql(a, Fix(0L)) {
    Fix(0L)
  } else if symval(q_modulus) is Nil {
    if floatp(a) || floatp(b) {
      num_div(a, b)
    } else {
      let (q, r) = num_floor(a, b~)
      if eql(Fix(0L), r) {
        q
      } else {
        ratmac__rat_error("CQUOTIENT: quotient is not exact")
      }
    }
  } else {
    ctimes(a, crecip(b))
  }
}

///|
/// ALG: the tellrat property of (car l) when $algebraic; nil for atoms.
fn alg(l : Value) -> Value raise {
  if atom(l) {
    Nil
  } else {
    ratmac__algv(car(l))
  }
}

///|
fn rat3a__alg(l : Value) -> Value {
  if atom(l) {
    Nil
  } else {
    ratmac__algv(car(l))
  }
}

///|
/// PACOEFP: X is a bare coefficient or a polynomial in an algebraic variable.
fn pacoefp(x : Value) -> Value raise {
  lbool(atom(x) || rat3a__alg(x).truthy())
}

///|
fn rat3a__pacoefp(x : Value) -> Bool {
  atom(x) || rat3a__alg(x).truthy()
}

///|
/// LEADTERM: the leading term of POLY as a polynomial.
fn leadterm(poly : Value) -> Value raise {
  if atom(poly) {
    poly
  } else {
    list3(car(poly), cadr(poly), caddr(poly))
  }
}

///|
/// CRECIP: inverse of N mod MODULUS, normalised to (-modulus/2, modulus/2],
/// by the extended Euclidean algorithm. Fixnum fast path for moduli < 2^15.
fn crecip(n : Value) -> Value raise {
  let m = symval(q_modulus)
  let mm = match m {
    Fix(v) if v >= 0L && v < 32768L => v
    _ => return crecip_general(n)
  }
  if !(num_le(Fix(-mm), n) && num_le(n, Fix(mm))) {
    merr("N is out of range [-MODULUS, MODULUS] in crecip.", []) |> ignore
  }
  let mut nn = to_int64(n)
  if nn < 0L {
    nn = nn + mm
  }
  let mut md = mm
  let mut remainder = nn
  let mut a = 1L
  let mut b = 0L
  let mod_copy = mm
  while remainder != 1L {
    if remainder == 0L {
      merr("CRECIP: ~M does not have an inverse with modulus=~M", [
        Fix(nn),
        symval(q_modulus),
      ])
      |> ignore
    }
    let quot = md / remainder
    let rem = md % remainder
    md = remainder
    remainder = rem
    let na = b - a * quot
    b = a
    a = na
  }
  if mod_copy == 2L {
    Fix(a & 1L)
  } else {
    let r = a % mod_copy
    let r = if r < 0L { r + mod_copy } else { r }
    if 2L * r <= mod_copy {
      Fix(r)
    } else {
      Fix(r - mod_copy)
    }
  }
}

///|
/// CRECIP-GENERAL: CRECIP for any modulus.
fn crecip_general(n : Value) -> Value raise {
  let modulus = symval(q_modulus)
  let mut md = modulus
  let mut remainder = if minusp(n) { num_add(n, modulus) } else { n }
  let mut a : Value = Fix(1L)
  let mut b : Value = Fix(0L)
  while !ratmac__eqn(remainder, Fix(1L)) {
    if zerop(remainder) {
      merr("CRECIP: ~M does not have an inverse with modulus=~M", [
        n,
        symval(q_modulus),
      ])
      |> ignore
    }
    let quotient = num_truncate(md, b=remainder).0
    let nmd = remainder
    let nrem = num_sub(md, num_mul(quotient, remainder))
    md = nmd
    remainder = nrem
    let na = num_sub(b, num_mul(a, quotient))
    b = a
    a = na
  }
  cmod(a)
}

///|
/// CEXPT: raise a coefficient to a non-negative integral power.
fn cexpt(base : Value, pow : Value) -> Value raise {
  if !(integerp(pow) && !minusp(pow)) {
    raise LispError::SimpleError(
      "CEXPT only defined for non-negative integral exponents.",
    )
  }
  if symval(q_modulus) is Nil {
    expt(base, pow)
  } else {
    let mut base = base
    let mut s = if oddp(pow) { base } else { Fix(1L) }
    let mut pow = ash(pow, -1)
    while !zerop(pow) {
      base = cmod(num_mul(base, base))
      if oddp(pow) {
        s = cmod(num_mul(s, base))
      }
      pow = ash(pow, -1)
    }
    s
  }
}

///|
/// SET-MODULUS: set MODULUS to a positive integer or nil.
fn set_modulus(m : Value) -> Value raise {
  if m is Nil || (integerp(m) && num_ge(m, Fix(1L))) {
    set(q_modulus, m) |> ignore
  } else {
    raise LispError::SimpleError("modulus must be a positive integer or nil")
  }
  Nil
}

///|
/// PCOEFADD: prepend the term COEFF*x^EXPONENT to the terms REMAINDER.
fn pcoefadd(exponent : Value, coeff : Value, remainder : Value) -> Value raise {
  if ratmac__pz(coeff) {
    remainder
  } else {
    cons(exponent, cons(coeff, remainder))
  }
}

///|
/// PPLUS: add two polynomials.
fn pplus(x : Value, y : Value) -> Value raise {
  if atom(x) {
    pcplus(x, y)
  } else if atom(y) {
    pcplus(y, x)
  } else if eq(car(x), car(y)) {
    psimp(car(x), ptptplus(cdr(y), cdr(x)))
  } else if ratmac__pgp(car(x), car(y)) {
    psimp(car(x), ptcplus(y, cdr(x)))
  } else {
    psimp(car(y), ptcplus(x, cdr(y)))
  }
}

///|
/// PTPTPLUS: add two lists of polynomial terms.
fn ptptplus(x : Value, y : Value) -> Value raise {
  if x is Nil {
    y
  } else if y is Nil {
    x
  } else if ratmac__eqn(car(x), car(y)) {
    pcoefadd(
      car(x),
      pplus(cadr(x), cadr(y)),
      ptptplus(cddr(x), cddr(y)),
    )
  } else if ratmac__gt(car(x), car(y)) {
    cons(car(x), cons(cadr(x), ptptplus(cddr(x), y)))
  } else {
    cons(car(y), cons(cadr(y), ptptplus(x, cddr(y))))
  }
}

///|
/// PCPLUS: add a coefficient to a polynomial.
fn pcplus(c : Value, p : Value) -> Value raise {
  if atom(p) {
    cplus(p, c)
  } else {
    psimp(car(p), ptcplus(c, cdr(p)))
  }
}

///|
/// PTCPLUS: add C (free of the main variable) to a list of terms.
fn ptcplus(c : Value, terms : Value) -> Value raise {
  if ratmac__pz(c) {
    terms
  } else if terms is Nil {
    list2(Fix(0L), c)
  } else if zerop(car(terms)) {
    pcoefadd(Fix(0L), pplus(c, cadr(terms)), Nil)
  } else {
    cons(car(terms), cons(cadr(terms), ptcplus(c, cddr(terms))))
  }
}

///|
/// PDIFFERENCE: X - Y.
fn pdifference(x : Value, y : Value) -> Value raise {
  if atom(x) {
    pcdiffer(x, y)
  } else if atom(y) {
    pcplus(num_neg(y), x)
  } else if eq(car(x), car(y)) {
    psimp(car(x), ptptdiffer(cdr(x), cdr(y)))
  } else if ratmac__pgp(car(x), car(y)) {
    psimp(car(x), ptcdiffer_minus(cdr(x), y))
  } else {
    psimp(car(y), ptcdiffer(x, cdr(y)))
  }
}

///|
/// PTPTDIFFER: difference of two lists of terms in the same variable.
fn ptptdiffer(x : Value, y : Value) -> Value raise {
  if x is Nil {
    ptminus(y)
  } else if y is Nil {
    x
  } else if ratmac__eqn(car(x), car(y)) {
    pcoefadd(
      car(x),
      pdifference(cadr(x), cadr(y)),
      ptptdiffer(cddr(x), cddr(y)),
    )
  } else if ratmac__gt(car(x), car(y)) {
    cons(car(x), cons(cadr(x), ptptdiffer(cddr(x), y)))
  } else {
    cons(car(y), cons(pminus(cadr(y)), ptptdiffer(x, cddr(y))))
  }
}

///|
/// PCDIFFER: C - P for a coefficient C.
fn pcdiffer(c : Value, p : Value) -> Value raise {
  if atom(p) {
    cdifference(c, p)
  } else {
    psimp(car(p), ptcdiffer(c, cdr(p)))
  }
}

///|
/// PTCDIFFER: C minus the polynomial given by TERMS.
fn ptcdiffer(c : Value, terms : Value) -> Value raise {
  if terms is Nil {
    if ratmac__pz(c) {
      Nil
    } else {
      list2(Fix(0L), c)
    }
  } else if zerop(car(terms)) {
    pcoefadd(Fix(0L), pdifference(c, cadr(terms)), Nil)
  } else {
    cons(car(terms), cons(pminus(cadr(terms)), ptcdiffer(c, cddr(terms))))
  }
}

///|
/// PTCDIFFER-MINUS: the polynomial given by TERMS minus C.
fn ptcdiffer_minus(terms : Value, c : Value) -> Value raise {
  if ratmac__pz(c) {
    terms
  } else if terms is Nil {
    list2(Fix(0L), pminus(c))
  } else if zerop(car(terms)) {
    pcoefadd(Fix(0L), pdifference(cadr(terms), c), Nil)
  } else {
    cons(car(terms), cons(cadr(terms), ptcdiffer_minus(cddr(terms), c)))
  }
}

///|
/// PCSUB: substitute VALS for VARS (sorted by POINTERGP) in P.
fn pcsub(p : Value, vals : Value, vars : Value) -> Value raise {
  if vals is Nil || atom(p) {
    p
  } else if eq(car(p), car(vars)) {
    ptcsub(cdr(p), car(vals), cdr(vals), cdr(vars))
  } else if ratmac__pgp(car(vars), car(p)) {
    pcsub(p, cdr(vals), cdr(vars))
  } else {
    psimp(car(p), ptcsub_args(cdr(p), vals, vars))
  }
}

///|
/// PCSUBST: substitute VAL for VAR2 in P.
fn pcsubst(p : Value, val : Value, var2 : Value) -> Value raise {
  if atom(p) {
    p
  } else if eq(car(p), var2) {
    ptcsub(cdr(p), val, Nil, Nil)
  } else if ratmac__pgp(var2, car(p)) {
    p
  } else {
    psimp(car(p), ptcsub_args(cdr(p), list1(val), list1(var2)))
  }
}

///|
/// PTCSUB: substitute VAL for the main variable of TERMS (Horner's scheme),
/// substituting VALS for VARS in the coefficients.
fn ptcsub(terms : Value, val : Value, vals : Value, vars : Value) -> Value raise {
  if eql(val, Fix(0L)) {
    pcsub(ptterm(terms, Fix(0L)), vals, vars)
  } else {
    let mut ts = cddr(terms)
    let mut ans = pcsub(cadr(terms), vals, vars)
    let mut last_le = car(terms)
    while !(ts is Nil) {
      let nts = cddr(ts)
      let nans = pplus(
        ptimes(ans, pexpt(val, num_sub(last_le, car(ts)))),
        pcsub(cadr(ts), vals, vars),
      )
      let nlast = car(ts)
      ts = nts
      ans = nans
      last_le = nlast
    }
    ptimes(ans, pexpt(val, last_le))
  }
}

///|
/// PTCSUB-ARGS: substitute VALS for VARS in the coefficients of TERMS.
fn ptcsub_args(terms : Value, vals : Value, vars : Value) -> Value raise {
  let acc = Collector::new()
  let mut t = terms
  while t is Cons(_) {
    let e = car(t)
    let coef = pcsub(cadr(t), vals, vars)
    if !ratmac__pz(coef) {
      acc.add(e)
      acc.add(coef)
    }
    t = cddr(t)
  }
  acc.result()
}

///|
/// PCSUBSTY: like PCSUB but sorts VARS (and accepts atoms).
fn pcsubsty(vals : Value, vars : Value, p : Value) -> Value raise {
  if vars is Nil {
    p
  } else if atom(vars) {
    pcsub(p, list1(vals), list1(vars))
  } else {
    let pairs = sort_list(mapcar2((a, b) => cons(a, b), vars, vals), (a, b) => ratmac__pgp(
      car(a),
      car(b),
    ))
    pcsub(p, mapcar(x => cdr(x), pairs), mapcar(x => car(x), pairs))
  }
}

///|
/// PDERIVATIVE: derivative of P with respect to VARI.
fn pderivative(p : Value, vari : Value) -> Value raise {
  if atom(p) {
    Fix(0L)
  } else if eq(vari, car(p)) {
    psimp(car(p), ptderivative(cdr(p)))
  } else if ratmac__pgp(vari, car(p)) {
    Fix(0L)
  } else {
    psimp(car(p), ptderivative_coeffs(cdr(p), vari))
  }
}

///|
fn ptderivative(terms : Value) -> Value raise {
  if terms is Nil || zerop(car(terms)) {
    Nil
  } else {
    pcoefadd(
      num_sub(car(terms), Fix(1L)),
      pctimes(cmod(car(terms)), cadr(terms)),
      ptderivative(cddr(terms)),
    )
  }
}

///|
fn ptderivative_coeffs(terms : Value, vari : Value) -> Value raise {
  if terms is Nil {
    Nil
  } else {
    pcoefadd(
      car(terms),
      pderivative(cadr(terms), vari),
      ptderivative_coeffs(cddr(terms), vari),
    )
  }
}

///|
/// PDIVIDE: division with remainder in F[V] (V the main variable of X);
/// returns (Q R), both rational functions.
fn pdivide(x : Value, y : Value) -> Value raise {
  if ratmac__pz(y) {
    ratmac__rat_error("PDIVIDE: Quotient by zero")
  } else if rat3a__pacoefp(y) {
    list2(ratreduce(x, y), rzero())
  } else if rat3a__pacoefp(x) {
    list2(rzero(), cons(x, Fix(1L)))
  } else if ratmac__pgp(car(x), car(y)) {
    list2(ratreduce(x, y), rzero())
  } else {
    let lcy = cons(caddr(y), Fix(1L))
    let mut q = rzero()
    let mut r = cons(x, Fix(1L))
    let mut k = num_sub(pdegree(x, car(y)), cadr(y))
    while !minusp(k) {
      let lcr = cons(caddr(car(r)), cdr(r))
      let quot = ratquotient(lcr, lcy)
      let quot_simp = cons(psimp(car(y), list2(k, car(quot))), cdr(quot))
      q = ratplus(q, quot_simp)
      r = ratplus(r, rattimes(cons(pminus(y), Fix(1L)), quot_simp, t))
      k = num_sub(pdegree(car(r), car(y)), cadr(y))
    }
    list2(q, r)
  }
}

///|
/// PEXPT: P^N for an integer N.
fn pexpt(p : Value, n : Value) -> Value raise {
  if ratmac__eqn(n, Fix(0L)) {
    Fix(1L)
  } else if ratmac__eqn(n, Fix(1L)) {
    p
  } else if minusp(n) {
    pquotient(Fix(1L), pexpt(p, num_neg(n)))
  } else if atom(p) {
    cexpt(p, n)
  } else if rat3a__alg(p).truthy() {
    pexptsq(p, n)
  } else if cdddr(p) is Nil {
    psimp(car(p), pcoefadd(num_mul(n, cadr(p)), pexpt(caddr(p), n), Nil))
  } else {
    // Binomial expansion of (b + rest)^n with b the leading term.
    let descending_powers = p__descending_powers(
      list3(car(p), cadr(p), caddr(p)),
      n,
    )
    let rest = psimp(car(p), cdddr(p))
    let mut b_list = descending_powers
    let mut k = 0L
    let mut n_choose_k : Value = Fix(1L)
    let mut rest_pow : Value = Fix(1L)
    let mut sum = car(descending_powers)
    while !num_gt(Fix(k), n) {
      b_list = cdr(b_list)
      k = k + 1L
      n_choose_k = num_truncate(
        num_mul(n_choose_k, num_sub(num_add(n, Fix(1L)), Fix(k))),
        b=Fix(k),
      ).0
      rest_pow = match k {
        1L => rest
        2L => pexpt(rest, Fix(2L))
        _ => ptimes(rest, rest_pow)
      }
      sum = pplus(
        sum,
        if b_list.truthy() {
          ptimes(pctimes(cmod(n_choose_k), rest_pow), car(b_list))
        } else {
          pctimes(cmod(n_choose_k), rest_pow)
        },
      )
    }
    sum
  }
}

///|
/// P-DESCENDING-POWERS: (P^N P^(N-1) ... P).
fn p__descending_powers(p : Value, n : Value) -> Value raise {
  let mut lst = list1(p)
  let cnt = to_int(n) - 1
  for _i in 0..<cnt {
    lst = cons(ptimes(p, car(lst)), lst)
  }
  lst
}

///|
/// PMINUSP: is the leading numerical coefficient negative?
fn pminusp(p : Value) -> Value raise {
  lbool(rat3a__pminusp(p))
}

///|
fn rat3a__pminusp(p : Value) -> Bool raise {
  let mut p = p
  while !realp(p) {
    if atom(p) {
      // (p-lc p) of a non-real atom is a Lisp error.
      raise type_error(p, "list")
    }
    p = caddr(p)
  }
  minusp(p)
}

///|
/// PMINUS: negation.
fn pminus(p : Value) -> Value raise {
  if atom(p) {
    num_neg(p)
  } else {
    cons(car(p), ptminus(cdr(p)))
  }
}

///|
fn ptminus(x : Value) -> Value raise {
  let acc = Collector::new()
  let mut t = x
  while t is Cons(_) {
    acc.add(car(t))
    acc.add(pminus(cadr(t)))
    t = cddr(t)
  }
  acc.result()
}

///|
/// PMOD: reduce P modulo MODULUS.
fn pmod(p : Value) -> Value raise {
  if atom(p) {
    cmod(p)
  } else {
    let acc = Collector::new()
    let mut t = cdr(p)
    while t is Cons(_) {
      let e = car(t)
      let coef = pmod(cadr(t))
      if !ratmac__pz(coef) {
        acc.add(e)
        acc.add(coef)
      }
      t = cddr(t)
    }
    psimp(car(p), acc.result())
  }
}

///|
/// PQUOTIENT: exact quotient X/Y over the integers (RAT-ERROR otherwise).
fn pquotient(x : Value, y : Value) -> Value raise {
  if atom(x) {
    if ratmac__pz(x) {
      Fix(0L)
    } else if atom(y) {
      cquotient(x, y)
    } else if rat3a__alg(y).truthy() {
      paquo(x, y)
    } else {
      ratmac__rat_error(
        "PQUOTIENT: Quotient by a polynomial of higher degree (case 1)",
      )
    }
  } else if atom(y) {
    if ratmac__pz(y) {
      ratmac__rat_error("PQUOTIENT: Quotient by zero")
    } else if symval(q_modulus).truthy() {
      pctimes(crecip(y), x)
    } else {
      pcquotient(x, y)
    }
  } else if rat3a__alg(y).truthy() {
    let v = with_special(q_d_algebraic, Nil, () => ratmac__ignore_rat_err(() => pquotient(
      x, y,
    )))
    if v.truthy() {
      v
    } else {
      patimes(x, rainv(y))
    }
  } else if ratmac__pgp(car(x), car(y)) {
    pcquotient(x, y)
  } else if ratmac__pgp(car(y), car(x)) {
    ratmac__rat_error(
      "PQUOTIENT: Quotient by a polynomial of higher degree (case 2a)",
    )
  } else if ratmac__gt(cadr(y), cadr(x)) {
    ratmac__rat_error(
      "PQUOTIENT: Quotient by a polynomial of higher degree (case 2b)",
    )
  } else {
    psimp(car(x), ptptquotient(cdr(x), cdr(y)))
  }
}

///|
/// PCQUOTIENT: divide each coefficient of P by Q (free of P's main var).
fn pcquotient(p : Value, q : Value) -> Value raise {
  let acc = Collector::new()
  let mut t = cdr(p)
  while t is Cons(_) {
    acc.add(car(t))
    acc.add(pquotient(cadr(t), q))
    t = cddr(t)
  }
  psimp(car(p), acc.result())
}

///|
/// PTPTQUOTIENT: exact long division of two term lists in one variable.
fn ptptquotient(u : Value, v : Value) -> Value raise {
  let mut q_terms : Value = Nil
  let mut u = u
  while !(u is Nil) {
    if ratmac__lt(car(u), car(v)) {
      ratmac__rat_error("PTPTQUOTIENT: Polynomial quotient is not exact")
      |> ignore
    }
    let le_q = num_sub(car(u), car(v))
    let lc_q = pquotient(cadr(u), cadr(v))
    q_terms = cons(lc_q, cons(le_q, q_terms))
    u = ptpt_subtract_powered_product(
      cddr(u),
      cddr(v),
      first(q_terms),
      second(q_terms),
    )
  }
  nreverse(q_terms)
}

///|
/// PTPT-SUBTRACT-POWERED-PRODUCT: terms of A - x^K * B * Q.
fn ptpt_subtract_powered_product(
  u : Value,
  v : Value,
  q : Value,
  k : Value,
) -> Value raise {
  if v is Nil {
    u
  } else if u is Nil {
    pcetimes1(v, k, pminus(q))
  } else {
    let hipow = num_add(car(v), k)
    if ratmac__gt(hipow, car(u)) {
      pcoefadd(
        hipow,
        ptimes(q, pminus(cadr(v))),
        ptpt_subtract_powered_product(u, cddr(v), q, k),
      )
    } else if ratmac__eqn(hipow, car(u)) {
      pcoefadd(
        hipow,
        pdifference(cadr(u), ptimes(q, cadr(v))),
        ptpt_subtract_powered_product(cddr(u), cddr(v), q, k),
      )
    } else {
      cons(
        car(u),
        cons(cadr(u), ptpt_subtract_powered_product(cddr(u), v, q, k)),
      )
    }
  }
}

///|
fn algord(var2 : Value) -> Value raise {
  if symval(q_d_algebraic).truthy() {
    get(var2, q_algord)
  } else {
    Nil
  }
}

///|
/// PSIMP: the polynomial with main variable VAR2 and terms X, simplified
/// (a constant term alone collapses to the coefficient; with ALGORD, fix
/// wrongly ordered coefficients).
fn psimp(var2 : Value, x : Value) -> Value raise {
  if x is Nil {
    Fix(0L)
  } else if atom(x) {
    x
  } else if zerop(car(x)) {
    cadr(x)
  } else if algord(var2).truthy() {
    let mut p = x
    let mut sum : Value = Fix(0L)
    while !(p is Nil) {
      if !(atom(cadr(p)) || ratmac__pgp(var2, car(cadr(p)))) {
        sum = pplus(
          sum,
          if zerop(car(p)) {
            cadr(p)
          } else {
            ptimes(list3(var2, car(p), Fix(1L)), cadr(p))
          },
        )
        rplaca(cdr(p), Fix(0L)) |> ignore
      }
      p = cddr(p)
    }
    if ratmac__pz(sum) {
      cons(var2, x)
    } else {
      pplus(sum, p__delete_zeros(var2, x))
    }
  } else {
    cons(var2, x)
  }
}

///|
/// P-DELETE-ZEROS: destructively delete zero-coefficient terms of X.
fn p__delete_zeros(var2 : Value, x : Value) -> Value raise {
  let x = cons(Nil, x)
  let mut p = x
  while !(cdr(p) is Nil) {
    if ratmac__pz(cadr(cdr(p))) {
      rplacd(p, cddr(cdr(p))) |> ignore
    } else {
      p = cddr(p)
    }
  }
  with_special(q_d_algebraic, Nil, () => psimp(var2, cdr(x)))
}

///|
/// PTTERM: the coefficient of z^N in the terms X.
fn ptterm(x : Value, n : Value) -> Value raise {
  let mut x = x
  while !(x is Nil) {
    if ratmac__lt(car(x), n) {
      return Fix(0L)
    } else if ratmac__eqn(car(x), n) {
      return cadr(x)
    }
    x = cddr(x)
  }
  Fix(0L)
}

///|
/// PTIMES: product of two polynomials.
fn ptimes(x : Value, y : Value) -> Value raise {
  if atom(x) {
    if ratmac__pz(x) {
      Fix(0L)
    } else {
      pctimes(x, y)
    }
  } else if atom(y) {
    if ratmac__pz(y) {
      Fix(0L)
    } else {
      pctimes(y, x)
    }
  } else if eq(car(x), car(y)) {
    palgsimp(car(x), ptimes1(cdr(x), cdr(y)), rat3a__alg(x))
  } else if ratmac__pgp(car(x), car(y)) {
    psimp(car(x), pctimes1(y, cdr(x)))
  } else {
    psimp(car(y), pctimes1(x, cdr(y)))
  }
}

///|
/// PTIMES1: product of two term lists in the same variable. The first
/// term of X times Y seeds the result, which the remaining terms are merged
/// into destructively.
fn ptimes1(x : Value, y_orig : Value) -> Value raise {
  let mut uuu = pcetimes1(y_orig, car(x), cadr(x))
  let mut vvv = uuu
  let mut x = cddr(x)
  while !(x is Nil) {
    let mut y = y_orig
    let xe = car(x)
    let xc = cadr(x)
    let mut e : Value = Nil
    let mut u : Value = Nil
    let mut c : Value = Nil
    // prog labels: 0=a1 1=a 2=b 3=e 4=d 5=c 6=return
    let mut lbl = 0
    while lbl != 6 {
      match lbl {
        0 => {
          if y is Nil {
            lbl = 6
            continue
          }
          e = num_add(xe, car(y))
          c = ptimes(cadr(y), xc)
          if ratmac__pz(c) {
            y = cddr(y)
            continue
          } else if vvv is Nil || ratmac__gt(e, car(vvv)) {
            vvv = ptptplus(uuu, list2(e, c))
            uuu = vvv
            y = cddr(y)
            continue
          } else if ratmac__eqn(e, car(vvv)) {
            c = pplus(c, cadr(vvv))
            if ratmac__pz(c) {
              vvv = ptptdiffer(uuu, list2(car(vvv), cadr(vvv)))
              uuu = vvv
            } else {
              rplaca(cdr(vvv), c) |> ignore
            }
            y = cddr(y)
            continue
          }
          lbl = 1
        }
        1 => {
          if !(cddr(vvv) is Nil) && ratmac__gt(caddr(vvv), e) {
            vvv = cddr(vvv)
            continue
          }
          u = cdr(vvv)
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
          e = num_add(xe, car(y))
          c = ptimes(cadr(y), xc)
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
    x = cddr(x)
  }
  uuu
}

///|
/// PCETIMES1: C * V^E * Y for terms Y.
fn pcetimes1(y : Value, e : Value, c : Value) -> Value raise {
  let acc = Collector::new()
  let mut t = y
  while t is Cons(_) {
    let ex = car(t)
    let coef = ptimes(c, cadr(t))
    if !ratmac__pz(coef) {
      acc.add(num_add(e, ex))
      acc.add(coef)
    }
    t = cddr(t)
  }
  acc.result()
}

///|
fn pctimes(c : Value, p : Value) -> Value raise {
  if atom(p) {
    ctimes(c, p)
  } else {
    psimp(car(p), pctimes1(c, cdr(p)))
  }
}

///|
fn pctimes1(c : Value, terms : Value) -> Value raise {
  let acc = Collector::new()
  let mut t = terms
  while t is Cons(_) {
    let ex = car(t)
    let coef = ptimes(c, cadr(t))
    if !ratmac__pz(coef) {
      acc.add(ex)
      acc.add(coef)
    }
    t = cddr(t)
  }
  acc.result()
}

///|
fn leadalgcoef(p : Value) -> Value raise {
  let mut p = p
  while !rat3a__pacoefp(p) {
    p = caddr(p)
  }
  p
}

///|
fn painvmod(q : Value) -> Value raise {
  if atom(q) {
    crecip(q)
  } else {
    paquo(list3(car(q), Fix(0L), Fix(1L)), q)
  }
}

///|
/// PALGSIMP: reduce P modulo the minimal polynomial TELL = (N X) -> X^(1/N).
fn palgsimp(var2 : Value, p : Value, tell : Value) -> Value raise {
  psimp(
    var2,
    if tell is Nil || p is Nil || ratmac__lt(car(p), car(tell)) {
      p
    } else if cddr(tell) is Nil {
      pasimp1(p, car(tell), cadr(tell))
    } else {
      pgcd1(p, tell)
    },
  )
}

///|
/// PASIMP1: assumes deg <= (car p); destructive.
fn pasimp1(p : Value, deg : Value, kernel : Value) -> Value raise {
  let mut a = p
  let mut b = p
  while !(a is Nil || ratmac__lt(car(a), deg)) {
    rplaca(a, num_sub(car(a), deg)) |> ignore
    let na = cddr(a)
    b = a
    a = na
  }
  rplacd(cdr(b), Nil) |> ignore
  ptptplus(pctimes1(kernel, p), a)
}

///|
fn monize(p : Value) -> Value raise {
  if atom(p) {
    if ratmac__pz(p) {
      p
    } else {
      Fix(1L)
    }
  } else {
    cons(car(p), pmonicize(copy_list(cdr(p))))
  }
}

///|
/// PMONICIZE: make the terms P monic (clobbers P).
fn pmonicize(p : Value) -> Value raise {
  if equal(cadr(p), Fix(1L)) {
    p
  } else {
    pmon1(painvmod(leadalgcoef(cadr(p))), p) |> ignore
    p
  }
}

///|
fn pmon1(mult : Value, l : Value) -> Value raise {
  if l.truthy() {
    pmon1(mult, cddr(l)) |> ignore
    let v = ptimes(mult, cadr(l))
    rplaca(cdr(l), v) |> ignore
    v
  } else {
    Nil
  }
}

///|
/// PMONZ: A^(N-1)*P(X/A), A the leading coefficient.
fn pmonz(poly : Value) -> Value raise {
  let poly = pabs(poly)
  let lc = caddr(poly)
  if equal(lc, Fix(1L)) {
    poly
  } else {
    let mut p = cdddr(poly)
    let p1 = list3(car(poly), cadr(poly), Fix(1L))
    let mut mult : Value = Fix(1L)
    let mut deg = num_sub(cadr(poly), Fix(1L))
    while !(p is Nil) {
      mult = ptimes(mult, pexpt(lc, num_sub(deg, car(p))))
      nconc(p1, list2(car(p), ptimes(mult, cadr(p)))) |> ignore
      let np = cddr(p)
      deg = car(p)
      p = np
    }
    p1
  }
}

// THESE ARE ROUTINES FOR MANIPULATING ALGEBRAIC NUMBERS

///|
fn algnormal(p : Value) -> Value raise {
  car(rquotient(p, leadalgcoef(p)))
}

///|
fn algcontent(p : Value) -> Value raise {
  let lcf = leadalgcoef(p)
  let r = rquotient(p, lcf)
  let prim = car(r)
  let denom = cdr(r)
  list2(ratreduce(lcf, denom), prim)
}

///|
/// RQUOTIENT: finds the pseudo quotient if the pseudo remainder is 0.
fn rquotient(p : Value, q : Value) -> Value raise {
  with_special(q_algfac_star, Nil, () => {
    let mut p = p
    let mut q = q
    if equal(p, q) {
      return cons(Fix(1L), Fix(1L))
    }
    if atom(q) {
      return ratreduce(p, q)
    }
    let mut a = testdivide(p, q)
    if a.truthy() {
      return cons(a, Fix(1L))
    }
    if rat3a__alg(q).truthy() {
      return rattimes(cons(p, Fix(1L)), rainv(q), t)
    }
    a = leadalgcoef(q)
    if rat3a__alg(a).truthy() {
      a = rainv(a)
      p = ptimes(p, car(a))
      q = ptimes(q, car(a))
      a = cdr(a)
    }
    let e = num_add(num_add(Fix(1L), num_neg(cadr(q))), pdegree(p, car(q)))
    if minusp(e) {
      ratmac__rat_error(
        "RQUOTIENT: Quotient by a polynomial of higher degree",
      )
      |> ignore
    }
    a = pexpt(a, e)
    let first = {
      let v = testdivide(ptimes(a, p), q)
      if v.truthy() {
        v
      } else {
        a = pexpt(caddr(q), e)
        pquotient(ptimes(a, p), q)
      }
    }
    ratreduce(first, a)
  })
}

///|
fn patimes(x : Value, r : Value) -> Value raise {
  pquotientchk(ptimes(x, car(r)), cdr(r))
}

///|
fn paquo(x : Value, y : Value) -> Value raise {
  patimes(x, rainv(y))
}

///|
fn mpget(var2 : Value) -> Value raise {
  let var2 = alg(var2)
  if var2 is Nil {
    Nil
  } else if cddr(var2).truthy() {
    var2
  } else {
    list4(car(var2), Fix(1L), Fix(0L), pminus(cadr(var2)))
  }
}

///|
/// RAINV: the inverse of Q as a rational function (using the minimal
/// polynomial of its main variable when algebraic).
fn rainv(q : Value) -> Value raise {
  if atom(q) {
    if symval(q_modulus).truthy() {
      cons(crecip(q), Fix(1L))
    } else {
      cons(Fix(1L), q)
    }
  } else {
    let p = mpget(q)
    with_special(q_var, car(q), () => {
      if p is Nil {
        cons(Fix(1L), q)
      } else {
        let var_ = symval(q_var)
        let p = car(
          with_special(q_d_ratalgdenom, Nil, () => bprog(q, cons(var_, p), var_)),
        )
        rattimes(cons(car(p), Fix(1L)), rainv(cdr(p)), t)
      }
    })
  }
}

///|
/// PEXPTSQ: P^N by repeated squaring.
fn pexptsq(p : Value, n : Value) -> Value raise {
  let mut p = p
  let mut s = if oddp(n) { p } else { Fix(1L) }
  let mut n = ash(n, -1)
  while !zerop(n) {
    p = ptimes(p, p)
    if oddp(n) {
      s = ptimes(s, p)
    }
    n = ash(n, -1)
  }
  s
}
