// Port of src/polyrz.lisp: package for finding real zeros of univariate
// polynomials with integer coefficients using Sturm sequences.

///|
fn d_realroots(exp_ : Value, eps? : Value) -> Value raise {
  let eps = match eps {
    Some(e) => e
    None => symval(q_d_rootsepsilon)
  }
  let mut exp1 = meqhk(exp_)
  if d_ratp(exp1).truthy() {
    exp1 = d_ratdisrep(exp1)
  }
  if !mnump(eps).truthy() || mnegp(eps).truthy() || equal(eps, Fix(0L)) {
    merr(
      "realroots: second argument must be a positive number; found: ~M",
      [eps],
    )
    |> ignore
  }
  with_special(q_d_keepfloat, Nil, () => sturmseq(exp_, exp1, eps))
}

///|
fn unipoly(exp_ : Value, exp1 : Value) -> Value raise {
  let exp1 = cadr(ratf(exp1))
  if !atom(exp1) && cdr(exp1).iter().all(v => atom(v)) {
    exp1
  } else {
    merr(
      "UNIPOLY: argument must be a univariate polynomial with rational coefficients; found: ~M",
      [exp_],
    )
  }
}

///|
fn makrat(pt : Value) -> Value raise {
  if floatp(pt) {
    maxima_rationalize(pt)
  } else if numberp(pt) {
    cons(pt, Fix(1L))
  } else if d_bfloatp(pt).truthy() {
    bigfloat2rat(pt)
  } else if atom(pt) {
    merr("MAKRAT: argument must be a number; found: ~M", [pt])
  } else if equal(caar(pt), q_rat) {
    cons(cadr(pt), caddr(pt))
  } else {
    merr("MAKRAT: argument must be a number; found: ~M", [pt])
  }
}

///|
fn sturmseq(exp_ : Value, exp1 : Value, eps : Value) -> Value raise {
  with_specials(
    [(q_varlist, Nil), (q_d_factorflag, Nil), (q_d_ratprint, Nil), (q_d_ratfac, Nil)],
    () => if symval(q_d_programmode).truthy() {
      cons(
        list1(q_mlist),
        multout(findroots(psqfr(pabs(unipoly(exp_, exp1))), makrat(eps))),
      )
    } else {
      let equations = solve2(
        findroots(psqfr(pabs(unipoly(exp_, exp1))), makrat(eps)),
        Nil,
      ).1
      cons(list1(q_mlist), equations)
    },
  )
}

///|
fn sturm1(poly : Value, eps : Value) -> Value raise {
  let b = cons(root_bound(cdr(poly)), Fix(1L))
  let llist = isolat(poly, cons(num_neg(car(b)), cdr(b)), b)
  mapcar(int_ => refine(poly, car(int_), cdr(int_), eps), llist)
}

///|
fn root_bound(p : Value) -> Value raise {
  let mut p = p
  let n = car(p)
  let lcf = num_abs(cadr(p))
  let loglcf = integer_length(lcf) - 2
  let mut logb : Value = Fix(1L)
  while true {
    p = cddr(p)
    if p is Nil {
      return expt(Fix(2L), logb)
    }
    let coef = num_abs(cadr(p))
    if num_lt(coef, lcf) {
      continue
    }
    logb = num_max(
      logb,
      one_plus(
        ceil(int(integer_length(coef) - loglcf - 1), num_sub(n, car(p))),
      ),
    )
  }
  Nil
}

///|
/// CEILING FOR POS A,B
fn ceil(a : Value, b : Value) -> Value raise {
  num_add(quot(a, b), signum_(num_rem(a, b)))
}

///|
fn sturmapc(fn_ : Value, llist : Value, multiplicity : Value) -> Value raise {
  if llist is Nil {
    Nil
  } else {
    cons(
      funcall(fn_, [car(llist)]),
      cons(multiplicity, sturmapc(fn_, cdr(llist), multiplicity)),
    )
  }
}

///|
fn findroots(l : Value, eps : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if numberp(car(l)) {
    findroots(cddr(l), eps)
  } else {
    append(
      sturmapc(q_sturmout, sturm1(car(l), eps), cadr(l)),
      findroots(cddr(l), eps),
    )
  }
}

///|
fn sturmout(int_ : Value) -> Value raise {
  list3(
    list2(q_mequal, q_simp),
    car(symval(q_varlist)),
    midout(rhalf(rplus_star(car(int_), cadr(int_)))),
  )
}

///|
fn midout(pt : Value) -> Value raise {
  if equal(cdr(pt), Fix(1L)) {
    car(pt)
  } else if symval(q_d_float).truthy() {
    fpcofrat1(car(pt), cdr(pt))
  } else {
    list3(list2(q_rat, q_simp), car(pt), cdr(pt))
  }
}

///|
/// PRIMITIVE UNIVAR. POLY
fn uprimitive(p : Value) -> Value raise {
  pquotient(p, ucontent(p))
}

///|
fn sturm(p : Value) -> Value raise {
  let mut p1 = uprimitive(p)
  let mut p2 = uprimitive(pderivative(p1, car(p1)))
  let mut seq = list2(p2, p1)
  while true {
    let r = prem(p1, pabs(p2))
    if pzerop(r).truthy() {
      return reverse(seq)
    }
    p1 = p2
    p2 = pminus(uprimitive(r))
    seq = cons(p2, seq)
  }
  Nil
}

///|
fn signum_(x : Value) -> Value raise {
  if zerop(x) {
    Fix(0L)
  } else if minusp(x) {
    Fix(-1L)
  } else {
    Fix(1L)
  }
}

///|
/// IVAR COUNTS SIGN CHANGES IN A STURM SEQUENCE
fn ivar(seq : Value, pt : Value) -> Value raise {
  let mut seq = seq
  let mut v : Value = Fix(0L)
  let mut ls : Value = Fix(0L)
  while true {
    if seq is Nil {
      return v
    }
    let s = reval(car(seq), pt)
    seq = cdr(seq)
    if minusp(num_mul(s, ls)) {
      v = one_plus(v)
    } else if !zerop(ls) {
      continue
    }
    ls = s
  }
  Nil
}

///|
fn ivar2(seq : Value, pt : Value) -> Value raise {
  if !atom(pt) {
    ivar(seq, pt)
  } else {
    let seq = mapcar(x => leadterm(x), seq)
    ivar(seq, cons(pt, Fix(1L)))
  }
}

///|
/// OUTPUT SIGN(P(R)) , R RATIONAL (A.B)
fn reval(p : Value, r : Value) -> Value raise {
  if pcoefp(p).truthy() {
    signum_(p)
  } else if zerop(car(r)) {
    signum_(ptterm(cdr(p), Fix(0L)))
  } else {
    let mut bi : Value = Fix(1L)
    let mut v : Value = Fix(0L)
    let mut p = cdr(p)
    let mut m = car(p)
    let a = car(r)
    let b = cdr(r)
    while true {
      let mut c : Value = Fix(0L)
      if equal(m, car(p)) {
        c = cadr(p)
        p = cddr(p)
      }
      if zerop(m) {
        return signum_(num_add(v, num_mul(bi, c)))
      }
      v = num_mul(a, num_add(v, num_mul(bi, c)))
      bi = num_mul(bi, b)
      m = one_minus(m)
    }
    Nil
  }
}

///|
fn makpoint(pt : Value) -> Value raise {
  if eq(pt, q_d_inf) {
    Fix(1L)
  } else if eq(pt, q_d_minf) {
    Fix(-1L)
  } else {
    makrat(d_rationalize(with_special(q_d_numer, t, () => meval(pt))))
  }
}

///|
fn d_nroots(
  exp_ : Value,
  l? : Value = q_d_minf,
  r? : Value = q_d_inf,
) -> Value raise {
  with_specials([(q_varlist, Nil), (q_d_keepfloat, Nil), (q_d_ratfac, Nil)], () => nroots(
    unipoly(exp_, meqhk(exp_)),
    makpoint(l),
    makpoint(r),
  ))
}

///|
fn nroots(p : Value, l : Value, r : Value) -> Value raise {
  rootaddup(psqfr(p), l, r)
}

///|
fn rootaddup(llist : Value, l : Value, r : Value) -> Value raise {
  if llist is Nil {
    Fix(0L)
  } else if numberp(car(llist)) {
    rootaddup(cddr(llist), l, r)
  } else {
    num_add(
      rootaddup(cddr(llist), l, r),
      num_mul(cadr(llist), nroot1(car(llist), l, r)),
    )
  }
}

///|
fn nroot1(p : Value, l : Value, r : Value) -> Value raise {
  let seq = sturm(p)
  num_sub(ivar2(seq, l), ivar2(seq, r))
}

///|
/// RETURNS ROOT IN INTERVAL OF FORM (A,B])
fn isolat(p : Value, l : Value, r : Value) -> Value raise {
  let mut l = l
  let mut r = r
  let seq = sturm(p)
  let mut lv = ivar(seq, l)
  let mut rv = ivar(seq, r)
  let mut tlist : Value = Nil
  let mut islist : Value = Nil
  if equal(lv, rv) {
    return Nil
  }
  while true {
    // a
    let rts = num_sub(lv, rv)
    if num_gt(rts, Fix(1L)) {
      // b
      let mid = rhalf(rplus_star(l, r))
      let midv = ivar(seq, mid)
      if !equal(lv, midv) {
        tlist = append(list4(lv, midv, l, mid), tlist)
      }
      l = mid
      lv = midv
      continue
    } else if equal(rts, Fix(1L)) {
      islist = cons(cons(l, r), islist)
    }
    if tlist is Nil {
      return islist
    }
    lv = car(tlist)
    rv = cadr(tlist)
    l = caddr(tlist)
    r = cadddr(tlist)
    tlist = cddddr(tlist)
  }
  Nil
}

///|
fn refine(p : Value, l : Value, r : Value, eps : Value) -> Value raise {
  let mut l = l
  let mut r = r
  let sr = reval(p, r)
  if zerop(sr) {
    return list2(r, r)
  }
  while true {
    if rlessp(rdifference_star(r, l), eps).truthy() {
      return list2(l, r)
    }
    let mid = rhalf(rplus_star(l, r))
    let smid = reval(p, mid)
    if zerop(smid) {
      return list2(mid, mid)
    } else if equal(smid, sr) {
      r = mid
    } else {
      l = mid
    }
  }
  Nil
}

///|
fn rhalf(r : Value) -> Value raise {
  rreduce(car(r), num_mul(Fix(2L), cdr(r)))
}

///|
fn rreduce(a : Value, b : Value) -> Value raise {
  let g = num_abs(num_gcd(a, b))
  cons(num_truncate(a, b=g).0, num_truncate(b, b=g).0)
}

///|
fn rplus_star(a : Value, b : Value) -> Value raise {
  cons(
    num_add(num_mul(car(a), cdr(b)), num_mul(car(b), cdr(a))),
    num_mul(cdr(a), cdr(b)),
  )
}

///|
fn rdifference_star(a : Value, b : Value) -> Value raise {
  rplus_star(a, cons(num_neg(car(b)), cdr(b)))
}

///|
fn rlessp(a : Value, b : Value) -> Value raise {
  lbool(num_lt(num_mul(car(a), cdr(b)), num_mul(car(b), cdr(a))))
}

///|
/// This next function is to do what SOLVE2 should do in programmode
fn multout(rootlist : Value) -> Value raise {
  let mut rtlst : Value = Nil
  let mut multlst : Value = Nil
  let mut lunch = rootlist
  while !(lunch is Nil) {
    rtlst = cons(car(lunch), rtlst)
    multlst = cons(cadr(lunch), multlst)
    lunch = cddr(lunch)
  }
  let rootlist = cons(reverse(rtlst), reverse(multlst))
  set(q_d_multiplicities, cons(list1(q_mlist), cdr(rootlist))) |> ignore
  car(rootlist)
}

///|
fn init_polyrz() -> Unit raise {
  ()
}
