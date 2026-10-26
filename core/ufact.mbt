// Port of src/ufact.lisp: dense univariate polynomial arithmetic over the
// integers modulo MODULUS.
//
// Dense representation: (degree c_n c_{n-1} ... c_0).

///|
fn dprep(p : Value) -> Value raise {
  let n = car(p)
  let mut pp = p
  let mut e = to_int(car(p))
  let mut l : Value = Nil
  while e >= 0 {
    if equal(int(e), car(pp)) {
      l = cons(cadr(pp), l)
      pp = cddr(pp)
    } else {
      l = cons(Fix(0L), l)
    }
    e -= 1
  }
  cons(n, nreverse(l))
}

///|
fn dpdisrep(l : Value) -> Value raise {
  if zerop(car(l)) {
    cadr(l)
  } else {
    let mut ll : Value = Nil
    let mut n = 0
    let mut r = nreverse(cdr(l))
    while !(r is Nil) {
      if !num_eq(car(r), Fix(0L)) {
        ll = cons(int(n), cons(car(r), ll))
      }
      r = cdr(r)
      n += 1
    }
    ll
  }
}

///|
fn dpgcd(p : Value, q : Value) -> Value raise {
  let (p0, q0) = if num_lt(car(p), car(q)) { (q, p) } else { (p, q) }
  let mut p = copy_list(p0)
  let mut q = copy_list(q0)
  while !num_eq(car(q), Fix(0L)) {
    let np = q
    let nq = dpremquo(p, q, Nil)
    p = np
    q = nq
  }
  if num_eq(cadr(q), Fix(0L)) {
    p
  } else {
    list2(Fix(0L), Fix(1L))
  }
}

///|
fn dpdif(p : Value, q : Value) -> Value raise {
  if num_gt(car(p), car(q)) {
    let mut i = car(p)
    let mut pl = cdr(p)
    let mut l : Value = Nil
    while !num_eq(i, car(q)) {
      l = cons(car(pl), l)
      i = one_minus(i)
      pl = cdr(pl)
    }
    dpdif1(pl, cdr(q), l)
  } else if num_lt(car(p), car(q)) {
    let mut i = car(q)
    let mut ql = cdr(q)
    let mut l : Value = Nil
    while !num_eq(i, car(p)) {
      l = cons(cminus(car(ql)), l)
      i = one_minus(i)
      ql = cdr(ql)
    }
    dpdif1(cdr(p), ql, l)
  } else {
    dpdif1(cdr(p), cdr(q), Nil)
  }
}

///|
fn dpdif1(p1 : Value, q1 : Value, l : Value) -> Value raise {
  let mut pl = p1
  let mut ql = q1
  let mut ll = l
  while !(pl is Nil) {
    ll = cons(cdifference(car(pl), car(ql)), ll)
    pl = cdr(pl)
    ql = cdr(ql)
  }
  dpsimp(nreverse(ll))
}

///|
fn dpsimp(pl : Value) -> Value raise {
  let pl = ufact_strip_zeroes(pl)
  if pl is Nil {
    list2(Fix(0L), Fix(0L))
  } else {
    cons(int(length(pl) - 1), pl)
  }
}

///|
fn dpderiv(p : Value) -> Value raise {
  if num_eq(Fix(0L), car(p)) {
    list2(Fix(0L), Fix(0L))
  } else {
    let mut l = cdr(p)
    let mut i = car(p)
    let mut dp : Value = Nil
    while !num_eq(i, Fix(0L)) {
      dp = cons(ctimes(i, car(l)), dp)
      l = cdr(l)
      i = one_minus(i)
    }
    cons(one_minus(car(p)), nreverse(dp))
  }
}

///|
/// Assumes MODULUS > degree.
fn dpsqfr(q : Value) -> Value raise {
  let mut c = q
  let mut d = dpderiv(q)
  let mut i = 0
  let mut p : Value = Nil
  let mut pl : Value = Nil
  while !num_eq(Fix(0L), car(c)) {
    if p.truthy() {
      d = dpdif(d, dpderiv(c))
      p = dpgcd(c, d)
      if num_gt(car(p), Fix(0L)) {
        pl = cons(cons(int(i), p), pl)
      }
    } else {
      p = dpgcd(c, d)
      if num_eq(car(p), Fix(0L)) {
        return list1(cons(Fix(1L), c))
      }
    }
    let nc = dpmodquo(c, p)
    let nd = dpmodquo(d, p)
    c = nc
    d = nd
    i += 1
  }
  pl
}

///|
fn dpmodrem(p : Value, q : Value) -> Value raise {
  if num_lt(car(p), car(q)) {
    p
  } else if num_eq(car(q), Fix(0L)) {
    list2(Fix(0L), Fix(0L))
  } else {
    dpremquo(copy_list(p), copy_list(q), Nil)
  }
}

///|
fn dpmodquo(p : Value, q : Value) -> Value raise {
  if num_lt(car(p), car(q)) {
    list2(Fix(0L), Fix(0L))
  } else if num_eq(car(q), Fix(0L)) {
    if equal(cadr(q), Fix(1L)) {
      p
    } else {
      cons(car(p), mapcar(c => cquotient(c, cadr(q)), cdr(p)))
    }
  } else {
    dpremquo(copy_list(p), copy_list(q), t)
  }
}

///|
/// If FLAG is T, return quotient.  Otherwise return remainder.
fn dpremquo(p : Value, q : Value, flag : Value) -> Value raise {
  let mut p = p
  let mut alpha : Value = Fix(1L)
  let mut l : Value = Nil
  if num_eq(cadr(q), Fix(1L)) {
    alpha = Fix(1L)
  } else {
    alpha = crecip(cadr(q))
    let mut ll = cddr(q)
    while !(ll is Nil) {
      rplaca(ll, ctimes(car(ll), alpha)) |> ignore
      ll = cdr(ll)
    }
    rplaca(cdr(q), Fix(1L)) |> ignore
  }
  while true {
    // a
    if flag.truthy() {
      l = cons(ctimes(cadr(p), alpha), l)
    }
    let mut lp = cddr(p)
    let mut lq = cddr(q)
    // b
    while true {
      rplaca(lp, cdifference(car(lp), ctimes(car(lq), cadr(p)))) |> ignore
      lq = cdr(lq)
      if lq is Nil {
        break
      }
      lp = cdr(lp)
    }
    let mut e = one_minus(car(p))
    let mut pp = cddr(p)
    while true {
      if pp is Nil {
        p = list2(Fix(0L), Fix(0L))
        break
      }
      if numberp(car(pp)) && zerop(car(pp)) {
        if flag.truthy() && !num_lt(e, car(q)) {
          l = cons(Fix(0L), l)
        }
      } else {
        p = cons(e, pp)
        break
      }
      e = one_minus(e)
      pp = cdr(pp)
    }
    if num_lt(car(p), car(q)) {
      return if flag.truthy() { dpsimp(nreverse(l)) } else { p }
    }
  }
  Nil
}

///|
fn ufact_strip_zeroes(l : Value) -> Value raise {
  let mut l = l
  while pzerop(car(l)).truthy() {
    l = cdr(l)
  }
  l
}

///|
fn cpres1(a : Value, b : Value) -> Value raise {
  let mut v = 0L
  let mut a = dprep(a)
  let mut b = dprep(b)
  let mut res : Value = Fix(1L)
  while true {
    let a3 = dpmodrem(a, b)
    v = v ^ (to_int64(car(a)) & to_int64(car(b)) & 1L)
    res = ctimes(res, cexpt(cadr(b), num_sub(car(a), car(a3))))
    if num_eq(Fix(0L), car(a3)) {
      res = ctimes(res, cexpt(cadr(a3), car(b)))
      return if v % 2L != 0L { cminus(res) } else { res }
    }
    a = b
    b = a3
  }
  Nil
}
