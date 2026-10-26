// Port of src/result.lisp: polynomial resultants, discriminants and the
// Bezout matrix.

///|
fn d_poly_discriminant(poly : Value, var_ : Value) -> Value raise {
  let b1 = bind(q_varlist, list1(var_))
  defer unbind(b1)
  let b2 = bind(q_d_ratfac, Nil)
  defer unbind(b2)
  let b3 = bind(q_genvar, Nil)
  defer unbind(b3)
  let rform_ = rform(poly)
  let rvar = car(last(symval(q_genvar)))
  let poly = car(rform_)
  let n = pdegree(poly, rvar)
  if num_eq(n, Fix(1L)) {
    Fix(1L)
  } else if num_eq(n, Fix(0L)) || !atom(cdr(rform_)) {
    merr(
      "poly_discriminant: first argument must be a polynomial in ~:M; found: ~M",
      [var_, poly],
    )
  } else {
    pdis(
      presign(
        ash(num_mul(n, one_minus(n)), -1),
        pquotient(resultant(poly, pderivative(poly, rvar)), p__lc(poly)),
      ),
    )
  }
}

///|
fn d_resultant(a : Value, b : Value, mainvar : Value) -> Value raise {
  let bs = bind_all([
    (q_varlist, list1(mainvar)),
    (q_genvar, Nil),
    (q_d_ratfac, t),
    (q_d_keepfloat, Nil),
  ])
  defer unbind_all(bs)
  let mut a = a
  let mut b = b
  let mut formflag = false
  let mut ans : Value = Fix(1L)
  if d_ratp(a).truthy() {
    a = d_ratdisrep(a)
    formflag = true
  }
  if d_ratp(b).truthy() {
    b = d_ratdisrep(b)
    formflag = true
  }
  newvar(a) |> ignore
  newvar(b) |> ignore
  a = lmake2(cadr(ratrep_star(a)), Nil)
  b = lmake2(cadr(ratrep_star(b)), Nil)
  let mainvar = caadr(ratrep_star(mainvar))
  for a_term in a.iter() {
    for b_term in b.iter() {
      let res = result1(car(a_term), car(b_term), mainvar)
      ans = ptimes(
        ans,
        pexpt(
          if zerop(third(res)) {
            first(res)
          } else {
            ptimeschk(first(res), pexpt(makprod(second(res), Nil), third(res)))
          },
          num_mul(cdr(a_term), cdr(b_term)),
        ),
      )
    }
  }
  if formflag {
    pdis_star(ans)
  } else {
    pdis(ans)
  }
}

///|
fn result1(p1 : Value, p2 : Value, var_ : Value) -> Value raise {
  if pcoefp(p1).truthy() || pointergp(var_, car(p1)).truthy() {
    list3(Fix(1L), p1, pdegree(p2, var_))
  } else if pcoefp(p2).truthy() || pointergp(var_, car(p2)).truthy() {
    list3(Fix(1L), p2, pdegree(p1, var_))
  } else if cdddr(p1) is Nil {
    if cdddr(p2) is Nil {
      list3(Fix(0L), Fix(0L), Fix(1L))
    } else {
      list3(pexpt(caddr(p1), cadr(p2)), pcsubsty(Fix(0L), var_, p2), cadr(p1))
    }
  } else if cdddr(p2) is Nil {
    list3(
      presign(num_mul(cadr(p1), cadr(p2)), pexpt(caddr(p2), cadr(p1))),
      pcsubsty(Fix(0L), var_, p1),
      cadr(p2),
    )
  } else {
    let g = num_gcd(pgcdexpon(p1), pgcdexpon(p2))
    if num_gt(g, Fix(1L)) {
      list3(
        Fix(1L),
        resultant(pexpon_star_sl_sl(p1, g, Nil), pexpon_star_sl_sl(p2, g, Nil)),
        g,
      )
    } else {
      list3(Fix(1L), resultant(p1, p2), Fix(1L))
    }
  }
}

///|
/// Assumes same main var.
fn resultant(p1 : Value, p2 : Value) -> Value raise {
  if num_gt(p__le(p2), p__le(p1)) {
    presign(num_mul(p__le(p1), p__le(p2)), resultant(p2, p1))
  } else {
    let r = symval(q_d_resultant)
    if eq(r, q_d_subres) {
      subresult(p1, p2)
    } else if eq(r, q_d_red) {
      redresult(p1, p2)
    } else {
      merr("resultant: no such algorithm: ~M", [r])
    }
  }
}

///|
fn presign(n : Value, p : Value) -> Value raise {
  if oddp(n) {
    pminus(p)
  } else {
    p
  }
}

///|
/// Computes resultant using subresultant PRS. See Brown, "The Subresultant
/// PRS Algorithm" (TOMS Sept. 1978), Algorithm 1.
fn subresult(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut g : Value = Fix(1L)
  let mut h : Value = Fix(1L)
  let mut d : Value = Fix(0L)
  let mut h1d : Value = Fix(1L)
  let mut first_iter = true
  while true {
    if !first_iter {
      g = p__lc(p)
      h = pquotient(pexpt(g, d), h1d)
    }
    first_iter = false
    let degq = pdegree(q, p__var(p))
    d = num_sub(p__le(p), degq)
    h1d = if equal(h, Fix(1L)) { Fix(1L) } else { pexpt(h, one_minus(d)) }
    if zerop(degq) {
      return if pzerop(q).truthy() {
        q
      } else {
        pquotient(pexpt(q, d), h1d)
      }
    }
    let np = q
    let nq = presign(
      one_plus(d),
      pquotient(prem(p, q), ptimes(g, ptimes(h, h1d))),
    )
    p = np
    q = nq
  }
  Nil
}

///|
/// Multivariate polynomial resultants using modified reduced p.r.s.
fn redresult(u : Value, v : Value) -> Value raise {
  let mut u = u
  let mut v = v
  let mut a : Value = Fix(1L)
  let mut sigma : Value = Fix(0L)
  let mut c : Value = Fix(1L)
  while true {
    let r = prem(u, v)
    if pzerop(r).truthy() {
      return pzero()
    }
    c = ptimeschk(
      c,
      pexpt(
        p__lc(v),
        num_mul(
          num_sub(p__le(u), p__le(v)),
          num_sub(num_sub(p__le(v), pdegree(r, p__var(u))), Fix(1L)),
        ),
      ),
    )
    sigma = num_add(sigma, num_mul(p__le(u), p__le(v)))
    if zerop(pdegree(r, p__var(u))) {
      return presign(sigma, pquotient(pexpt(pquotientchk(r, a), p__le(v)), c))
    }
    let nu = v
    let nv = pquotientchk(r, a)
    let na = pexpt(p__lc(v), num_sub(num_add(p__le(u), Fix(1L)), p__le(v)))
    u = nu
    v = nv
    a = na
  }
  Nil
}

// NOTE: MATRIX PRODUCED IS ALWAYS SYMMETRIC ABOUT THE MINOR DIAGONAL.

///|
fn d_bezout(p : Value, q : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(var_)), (q_genvar, Nil)])
  defer unbind_all(bs)
  newvar(p) |> ignore
  newvar(q) |> ignore
  let p = cadr(ratrep_star(p))
  let q = cadr(ratrep_star(q))
  let m = if num_gt(cadr(q), cadr(p)) { bezout(q, p) } else { bezout(p, q) }
  cons(
    list1(q_d_matrix),
    mapcar(l => cons(list1(q_mlist), mapcar(x => pdis(x), l)), m),
  )
}

///|
fn vmake(poly : Value, n : Value, n_starl : Value) -> Value raise {
  let mut poly = poly
  let mut l = n_starl
  let mut i = one_minus(n)
  while !minusp(i) {
    if poly is Nil || num_lt(car(poly), i) {
      l = cons(Fix(0L), l)
    } else {
      l = cons(cadr(poly), l)
      poly = cddr(poly)
    }
    i = one_minus(i)
  }
  nreverse(l)
}

///|
fn bezout(p : Value, q : Value) -> Value raise {
  let n = one_plus(p__le(p))
  let n2 = to_int(num_sub(n, p__le(q)))
  let a = vmake(p__terms(p), n, Nil)
  let b = vmake(p__terms(q), n, Nil)
  let ar = reverse(nthcdr(n2, a))
  let br = reverse(nthcdr(n2, b))
  let mut l : Value = Nil
  for _ in 0..<to_int(n) {
    l = cons(Fix(0L), l)
  }
  let lep = to_int(p__le(p))
  rplacd(nthcdr(lep - 1, a), Nil) |> ignore
  rplacd(nthcdr(lep - 1, b), Nil) |> ignore
  let rows = Collector::new()
  let mut arl = ar
  let mut brl = br
  while arl is Cons(_) && brl is Cons(_) {
    let ar1 = car(arl)
    let br1 = car(brl)
    // (mapcar (lambda (a b l) ...) a b (cons 0 l))
    let acc = Collector::new()
    let mut x = a
    let mut y = b
    let mut z = cons(Fix(0L), l)
    while x is Cons(_) && y is Cons(_) && z is Cons(_) {
      acc.add(
        ppluschk(
          car(z),
          pdifference(ptimes(br1, car(x)), ptimes(ar1, car(y))),
        ),
      )
      x = cdr(x)
      y = cdr(y)
      z = cdr(z)
    }
    l = acc.result()
    rows.add(l)
    arl = cdr(arl)
    brl = cdr(brl)
  }
  let tail = if pzerop(car(b)).truthy() {
    let mut bb = vmake(cdr(q), cadr(p), Nil)
    let mut m : Value = Nil
    while pzerop(car(bb)).truthy() {
      let nb = rot_star(bb)
      m = cons(bb, m)
      bb = nb
    }
    cons(bb, m)
  } else {
    Nil
  }
  nconc(rows.result(), tail)
}

///|
fn rot_star(b : Value) -> Value raise {
  let b = copy_list(b)
  match b {
    Cons(c) => append(c.cdr, list1(c.car))
    _ => Nil
  }
}

///|
fn ppluschk(p : Value, q : Value) -> Value raise {
  if pzerop(p).truthy() {
    q
  } else {
    pplus(p, q)
  }
}
