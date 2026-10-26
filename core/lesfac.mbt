// Port of src/lesfac.lisp: factored-form (RATFAC) arithmetic and
// partial factoring helpers for the rational function package.

///|
fn getunhack(gen : Value) -> Value raise {
  let v = get(gen, q_unhacked)
  if v.truthy() {
    v
  } else {
    pget(gen)
  }
}

///|
fn frpoly_q(r : Value) -> Value raise {
  lbool(equal(Fix(1L), cdr(r)))
}

///|
/// `(setcall fn a b args...)` as a function: calls FN on A, B and ARGS and
/// returns the first element of the result.  The macro also assigns the
/// second and third elements to A and B; call sites do that inline.
fn setcall(fn_ : Value, a : Value, b : Value, args : Value) -> Value raise {
  first(apply(fn_, cons(a, cons(b, args))))
}

///|
fn pquocof(p : Value, q : Value) -> (Value, Value, Value) raise {
  let qq = testdivide(p, q)
  if qq.truthy() {
    (q, qq, Fix(1L))
  } else {
    (Fix(1L), p, q)
  }
}

///|
fn polyst(a : Value) -> Value raise {
  if pcoefp(a).truthy() {
    list1(a)
  } else {
    cons(cons(car(a), cadr(a)), polyst(caddr(a)))
  }
}

///|
fn cdinf(a : Value, b : Value, both : Value) -> (Value, Value, Value) raise {
  if pcoefp(a).truthy() || pcoefp(b).truthy() {
    (Fix(1L), a, b)
  } else {
    let a = list1(copy_tree(a))
    let b = list1(if both.truthy() { copy_tree(b) } else { b })
    let r = cd1(a, b, both)
    (r, car(a), car(b))
  }
}

///|
fn cd1(a : Value, b : Value, both : Value) -> Value raise {
  if pcoefp(car(a)).truthy() || pcoefp(car(b)).truthy() {
    Fix(1L)
  } else if eq(caar(a), caar(b)) {
    let mut b = b
    let base = pget(caar(a)) // CHECK FOR ALG. TRUNC.
    let e = if both.truthy() {
      num_add(cadar(a), cadar(b))
    } else {
      cadar(a)
    }
    rplaca(a, caddar(a)) |> ignore
    if both.truthy() {
      rplaca(b, caddar(b)) |> ignore
    } else {
      b = cddar(b)
    }
    let x = pexpt(base, e)
    ptimes(x, cd1(a, b, both))
  } else if pointergp(caar(a), caar(b)).truthy() {
    cd1(cddar(a), b, both)
  } else {
    cd1(a, cddar(b), both)
  }
}

///|
fn lmake(p : Value, l : Value) -> Value raise {
  if pcoefp(p).truthy() {
    cons(p, l)
  } else if get(car(p), q_unhacked).truthy() {
    lmake(caddr(p), cons(cons(car(p), cadr(p)), l))
  } else {
    let l = lmake(caddr(p), l)
    rplaca(l, list3(car(p), cadr(p), car(l)))
  }
}

///|
fn lmake2(p : Value, l : Value) -> Value raise {
  let l = lmake(p, l)
  for x in cdr(l).iter() {
    rplaca(x, getunhack(car(x))) |> ignore
  }
  if equal(car(l), Fix(1L)) {
    cdr(l)
  } else {
    rplaca(l, cons(car(l), Fix(1L)))
  }
}

///|
fn pmake(l : Value) -> Value raise {
  if l is Nil {
    Fix(1L)
  } else if zerop(cdar(l)) {
    pmake(cdr(l))
  } else if numberp(caar(l)) {
    // CLAUSE SHOULD BE ELIMINATED ASAP
    ptimes(cexpt(caar(l), cdar(l)), pmake(cdr(l)))
  } else {
    ptimes(list3(caar(l), cdar(l), Fix(1L)), pmake(cdr(l)))
  }
}

///|
/// Factored PGCDCOFACTS.
fn fpgcdco(p : Value, q : Value) -> (Value, Value, Value) raise {
  let b = bind(q_d_ratfac, Nil)
  defer unbind(b)
  if pcoefp(p).truthy() || pcoefp(q).truthy() {
    let r = pgcdcofacts(p, q)
    (first(r), second(r), third(r))
  } else {
    let r = pgcdcofacts(p, q)
    let g0 = first(r)
    let p1 = lmake(second(r), Nil)
    let q1 = lmake(third(r), Nil)
    let gcdl = mapcar(x => pmake(x), lgcd1(cdr(p1), cdr(q1)))
    let v1 = ptimeschk(g0, car(gcdl))
    (v1, ptimeschk(car(p1), cadr(gcdl)), ptimeschk(car(q1), caddr(gcdl)))
  }
}

///|
/// GCD of poly list for EZGCD with RATFAC.
fn facmgcd(pl : Value) -> Value raise {
  let mut l = cdr(pl)
  let mut ans : Value = Nil
  let mut gcd = car(pl)
  while !(l is Nil) {
    let (g, x, y) = fpgcdco(gcd, car(l))
    if equal(g, Fix(1L)) {
      return cons(Fix(1L), pl)
    } else if ans is Nil {
      ans = list1(x)
    } else if !equal(x, Fix(1L)) {
      let mut l2 = ans
      while !(l2 is Nil) {
        rplaca(l2, ptimes(x, car(l2))) |> ignore
        l2 = cdr(l2)
      }
    }
    ans = cons(y, ans)
    gcd = g
    l = cdr(l)
  }
  cons(gcd, nreverse(ans))
}

// NOTE: ITEMS ON VARLIST ARE POS. NORMAL
// INTEGER COEF GCD=1 AND LEADCOEF. IS POS.

///|
fn lgcd1(a : Value, b : Value) -> Value raise {
  let ptlist = mapcar(_ => b, a)
  let mut g : Value = Nil
  let mut aa = a
  let mut pt = ptlist
  while !(aa is Nil) {
    let mut ai = getunhack(caar(aa))
    for bb = car(pt); !(bb is Nil); bb = cdr(bb) {
      if zerop(cdar(bb)) {
        continue // nextb
      }
      let mut d1 : Value = Fix(1L)
      let mut d2 : Value = Fix(1L)
      let mut bj = getunhack(caar(bb))
      let c : Value = if pirredp(caar(aa)).truthy() {
        if pirredp(caar(bb)).truthy() {
          Fix(1L)
        } else {
          let (x, y, z) = pquocof(bj, ai)
          bj = y
          ai = z
          x
        }
      } else if pirredp(caar(bb)).truthy() {
        let (x, y, z) = pquocof(ai, bj)
        ai = y
        bj = z
        x
      } else {
        let r = pgcdcofacts(ai, bj)
        bj = third(r)
        ai = second(r)
        first(r)
      }
      if equal(c, Fix(1L)) {
        continue // nextb
      }
      if !equal(ai, Fix(1L)) {
        // aloop: do not count how often an algebraic C divides AI and BJ:
        // a unit such as %i divides them any number of times.
        while !alg(c).truthy() {
          let t1 = testdivide(ai, c)
          if !t1.truthy() {
            break
          }
          ai = t1
          d1 = one_plus(d1)
        }
      }
      // bloop
      if num_eq(d1, Fix(1L)) && !equal(bj, Fix(1L)) && !alg(c).truthy() {
        let mut t1 = testdivide(bj, c)
        while t1.truthy() {
          bj = t1
          d2 = one_plus(d2)
          t1 = testdivide(bj, c)
        }
      }
      let mp = makprodg(c, t)
      d1 = num_mul(d1, cdar(aa))
      d2 = num_mul(d2, cdar(bb))
      g = cons(cons(mp, num_min(d1, d2)), g)
      if num_gt(d1, cdar(g)) {
        rplacd(last(aa), list1(cons(caar(g), num_sub(d1, cdar(g))))) |> ignore
        rplacd(last(pt), list1(cdr(bb))) |> ignore
      }
      if num_gt(d2, cdar(g)) {
        rplacd(last(bb), list1(cons(caar(g), num_sub(d2, cdar(g))))) |> ignore
      }
      rplaca(car(aa), makprodg(ai, t)) |> ignore
      rplaca(car(bb), makprodg(bj, t)) |> ignore
      if equal(bj, Fix(1L)) {
        rplacd(car(bb), Fix(0L)) |> ignore
      }
      if equal(ai, Fix(1L)) {
        rplacd(car(aa), Fix(0L)) |> ignore
        break
      }
    }
    aa = cdr(aa)
    pt = cdr(pt)
  }
  list3(g, a, b)
}

///|
fn makprodg(p : Value, sw : Value) -> Value raise {
  if pcoefp(p).truthy() {
    p
  } else if pureprod(p).truthy() && !equal(p, pget(car(p))) {
    // A monomial such as -%i needs a kernel of its own, since its main
    // variable alone, which MAKPROD would give, drops the coefficient.
    maksym(p)
  } else {
    car(makprod(p, sw))
  }
}

///|
/// The Lisp function returns the three values of PGCDCOFACTS; the declared
/// signature only has room for two.  See `lesfac__dopgcdcofacts3`.
fn dopgcdcofacts(x : Value, y : Value) -> (Value, Value) raise {
  let (a, b, _) = lesfac__dopgcdcofacts3(x, y)
  (a, b)
}

///|
fn lesfac__dopgcdcofacts3(x : Value, y : Value) -> (Value, Value, Value) raise {
  let bs = bind_all([(q_d_gcd, symval(q_d_gcd)), (q_d_ratfac, Nil)])
  defer unbind_all(bs)
  if memq(symval(q_d_gcd), symval(q_ear_gcdl)) is Nil {
    set(q_d_gcd, q_d_ez) |> ignore
  }
  let r = pgcdcofacts(x, y)
  (first(r), second(r), third(r))
}

///|
fn facrplus(x : Value, y : Value) -> Value raise {
  let mut a = car(x)
  let mut b = cdr(x)
  let mut c = car(y)
  let mut d = cdr(y)
  let (x1, a1, c1) = lesfac__dopgcdcofacts3(a, c)
  let x = x1
  a = a1
  c = c1
  let (y1, b1, d1) = fpgcdco(b, d)
  let mut y = y1
  b = b1
  d = d1
  a = makprod(
    pplus(pflatten(ptimeschk(a, d)), pflatten(ptimeschk(b, c))),
    Nil,
  )
  b = ptimeschk(b, d)
  if symval(q_d_algebraic).truthy() {
    y = ptimeschk(y, b)
    let (_, y2, a2) = fpgcdco(y, a) // for unexpected gcd
    y = y2
    a = a2
    cons(ptimes(x, a), y)
  } else {
    let (c3, y3, b3) = cdinf(y, b, Nil)
    c = c3
    y = y3
    b = b3
    let (_, y4, a4) = fpgcdco(y, a)
    y = y4
    a = a4
    cons(ptimes(x, a), ptimeschk(y, ptimeschk(c, b)))
  }
}

///|
fn mfacpplus(l : Value) -> Value raise {
  let gv = symval(q_d_gcd)
  let bs = bind_all([
    (q_d_gcd, if gv.truthy() { gv } else { q_d_ez }),
    (q_d_ratfac, Nil),
  ])
  defer unbind_all(bs)
  let g = oldcontent2(
    sort_list(copy_list(l), (p, q) => contodr(p, q).truthy()),
    Fix(0L),
  )
  if pzerop(g).truthy() {
    g
  } else {
    let mut a = pflatten(pquotient(car(l), g))
    let mut ll = cdr(l)
    while !(ll is Nil) {
      a = pplus(a, pflatten(pquotient(car(ll), g)))
      ll = cdr(ll)
    }
    ptimes(g, makprod(a, Nil))
  }
}

///|
fn facrtimes(x : Value, y : Value, gcdsw : Value) -> Value raise {
  if !gcdsw.truthy() {
    cons(ptimes(car(x), car(y)), ptimeschk(cdr(x), cdr(y)))
  } else {
    let (g1, g2, g3) = cdinf(car(x), car(y), t)
    let (h1, h2, h3) = cdinf(cdr(x), cdr(y), t)
    let (_, x2, x3) = fpgcdco(g2, h3)
    let (_, y2, y3) = fpgcdco(g3, h2)
    cons(ptimes(g1, ptimes(x2, y2)), ptimeschk(h1, ptimeschk(x3, y3)))
  }
}

///|
/// For RAT3D.
fn pfacprod(poly : Value) -> Value raise {
  if pcoefp(poly).truthy() {
    cfactor(poly)
  } else {
    nconc(pfacprod(caddr(poly)), list2(pget(car(poly)), cadr(poly)))
  }
}

///|
fn fpcontent(poly : Value) -> Value raise {
  let bnd = bind(q_d_ratfac, Nil) // algebraic uses
  defer unbind(bnd)
  let mut poly = oldcontent(poly) // rattimes?
  let a = lowdeg(cdadr(poly)) // main var. content
  if plusp(a) {
    let a = list3(caadr(poly), a, Fix(1L))
    poly = list2(ptimes(car(poly), a), pquotient(cadr(poly), a))
  }
  if pminusp(cadr(poly)).truthy() {
    list2(pminus(car(poly)), pminus(cadr(poly)))
  } else {
    poly
  }
}

///|
/// LOWDEG computes the lowest degree of a polynomial. - RZ
fn lowdeg(p : Value) -> Value raise {
  let mut l = p
  while !(cddr(l) is Nil) {
    l = cddr(l)
  }
  car(l)
}

///|
fn makprod(poly : Value, contswitch : Value) -> Value raise {
  if pureprod(poly).truthy() {
    poly
  } else if cdddr(poly) is Nil {
    ptimes(
      list3(car(poly), cadr(poly), Fix(1L)),
      makprod(caddr(poly), contswitch),
    )
  } else if contswitch.truthy() {
    makprod1(poly)
  } else {
    let poly = fpcontent(poly)
    let x = makprod(car(poly), contswitch)
    ptimes(x, makprod1(cadr(poly)))
  }
}

///|
fn makprod1(poly : Value) -> Value raise {
  let mut v = symval(q_varlist)
  let mut g = symval(q_genvar)
  let p = pdis(poly)
  while !(v is Nil) {
    if alike1(p, car(v)).truthy() {
      return pget(car(g))
    }
    v = cdr(v)
    g = cdr(g)
  }
  maksymp(poly)
}

///|
fn maksym(p : Value) -> Value raise {
  let g = gensym()
  let e = pdis(p)
  putprop(g, e, q_disrep) |> ignore
  valput(g, one_minus(valget(car(symval(q_genvar))))) |> ignore
  set(q_genvar, cons(g, symval(q_genvar))) |> ignore
  set(q_varlist, cons(e, symval(q_varlist))) |> ignore
  putprop(g, p, q_unhacked) |> ignore
  g
}

///|
fn maksymp(p : Value) -> Value raise {
  if atom(p) {
    p
  } else {
    pget(maksym(p))
  }
}

///|
fn pflatten(h : Value) -> Value raise {
  let mut m = listovars(h)
  while !(m is Nil) {
    let p = getunhack(car(m))
    if !(p is Nil || eq(car(m), car(p))) {
      return with_special(q_d_ratfac, Nil, () => pflat1(h))
    }
    m = cdr(m)
  }
  h
}

///|
fn pflat1(p : Value) -> Value raise {
  if pcoefp(p).truthy() {
    p
  } else if cdddr(p) is Nil {
    let x = pexpt(getunhack(car(p)), cadr(p))
    ptimes(x, pflat1(caddr(p)))
  } else {
    let val = getunhack(car(p))
    let mut ld = cadr(p)
    let mut a = cdddr(p)
    let mut ans = pflat1(caddr(p))
    while !(a is Nil) {
      let x = ptimes(ans, pexpt(val, num_sub(ld, car(a))))
      ans = pplus(x, pflat1(cadr(a)))
      ld = car(a)
      a = cddr(a)
    }
    ptimes(ans, pexpt(val, ld))
  }
}

///|
fn pirredp(x : Value) -> Value raise {
  let x = get(x, q_disrep)
  if x.truthy() {
    if atom(x) {
      t
    } else {
      memq(q_irreducible, cdar(x))
    }
  } else {
    Nil
  }
}
