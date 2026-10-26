// Port of src/pois3.lisp: general Poisson series.

///|
fn pois3__shift() -> Value {
  symval(q_poishift)
}

///|
fn pois3__mpois(s : Value, c : Value) -> Value {
  list3(list2(q_mpois, q_simp), s, c)
}

// THESE ARE THE ONLY COEFFICIENT DEPENDENT ROUTINES.

///|
/// POISCDECODE DECODES A COEFFICIENT
fn poiscdecode(x : Value) -> Value raise {
  x
}

///|
/// INTOPOISCO PUTS AN EXPRESSION INTO POISSON COEFFICIENT FORM
fn intopoisco(x : Value) -> Value raise {
  simplifya(x, Nil)
}

///|
/// POISCO+ ADDS 2 COEFFICIENTS
fn poisco_plus(r : Value, s : Value) -> Value raise {
  simplifya(list3(list1(q_mplus), r, s), Nil)
}

///|
/// POISCO* MULTIPLIES 2 COEFFICIENTS
fn poisco_star(r : Value, s : Value) -> Value raise {
  simplifya(list3(list1(q_mtimes), r, s), Nil)
}

///|
/// HALVE DIVIDES A COEFFICIENT BY 2
fn halve(r : Value) -> Value raise {
  simplifya(
    list3(list1(q_mtimes), list3(list1(q_rat), int(1), int(2)), r),
    Nil,
  )
}

///|
/// POISSUBSTCO SUBSTITUTES AN EXPRESSION FOR A VARIABLE IN A COEFFICIENT.
fn poissubstco(a : Value, b : Value, c : Value) -> Value raise {
  maxima_substitute(a, b, c)
}

///|
/// THIS DIFFERENTIATES A COEFFICIENT
fn poiscodif(h : Value, var_ : Value) -> Value raise {
  d_diff(list2(h, var_))
}

///|
/// THIS INTEGRATES A COEFFICIENT
fn poiscointeg(h : Value, var_ : Value) -> Value raise {
  intopoisco(d_integrate(poiscdecode(h), var_))
}

///|
/// TEST FOR ZERO
fn poispzero(x : Value) -> Value raise {
  zerop1(x)
}

///|
fn fumcheck(x : Value) -> Value raise {
  lbool(!(atom(x) && integerp(x) && num_lt(num_abs(x), symval(q_poistsm))))
}

///|
fn checkencode(r : Value) -> Value raise {
  let mut r = r
  for v in [q_d_u, q_d_v, q_d_w, q_d_x, q_d_y, q_d_z] {
    let q = d_coeff(r, v)
    if fumcheck(q).truthy() {
      return Nil
    }
    r = simplifya(
      list3(list1(q_mplus), r, list4(list1(q_mtimes), int(-1), v, q)),
      Nil,
    )
  }
  if equal(r, int(0)) {
    t
  } else {
    Nil
  }
}

///|
fn d_poissimp(x : Value) -> Value raise {
  if mbagp(x).truthy() {
    cons(car(x), mapcar(y => d_poissimp(y), cdr(x)))
  } else {
    d_outofpois(x)
  }
}

///|
/// THIS TELLS THE EVALUATOR TO KEEP OUT OF POISSON $SERIES.
fn mpois(x : Value) -> Value raise {
  x
}

///|
fn d_poisplus(a : Value, b : Value) -> Value raise {
  let a = intopois(a)
  let b = intopois(b)
  pois3__mpois(poismerge22(cadr(a), cadr(b)), poismerge22(caddr(a), caddr(b)))
}

///|
fn d_poismap(p : Value, sinfn : Value, cosfn : Value) -> Value raise {
  with_specials([(q_n_starb, Nil), (q_n_starfn, Nil)], () => {
    let p = intopois(p)
    set(q_n_starfn, list1(sinfn)) |> ignore
    let s = poismap(cadr(p))
    set(q_n_starfn, list1(cosfn)) |> ignore
    list3(car(p), s, poismap(caddr(p)))
  })
}

///|
fn poismap(y : Value) -> Value raise {
  if y is Nil {
    Nil
  } else {
    set(
      q_n_starb,
      meval(
        list3(symval(q_n_starfn), poiscdecode(cadr(y)), poisdecodec(car(y))),
      ),
    )
    |> ignore
    tcons3(car(y), intopoisco(symval(q_n_starb)), poismap(cddr(y)))
  }
}

///|
fn poismerge22(r : Value, s : Value) -> Value raise {
  if r is Nil {
    s
  } else if s is Nil {
    r
  } else if equal(car(r), car(s)) {
    let tt = poisco_plus(cadr(r), cadr(s))
    if poispzero(tt).truthy() {
      poismerge22(cddr(r), cddr(s))
    } else {
      cons(car(s), cons(tt, poismerge22(cddr(r), cddr(s))))
    }
  } else if num_lt(car(r), car(s)) {
    cons(car(r), cons(cadr(r), poismerge22(cddr(r), s)))
  } else {
    cons(car(s), cons(cadr(s), poismerge22(cddr(s), r)))
  }
}

///|
fn poiscosine(m : Value) -> Value raise {
  let mut m = poisencode(m)
  if poisnegpred(m).truthy() {
    m = poischangesign(m)
  }
  pois3__mpois(Nil, list2(m, int(1)))
}

///|
fn poissine(m : Value) -> Value raise {
  let m = poisencode(m)
  if poisnegpred(m).truthy() {
    pois3__mpois(list2(poischangesign(m), int(-1)), Nil)
  } else {
    pois3__mpois(list2(m, int(1)), Nil)
  }
}

///|
fn d_intopois(x : Value) -> Value raise {
  with_special(q_n_stara, Nil, () => intopois(x))
}

///|
fn intopois(a : Value) -> Value raise {
  if atom(a) {
    if equal(a, int(0)) {
      symval(q_d_poisz)
    } else {
      pois3__mpois(Nil, list2(pois3__shift(), intopoisco(a)))
    }
  } else if eq(caar(a), q_mpois) {
    a
  } else if eq(caar(a), q_p_sin) {
    poissine(cadr(a))
  } else if eq(caar(a), q_p_cos) {
    poiscosine(cadr(a))
  } else if eq(caar(a), q_mexpt) &&
    integerp(caddr(a)) &&
    num_gt(caddr(a), int(0)) {
    d_poisexpt(intopois(cadr(a)), caddr(a))
  } else if eq(caar(a), q_mplus) {
    set(q_n_stara, intopois(cadr(a))) |> ignore
    for z in cddr(a).iter() {
      let cur = symval(q_n_stara)
      set(q_n_stara, d_poisplus(cur, intopois(z))) |> ignore
    }
    symval(q_n_stara)
  } else if eq(caar(a), q_mtimes) {
    set(q_n_stara, intopois(cadr(a))) |> ignore
    for z in cddr(a).iter() {
      let cur = symval(q_n_stara)
      set(q_n_stara, d_poistimes(cur, intopois(z))) |> ignore
    }
    symval(q_n_stara)
  } else if eq(caar(a), q_mrat) {
    intopois(ratdisrep(a))
  } else {
    pois3__mpois(Nil, list2(pois3__shift(), intopoisco(a)))
  }
}

///|
fn tcons(r : Value, s : Value) -> Value raise {
  if poispzero(car(s)).truthy() {
    cdr(s)
  } else {
    cons(r, s)
  }
}

///|
fn poisnegpred(d_n : Value) -> Value raise {
  let mut n = d_n
  while true {
    if equal(n, int(0)) {
      return Nil
    }
    let r = num_sub(num_rem(n, symval(q_poists)), symval(q_poistsm))
    if num_gt(r, int(0)) {
      return Nil
    } else if num_gt(int(0), r) {
      return t
    } else {
      n = quot(n, symval(q_poists))
    }
  }
  Nil
}

///|
fn poischangesign(d_n : Value) -> Value raise {
  num_sub(num_mul(pois3__shift(), int(2)), d_n)
}

///|
fn poisencode(h_star : Value) -> Value raise {
  with_special(q_h_star, h_star, () => {
    if !checkencode(symval(q_h_star)).truthy() {
      // NOT CLEAR WHAT IS ILLEGAL HERE
      merr("poissimp: illegal argument: ~M", [symval(q_h_star)]) |> ignore
    }
    let pv = symval(q_poisvals)
    with_specials(
      [
        (q_d_z, nth(0, pv)),
        (q_d_y, nth(1, pv)),
        (q_d_x, nth(2, pv)),
        (q_d_w, nth(3, pv)),
        (q_d_v, nth(4, pv)),
        (q_d_u, nth(5, pv)),
      ],
      () => {
        set(q_h_star, meval(symval(q_h_star))) |> ignore
        if !integerp(symval(q_h_star)) {
          merr("poisson: illegal trigonometric argument.", []) |> ignore
        }
        num_add(pois3__shift(), symval(q_h_star))
      },
    )
  })
}

///|
fn poisdecodec(m : Value) -> Value raise {
  let mut h = m
  let poists = symval(q_poists)
  let poistsm = symval(q_poistsm)
  let mut arg_ = list3(
    list1(q_mtimes),
    num_sub(num_rem(h, poists), poistsm),
    q_d_u,
  )
  for v in [q_d_v, q_d_w, q_d_x, q_d_y, q_d_z] {
    h = quot(h, poists)
    arg_ = list3(
      list1(q_mplus),
      arg_,
      list3(list1(q_mtimes), num_sub(num_rem(h, poists), poistsm), v),
    )
  }
  simplifya(arg_, Nil)
}

///|
/// THIS PROGRAM MULTIPLIES A POISSON SERIES P BY A NON-SERIES, C, WHICH IS
/// FREE OF SINES AND COSINES.
fn d_poisctimes(c : Value, p : Value) -> Value raise {
  let p = intopois(p)
  let c = intopoisco(c)
  pois3__mpois(poisctimes1(c, cadr(p)), poisctimes1(c, caddr(p)))
}

///|
fn d_outofpois(p : Value) -> Value raise {
  let mut p = p
  let mut ans : Value = Nil
  if atom(p) || !eq(caar(p), q_mpois) {
    p = intopois(p)
  }
  // DO SINES
  let mut m = cadr(p)
  while !(m is Nil) {
    ans = cons(
      list3(
        list1(q_mtimes),
        poiscdecode(cadr(m)),
        list2(list1(q_p_sin), poisdecodec(car(m))),
      ),
      ans,
    )
    m = cddr(m)
  }
  // DO COSINES
  let mut m = caddr(p)
  while !(m is Nil) {
    ans = cons(
      list3(
        list1(q_mtimes),
        poiscdecode(cadr(m)),
        if equal(car(m), pois3__shift()) {
          int(1)
        } else {
          list2(list1(q_p_cos), poisdecodec(car(m)))
        },
      ),
      ans,
    )
    m = cddr(m)
  }
  if ans is Nil {
    int(0)
  } else {
    simplifya(cons(list1(q_mplus), ans), Nil)
  }
}

///|
fn d_printpois(p : Value) -> Value raise {
  let p = intopois(p)
  // DO SINES
  let mut m = cadr(p)
  while !(m is Nil) {
    displa(
      simplifya(
        list3(
          list1(q_mtimes),
          poiscdecode(cadr(m)),
          list2(list1(q_p_sin), poisdecodec(car(m))),
        ),
        t,
      ),
    )
    |> ignore
    terpri()
    finish_output()
    m = cddr(m)
  }
  // DO COSINES
  let mut m = caddr(p)
  while !(m is Nil) {
    displa(
      simplifya(
        list3(
          list1(q_mtimes),
          poiscdecode(cadr(m)),
          if equal(car(m), pois3__shift()) {
            int(1)
          } else {
            list2(list1(q_p_cos), poisdecodec(car(m)))
          },
        ),
        t,
      ),
    )
    |> ignore
    terpri()
    finish_output()
    m = cddr(m)
  }
  q_d_done
}

///|
fn pois3__trig_var(m : Value) -> Bool {
  eq(m, q_d_u) ||
  eq(m, q_d_v) ||
  eq(m, q_d_w) ||
  eq(m, q_d_x) ||
  eq(m, q_d_y) ||
  eq(m, q_d_z)
}

///|
/// $POISDIFF DIFFERENTIATES A POISSON SERIES WRT X, Y, Z, U, V, W, OR A
/// COEFF VAR.
fn d_poisdiff(p : Value, m : Value) -> Value raise {
  with_special(q_m, m, () => {
    let p = intopois(p)
    if pois3__trig_var(m) {
      list3(car(p), cosdif(caddr(p), m), sindif(cadr(p), m))
    } else {
      list3(car(p), poisdif4(cadr(p)), poisdif4(caddr(p)))
    }
  })
}

///|
fn poisdif4(y : Value) -> Value raise {
  if y is Nil {
    Nil
  } else {
    tcons3(car(y), poiscodif(cadr(y), symval(q_m)), poisdif4(cddr(y)))
  }
}

///|
/// COSDIF DIFFERENTIATES COSINES TO GET SINES
fn cosdif(h : Value, m : Value) -> Value raise {
  if h is Nil {
    Nil
  } else {
    tcons(
      car(h),
      cons(
        poisco_star(intopoisco(num_neg(poisxcoef(car(h), m))), cadr(h)),
        cosdif(cddr(h), m),
      ),
    )
  }
}

///|
fn sindif(h : Value, m : Value) -> Value raise {
  if h is Nil {
    Nil
  } else {
    tcons(
      car(h),
      cons(
        poisco_star(intopoisco(poisxcoef(car(h), m)), cadr(h)),
        sindif(cddr(h), m),
      ),
    )
  }
}

///|
fn poisxcoef(h : Value, m : Value) -> Value raise {
  let idx = cadr(
    memq(
      m,
      list([
        q_d_u,
        int(0),
        q_d_v,
        int(1),
        q_d_w,
        int(2),
        q_d_x,
        int(3),
        q_d_y,
        int(4),
        q_d_z,
        int(5),
      ]),
    ),
  )
  num_sub(
    num_rem(quot(h, expt(symval(q_poists), idx)), symval(q_poists)),
    symval(q_poistsm),
  )
}

// AVL BALANCED TREE SEARCH AND INSERTION.
// NODE LOOKS LIKE (KEY (LLINK .  RLKINK) BALANCEFACTOR .  RECORD)
// PROGRAM FOLLOWS ALGORITHM GIVEN IN KNUTH VOL. 3 455-57

///|
/// macro (key x) = (car x)
fn key(l : Value) -> Value raise {
  car(car(l))
}

///|
/// macro (llink x) = (caadr x)
fn llink(l : Value) -> Value raise {
  caadr(car(l))
}

///|
/// macro (rlink x) = (cdadr x)
fn rlink(l : Value) -> Value raise {
  cdadr(car(l))
}

///|
/// macro (bp x) = (caddr x)
fn bp(l : Value) -> Value raise {
  caddr(car(l))
}

///|
/// macro (rec x) = (cdddr x)
fn rec(l : Value) -> Value raise {
  cdddr(car(l))
}

///|
/// macro (order< ...) = (< ...)
fn order_lt(l : Value) -> Value raise {
  let mut p = l
  while !(cdr(p) is Nil) {
    if !num_lt(car(p), cadr(p)) {
      return Nil
    }
    p = cdr(p)
  }
  t
}

///|
/// macro (order= ...) = (= ...)
fn order_eq(l : Value) -> Value raise {
  let mut p = l
  while !(cdr(p) is Nil) {
    if !num_eq(car(p), cadr(p)) {
      return Nil
    }
    p = cdr(p)
  }
  t
}

///|
/// macro (setrlink node v) = (rplacd (cadr node) v)
fn setrlink(l : Value) -> Value raise {
  rplacd(cadr(car(l)), cadr(l))
}

///|
/// macro (setllink node v) = (rplaca (cadr node) v)
fn setllink(l : Value) -> Value raise {
  rplaca(cadr(car(l)), cadr(l))
}

///|
/// macro (setbp node v) = (rplaca (cddr node) v)
fn setbp(l : Value) -> Value raise {
  rplaca(cddr(car(l)), cadr(l))
}

///|
/// macro (setrec node v) = (rplacd (cddr node) v)
fn setrec(l : Value) -> Value raise {
  rplacd(cddr(car(l)), cadr(l))
}

///|
fn pois3__key(x : Value) -> Value {
  car(x)
}

///|
fn pois3__llink(x : Value) -> Value {
  caadr(x)
}

///|
fn pois3__rlink(x : Value) -> Value {
  cdadr(x)
}

///|
fn pois3__bp(x : Value) -> Value {
  caddr(x)
}

///|
fn pois3__setrlink(x : Value, v : Value) -> Unit {
  rplacd(cadr(x), v) |> ignore
}

///|
fn pois3__setllink(x : Value, v : Value) -> Unit {
  rplaca(cadr(x), v) |> ignore
}

///|
fn pois3__setbp(x : Value, v : Int) -> Unit {
  rplaca(cddr(x), int(v)) |> ignore
}

///|
fn pois3__bp_is(x : Value, v : Int) -> Bool raise {
  num_eq(pois3__bp(x), int(v))
}

///|
fn insert_it(pp : Value, newrec : Value) -> Value raise {
  rplacd(cddr(pp), poisco_plus(cdddr(pp), newrec))
}

///|
priv enum Pois3Avl {
  A2
  A3
  A4
  A6
  A6Loop
  A7
  A7L
  A9L
  A7R
  A9R
  A10
}

///|
fn avlinsert(k : Value, newrec : Value, head : Value) -> Value raise {
  let mut tt = head
  let mut pp = pois3__rlink(head)
  let mut ss = pp
  let mut qq : Value = Nil
  let mut rr : Value = Nil
  let new_node = fn() {
    cons(k, cons(cons(Nil, Nil), cons(int(0), newrec)))
  }
  let mut state = Pois3Avl::A2
  while true {
    match state {
      A2 =>
        if num_lt(k, pois3__key(pp)) {
          state = A3
        } else if num_lt(pois3__key(pp), k) {
          state = A4
        } else {
          insert_it(pp, newrec) |> ignore
          return head
        }
      A3 => {
        qq = pois3__llink(pp)
        if qq is Nil {
          pois3__setllink(pp, new_node())
          state = A6
          continue
        } else if pois3__bp_is(qq, 0) {
          ()
        } else {
          tt = pp
          ss = qq
        }
        pp = qq
        state = A2
      }
      A4 => {
        qq = pois3__rlink(pp)
        if qq is Nil {
          pois3__setrlink(pp, new_node())
          state = A6
          continue
        } else if pois3__bp_is(qq, 0) {
          ()
        } else {
          tt = pp
          ss = qq
        }
        pp = qq
        state = A2
      }
      A6 => {
        if num_lt(k, pois3__key(ss)) {
          pp = pois3__llink(ss)
        } else {
          pp = pois3__rlink(ss)
        }
        rr = pp
        state = A6Loop
      }
      A6Loop =>
        if num_lt(k, pois3__key(pp)) {
          pois3__setbp(pp, -1)
          pp = pois3__llink(pp)
        } else if num_lt(pois3__key(pp), k) {
          pois3__setbp(pp, 1)
          pp = pois3__rlink(pp)
        } else if num_eq(k, pois3__key(pp)) {
          state = A7
        }
      A7 => state = if num_lt(k, pois3__key(ss)) { A7L } else { A7R }
      A7L => {
        if pois3__bp_is(ss, 0) {
          pois3__setbp(ss, -1)
          pois3__setllink(head, num_add(pois3__llink(head), int(1)))
          return head
        } else if pois3__bp_is(ss, 1) {
          pois3__setbp(ss, 0)
          return head
        }
        if !pois3__bp_is(rr, -1) {
          state = A9L
          continue
        }
        pp = rr
        pois3__setllink(ss, pois3__rlink(rr))
        pois3__setrlink(rr, ss)
        pois3__setbp(ss, 0)
        pois3__setbp(rr, 0)
        state = A10
      }
      A9L => {
        pp = pois3__rlink(rr)
        pois3__setrlink(rr, pois3__llink(pp))
        pois3__setllink(pp, rr)
        pois3__setllink(ss, pois3__rlink(pp))
        pois3__setrlink(pp, ss)
        if pois3__bp_is(pp, -1) {
          pois3__setbp(ss, 1)
          pois3__setbp(rr, 0)
        } else if pois3__bp_is(pp, 0) {
          pois3__setbp(ss, 0)
          pois3__setbp(rr, 0)
        } else if pois3__bp_is(pp, 1) {
          pois3__setbp(ss, 0)
          pois3__setbp(rr, -1)
        }
        pois3__setbp(pp, 0)
        state = A10
      }
      A7R => {
        if pois3__bp_is(ss, 0) {
          pois3__setbp(ss, 1)
          pois3__setllink(head, num_add(pois3__llink(head), int(1)))
          return head
        } else if pois3__bp_is(ss, -1) {
          pois3__setbp(ss, 0)
          return head
        }
        if !pois3__bp_is(rr, 1) {
          state = A9R
          continue
        }
        pp = rr
        pois3__setrlink(ss, pois3__llink(rr))
        pois3__setllink(rr, ss)
        pois3__setbp(ss, 0)
        pois3__setbp(rr, 0)
        state = A10
      }
      A9R => {
        pp = pois3__llink(rr)
        pois3__setllink(rr, pois3__rlink(pp))
        pois3__setrlink(pp, rr)
        pois3__setrlink(ss, pois3__llink(pp))
        pois3__setllink(pp, ss)
        if pois3__bp_is(pp, 1) {
          pois3__setbp(ss, -1)
          pois3__setbp(rr, 0)
        } else if pois3__bp_is(pp, 0) {
          pois3__setbp(ss, 0)
          pois3__setbp(rr, 0)
        } else if pois3__bp_is(pp, -1) {
          pois3__setbp(ss, 0)
          pois3__setbp(rr, 1)
        }
        pois3__setbp(pp, 0)
        state = A10
      }
      A10 => {
        if eq(ss, pois3__rlink(tt)) {
          pois3__setrlink(tt, pp)
        } else {
          pois3__setllink(tt, pp)
        }
        return head
      }
    }
  }
  head
}

///|
fn avlinit(key : Value, rec : Value) -> Value raise {
  cons(
    q_top,
    cons(
      cons(int(0), cons(key, cons(cons(Nil, Nil), cons(int(0), rec)))),
      cons(int(0), Nil),
    ),
  )
}

///|
/// UNTREE CONVERTS THE TREE TO A LIST WHICH LOOKS LIKE ( SMALLEST-KEY
/// RECORD NEXT-SMALLEST-KEY RECORD ....  LARGEST-KEY RECORD)
fn untree(h : Value) -> Value raise {
  with_special(q_ans, Nil, () => {
    untree1(pois3__rlink(h)) |> ignore
    symval(q_ans)
  })
}

///|
fn untree1(h : Value) -> Value raise {
  if h is Nil {
    symval(q_ans)
  } else if pois3__rlink(h) is Nil {
    set(q_ans, tcons3(car(h), cdddr(h), symval(q_ans))) |> ignore
    untree1(pois3__llink(h))
  } else {
    let k = car(h)
    let r = cdddr(h)
    set(q_ans, tcons3(k, r, untree1(pois3__rlink(h)))) |> ignore
    untree1(pois3__llink(h))
  }
}

///|
fn tcons3(r : Value, s : Value, tt : Value) -> Value raise {
  if poispzero(s).truthy() {
    tt
  } else {
    cons(r, cons(s, tt))
  }
}

///|
fn poismerges(a : Value, ae : Value, l : Value) -> Value raise {
  if equal(pois3__shift(), ae) {
    // SINE(0) IS 0
    l
  } else if poisnegpred(ae).truthy() {
    poismerge(poisco_star(int(-1), a), poischangesign(ae), l)
  } else {
    poismerge(a, ae, l)
  }
}

///|
fn poismergec(a : Value, ae : Value, l : Value) -> Value raise {
  if poisnegpred(ae).truthy() {
    poismerge(a, poischangesign(ae), l)
  } else {
    poismerge(a, ae, l)
  }
}

///|
fn poismerge(a : Value, ae : Value, l : Value) -> Value raise {
  if poispzero(a).truthy() {
    Nil
  } else {
    merge11(a, ae, l)
  }
}

///|
fn poismerge2(r : Value, s : Value) -> Value raise {
  if r is Nil {
    return s
  }
  if s is Nil {
    return r
  }
  let mut r = r
  let mut s = s
  let n = cons(int(0), r)
  let mut m = n
  while true {
    if r is Nil {
      rplacd(m, s) |> ignore
      return cdr(n)
    } else if s is Nil {
      return cdr(n)
    } else if equal(car(r), car(s)) {
      let tt = poisco_plus(cadr(r), cadr(s))
      if poispzero(tt).truthy() {
        rplacd(m, cddr(r)) |> ignore
        r = cddr(r)
        s = cddr(s)
      } else {
        rplaca(cdr(r), tt) |> ignore
        s = cddr(s)
        r = cddr(r)
        m = cddr(m)
      }
    } else if num_gt(car(r), car(s)) {
      rplacd(m, s) |> ignore
      s = cddr(s)
      rplacd(cddr(m), r) |> ignore
      m = cddr(m)
    } else {
      r = cddr(r)
      m = cddr(m)
    }
  }
  Nil
}

///|
fn merge11(a : Value, ae : Value, l : Value) -> Value raise {
  poismerge2(list2(ae, a), l)
}

///|
fn poismergesx(a : Value, ae : Value, l : Value) -> Value raise {
  if equal(pois3__shift(), ae) {
    // SINE(0) IS 0
    l
  } else if poisnegpred(ae).truthy() {
    avlinsert(poischangesign(ae), poisco_star(int(-1), a), l)
  } else {
    avlinsert(ae, a, l)
  }
}

///|
fn poismergecx(a : Value, ae : Value, l : Value) -> Value raise {
  if poisnegpred(ae).truthy() {
    avlinsert(poischangesign(ae), a, l)
  } else {
    avlinsert(ae, a, l)
  }
}

///|
fn poisctimes1(c : Value, h : Value) -> Value raise {
  if h is Nil {
    Nil
  } else if symval(q_trim).truthy() && trimf(car(h)).truthy() {
    poisctimes1(c, cddr(h))
  } else {
    tcons(car(h), cons(poisco_star(c, cadr(h)), poisctimes1(c, cddr(h))))
  }
}

///|
fn trimf(m : Value) -> Value raise {
  meval(
    list([
      list1(q_d_poistrim),
      poisxcoef(m, q_d_u),
      poisxcoef(m, q_d_v),
      poisxcoef(m, q_d_w),
      poisxcoef(m, q_d_x),
      poisxcoef(m, q_d_y),
      poisxcoef(m, q_d_z),
    ]),
  )
}

///|
fn d_poistimes(a : Value, b : Value) -> Value raise {
  with_special(q_trim, Nil, () => {
    let a = intopois(a)
    let b = intopois(b)
    if getl_lm_fcn_prop(q_d_poistrim, list2(q_expr, q_subr)).truthy() ||
      mget(q_d_poistrim, q_mexpr).truthy() {
      set(q_trim, t) |> ignore
    }
    if nonperiod(a).truthy() {
      return d_poisctimes(cadr(caddr(a)), b)
    } else if nonperiod(b).truthy() {
      return d_poisctimes(cadr(caddr(b)), a)
    }
    let shift = pois3__shift()
    let zero = intopoisco(int(0))
    let slc = avlinit(shift, zero)
    let clc = avlinit(shift, zero)
    let trim = fn() { symval(q_trim).truthy() }
    let pair = fn(ae : Value, x : Value) -> (Value, Value, Value, Value) raise {
      let t1 = num_add(num_add(ae, shift), num_neg(x))
      let t2 = num_add(num_add(ae, num_neg(shift)), x)
      if trim() {
        (t1, t2, trimf(t1), trimf(t2))
      } else {
        (t1, t2, Nil, Nil)
      }
    }
    // PROCEED THROUGH ALL THE SINES IN ARGUMENT A
    let mut sla = cadr(a)
    while !(sla is Nil) {
      let aa = halve(cadr(sla))
      let ae = car(sla)
      // SINE(U)*SINE(V) ==> (-COSINE(U+V) + COSINE(U-V))/2
      let mut slb = cadr(b)
      while !(slb is Nil) {
        let (t1, t2, f1, f2) = pair(ae, car(slb))
        let temp = poisco_star(aa, cadr(slb))
        if !poispzero(temp).truthy() {
          if !f1.truthy() {
            poismergecx(temp, t1, clc) |> ignore
          }
          if !f2.truthy() {
            poismergecx(poisco_star(int(-1), temp), t2, clc) |> ignore
          }
        }
        slb = cddr(slb)
      }
      // SINE*COSINE ==> SINE + SINE
      let mut clb = caddr(b)
      while !(clb is Nil) {
        let (t1, t2, f1, f2) = pair(ae, car(clb))
        let temp = poisco_star(aa, cadr(clb))
        if !poispzero(temp).truthy() {
          if !f1.truthy() {
            poismergesx(temp, t1, slc) |> ignore
          }
          if !f2.truthy() {
            poismergesx(temp, t2, slc) |> ignore
          }
        }
        clb = cddr(clb)
      }
      sla = cddr(sla)
    }
    // PROCEED THROUGH ALL THE COSINES IN ARGUMENT A
    let mut cla = caddr(a)
    while !(cla is Nil) {
      let aa = halve(cadr(cla))
      let ae = car(cla)
      // COSINE*SINE ==> SINE - SINE
      let mut slb = cadr(b)
      while !(slb is Nil) {
        let (t1, t2, f1, f2) = pair(ae, car(slb))
        let temp = poisco_star(aa, cadr(slb))
        if !poispzero(temp).truthy() {
          if !f1.truthy() {
            poismergesx(poisco_star(int(-1), temp), t1, slc) |> ignore
          }
          if !f2.truthy() {
            poismergesx(temp, t2, slc) |> ignore
          }
        }
        slb = cddr(slb)
      }
      // COSINE*COSINE ==> COSINE + COSINE
      let mut clb = caddr(b)
      while !(clb is Nil) {
        let (t1, t2, f1, f2) = pair(ae, car(clb))
        let temp = poisco_star(aa, cadr(clb))
        if !poispzero(temp).truthy() {
          if !f1.truthy() {
            poismergecx(temp, t1, clc) |> ignore
          }
          if !f2.truthy() {
            poismergecx(temp, t2, clc) |> ignore
          }
        }
        clb = cddr(clb)
      }
      cla = cddr(cla)
    }
    pois3__mpois(untree(slc), untree(clc))
  })
}

///|
fn d_poisexpt(p : Value, n : Value) -> Value raise {
  if !(integerp(n) && num_ge(n, int(0))) {
    merr("poisexpt: second argument must be a nonnegative integer; found: ~M", [
      n,
    ])
    |> ignore
  }
  let mut p = p
  let mut n = n
  let mut h : Value = Nil
  let mut u = if oddp(n) {
    p
  } else {
    h = intopois(int(1))
    h
  }
  while true {
    n = ash(n, -1)
    if zerop(n) {
      return u
    }
    p = d_poistimes(p, p)
    if oddp(n) {
      u = if equal(u, h) { p } else { d_poistimes(u, p) }
    }
  }
  u
}

///|
fn d_poissquare(a : Value) -> Value raise {
  d_poisexpt(a, int(2))
}

///|
/// $POISINT INTEGRATES A POISSON SERIES WRT X,Y, Z, U, V, W.  THE VARIABLE
/// OF INTEGRATION MUST OCCUR ONLY IN THE ARGUMENTS OF SIN OR COS, OR ONLY
/// IN THE COEFFICIENTS.  NON-PERIODIC TERMS ARE REMOVED.
fn d_poisint(p : Value, m : Value) -> Value raise {
  with_specials([(q_m, m), (q_b_star, Nil)], () => {
    let p = intopois(p)
    if pois3__trig_var(m) {
      list3(car(p), cosint_star(caddr(p), m), sinint_star(cadr(p), m))
    } else {
      list3(car(p), poisint4(cadr(p)), poisint4(caddr(p)))
    }
  })
}

///|
fn poisint4(y : Value) -> Value raise {
  if y is Nil {
    Nil
  } else {
    tcons3(car(y), poiscointeg(cadr(y), symval(q_m)), poisint4(cddr(y)))
  }
}

///|
/// COSINT* INTEGRATES COSINES TO GET SINES
fn cosint_star(h : Value, m : Value) -> Value raise {
  if h is Nil {
    return Nil
  }
  set(q_b_star, poisxcoef(car(h), m)) |> ignore
  if equal(int(0), symval(q_b_star)) {
    cosint_star(cddr(h), m)
  } else {
    let c = poisco_star(
      intopoisco(list3(list1(q_mexpt), symval(q_b_star), int(-1))),
      cadr(h),
    )
    tcons(car(h), cons(c, cosint_star(cddr(h), m)))
  }
}

///|
fn sinint_star(h : Value, m : Value) -> Value raise {
  if h is Nil {
    return Nil
  }
  set(q_b_star, poisxcoef(car(h), m)) |> ignore
  if equal(int(0), symval(q_b_star)) {
    sinint_star(cddr(h), m)
  } else {
    let c = poisco_star(
      intopoisco(
        list3(list1(q_mexpt), num_neg(poisxcoef(car(h), m)), int(-1)),
      ),
      cadr(h),
    )
    tcons(car(h), cons(c, sinint_star(cddr(h), m)))
  }
}

///|
/// $POISSUBST SUBSTITUTES AN EXPRESSION FOR A VARIABLE IN ARGUMENT OF TRIG
/// FUNCTIONS OR COEFFICIENTS.
fn poissubsta(a : Value, b_star : Value, c : Value) -> Value raise {
  with_specials([(q_b_star, b_star), (q_ss, Nil), (q_cc, Nil)], () => {
    set(
      q_h_star,
      num_sub(
        poisencode(
          list3(list1(q_mplus), a, list3(list1(q_mtimes), int(-1), b_star)),
        ),
        pois3__shift(),
      ),
    )
    |> ignore
    poissubst1s(cadr(c)) |> ignore
    poissubst1c(caddr(c)) |> ignore
    list3(car(c), symval(q_ss), symval(q_cc))
  })
}

///|
fn poissubst1s(c : Value) -> Value raise {
  if c is Nil {
    Nil
  } else {
    set(q_ss, poismerges(cadr(c), argsubst(car(c)), symval(q_ss))) |> ignore
    poissubst1s(cddr(c))
  }
}

///|
fn poissubst1c(c : Value) -> Value raise {
  if c is Nil {
    Nil
  } else {
    set(q_cc, poismergec(cadr(c), argsubst(car(c)), symval(q_cc))) |> ignore
    poissubst1c(cddr(c))
  }
}

///|
fn argsubst(c : Value) -> Value raise {
  num_add(c, num_mul(symval(q_h_star), poisxcoef(c, symval(q_b_star))))
}

///|
fn d_poissubst(
  aa : Value,
  bb : Value,
  cc : Value,
  dd? : Value = Nil,
  nn? : Value = Nil,
) -> Value raise {
  if dd.truthy() && nn.truthy() {
    fancypoissubst(aa, bb, intopois(cc), intopois(dd), nn)
  } else {
    let c = intopois(cc)
    with_specials([(q_a_star, aa), (q_b_star, bb)], () => if pois3__trig_var(
        symval(q_b_star),
      ) {
      poissubsta(symval(q_a_star), symval(q_b_star), c)
    } else {
      list3(car(c), poissubstco1(cadr(c)), poissubstco1(caddr(c)))
    })
  }
}

///|
fn poissubstco1(c : Value) -> Value raise {
  if c is Nil {
    Nil
  } else {
    tcons(
      car(c),
      cons(
        poissubstco(symval(q_a_star), symval(q_b_star), cadr(c)),
        poissubstco1(cddr(c)),
      ),
    )
  }
}

///|
/// SUBSTITUTES A+D FOR B IN C, WHERE D IS EXPANDED IN POWERSERIES TO ORDER N
fn fancypoissubst(
  a : Value,
  b_star : Value,
  c : Value,
  d : Value,
  n : Value,
) -> Value raise {
  with_specials(
    [
      (q_b_star, b_star),
      (q_h_star, Nil),
      (q_dc, Nil),
      (q_ds, Nil),
      (q_n_starans, Nil),
    ],
    () => {
      set(q_n_starans, pois3__mpois(Nil, Nil)) |> ignore
      let d = intopois(d)
      set(q_dc, intopois(int(1))) |> ignore
      set(q_ds, intopois(int(0))) |> ignore
      if equal(n, int(0)) {
        return d_poissubst(a, b_star, c)
      }
      fancypois1s(d, int(1), int(1), n) |> ignore
      set(
        q_h_star,
        num_sub(
          poisencode(
            list3(list1(q_mplus), a, list3(list1(q_mtimes), int(-1), b_star)),
          ),
          pois3__shift(),
        ),
      )
      |> ignore
      fancypas(cadr(c)) |> ignore
      fancypac(caddr(c)) |> ignore
      symval(q_n_starans)
    },
  )
}

///|
/// DP IS LAST POWER: D^(N-1), LIM IS HIGHEST TO GO
fn fancypois1s(d : Value, dp : Value, n : Value, lim : Value) -> Value raise {
  if num_gt(n, lim) {
    Nil
  } else {
    let ds = symval(q_ds)
    let dp = d_poistimes(dp, d)
    set(
      q_ds,
      d_poisplus(
        ds,
        d_poisctimes(
          list3(
            list1(q_rat),
            expt(int(-1), ash(num_sub(n, int(1)), -1)),
            factorial(n),
          ),
          dp,
        ),
      ),
    )
    |> ignore
    fancypois1c(d, dp, num_add(n, int(1)), lim)
  }
}

///|
/// DP IS LAST POWER: D^(N-1), LIM IS HIGHEST TO GO
fn fancypois1c(d : Value, dp : Value, n : Value, lim : Value) -> Value raise {
  if num_gt(n, lim) {
    Nil
  } else {
    let dc = symval(q_dc)
    let dp = d_poistimes(dp, d)
    set(
      q_dc,
      d_poisplus(
        dc,
        d_poisctimes(
          list3(list1(q_rat), expt(int(-1), ash(n, -1)), factorial(n)),
          dp,
        ),
      ),
    )
    |> ignore
    fancypois1s(d, dp, num_add(n, int(1)), lim)
  }
}

///|
/// SUBSTITUTING A+D FOR B, WITH DC AND DS THE SERIES FOR COS(D) AND SIN(D):
/// COS(R+K*B) ==> COS(R+K*A)*DC - K*SIN(R+K*A)*DS
/// SIN(R+K*B) ==> K*COS(R+K*A)*DS + SIN(R+K*A)*DC
/// THIS IS CORRECT ONLY FOR K = 1 OR -1.
fn fancypac(c : Value) -> Value raise {
  let mut c = c
  while !(c is Nil) {
    set(q_n_starcoef, poisxcoef(car(c), symval(q_b_star))) |> ignore
    if equal(symval(q_n_starcoef), int(0)) {
      set(
        q_n_starans,
        d_poisplus(
          symval(q_n_starans),
          pois3__mpois(Nil, list2(car(c), cadr(c))),
        ),
      )
      |> ignore
    } else {
      set(
        q_n_starcoef,
        poisco_star(cadr(c), intopoisco(symval(q_n_starcoef))),
      )
      |> ignore
      if !poispzero(symval(q_n_starcoef)).truthy() {
        set(q_n_starargc, argsubst(car(c))) |> ignore
        let ans = symval(q_n_starans)
        let argc = symval(q_n_starargc)
        set(
          q_n_starans,
          d_poisplus(
            ans,
            d_poisplus(
              d_poistimes(
                pois3__mpois(Nil, poismergec(cadr(c), argc, Nil)),
                symval(q_dc),
              ),
              d_poistimes(
                pois3__mpois(
                  poismerges(
                    poisco_star(int(-1), symval(q_n_starcoef)),
                    argc,
                    Nil,
                  ),
                  Nil,
                ),
                symval(q_ds),
              ),
            ),
          ),
        )
        |> ignore
      }
    }
    c = cddr(c)
  }
  Nil
}

///|
fn fancypas(c : Value) -> Value raise {
  let mut c = c
  while !(c is Nil) {
    set(q_n_starcoef, poisxcoef(car(c), symval(q_b_star))) |> ignore
    if equal(symval(q_n_starcoef), int(0)) {
      set(
        q_n_starans,
        d_poisplus(
          symval(q_n_starans),
          pois3__mpois(list2(car(c), cadr(c)), Nil),
        ),
      )
      |> ignore
    } else {
      set(
        q_n_starcoef,
        poisco_star(cadr(c), intopoisco(symval(q_n_starcoef))),
      )
      |> ignore
      if !poispzero(symval(q_n_starcoef)).truthy() {
        set(q_n_starargc, argsubst(car(c))) |> ignore
        let ans = symval(q_n_starans)
        let argc = symval(q_n_starargc)
        set(
          q_n_starans,
          d_poisplus(
            ans,
            d_poisplus(
              d_poistimes(
                pois3__mpois(Nil, poismergec(symval(q_n_starcoef), argc, Nil)),
                symval(q_ds),
              ),
              d_poistimes(
                pois3__mpois(poismerges(cadr(c), argc, Nil), Nil),
                symval(q_dc),
              ),
            ),
          ),
        )
        |> ignore
      }
    }
    c = cddr(c)
  }
  Nil
}

///|
fn init_pois3() -> Unit raise {
  // (let ((n 5)) (setq poists ... ))
  let n = 5
  set(q_poists, expt(int(2), int(n))) |> ignore
  let vals = []
  for i = 5; i >= 0; i = i - 1 {
    vals.push(expt(symval(q_poists), int(i)))
  }
  set(q_poisvals, list(vals)) |> ignore
  set(q_poistsm, expt(int(2), int(n - 1))) |> ignore
  let mut sum = int(0)
  for i in 0..=5 {
    sum = num_add(sum, num_mul(symval(q_poistsm), expt(symval(q_poists), int(i))))
  }
  set(q_poishift, sum) |> ignore
  set(q_d_poisz, list3(list2(q_mpois, q_simp), Nil, Nil)) |> ignore
  set(
    q_d_pois1,
    list3(list2(q_mpois, q_simp), Nil, list2(symval(q_poishift), int(1))),
  )
  |> ignore
}
