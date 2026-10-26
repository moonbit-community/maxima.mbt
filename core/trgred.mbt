// Port of src/trgred.lisp: trigreduce, and SP1, the first pass of power
// series expansion.
//
// The Trigreduce file contains a group of routines which can be used to
// make trigonometric simplifications of expressions. The bulk of the
// routines here involve the reductions of products of sin's and cos's.
//
//   *TRIGRED   indicates that the special simplifications for $TRIGREDUCE
//              are to be used.
//   *NOEXPAND  indicates that trig functions of sums of angles are not to
//              be used.

///|
let trgred__expt2_pattern : Value = try! lread(
  "((mplus) ((coeffpp) (fr freevar)) ((coeffpp) (exp true)))",
)

///|
let trgred__trigex_pattern : Value = try! lread(
  "((mplus) ((coeffpp) (a freevar)) ((coeffpp) (b true)))",
)

///|
/// `(m+l l)`
fn trgred__m_plus_l(l : Value) -> Value raise {
  addn(l, Nil)
}

///|
/// `(m*l l)`
fn trgred__m_times_l(l : Value) -> Value raise {
  muln(l, Nil)
}

///|
/// `(m- x)` with one argument: `(mul* -1 x)`.
fn trgred__m_neg(x : Value) -> Value raise {
  mul2_star(Fix(-1L), x)
}

///|
/// `(signp e x)`: x is a number equal to zero.
fn trgred__signp_e(x : Value) -> Bool raise {
  numberp(x) && zerop(x)
}

///|
fn trgred__trig12() -> Value {
  list([
    q_p_cos, q_p_sin, q_p_tan, q_p_cot, q_p_sec, q_p_csc, q_p_cosh, q_p_sinh, q_p_tanh,
    q_p_coth, q_p_sech, q_p_csch,
  ])
}

///|
/// Without the check for the value of $simp, trigreduce can enter an endless
/// loop--for example trigreduce((-1)*x).
fn d_trigreduce(exp_ : Value, var_? : Value = q_n_starnovar) -> Value raise {
  with_specials(
    [
      (q_var, var_),
      (q_n_startrigred, t),
      (q_n_starnoexpand, t),
      (q_d_trigexpand, Nil),
      (q_d_verbose, Nil),
      (q_d_ratprint, Nil),
    ],
    () => if symval(q_d_simp).truthy() { gcdred(sp1(exp_)) } else { exp_ },
  )
}

///|
/// The first pass in power series expansion (used by $powerseries in
/// series.lisp), but also used by $trigreduce. Expands / reduces the
/// expression E as a function VAR, controlled by the *TRIGRED and *NOEXPAND
/// flags.
fn sp1(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    // We recognise some special patterns that are expressed as sums, such
    // as 1+tan(x)^2 => sec(x)^2. Rewrite using the first matching pattern
    // (and recurse to try to simplify further). If no pattern matches,
    // expand each term in the sum.
    for pair in symval(q_ear_trans_list_plus).iter() {
      let match_ = m2(e, first(pair))
      if match_.truthy() {
        let v = sp1(sch_replace(match_, second(pair)))
        if v.truthy() {
          return v
        }
        break
      }
    }
    trgred__m_plus_l(mapcar(x => sp1(x), cdr(e)))
  } else if eq(caar(e), q_mtimes) {
    sp1times(e)
  } else if eq(caar(e), q_mexpt) {
    sp1expt(sp1(cadr(e)), sp1(caddr(e)))
  } else if eq(caar(e), q_p_log) {
    sp1log(sp1(cadr(e)))
  } else if memq(caar(e), trgred__trig12()).truthy() {
    sp1trig(
      list2(car(e), with_special(q_n_starnoexpand, t, () => sp1(cadr(e)))),
    )
  } else if memq(
      caar(e),
      list([
        q_p_asin, q_p_acos, q_p_atan, q_p_acot, q_p_asec, q_p_acsc, q_p_asinh,
        q_p_acosh, q_p_atanh, q_p_acoth, q_p_asech, q_p_acsch,
      ]),
    ).truthy() {
    sp1atrig(caar(e), with_special(q_n_starnoexpand, t, () => sp1(cadr(e))))
  } else if eq(caar(e), q_mrat) {
    sp1(ratdisrep(e))
  } else if mbagp(e).truthy() {
    cons(list1(caar(e)), mapcar(u => gcdred(sp1(u)), cdr(e)))
  } else if eq(caar(e), q_p_integrate) {
    list_star([list1(q_p_integrate), sp1(cadr(e)), cddr(e)])
  } else {
    recur_apply(lfunc("sp1", args => sp1(arg(args, 0))), e)
  }
}

///|
fn trigfp(e : Value) -> Value raise {
  lbool((!atom(e) && trigp(caar(e)).truthy()) || equal(e, Fix(1L)))
}

///|
fn gcdred(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    trgred__m_plus_l(mapcar(x => gcdred(x), cdr(e)))
  } else if eq(caar(e), q_mtimes) {
    let mut nn = list1(Fix(1L))
    let mut nd = list1(Fix(1L))
    let mut ee = cdr(e)
    while ee is Cons(_) {
      let f = car(ee)
      if mexptp(f).truthy() &&
        (
          (numberp(caddr(f)) && minusp(caddr(f))) ||
          (
            mtimesp(caddr(f)).truthy() &&
            numberp(cadr(caddr(f))) &&
            minusp(cadr(caddr(f)))
          )
        ) {
        nd = cons(power_star(cadr(f), trgred__m_neg(caddr(f))), nd)
      } else if ratnump(f).truthy() {
        nn = cons(cadr(f), nn)
        nd = cons(caddr(f), nd)
      } else {
        nn = cons(f, nn)
      }
      ee = cdr(ee)
    }
    nn = trgred__m_times_l(nn)
    nd = trgred__m_times_l(nd)
    if equal(nd, Fix(1L)) {
      nn
    } else {
      let gcd = d_gcd(nn, nd, Nil)
      if equal(gcd, Fix(1L)) {
        e
      } else {
        div_star(cadr(d_divide(nn, gcd, Nil)), cadr(d_divide(nd, gcd, Nil)))
      }
    }
  } else {
    recur_apply(lfunc("gcdred", args => gcdred(arg(args, 0))), e)
  }
}

///|
fn sp1times(e : Value) -> Value raise {
  with_specials(
    [(q_ear_trigbuckets, Nil), (q_ear_hyperbuckets, Nil), (q_n_starlin, list1(Fix(0L)))],
    () => {
      let mut fr : Value = Nil
      let mut g = list1(Fix(1L))
      let var_ = symval(q_var)
      for factor in cdr(e).iter() {
        if mnump(factor).truthy() ||
          (!eq(var_, q_n_starnovar) && free(factor, var_).truthy()) {
          fr = cons(factor, fr)
        } else if atom(factor) {
          g = cons(factor, g)
        } else if trigfp(factor).truthy() ||
          (eq(caar(factor), q_mexpt) && trigfp(cadr(factor)).truthy()) {
          sp1add(factor) |> ignore
        } else {
          g = cons(factor, g)
        }
      }
      g = mapcar(x => sp1(x), g)
      mapc(q => sp1sincos(q, t) |> ignore, symval(q_ear_trigbuckets)) |> ignore
      mapc(q => sp1sincos(q, Nil) |> ignore, symval(q_ear_hyperbuckets))
      |> ignore
      fr = cons(
        with_special(q_d_float, Nil, () => power_star(
          symval(q_n1_sl_sl2),
          trgred__m_plus_l(symval(q_n_starlin)),
        )),
        fr,
      )
      set(q_n_starlin, Nil) |> ignore
      let tr = cons(
        q_op_star,
        mapcan(b => sp1untrep(b), symval(q_ear_trigbuckets)),
      )
      let a1 = sp1tlin(tr, t)
      let a2 = sp1tplus(symval(q_n_starlin), t)
      g = nconc_n([a1, a2, g])
      set(q_n_starlin, Nil) |> ignore
      let hyp = cons(
        q_op_star,
        mapcan(b => sp1untrep(b), symval(q_ear_hyperbuckets)),
      )
      let b1 = sp1tlin(hyp, Nil)
      let b2 = sp1tplus(symval(q_n_starlin), Nil)
      g = nconc_n([b1, b2, g])
      g = d_expand(
        with_special(q_d_keepfloat, t, () => d_ratsimp(
          cons(list1(q_mtimes), g),
          Nil,
        )),
      )
      if mtimesp(g).truthy() {
        g = mapcar(x => sp1(x), cdr(g))
      } else {
        g = list1(sp1(g))
      }
      trgred__m_times_l(cons(Fix(1L), nconc_n([g, fr, cdr(tr), cdr(hyp)])))
    },
  )
}

///|
fn sp1tlin(l : Value, trig : Value) -> Value raise {
  let ops = if trig.truthy() {
    list2(q_p_sin, q_p_cos)
  } else {
    list2(q_p_sinh, q_p_cosh)
  }
  if cdr(l) is Nil {
    Nil
  } else if atom(cadr(l)) {
    // a factor simplified by SP1UNTREP can be an atom or a power of one
    sp1tlin(cdr(l), trig)
  } else if eq(caaadr(l), q_mexpt) &&
    integerp(caddr(cadr(l))) &&
    !atom(cadadr(l)) &&
    memq(caaadr(cadr(l)), ops).truthy() {
    let a = funcall(
      cdr(assq(caaadr(cadr(l)), symval(q_ear_sc_hatndisp))),
      [caddr(cadr(l)), cadadr(cadr(l))],
    )
    cons(a, sp1tlin(rplacd(l, cddr(l)), trig))
  } else if memq(caaadr(l), ops).truthy() {
    set(q_n_starlin, cons(cadr(l), symval(q_n_starlin))) |> ignore
    sp1tlin(rplacd(l, cddr(l)), trig)
  } else {
    sp1tlin(cdr(l), trig)
  }
}

///|
/// multiply-sc-terms of SP1TPLUS: rewrites a*sc as a sum of sines and
/// cosines, returning the list of terms of that sum.
fn trgred__multiply_sc_terms(term : Value, sc : Value, trig : Value) -> Value raise {
  let coefficient = if mtimesp(term).truthy() { cadr(term) } else { Nil }
  let term_sc = if mtimesp(term).truthy() { caddr(term) } else { term }
  let expanded = sp1sintcos(term_sc, sc, trig)
  // expanded will now either be sin(foo) or cos(foo) OR it will be a sum of
  // such terms.
  if coefficient is Nil {
    list1(expanded)
  } else if atom(expanded) ||
    memq(caar(expanded), list([q_p_sin, q_p_cos, q_p_sinh, q_p_cosh])).truthy() {
    list1(mul2_star(coefficient, expanded))
  } else if mplusp(expanded).truthy() {
    mapcar(summand => mul2_star(coefficient, summand), cdr(expanded))
  } else {
    // SP1SINTCOS can also return numbers and constant expressions. Assume
    // that's the case here.
    list1(mul2_star(coefficient, expanded))
  }
}

///|
/// Rewrite a product of sines and cosines as a sum.
///
/// L is a list of sines and cosines, representing their product. ANS starts
/// as the first; then for each term in the rest of the list, we multiply
/// the answer found so far by that term. The factor of 2^(k-1), where k is
/// the length of the list, is returned separately.
fn sp1tplus(l : Value, trig : Value) -> Value raise {
  if l is Nil || cdr(l) is Nil {
    l
  } else {
    let mut ans = list1(first(l))
    for sc in rest(l).iter() {
      let s = trgred__m_plus_l(
        mapcan(q => trgred__multiply_sc_terms(q, sc, trig), ans),
      )
      // Treat the sum as a list of its terms
      ans = if mplusp(s).truthy() { cdr(s) } else { list1(s) }
    }
    list2(
      mk(q_rat, [Fix(1L), expt(Fix(2L), int(length(l) - 1))]),
      trgred__m_plus_l(ans),
    )
  }
}

///|
/// The core of trigreduce. Performs transformations like
/// sin(x)*cos(x) => sin(2*x).
///
/// This function only does something non-trivial if both a and b have one
/// of sin, cos, sinh and cosh as top-level operators.
fn sp1sintcos(a : Value, b : Value, trig : Value) -> Value raise {
  let scs = list([q_p_sin, q_p_cos, q_p_sinh, q_p_cosh])
  if atom(a) ||
    atom(b) ||
    !memq(caar(a), scs).truthy() ||
    !memq(caar(b), scs).truthy() {
    return mul3(Fix(2L), a, b)
  }
  let x = add2_star(cadr(a), cadr(b))
  let mut y = sub_star(cadr(a), cadr(b))
  if !eq(caar(a), caar(b)) {
    let b = if trig.truthy() { list1(q_p_sin) } else { list1(q_p_sinh) }
    if !(eq(caar(a), q_p_sin) || eq(caar(a), q_p_sinh)) {
      y = trgred__m_neg(y)
    }
    add2_star(list2(b, x), list2(b, y))
  } else if memq(caar(a), list2(q_p_cos, q_p_cosh)).truthy() {
    add2_star(list2(list1(caar(a)), x), list2(list1(caar(a)), y))
  } else if trig.truthy() {
    sub_star(list2(list1(q_p_cos), y), list2(list1(q_p_cos), x))
  } else {
    sub_star(list2(list1(q_p_cosh), x), list2(list1(q_p_cosh), y))
  }
}

///|
/// For COS(X)^2, TRIGBUCKET is (X (1 (COS . 2))) or, more generally,
/// (arg (numfactor-of-arg (operator . exponent)))
fn sp1add(e : Value) -> Value raise {
  let mut e = e
  let n = if eq(caar(e), q_mexpt) {
    if num_eq(signum1(caddr(e)), Fix(-1L)) {
      let n = trgred__m_neg(caddr(e))
      e = cons(list1(zl_get(caaadr(e), q_recip)), cdadr(e))
      n
    } else {
      let n = caddr(e)
      e = cadr(e)
      n
    }
  } else {
    Fix(1L)
  }
  let arg = sp1kget(cadr(e))
  with_special(q_ear_laws, symval(q_ear_hyperlaws), () => {
    if memq(
        caar(e),
        list([q_p_sin, q_p_cos, q_p_tan, q_p_cot, q_p_sec, q_p_csc]),
      ).truthy() {
      let buc = assoc_equal(cdr(arg), symval(q_ear_trigbuckets))
      if buc.truthy() {
        set(q_ear_laws, symval(q_ear_triglaws)) |> ignore
        sp1addbuc(caar(e), car(arg), n, buc)
      } else {
        set(
          q_ear_trigbuckets,
          cons(
            list2(cdr(arg), list2(car(arg), cons(caar(e), n))),
            symval(q_ear_trigbuckets),
          ),
        )
      }
    } else {
      let buc = assoc_equal(cdr(arg), symval(q_ear_hyperbuckets))
      if buc.truthy() {
        sp1addbuc(caar(e), car(arg), n, buc)
      } else {
        set(
          q_ear_hyperbuckets,
          cons(
            list2(cdr(arg), list2(car(arg), cons(caar(e), n))),
            symval(q_ear_hyperbuckets),
          ),
        )
      }
    }
  })
}

///|
/// FUNCTION, ARGUMENT, EXPONENT, BUCKET LIST
fn sp1addbuc(f : Value, arg : Value, n : Value, b : Value) -> Value raise {
  if cdr(b).truthy() && alike1(arg, caadr(b)).truthy() {
    // GOES IN THIS BUCKET
    sp1putbuc(f, n, cadr(b))
  } else if cdr(b) is Nil || great(caadr(b), arg).truthy() {
    rplacd(b, cons(list2(arg, cons(f, n)), cdr(b)))
  } else {
    sp1addbuc(f, arg, n, cdr(b))
  }
}

///|
/// PUT IT IN THERE
fn sp1putbuc(f : Value, n : Value, n_starbuc : Value) -> Value raise {
  let mut n = n
  let mut buc = n_starbuc
  while cdr(buc).truthy() {
    if eq(f, caadr(buc)) {
      // SAME FUNCTION, SO BOOST EXPONENT
      return rplacd(cadr(buc), add2_star(n, cdadr(buc)))
    } else if eq(caadr(buc), zl_get(f, q_recip)) {
      // RECIPROCAL FUNCTIONS
      n = sub_star(cdadr(buc), n)
      return if trgred__signp_e(n) {
        rplacd(buc, cddr(buc))
      } else if num_eq(signum1(n), Fix(-1L)) {
        rplaca(cadr(buc), f) |> ignore
        rplacd(cadr(buc), neg(n))
      } else {
        rplacd(cadr(buc), n)
      }
    } else {
      let nf = zl_get(zl_get(symval(q_ear_laws), caadr(buc)), f)
      if nf is Nil {
        // NO SIMPLIFICATIONS HERE
        ()
      } else if equal(n, cdadr(buc)) {
        // EXPONENTS MATCH
        rplacd(buc, cddr(buc)) |> ignore
        // TO MAKE SURE IT DOESN'T OCCUR TWICE
        return sp1putbuc1(nf, n, n_starbuc)
      } else {
        let m = sp1great(n, cdadr(buc))
        if eq(m, q_nomatch) {
          ()
        } else if m.truthy() {
          let m = cdadr(buc)
          rplacd(buc, cddr(buc)) |> ignore
          sp1putbuc1(nf, m, n_starbuc) |> ignore
          sp1putbuc1(f, sub_star(n, m), n_starbuc) |> ignore
          return t
        } else {
          rplacd(cadr(buc), sub_star(cdadr(buc), n)) |> ignore
          return sp1putbuc1(nf, n, n_starbuc)
        }
      }
    }
    buc = cdr(buc)
  }
  rplacd(buc, list1(cons(f, n)))
}

///|
fn sp1putbuc1(f : Value, n : Value, buc : Value) -> Value raise {
  if cdr(buc) is Nil {
    rplacd(buc, list1(cons(f, n)))
  } else if eq(f, caadr(buc)) {
    rplacd(cadr(buc), add2_star(n, cdadr(buc)))
  } else {
    sp1putbuc1(f, n, cdr(buc))
  }
}

///|
fn sp1great(x : Value, y : Value) -> Value raise {
  if mnump(x).truthy() {
    if mnump(y).truthy() {
      great(x, y)
    } else {
      q_nomatch
    }
  } else if atom(x) || atom(y) {
    q_nomatch
  } else if eq(caar(x), caar(y)) {
    let mut a : Value = Nil
    let mut b : Value = Nil
    let xs = if mnump(cadr(x)).truthy() {
      a = cadr(x)
      cddr(x)
    } else {
      a = Fix(1L)
      cdr(x)
    }
    let ys = if mnump(cadr(y)).truthy() {
      b = cadr(y)
      cddr(y)
    } else {
      b = Fix(1L)
      cdr(y)
    }
    if alike(xs, ys).truthy() {
      great(a, b)
    } else {
      q_nomatch
    }
  } else {
    q_nomatch
  }
}

///|
fn sp1untrep(b : Value) -> Value raise {
  mapcan(
    buc => mapcar(
      term => {
        let bas = simplifya(
          list2(list1(car(term)), mul2_star(car(b), car(buc))),
          t,
        )
        if equal(cdr(term), Fix(1L)) {
          bas
        } else {
          power_star(bas, cdr(term))
        }
      },
      cdr(buc),
    ),
    cdr(b),
  )
}

///|
/// FINDS NUMERIC COEFFICIENTS
fn sp1kget(e : Value) -> Value raise {
  if mtimesp(e).truthy() && numberp(cadr(e)) {
    let v = cons(cadr(e), trgred__m_times_l(cddr(e)))
    if v.truthy() {
      return v
    }
  }
  cons(Fix(1L), e)
}

///|
fn sp1sincos(l : Value, trig : Value) -> Value raise {
  mapcar(q => sp1sincos2(mul2_star(car(l), car(q)), q, trig), cdr(l))
}

///|
fn sp1sincos2(arg : Value, l : Value, trig : Value) -> Value raise {
  if cdr(l) is Nil {
    t
  } else {
    let a = memq(
      caadr(l),
      if trig is Nil {
        list([q_p_sinh, q_p_cosh, q_p_sinh, q_p_csch, q_p_sech, q_p_csch])
      } else {
        list([q_p_sin, q_p_cos, q_p_sin, q_p_csc, q_p_sec, q_p_csc])
      },
    )
    // THERE MUST BE SOMETHING TO MATCH TO.
    if a.truthy() && cddr(l).truthy() {
      sp1sincos1(cadr(a), l, arg, trig)
    } else {
      sp1sincos2(arg, cdr(l), trig)
    }
  }
}

///|
fn trgred__push_lin(x : Value) -> Unit {
  set(q_n_starlin, cons(x, symval(q_n_starlin))) |> ignore
}

///|
fn sp1sincos1(s : Value, l : Value, arg : Value, trig : Value) -> Value raise {
  let mut s = s
  let mut arg = arg
  let mut e : Value = Fix(1L)
  let mut ll = cdr(l)
  while cdr(ll).truthy() {
    if eq(s, caadr(ll)) {
      arg = mul2_star(Fix(2L), arg)
      if trig.truthy() {
        if memq(s, list2(q_p_sin, q_p_cos)).truthy() {
          s = q_p_sin
        } else {
          s = q_p_csc
          e = Fix(-1L)
        }
      } else if memq(s, list2(q_p_sinh, q_p_cosh)).truthy() {
        s = q_p_sinh
      } else {
        s = q_p_csch
        e = Fix(-1L)
      }
      if alike1(cdadr(ll), cdadr(l)).truthy() {
        sp1addto(s, arg, cdadr(l)) |> ignore
        trgred__push_lin(mul2_star(e, cdadr(l)))
        rplacd(ll, cddr(ll)) |> ignore // MUST BE IN THIS ORDER!!
        rplacd(l, cddr(l)) |> ignore
        return t
      }
      let g = sp1great(cdadr(l), cdadr(ll))
      if eq(g, q_nomatch) {
        ()
      } else if g is Nil {
        rplacd(cadr(ll), sub_star(cdadr(ll), cdadr(l))) |> ignore
        sp1addto(s, arg, cdadr(l)) |> ignore
        trgred__push_lin(mul2_star(e, cdadr(l)))
        rplacd(l, cddr(l)) |> ignore
        return t
      } else {
        rplacd(cadr(l), sub_star(cdadr(l), cdadr(ll))) |> ignore
        sp1addto(s, arg, cdadr(ll)) |> ignore
        trgred__push_lin(mul2_star(e, cdadr(ll)))
        rplacd(ll, cddr(ll)) |> ignore
        return t
      }
    }
    ll = cdr(ll)
  }
  t
}

///|
fn sp1addto(fn_ : Value, arg : Value, exp_ : Value) -> Value raise {
  let arg = list2(list1(fn_), arg)
  // leave the power unsimplified, like FN(ARG): SP1UNTREP simplifies it
  // later, while simplified now it could be something SP1ADD cannot put in
  // a bucket, such as 1/2 for sin(%pi/4)^2
  sp1add(
    if equal(exp_, Fix(1L)) {
      arg
    } else {
      list3(list1(q_mexpt), arg, exp_)
    },
  )
}

///|
fn sp1expt(b : Value, e : Value) -> Value raise {
  let var_ = symval(q_var)
  if mexptp(b).truthy() {
    power(sp1(b), sp1(e))
  } else if !trigfp(b).truthy() && free(e, var_).truthy() {
    power_star(b, e)
  } else if equal(b, q_d__pcte) {
    sp1expt2(e)
  } else if !eq(var_, q_n_starnovar) && free(b, var_).truthy() {
    sp1expt2(mul2_star(list2(list1(q_p_log), b), e))
  } else if consp(b) && consp(car(b)) && memq(caar(b), trgred__trig12()).truthy() {
    if num_eq(signum1(e), Fix(-1L)) {
      sp1expt(list2(list1(zl_get(caar(b), q_recip)), cadr(b)), neg(e))
    } else if numberp(e) &&
      plusp(e) &&
      memq(caar(b), list([q_p_sin, q_p_cos, q_p_sinh, q_p_cosh])).truthy() {
      funcall(cdr(assq(caar(b), symval(q_ear_sc_hatndisp))), [e, cadr(b)])
    } else {
      power_star(b, e)
    }
  } else {
    power_star(b, e)
  }
}

///|
fn sp1expt2(e : Value) -> Value raise {
  with_special(q_ear_schatc_ans, m2(e, trgred__expt2_pattern), () => {
    let ans = symval(q_ear_schatc_ans)
    let fr = cdr(assq(q_fr, ans))
    let exp_ = cdr(assq(q_exp, ans))
    if equal(fr, Fix(0L)) {
      power_star(q_d__pcte, exp_)
    } else {
      mul2_star(power_star(q_d__pcte, fr), power_star(q_d__pcte, exp_))
    }
  })
}

///|
/// Split TERMS into (VALUES NON-NEG OTHER) where NON-NEG and OTHER are a
/// partition of the elements of TERMS. Expressions that are known not to be
/// negative are placed in NON-NEG and all others end up in OTHER.
fn non_negative_split(terms : Value) -> (Value, Value) raise {
  let mut non_neg : Value = Nil
  let mut other : Value = Nil
  for term in terms.iter() {
    if memq(d_sign(term), list3(q_d_pos, q_d_pz, q_d_zero)).truthy() {
      non_neg = cons(term, non_neg)
    } else {
      other = cons(term, other)
    }
  }
  (non_neg, other)
}

///|
/// Try to expand a logarithm for use in a power series in VAR by splitting
/// up products.
fn sp1log(e : Value, no_recurse? : Value = Nil) -> Value raise {
  let var_ = symval(q_var)
  if symval(q_n_startrigred).truthy() || atom(e) || free(e, var_).truthy() {
    // If E is free of VAR, is an atom, or we're supposed to be reducing
    // rather than expanding, then just return E.
    list2(list1(q_p_log), e)
  } else if eq(caar(e), q_mplus) {
    // The logarithm of a sum doesn't simplify very nicely, but call $factor
    // to see if we can pull out one or more terms and then recurse.
    let exp_ = add2_star(Fix(-1L), e)
    with_specials([(q_n_stara, Nil), (q_n_starn, Nil)], () => if smono(
        exp_, var_,
      ).truthy() {
      list2(list1(q_p_log), e)
    } else if no_recurse is Nil {
      sp1log(d_factor(e), no_recurse=t)
    } else {
      sp1log2(e)
    })
  } else if eq(caar(e), q_mtimes) {
    // A product is much more promising: log(ab) => log(a)+log(b), pulling
    // out only the terms we know to be non-negative.
    let (non_neg, other) = non_negative_split(cdr(e))
    if non_neg is Nil {
      sp1log2(e)
    } else {
      sp1(trgred__m_plus_l(mapcar(x => sp1log(x), append(other, non_neg))))
    }
  } else if eq(caar(e), q_mexpt) {
    // Similarly, transform log(a^b) => b log(a) and pass back to SP1.
    sp1(mul2_star(caddr(e), list2(list1(q_p_log), cadr(e))))
  } else {
    // If we can't find any other expansions, pass the result to SP1LOG2,
    // which tries again after expressing E as integrate(diff(e)/e).
    sp1log2(e)
  }
}

///|
/// We didn't manage to expand the expression, so make use of the fact that
/// diff(log(f(x)), x) = f'(x)/f(x):
///   log(f(x0+h)) = integrate(diff(f(x0+k))/f(x0+k), k, 0, h) + log(f(x0))
/// The "x0" about which we expand is always zero.
fn sp1log2(e : Value) -> Value raise {
  let var_ = symval(q_var)
  if symval(q_d_verbose).truthy() {
    mtell(list1(Str("trigreduce: failed to expand.~%~%"))) |> ignore
    show_exp(list2(list1(q_p_log), e)) |> ignore
    mtell(
      list2(
        Str("trigreduce: try again after applying rule:~2%~M~%~%"),
        list3(
          list1(q_mlabel),
          Nil,
          out_of(
            mk(q_mequal, [
              mk(q_p_log, [e]),
              mk(q_p_integrate, [
                mk(q_mquotient, [mk(q_p_derivative, [e, var_, Fix(1L)]), e]),
                var_,
              ]),
            ]),
          ),
        ),
      ),
    )
    |> ignore
  }
  let dummy_sym = d_gensym()
  add2_star(
    list2(list1(q_p_log), d_limit(list3(e, var_, Fix(0L)))),
    list([
      list1(q_p_integrate),
      maxima_substitute(dummy_sym, var_, sp1(div_star(sdiff(e, var_), e))),
      dummy_sym,
      Fix(0L),
      var_,
    ]),
  )
}

///|
fn sp1trig(e : Value) -> Value raise {
  if atom(cadr(e)) {
    simplify(e)
  } else if eq(caaadr(e), zl_get(caar(e), q_d_inverse)) {
    sp1(cadadr(e))
  } else if eq(caaadr(e), zl_get(zl_get(caar(e), q_recip), q_d_inverse)) {
    sp1(inv_star(cadadr(e)))
  } else if symval(q_n_startrigred) is Nil &&
    symval(q_n_starnoexpand) is Nil &&
    eq(caaadr(e), q_mplus) {
    sp1trigex(e)
  } else {
    e
  }
}

///|
/// Return the expansion of ((trigfun) ((mplus) a b)). For example
/// sin(a+b) = sin(a)cos(b) + cos(a)sin(b).
fn expand_trig_of_sum(trigfun : Value, a : Value, b : Value) -> Value raise {
  fn expand_it(
    plus : Bool,
    f1 : Value,
    f2 : Value,
    f3 : Value,
    f4 : Value,
  ) -> Value raise {
    let x = mul2_star(sp1trig(list2(list1(f1), a)), sp1trig(list2(list1(f2), b)))
    let y = mul2_star(sp1trig(list2(list1(f3), a)), sp1trig(list2(list1(f4), b)))
    if plus {
      add2_star(x, y)
    } else {
      sub_star(x, y)
    }
  }

  if eq(trigfun, q_p_sin) {
    expand_it(true, q_p_sin, q_p_cos, q_p_cos, q_p_sin)
  } else if eq(trigfun, q_p_cos) {
    expand_it(false, q_p_cos, q_p_cos, q_p_sin, q_p_sin)
  } else if eq(trigfun, q_p_sinh) {
    expand_it(true, q_p_sinh, q_p_cosh, q_p_cosh, q_p_sinh)
  } else if eq(trigfun, q_p_cosh) {
    expand_it(false, q_p_cosh, q_p_cosh, q_p_sinh, q_p_sinh)
  } else {
    raise LispError::SimpleError(
      "ECASE: " + prin1_to_string(trigfun) +
      " fell through ECASE expression; wanted one of (%SIN %COS %SINH %COSH)",
    )
  }
}

///|
/// Try to expand f(a+b) where f is sin, cos, sinh or cosh.
fn sp1trigex(e : Value) -> Value raise {
  // Ideally, we'd like to split the argument of the trig function into
  // terms that involve VAR and those that are free of it.
  let w = m2(cadr(e), trgred__trigex_pattern)
  if w.truthy() && cdras(q_a, w).truthy() && cdras(q_b, w).truthy() {
    let mut a = cdr(assq(q_a, w))
    let mut b = cdr(assq(q_b, w))
    // Make sure that if B is zero then so is A (to simplify the cond)
    if trgred__signp_e(b) {
      let tmp = a
      a = b
      b = tmp
    }
    // If A is zero (because the argument of trig function is a sum of terms,
    // all of which involve VAR), then fall back on a different splitting, by
    // terms of taking the first term of B.
    if trgred__signp_e(a) && !atom(b) && eq(caar(b), q_mplus) {
      expand_trig_of_sum(
        caar(e),
        cadr(b),
        if cdddr(b).truthy() {
          cons(car(b), cddr(b))
        } else {
          caddr(b)
        },
      )
    } else if trgred__signp_e(a) {
      // For some weird reason, B isn't a sum. Give up.
      e
    } else {
      // Do the splitting we intended in the first place.
      expand_trig_of_sum(caar(e), a, b)
    }
  } else {
    // E doesn't match f(a+b). Return it unmodified.
    e
  }
}

///|
fn sp1atrig(fn_ : Value, exp_ : Value) -> Value raise {
  if atom(exp_) {
    sp1atrig2(fn_, exp_)
  } else if eq(fn_, zl_get(caar(exp_), q_d_inverse)) {
    // Punt to general simplifier, which has fairly extensive and more
    // careful treatment of trig inverses. Start over with SP1 only if it
    // looks like the simplifier was able to do something.
    let fn_exp = list2(list1(fn_), exp_)
    let fn_exp_1 = resimplify(fn_exp)
    if alike1(fn_exp_1, fn_exp).truthy() {
      fn_exp
    } else {
      sp1(fn_exp_1)
    }
  } else {
    sp1atrig2(fn_, exp_)
  }
}

///|
fn sp1atrig2(fn_ : Value, exp_ : Value) -> Value raise {
  let mut fn_ = fn_
  let mut exp_ = exp_
  if memq(
      fn_,
      list([q_p_cot, q_p_sec, q_p_csc, q_p_coth, q_p_sech, q_p_csch]),
    ).truthy() {
    exp_ = sp1(inv_star(exp_))
    fn_ = cdr(
      assq(
        fn_,
        list([
          cons(q_p_acot, q_p_atan),
          cons(q_p_asec, q_p_acos),
          cons(q_p_acsc, q_p_asin),
          cons(q_p_acoth, q_p_atanh),
          cons(q_p_asech, q_p_acosh),
          cons(q_p_acsch, q_p_asinh),
        ]),
      ),
    )
  }
  if symval(q_n_startrigred) is Nil &&
    memq(fn_, list2(q_p_acos, q_p_acosh)).truthy() {
    add2_star(
      symval(q_half_pctpi),
      list2(
        list1(
          cdr(
            assq(
              fn_,
              list2(cons(q_p_acos, q_p_asin), cons(q_p_acosh, q_p_asinh)),
            ),
          ),
        ),
        exp_,
      ),
    )
  } else {
    list2(list1(fn_), exp_)
  }
}

///|
fn sin_hatn(p_n : Value, v : Value) -> Value raise {
  sc_hatn(
    p_n,
    v,
    if oddp(p_n) {
      list1(q_p_sin)
    } else {
      list1(q_p_cos)
    },
    lbool(!oddp(p_n)),
    power_star(Fix(-1L), add2_star(ash(p_n, -1), q_k)),
  )
}

///|
fn sinh_hatn(p_n : Value, v : Value) -> Value raise {
  if oddp(p_n) {
    sc_hatn(p_n, v, list1(q_p_sinh), Nil, power_star(Fix(-1L), q_k))
  } else if zerop(num_mod(p_n, Fix(4L))) {
    sc_hatn(p_n, v, list1(q_p_cosh), t, power_star(Fix(-1L), q_k))
  } else {
    trgred__m_neg(
      sc_hatn(
        p_n,
        v,
        list1(q_p_cosh),
        t,
        trgred__m_neg(power_star(Fix(-1L), q_k)),
      ),
    )
  }
}

///|
fn cos_hatn(p_n : Value, v : Value) -> Value raise {
  sc_hatn(p_n, v, list1(q_p_cos), lbool(!oddp(p_n)), Fix(1L))
}

///|
fn cosh_hatn(p_n : Value, v : Value) -> Value raise {
  sc_hatn(p_n, v, list1(q_p_cosh), lbool(!oddp(p_n)), Fix(1L))
}

///|
fn sc_hatn(
  p_n : Value,
  v : Value,
  fn_ : Value,
  fl : Value,
  coef : Value,
) -> Value raise {
  if minusp(p_n) {
    merr("trigreduce: internal error; %N must be nonnegative, found: ~M", [p_n])
    |> ignore
  }
  mul2_star(
    mk(q_rat, [Fix(1L), expt(Fix(2L), p_n)]),
    add2_star(
      if fl.truthy() {
        mk(q_p_binomial, [p_n, ash(p_n, -1)])
      } else {
        Fix(0L)
      },
      maxima_substitute(
        v,
        q_trig_var,
        dosum(
          addn(
            list1(muln_star([
              Fix(2L),
              mk(q_p_binomial, [p_n, q_k]),
              coef,
              list2(
                fn_,
                mul2_star(q_trig_var, add2_star(p_n, mul2_star(Fix(-2L), q_k))),
              ),
            ])),
            Nil,
          ),
          q_k,
          Fix(0L),
          ash(one_minus(p_n), -1),
          t,
        ),
      ),
    ),
  )
}

///|
fn init_trgred() -> Unit raise {
  defvar_init(
    q_ear_trans_list_plus,
    lread(
      #|((((mplus) ((coeffpt) (c true) ((mexpt) ((%tan) (var* (uvar) x true)) 2))
      #|   (var* (uvar) c))
      #|  ((mtimes) c ((mexpt) ((%sec) x) 2)))
      #| (((mplus) ((coeffpt) (c true) ((mexpt) ((%cot) (var* (uvar) x true)) 2))
      #|   (var* (uvar) c))
      #|  ((mtimes) c ((mexpt) ((%csc) x) 2)))
      #| (((mplus) ((coeffpt) (c true) ((mexpt) ((%tanh) (var* (uvar) x true)) 2))
      #|   ((mtimes) -1 (var* (uvar) c)))
      #|  ((mtimes) -1 c ((mexpt) ((%sech) x) 2)))
      #| (((mplus) ((coeffpt) (c true) ((mexpt) ((%coth) (var* (uvar) x true)) 2))
      #|   ((mtimes) -1 (var* (uvar) c)))
      #|  ((mtimes) c ((mexpt) ((%csch) x) 2))))
      ,
    ),
  )
  defvar_init(
    q_ear_triglaws,
    lread(
      #|(* %sin (* %cot %cos %sec %tan) %cos (* %tan %sin %csc %cot)
      #|   %tan (* %cos %sin %csc %sec) %cot (* %sin %cos %sec %csc)
      #|   %sec (* %sin %tan %cot %csc) %csc (* %cos %cot %tan %sec))
      ,
    ),
  )
  defvar_init(
    q_ear_hyperlaws,
    lread(
      #|(* %sinh (* %coth %cosh %sech %tanh) %cosh (* %tanh %sinh %csch %coth)
      #|   %tanh (* %cosh %sinh %csch %sech) %coth (* %sinh %cosh %sech %csch)
      #|   %sech (* %sinh %tanh %coth %csch) %csch (* %cosh %coth %tanh %sech))
      ,
    ),
  )
  defvar_init(
    q_ear_sc_hatndisp,
    list([
      cons(q_p_sin, q_sin_hatn),
      cons(q_p_cos, q_cos_hatn),
      cons(q_p_sinh, q_sinh_hatn),
      cons(q_p_cosh, q_cosh_hatn),
    ]),
  )
  // (defmfun ($trigreduce :properties ((evfun t))) ...)
  putprop(q_d_trigreduce, t, q_evfun) |> ignore
}
