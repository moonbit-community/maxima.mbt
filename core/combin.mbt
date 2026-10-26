// Port of src/combin.lisp (part 1): minfactorial and factcomb, Euler and
// Bernoulli numbers, zeta, Fibonacci and Lucas numbers.

///|
fn combin__nums(xs : Array[Int]) -> Value {
  list(xs.map(x => int(x)))
}

// ---------------------------------------------------------------------------
// minfactorial and factcomb stuff

///|
fn d_makefact(e : Value) -> Value raise {
  with_special(q_makef, t, () => if atom(e) {
    e
  } else {
    simplify(makefact1(e))
  })
}

///|
fn makefact1(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_p_binomial) {
    let x = makefact1(cadr(e))
    let y = makefact1(caddr(e))
    subst(
      x,
      q_x,
      subst(
        y,
        q_y,
        lread(
          "((mtimes) ((mfactorial) x) ((mexpt) ((mfactorial) y) -1) ((mexpt) ((mfactorial) ((mplus) x ((mtimes) -1 y))) -1))",
        ),
      ),
    )
  } else if eq(caar(e), q_p_gamma) {
    list2(list1(q_mfactorial), list3(list1(q_mplus), int(-1), makefact1(cadr(e))))
  } else if eq(caar(e), q_p_beta) {
    makefact1(
      subst(
        cadr(e),
        q_x,
        subst(
          caddr(e),
          q_y,
          lread(
            "((mtimes) ((%gamma) x) ((%gamma) y) ((mexpt) ((%gamma) ((mplus) x y)) -1))",
          ),
        ),
      ),
    )
  } else {
    recur_apply(q_makefact1, e)
  }
}

///|
fn d_makegamma(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    simplify(makegamma1(d_makefact(e)))
  }
}

///|
struct CombinMinfact {
  mut mfactl : Value
  mut factlist : Value
}

///|
fn combin__member_equal4(x : Value) -> Bool {
  eq(x, q_p_sum) || eq(x, q_p_derivative) || eq(x, q_p_integrate) || eq(x, q_p_product)
}

///|
fn combin__evfact(st : CombinMinfact, e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mfactorial) {
    // Replace factorial with simplified expression from *factlist.
    simplifya(cdr(assoc_equal(cadr(e), st.factlist)), Nil)
  } else if combin__member_equal4(caar(e)) {
    cons(list1(caar(e)), cons(combin__evfact(st, cadr(e)), cddr(e)))
  } else {
    recur_apply(lfunc("evfact", args => combin__evfact(st, arg(args, 0))), e)
  }
}

///|
fn combin__adfactl(st : CombinMinfact, e : Value, l : Value) -> Value raise {
  if l is Nil {
    st.mfactl = cons(list1(e), st.mfactl)
    st.mfactl
  } else {
    let n = d_ratsimp(mk(q_mplus, [e, mk(q_mtimes, [int(-1), caar(l)])]), Nil)
    if numberp(n) {
      if plusp(n) {
        rplacd(car(l), cons(e, cdar(l)))
      } else {
        rplaca(l, cons(e, car(l)))
      }
    } else {
      combin__adfactl(st, e, cdr(l))
    }
  }
}

///|
fn combin__getfact(st : CombinMinfact, e : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if eq(caar(e), q_mfactorial) {
    if member_equal(cadr(e), st.factlist) is Nil {
      st.factlist = cons(cadr(e), st.factlist)
      combin__adfactl(st, cadr(e), st.mfactl) |> ignore
      st.factlist
    } else {
      Nil
    }
  } else if combin__member_equal4(caar(e)) {
    combin__getfact(st, cadr(e))
  } else {
    mapc(x => combin__getfact(st, x) |> ignore, cdr(e))
  }
}

///|
fn combin__evfac1(st : CombinMinfact, e : Value) -> Value raise {
  let mut al = st.mfactl
  while member_equal(car(e), car(al)) is Nil {
    al = cdr(al)
  }
  rplaca(
    e,
    cons(
      car(e),
      list3(
        list1(q_mtimes),
        gfact(
          car(e),
          d_ratsimp(list3(list1(q_mplus), car(e), list3(list1(q_mtimes), int(-1), caar(al))), Nil),
          int(1),
        ),
        list2(list1(q_mfactorial), caar(al)),
      ),
    ),
  )
}

///|
fn d_minfactorial(e : Value) -> Value raise {
  let st = { mfactl: Nil, factlist: Nil }
  let mut e = e
  if specrepp(e).truthy() {
    e = specdisrep(e)
  }
  combin__getfact(st, e) |> ignore
  let mut l = st.factlist
  while !(l is Nil) {
    combin__evfac1(st, l) |> ignore
    l = cdr(l)
  }
  combin__evfact(st, e)
}

///|
fn d_factcomb(e : Value) -> Value raise {
  let ratrep = !atom(e) && eq(caar(e), q_mrat)
  with_specials([(q_varlist, symval(q_varlist)), (q_d_ratfac, Nil)], () => {
    let mut e = e
    if ratrep {
      e = ratdisrep(e)
    }
    e = factcomb(e)
    e = if atom(e) {
      e
    } else {
      simplify(cons(list1(caar(e)), mapcar(x => factcomb1(x), cdr(e))))
    }
    if !symval(q_d_sumsplitfact).truthy() {
      e = d_minfactorial(e)
    }
    if ratrep {
      ratf(e)
    } else {
      e
    }
  })
}

///|
fn factcomb1(e : Value) -> Value raise {
  if free(e, q_mfactorial).truthy() {
    e
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) || eq(caar(e), q_mexpt) {
    cons(list1(caar(e)), mapcar(x => factcomb1(x), cdr(e)))
  } else {
    let e = factcomb(e)
    if atom(e) {
      e
    } else {
      cons(list1(caar(e)), mapcar(x => factcomb1(x), cdr(e)))
    }
  }
}

///|
fn factcomb(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if free(e, q_mfactorial).truthy() {
    e
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    factpluscomb(factcombplus(e))
  } else if eq(caar(e), q_mexpt) {
    simpexpt(mk(q_mexpt, [factcomb(cadr(e)), factcomb(caddr(e))]), int(1), Nil)
  } else if eq(caar(e), q_mrat) {
    factrat(e)
  } else {
    cons(car(e), mapcar(x => factcomb(x), cdr(e)))
  }
}

///|
fn factrat(e : Value) -> Value raise {
  with_specials([(q_nn_star, Nil), (q_dn_star, Nil)], () => {
    let e = factqsnt(
      d_ratdisrep(cons(car(e), cons(cadr(e), int(1)))),
      d_ratdisrep(cons(car(e), cons(cddr(e), int(1)))),
    )
    numden(e) |> ignore
    div_star(
      factpluscomb(symval(q_nn_star)),
      factpluscomb(symval(q_dn_star)),
    )
  })
}

///|
fn factqsnt(num : Value, den : Value) -> Value raise {
  if equal(num, int(0)) {
    int(0)
  } else {
    with_specials([(q_nn_star, Nil), (q_dn_star, Nil)], () => {
      let e = factpluscomb(div_star(den, num))
      numden(e) |> ignore
      factpluscomb(div_star(symval(q_dn_star), symval(q_nn_star)))
    })
  }
}

///|
fn factcombplus(e : Value) -> Value raise {
  with_specials([(q_nn_star, Nil), (q_dn_star, Nil)], () => {
    let mut l1 = nplus(e)
    let mut l2 : Value = Nil
    while !(l1 is Nil) {
      numden(car(l1)) |> ignore
      for l4 in list_to_array(l2) {
        if !free(d_gcd(symval(q_dn_star), cdr(l4), Nil), q_mfactorial).truthy() {
          numden(
            list3(
              list1(q_mplus),
              div_star(symval(q_nn_star), symval(q_dn_star)),
              div_star(car(l4), cdr(l4)),
            ),
          )
          |> ignore
          l2 = combin__delete_first_eq(l4, l2)
        }
      }
      l2 = nconc(l2, list1(cons(symval(q_nn_star), symval(q_dn_star))))
      l1 = cdr(l1)
    }
    simplus(
      cons(list1(q_mplus), mapcar(q => factqsnt(car(q), cdr(q)), l2)),
      int(1),
      Nil,
    )
  })
}

///|
/// `(delete x l :count 1 :test #'eq)`
fn combin__delete_first_eq(x : Value, l : Value) -> Value {
  if l is Nil {
    Nil
  } else if eq(car(l), x) {
    cdr(l)
  } else {
    let mut p = l
    while !(cdr(p) is Nil) {
      if eq(cadr(p), x) {
        rplacd(p, cddr(p)) |> ignore
        break
      }
      p = cdr(p)
    }
    l
  }
}

///|
/// The closure variable DONEL shared by GETFACTORIAL, FACTPLUS1 and
/// FACTPLUSCOMB.
let combin__donel : Ref[Value] = { val: Nil }

///|
fn getfactorial(e : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    let mut l = cdr(e)
    while !(l is Nil) {
      let a = getfactorial(car(l))
      if a.truthy() {
        return a
      }
      l = cdr(l)
    }
    Nil
  } else if eq(caar(e), q_mexpt) {
    getfactorial(cadr(e))
  } else if eq(caar(e), q_mfactorial) {
    if memalike(cadr(e), combin__donel.val) is Nil {
      combin__donel.val = cons(cadr(e), combin__donel.val)
      list2(list1(q_mfactorial), car(combin__donel.val))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn factplus1(exp_ : Value, e : Value, fact : Value) -> Value raise {
  let mut l = exp_
  let mut i = 2
  let mut fpn = list3(list1(q_mplus), fact, int(1))
  while !(l is Nil) {
    let div = dypheyed(car(l), list3(list1(q_mexpt), fpn, e))
    if (symval(q_d_sumsplitfact).truthy() || equal(cadr(div), int(0))) &&
      !equal(car(div), int(0)) {
      rplaca(l, cadr(div)) |> ignore
      let nv = if cadr(l).truthy() {
        simplus(list3(list1(q_mplus), car(div), cadr(l)), int(1), Nil)
      } else {
        combin__donel.val = cons(simplus(fpn, int(1), Nil), combin__donel.val)
        car(div)
      }
      rplacd(l, cons(nv, cddr(l))) |> ignore
    }
    l = cdr(l)
    fpn = list3(list1(q_mplus), fact, int(i))
    i += 1
  }
  exp_
}

///|
fn factpluscomb(e : Value) -> Value raise {
  let mut e = e
  combin__donel.val = Nil
  while true {
    e = factexpand(e)
    let fact = getfactorial(e)
    if !fact.truthy() {
      return e
    }
    let indl = mapcar(q => factplusdep(q, fact), nplus(e))
    let tt = factpowerselect(indl, nplus(e), fact)
    e = if cdr(tt).truthy() {
      cons(list1(q_mplus), mapcar(q => factplus2(q, fact), tt))
    } else {
      factplus2(car(tt), fact)
    }
  }
  e
}

///|
fn nplus(e : Value) -> Value raise {
  if eq(caar(e), q_mplus) {
    cdr(e)
  } else {
    list1(e)
  }
}

///|
fn factexpand(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) {
    simplus(cons(list1(q_mplus), mapcar(x => factexpand(x), cdr(e))), int(1), Nil)
  } else if free(e, q_mfactorial).truthy() {
    e
  } else {
    d_expand(e)
  }
}

///|
fn factplusdep(e : Value, fact : Value) -> Value raise {
  if alike1(e, fact).truthy() {
    int(1)
  } else if atom(e) {
    Nil
  } else if eq(caar(e), q_mtimes) {
    let mut l = cdr(e)
    while !(l is Nil) {
      let out = factplusdep(car(l), fact)
      if out.truthy() {
        return out
      }
      l = cdr(l)
    }
    Nil
  } else if eq(caar(e), q_mexpt) {
    let fto = factplusdep(cadr(e), fact)
    if fto.truthy() {
      simptimes(list3(list1(q_mtimes), fto, caddr(e)), int(1), t)
    } else {
      Nil
    }
  } else if eq(caar(e), q_mplus) {
    same(mapcar(q => factplusdep(q, fact), cdr(e)))
  } else {
    Nil
  }
}

///|
fn same(l : Value) -> Value raise {
  let ca = car(l)
  let mut cd = cdr(l)
  while !(cd is Nil) {
    if !alike1(ca, car(cd)).truthy() {
      return Nil
    }
    cd = cdr(cd)
  }
  ca
}

///|
fn factpowerselect(indl : Value, e : Value, fact : Value) -> Value raise {
  let mut l : Value = Nil
  let mut i = indl
  let mut j = e
  while !(i is Nil) {
    let mut expt = car(i)
    let exp_ = if expt.truthy() {
      let ex = d_divide(car(j), mk(q_mexpt, [fact, expt]), Nil)
      // (car j) need not involve fact^expt since fact^expt may be the gcd
      // of the num and denom of (car j) and $divide will cancel this out.
      if !equal(cadr(ex), int(0)) {
        cadr(ex)
      } else {
        expt = Nil
        caddr(ex)
      }
    } else {
      car(j)
    }
    if l is Nil {
      l = list1(list2(expt, exp_))
    } else {
      let fl = assolike(expt, l)
      if fl.truthy() {
        nconc(fl, list1(exp_)) |> ignore
      } else {
        nconc(l, list1(list2(expt, exp_))) |> ignore
      }
    }
    i = cdr(i)
    j = cdr(j)
  }
  l
}

///|
fn factplus2(l : Value, fact : Value) -> Value raise {
  let expt = car(l)
  if expt.truthy() {
    factplus0(
      if cddr(l).truthy() {
        rplaca(l, list1(q_mplus))
      } else {
        cadr(l)
      },
      expt,
      cadr(fact),
    )
  } else {
    rplaca(l, list1(q_mplus))
  }
}

///|
fn factplus0(r : Value, e : Value, fact : Value) -> Value raise {
  let mut r = r
  let mut i = -1
  let mut fpn = fact
  let mut j = -1
  let mut exp_ : Value = Nil
  while true {
    let rfpn = simpexpt(list3(list1(q_mexpt), fpn, int(-1)), int(1), Nil)
    let div = dypheyed(r, simpexpt(list3(list1(q_mexpt), rfpn, e), int(1), Nil))
    if !(symval(q_d_sumsplitfact).truthy() || equal(cadr(div), int(0))) ||
      equal(car(div), int(0)) {
      let terms = factplus1(cons(r, exp_), e, fpn)
      let fpn0 = fpn
      return simplus(
        cons(
          list1(q_mplus),
          mapcar(
            q => {
              j += 1
              list3(
                list1(q_mtimes),
                q,
                list3(
                  list1(q_mexpt),
                  list2(list1(q_mfactorial), list3(list1(q_mplus), fpn0, int(j))),
                  e,
                ),
              )
            },
            terms,
          ),
        ),
        int(1),
        Nil,
      )
    } else {
      r = car(div)
      exp_ = cons(cadr(div), exp_)
    }
    fpn = list3(list1(q_mplus), fact, int(i))
    i -= 1
  }
  Nil
}

///|
fn dypheyed(r : Value, f : Value) -> Value raise {
  newvar(r) |> ignore
  let r1 = ratf(f)
  let p1 = pdegreevector(cadr(r1))
  let p2 = pdegreevector(cddr(r1))
  let mut i = p1
  let mut j = p2
  let mut k = caddar(r1)
  while !(k is Nil) {
    if num_gt(car(i), car(j)) {
      return cdr(d_divide(r, f, list1(car(k))))
    }
    i = cdr(i)
    j = cdr(j)
    k = cdr(k)
  }
  kansel(r, cadr(r1), cddr(r1))
}

///|
fn kansel(r : Value, n : Value, d : Value) -> Value raise {
  let r1 = ratf(r)
  let p1 = testdivide(cadr(r1), n)
  let p2 = testdivide(cddr(r1), d)
  if p1.truthy() && p2.truthy() {
    cons(rdis(cons(p1, p2)), list1(int(0)))
  } else {
    cons(int(0), list1(r))
  }
}

// ---------------------------------------------------------------------------
// euler and bernoulli stuff

///|
fn nxtbincoef(m : Value, nom : Value, combin_a : Value) -> Value raise {
  num_truncate(num_mul(nom, num_sub(combin_a, m)), b=m).0
}

///|
fn euler(p_a_star : Value) -> Value raise {
  with_special(q_d_zerobern, q_p_op_dol_sl_hash_amp, () => {
    let a = p_a_star
    let mut nom = int(1)
    let mut k = a
    let mut fl = false
    let mut e = int(0)
    let combin_a = num_add(a, int(1))
    while true {
      if zerop(k) {
        e = num_neg(e)
        aset1(symval(q_ear_eu), to_int(ash(a, -1)) - 1, e) |> ignore
        putprop(q_ear_eu, ash(a, -1), q_lim) |> ignore
        return e
      }
      nom = nxtbincoef(num_add(num_sub(a, k), int(1)), nom, combin_a)
      k = num_sub(k, int(1))
      fl = !fl
      if fl {
        continue
      }
      e = num_add(e, num_mul(nom, ftake(q_p_euler, [k])))
    }
    e
  })
}

///|
fn simp__pcteuler(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_euler, [q_d_u]),
    )
    |> ignore
  }
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  if fixnump(u) && num_ge(u, int(0)) {
    combin__euler_fn(u)
  } else {
    eqtest(cons(list1(q_p_euler), list1(u)), form)
  }
}

///|
fn combin__euler_fn(s : Value) -> Value raise {
  let s = with_special(q_d_float, Nil, () => if !fixnump(s) ||
    num_lt(s, int(0)) {
    list2(list1(q_d_euler), s)
  } else if zerop(s) {
    int(1)
  } else {
    let n = s
    let zb = symval(q_d_zerobern)
    if zb.truthy() {
      let h = ash(n, -1)
      if oddp(n) {
        int(0)
      } else if !num_gt(h, get(q_ear_eu, q_lim)) {
        aref1(symval(q_ear_eu), to_int(h) - 1)
      } else if eq(zb, q_p_op_dol_sl_hash_amp) {
        euler(n)
      } else {
        set(
          q_ear_eu,
          adjust_array(symval(q_ear_eu), [to_int(h) + 1], initial=int(0)),
        )
        |> ignore
        euler(n)
      }
    } else if num_le(n, get(q_ear_eu, q_lim)) {
      aref1(symval(q_ear_eu), to_int(n) - 1)
    } else {
      set(
        q_ear_eu,
        adjust_array(symval(q_ear_eu), [to_int(n) + 1], initial=int(0)),
      )
      |> ignore
      euler(num_mul(int(2), n))
    }
  })
  simplify(s)
}

///|
fn bern(p_a_star : Value) -> Value raise {
  with_special(q_d_zerobern, q_d_op_sl_hash_amp, () => {
    let mut k = int(0)
    let l = num_sub(p_a_star, int(1))
    let mut a_star = num_add(p_a_star, int(1))
    let mut nom = int(1)
    let mut a = int(1)
    let mut b = int(1)
    let combin_a = num_add(a_star, int(1))
    while true {
      if num_eq(k, l) {
        let bb = n_starred(a, num_mul(num_mul(int(-1), b), a_star))
        a_star = num_sub(ash(a_star, -1), int(1))
        putprop(q_bern, a_star, q_lim) |> ignore
        aset1(symval(q_ear_bn), to_int(a_star), cadr(bb)) |> ignore
        aset1(symval(q_ear_bd), to_int(a_star), caddr(bb)) |> ignore
        return bb
      }
      k = num_add(k, int(1))
      nom = nxtbincoef(k, nom, combin_a)
      let bb = ftake(q_p_bern, [k])
      a = num_add(num_mul(num_mul(b, nom), num1(bb)), num_mul(a, denom1(bb)))
      b = num_mul(b, denom1(bb))
      a = n_starred(a, b)
      b = denom1(a)
      a = num1(a)
    }
    Nil
  })
}

///|
/// bern - the n'th Bernoulli number for integer u.
fn simp__pctbern(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(form, required_arg_count=int(1), pretty_name=mk(q_p_bern, [q_d_u]))
    |> ignore
  }
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  if fixnump(u) && !num_lt(u, int(0)) {
    combin__bern_fn(u)
  } else {
    eqtest(cons(list1(q_p_bern), list1(u)), form)
  }
}

///|
fn combin__bern_fn(s : Value) -> Value raise {
  let s = with_special(q_d_float, Nil, () => if !fixnump(s) ||
    num_lt(s, int(0)) {
    list2(list1(q_d_bern), s)
  } else if num_eq(s, int(0)) {
    int(1)
  } else if num_eq(s, int(1)) {
    mk(q_rat, [int(-1), int(2)])
  } else if num_eq(s, int(2)) {
    mk(q_rat, [int(1), int(6)])
  } else {
    let mut n = s
    let zb = symval(q_d_zerobern)
    if zb.truthy() {
      if oddp(n) {
        int(0)
      } else {
        n = num_sub(ash(n, -1), int(1))
        if !num_gt(n, get(q_bern, q_lim)) {
          list3(
            list1(q_rat),
            aref1(symval(q_ear_bn), to_int(n)),
            aref1(symval(q_ear_bd), to_int(n)),
          )
        } else if eq(zb, q_d_op_sl_hash_amp) {
          bern(num_mul(int(2), num_add(n, int(1))))
        } else {
          n = num_add(n, int(1))
          set(q_ear_bn, adjust_array(symval(q_ear_bn), [to_int(n)], initial=int(0)))
          |> ignore
          set(q_ear_bd, adjust_array(symval(q_ear_bd), [to_int(n)], initial=int(0)))
          |> ignore
          bern(num_mul(int(2), n))
        }
      }
    } else if !num_gt(n, get(q_bern, q_lim)) {
      list3(
        list1(q_rat),
        aref1(symval(q_ear_bn), to_int(n) - 2),
        aref1(symval(q_ear_bd), to_int(n) - 2),
      )
    } else {
      set(
        q_ear_bn,
        adjust_array(symval(q_ear_bn), [to_int(n) + 1], initial=int(0)),
      )
      |> ignore
      set(
        q_ear_bd,
        adjust_array(symval(q_ear_bd), [to_int(n) + 1], initial=int(0)),
      )
      |> ignore
      bern(num_mul(int(2), num_sub(n, int(1))))
    }
  })
  simplify(s)
}

///|
/// Bernoulli polynomials: B[n](x) = sum(b[k]*binomial(n,k)*x^(n-k), k, 0, n)
fn d_bernpoly(x : Value, s : Value) -> Value raise {
  with_special(q_d_zerobern, t, () => if !fixnump(s) {
    list3(list1(q_d_bernpoly), x, s)
  } else if num_gt(s, int(-1)) {
    let n = to_int(s)
    let mut sum = cons(
      if n == 0 && zerop1(x).truthy() {
        add2(int(1), x)
      } else {
        power(x, int(n))
      },
      Nil,
    )
    let mut k = 1
    while k <= n {
      sum = cons(
        mul3(
          binocomp(int(n), int(k)),
          ftake(q_p_bern, [int(k)]),
          if n == k && zerop1(x).truthy() {
            add2(int(1), x)
          } else {
            power(x, int(n - k))
          },
        ),
        sum,
      )
      k += 1
    }
    addn(sum, t)
  } else {
    list3(list1(q_d_bernpoly), x, s)
  })
}

///|
/// Euler polynomials.
fn d_eulerpoly(x : Value, s : Value) -> Value raise {
  with_special(q_d_zerobern, t, () => if !fixnump(s) {
    list3(list1(q_d_eulerpoly), x, s)
  } else if num_gt(s, int(-1)) {
    let n = to_int(s)
    let mut y = sub(x, div(int(1), int(2)))
    let mut sum = cons(
      if zerop1(y).truthy() && n == 0 {
        add2(int(1), y)
      } else {
        power(y, int(n))
      },
      Nil,
    )
    let mut k = 1
    while k <= n {
      let f1 = binocomp(int(n), int(k))
      let f2 = ftake(q_p_euler, [int(k)])
      let f3 = power(int(2), mul2(int(-1), int(k)))
      y = sub(x, div(int(1), int(2)))
      let f4 = if zerop1(y).truthy() && n == k {
        add2(int(1), y)
      } else {
        power(y, int(n - k))
      }
      sum = cons(muln_([f1, f2, f3, f4]), sum)
      k += 1
    }
    d_expand(addn(sum, t))
  } else {
    list3(list1(q_d_eulerpoly), x, s)
  })
}

// ---------------------------------------------------------------------------
// zeta

///|
fn simplim_pctzeta(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let arg_ = limit(cadr(expr), var_, val, q_think)
  let dir = limit(add2(cadr(expr), neg(arg_)), var_, val, q_think)
  if onep1(arg_).truthy() {
    if eq(dir, q_d_zeroa) {
      q_d_inf
    } else if eq(dir, q_d_zerob) {
      q_d_minf
    } else {
      q_d_infinity
    }
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list2(list1(q_p_zeta), arg_))
  }
}

///|
fn simp__pctzeta(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(form, required_arg_count=int(1), pretty_name=mk(q_p_zeta, [q_d_z]))
    |> ignore
  }
  let mut z = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = fn() -> Value raise {
    eqtest(cons(list1(q_p_zeta), list1(z)), form)
  }
  // Check for special values
  if eq(z, q_d_inf) {
    int(1)
  } else if alike1(z, lread("((mtimes) -1 $minf)")).truthy() {
    int(1)
  } else if zerop1(z).truthy() {
    if d_bfloatp(z).truthy() {
      d_bfloat(mk(q_rat, [int(-1), int(2)]))
    } else if floatp(z) {
      Flo(-0.5)
    } else {
      mk_simp(q_rat, [int(-1), int(2)])
    }
  } else if onep1(z).truthy() {
    simp_domain_error(list2(Str("zeta: zeta(~:M) is undefined."), z))
  } else if bigfloat_numerical_eval_p(list1(z)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() ||
    float_numerical_eval_p(list1(z)).truthy() ||
    complex_float_numerical_eval_p(list1(z)).truthy() {
    // Check for numerical evaluation
    funcall(q_to, [float_zeta(z)])
  } else if integerp(z) {
    // Check for transformations and argument simplifications
    if oddp(z) {
      if num_gt(z, int(1)) {
        give_up()
      } else {
        z = sub(int(1), z)
        mul2(int(-1), div(ftake(q_p_bern, [z]), z))
      }
    } else if minusp(z) {
      int(0)
    } else if !symval(q_d_zeta_pctpi).truthy() {
      give_up()
    } else {
      with_specials([(q_d_numer, Nil), (q_d_float, Nil)], () => mul2(
        power(q_d__pctpi, z),
        mul2(
          div(power(int(2), num_sub(z, int(1))), take(list1(q_mfactorial), [z])),
          take(list1(q_mabs), [ftake(q_p_bern, [z])]),
        ),
      ))
    }
  } else if mnegp(z).truthy() {
    // z is a negative number.  Use the relationship (A&S 23.2.6):
    //  zeta(s) = 2^s*%pi^(s-1)*sin(%pi/2*s)*gamma(1-s)*zeta(1-s)
    muln_([
      power(int(2), z),
      power(q_d__pctpi, sub(z, int(1))),
      ftake(q_p_sin, [div(mul2(q_d__pctpi, z), int(2))]),
      ftake(q_p_gamma, [sub(int(1), z)]),
      ftake(q_p_zeta, [sub(int(1), z)]),
    ])
  } else {
    give_up()
  }
}

///|
/// Call a generic function of the bigfloat package by name.
fn combin__bf(name : String, args : Array[Value]) -> Value raise {
  funcall(sym("bigfloat::" + name), args)
}

///|
fn combin__bf_add(args : Array[Value]) -> Value raise {
  bf_op_plus(list(args))
}

///|
fn combin__bf_mul(args : Array[Value]) -> Value raise {
  bf_op_star(list(args))
}

///|
fn combin__bf_sub(a : Value, b : Value) -> Value raise {
  bf_op_(a, list1(b))
}

///|
fn combin__bf_div(a : Value, b : Value) -> Value raise {
  bf_op_sl(a, list1(b))
}

///|
/// Numerical zeta, using the algorithm of Proposition 2 of
/// http://numbers.computation.free.fr/Constants/Miscellaneous/zetaevaluations.pdf
fn float_zeta(s : Value) -> Value raise {
  // If s is a rational (real or complex), convert to a float.
  let mut s = bf_to(s)
  match s {
    Fix(_) | Big(_) | Ratio(_, _) => s = lfloat(s)
    Cplx(re, im) if rationalp(re) && rationalp(im) =>
      s = make_complex(lfloat(re), lfloat(im))
    _ => ()
  }
  let sigma = combin__bf("realpart", [s])
  let tau = combin__bf("imagpart", [s])
  if combin__bf("<", [
      combin__bf("abs", [combin__bf_mul([s, s])]),
      combin__bf("epsilon", [s]),
    ]).truthy() {
    // abs(s)^2 < epsilon, use the expansion zeta(s) = -1/2-1/2*log(2*%pi)*s
    let half = make_ratio(@bigint.BigInt::from_int(-1), @bigint.BigInt::from_int(2))
    combin__bf_add([
      half,
      combin__bf_mul([
        half,
        bf_log(combin__bf_mul([int(2), combin__bf("%pi", [s])])),
        s,
      ]),
    ])
  } else if !combin__bf("plusp", [sigma]).truthy() {
    // Reflection formula:
    // zeta(s) = 2^s*%pi^(s-1)*sin(%pi*s/2)*gamma(1-s)*zeta(1-s)
    let n = combin__bf("floor", [sigma])
    // If s is a negative even integer, zeta(s) is zero.
    if combin__bf("zerop", [tau]).truthy() &&
      combin__bf("=", [n, sigma]).truthy() &&
      evenp(n) {
      return combin__bf("float", [Flo(0.0), sigma])
    }
    combin__bf_mul([
      combin__bf("expt", [int(2), s]),
      combin__bf("expt", [combin__bf("%pi", [s]), combin__bf_sub(s, int(1))]),
      combin__bf("sin", [
        combin__bf_mul([combin__bf_div(combin__bf("%pi", [s]), int(2)), s]),
      ]),
      bf_to(ftake(q_p_gamma, [funcall(q_to, [combin__bf_sub(int(1), s)])])),
      float_zeta(combin__bf_sub(int(1), s)),
    ])
  } else {
    // The general formula from above.
    let logh = combin__bf_sub(
      if combin__bf("zerop", [tau]).truthy() {
        int(0)
      } else {
        combin__bf_add([
          combin__bf_mul([Flo(1.6), combin__bf("abs", [tau])]),
          bf_log(bf_1_plus(combin__bf("abs", [combin__bf_div(tau, sigma)]))),
        ])
      },
      bf_log(
        combin__bf("abs", [
          combin__bf_sub(
            int(1),
            combin__bf("expt", [int(2), combin__bf_sub(int(1), s)]),
          ),
        ]),
      ),
    )
    let logeps = bf_log(combin__bf("epsilon", [s]))
    let n = num_max(
      combin__bf("ceiling", [
        combin__bf_div(combin__bf_sub(logh, logeps), bf_log(int(8))),
      ]),
      int(1),
    )
    let mut sum1 = int(0)
    let mut sum2 = int(0)
    // sum(binomial(n,j), j, k, n) = sum(binomial(n,j), j, n, k)
    let binsum = fn(k : Value, n : Value) -> Value raise {
      let mut sum = int(0)
      let mut term = int(1)
      let mut j = n
      while num_ge(j, k) {
        sum = num_add(sum, term)
        term = num_div(num_mul(term, j), num_add(num_add(n, int(1)), num_neg(j)))
        j = num_sub(j, int(1))
      }
      sum
    }
    // sum1 = sum((-1)^(k-1)/k^s,k,1,n)
    // sum2 = (-1)^n*sum((-1)^(m-1)*e(n,m)/(n+k)^s, k, 1, n)
    let mut k = int(1)
    while num_le(k, n) {
      let d = combin__bf("expt", [k, s])
      let sgn = expt(int(-1), num_sub(k, int(1)))
      sum1 = combin__bf_add([sum1, combin__bf_div(sgn, d)])
      sum2 = combin__bf_add([
        sum2,
        combin__bf_div(
          num_mul(sgn, binsum(k, n)),
          combin__bf("expt", [num_add(k, n), s]),
        ),
      ])
      k = num_add(k, int(1))
    }
    if oddp(n) {
      sum2 = bf_op_(sum2, Nil)
    }
    combin__bf_div(
      combin__bf_add([sum1, combin__bf_div(sum2, combin__bf("expt", [int(2), n]))]),
      combin__bf_sub(int(1), combin__bf("expt", [int(2), combin__bf_sub(int(1), s)])),
    )
  }
}

// ---------------------------------------------------------------------------
// Fibonacci and Lucas numbers

///|
/// Returns the N'th Fibonacci number.
fn d_fib(n : Value) -> Value raise {
  if fixnump(n) {
    ffib(n)
  } else {
    list2(list1(q_d_fib), n)
  }
}

///|
/// The closure variable PREVFIB of FFIB.
let combin__prevfib : Ref[Value] = { val: Nil }

///|
/// Main routine for computing the n'th Fibonacci number where n is an
/// integer.
fn ffib(p_n : Value) -> Value raise {
  let n = to_int64(p_n)
  if n == -1L {
    combin__prevfib.val = int(-1)
    int(1)
  } else if n == 0L {
    combin__prevfib.val = int(1)
    int(0)
  } else {
    // f2 = fib(n/2) or fib((n-1)/2)
    let mut f2 = ffib(int64((n & -2L) >> 1))
    let x = num_add(f2, combin__prevfib.val)
    let y = num_mul(combin__prevfib.val, combin__prevfib.val)
    let z = num_mul(f2, f2)
    f2 = num_sub(num_mul(x, x), y)
    combin__prevfib.val = num_add(y, z)
    if n % 2L != 0L {
      let old_prev = combin__prevfib.val
      combin__prevfib.val = f2
      f2 = num_add(f2, old_prev)
    }
    f2
  }
}

///|
/// Returns the N'th Lucas number.
fn d_lucas(n : Value) -> Value raise {
  if fixnump(n) {
    lucas(n)
  } else {
    list2(list1(q_d_lucas), n)
  }
}

///|
fn lucas(n : Value) -> Value raise {
  let mut w = int(2)
  let mut x = int(2)
  let mut y = int(1)
  let sign = signum(n)
  let n = num_abs(n)
  let mut i = integer_length(n) - 1
  while i >= 0 {
    let u = num_mul(x, x)
    let v = num_mul(y, y)
    if logbitp(i, n) {
      y = num_add(v, w)
      x = num_add(num_add(y, num_neg(u)), w)
      w = int(-2)
    } else {
      x = num_sub(u, w)
      y = num_add(num_add(v, w), num_neg(x))
      w = int(2)
    }
    i -= 1
  }
  if num_eq(int(1), sign) || !logbitp(0, n) {
    x
  } else {
    neg(x)
  }
}

///|
fn init_combin() -> Unit raise {
  let bn = [
    0, -1, 1, -1, 5, -691, 7, -3617, 43867, -174611, 854513, -236364091, 8553103,
  ]
  let bn_arr = make_array([17], initial=int(0))
  for i, v in bn {
    aset1(bn_arr, i, int(v)) |> ignore
  }
  aset1(bn_arr, 13, int64(-23749461029L)) |> ignore
  aset1(bn_arr, 14, int64(8615841276005L)) |> ignore
  aset1(bn_arr, 15, int64(-7709321041217L)) |> ignore
  aset1(bn_arr, 16, int64(2577687858367L)) |> ignore
  defvar_init(q_ear_bn, bn_arr)
  let bd = [
    0, 30, 42, 30, 66, 2730, 6, 510, 798, 330, 138, 2730, 6, 870, 14322, 510, 6,
  ]
  let bd_arr = make_array([17], initial=int(0))
  for i, v in bd {
    aset1(bd_arr, i, int(v)) |> ignore
  }
  defvar_init(q_ear_bd, bd_arr)
  let eu : Array[Int64] = [
    -1L, 5L, -61L, 1385L, -50521L, 2702765L, -199360981L, 19391512145L, -2404879675441L,
    370371188237525L, -69348874393137901L,
  ]
  let eu_arr = make_array([11], initial=int(0))
  for i, v in eu {
    aset1(eu_arr, i, int64(v)) |> ignore
  }
  defvar_init(q_ear_eu, eu_arr)
  putprop(q_ear_eu, int(11), q_lim) |> ignore
  putprop(q_bern, int(16), q_lim) |> ignore
  putprop(q_p_zeta, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_zeta, lread("(mlist $matrix mequal)"), q_distribute_over)
  |> ignore
  putprop(q_p_zeta, q_simplim_pctzeta, q_simplim_pctfunction) |> ignore
  init_combin_2()
}
