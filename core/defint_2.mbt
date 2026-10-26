// Port of src/defint.lisp (part 2): residue methods, ztoinf, mtoinf,
// sin/cos integrals.

///|
fn difapply(ivar : Value, n : Value, d : Value, s : Value, fn1 : Value) -> Value raise {
  let b0 = bind(q_d_noprincipal, Nil)
  defer unbind(b0)
  let mut d = d
  if eq(
      d_asksign(
        addn_star([deg_var(d, ivar), defint__mneg(s), defint__mneg(Fix(2L))]),
      ),
      q_d_neg,
    ) {
    return Nil
  }
  set(q_d_noprincipal, t) |> ignore
  if !mexptp(d).truthy() {
    return Nil
  }
  let r = caddr(d)
  if !numberp(r) {
    return Nil
  } else if equal(n, Fix(1L)) &&
    // There are no calls where fn1 is ever equal to 'mtorat.  Hence
    // this case is never true.  What is this testing for?
    eq(fn1, q_mtorat) &&
    equal(Fix(1L), deg_var(cadr(d), ivar)) {
    return Fix(0L)
  }
  d = cadr(d)
  let m = deg_var(d, ivar)
  let mut k = div_star(add2_star(s, Fix(2L)), m)
  if eq(ask_integer(div_star(add2_star(s, Fix(2L)), m), q_d_any), q_d_yes) {
    ()
  } else {
    k = add2_star(Fix(1L), k)
  }
  if eq(d_sign(add2_star(r, defint__mneg(k))), q_d_pos) {
    return diffhk(fn1, n, d, k, add2_star(r, defint__mneg(k)), ivar)
  }
  Nil
}

///|
fn diffhk(
  fn1 : Value,
  n : Value,
  d : Value,
  r : Value,
  m : Value,
  ivar : Value,
) -> Value raise {
  let b0 = bind(q_ear_dflag, Nil)
  defer unbind(b0)
  set(q_ear_dflag, t) |> ignore
  let d1 = funcall(fn1, [
    n,
    power_star(add2(q_ear_z, d), r),
    mul2_star(r, deg_var(d, ivar)),
  ])
  if d1.truthy() {
    difap1(d1, r, q_ear_z, m, Fix(0L))
  } else {
    Nil
  }
}

///|
fn principal() -> Value raise {
  if symval(q_d_noprincipal).truthy() {
    diverg()
  } else if !symval(q_ear_pcprntd).truthy() {
    format(t, "Principal Value~%", []) |> ignore
    set(q_ear_pcprntd, t)
  } else {
    Nil
  }
}

///|
/// e is of form poly(x)*exp(m*%i*x)
/// s is degree of denominator
/// adds e to *bptu* or *bptd* according to sign of m
fn rib(e : Value, s : Value, ivar : Value) -> Value raise {
  if mnump(e).truthy() || constant(e).truthy() {
    set(q_ear_bptu, cons(e, symval(q_ear_bptu)))
  } else {
    let e1 = rmconst1(e, ivar)
    let c = car(e1)
    let nn = cdr(e1)
    let nd = s
    let (e2, updn) = ptimes_pcte(nn, nd, ivar) catch {
      LispError::Throw(tg, v) if eq(tg, q_ptimes_pcte) => (car(v), cadr(v))
      err => raise err
    }
    if e2 is Nil {
      Nil
    } else {
      let e3 = mul2_star(c, e2)
      if updn.truthy() {
        set(q_ear_bptu, cons(e3, symval(q_ear_bptu)))
      } else {
        set(q_ear_bptd, cons(e3, symval(q_ear_bptd)))
      }
    }
  }
}

///|
/// Check term is of form poly(x)*exp(m*%i*x)
/// n is degree of denominator.
/// (A throw to PTIMES%E carries the list of its two values.)
fn ptimes_pcte(term : Value, n : Value, ivar : Value) -> (Value, Value) raise {
  let mut updn : Value = Nil
  if mexptp(term).truthy() &&
    eq(cadr(term), q_d__pcte) &&
    polyinx(caddr(term), ivar, Nil).truthy() &&
    eq(
      d_sign(add2_star(deg_var(d_realpart(caddr(term)), ivar), Fix(-1L))),
      q_d_neg,
    ) &&
    eq(
      d_sign(
        add2_star(
          deg_var(set(q_nn_star, d_imagpart(caddr(term))), ivar),
          Fix(-2L),
        ),
      ),
      q_d_neg,
    ) {
    // Set updn to T if the coefficient of IVAR in the polynomial is
    // known to be positive.  Otherwise set to NIL.
    updn = lbool(
      eq(d_asksign(ratdisrep(ratcoef(symval(q_nn_star), ivar))), q_d_pos),
    )
    return (term, updn)
  }
  if mtimesp(term).truthy() &&
    set(q_nn_star, polfactors(term, ivar)).truthy() &&
    (
      car(symval(q_nn_star)) is Nil ||
      eq(
        d_sign(
          add2_star(n, defint__mneg(deg_var(car(symval(q_nn_star)), ivar))),
        ),
        q_d_pos,
      )
    ) &&
    !alike1(cadr(symval(q_nn_star)), term).truthy() &&
    {
      // Call ptimes%e and make sure we update updn, but only want the
      // return value from it to determine we this AND clause is true.
      let (result, u) = ptimes_pcte(cadr(symval(q_nn_star)), n, ivar)
      updn = u
      result.truthy()
    } {
    return (term, updn)
  }
  throw_tag(q_ptimes_pcte, list2(Nil, updn)) |> ignore
  (Nil, updn)
}

///|
fn csemidown(n : Value, d : Value, ivar : Value) -> Value raise {
  // Not sure what to do about PRINCIPAL values here.
  let b0 = bind(q_ear_pcprntd, t)
  defer unbind(b0)
  princip(
    res_var(
      ivar,
      n,
      d,
      lfunc("lowerhalf", args => lowerhalf(arg(args, 0))),
      lfunc("csemidown-lambda", args => if equal(
          d_imagpart(arg(args, 0)),
          Fix(0L),
        ) {
        t
      } else {
        Nil
      }),
    ),
  )
}

///|
fn lowerhalf(j : Value) -> Value raise {
  lbool(eq(d_asksign(d_imagpart(j)), q_d_neg))
}

///|
fn upperhalf(j : Value) -> Value raise {
  lbool(eq(d_asksign(d_imagpart(j)), q_d_pos))
}

///|
fn csemiup(n : Value, d : Value, ivar : Value) -> Value raise {
  // I'm not sure what to do about PRINCIPAL values here.
  let b0 = bind(q_ear_pcprntd, t)
  defer unbind(b0)
  princip(
    res_var(
      ivar,
      n,
      d,
      lfunc("upperhalf", args => upperhalf(arg(args, 0))),
      lfunc("csemiup-lambda", args => if equal(
          d_imagpart(arg(args, 0)),
          Fix(0L),
        ) {
        t
      } else {
        Nil
      }),
    ),
  )
}

///|
fn princip(n : Value) -> Value raise {
  if n is Nil {
    Nil
  } else {
    let a = if car(n).truthy() { mul2(Fix(2L), car(n)) } else { Fix(0L) }
    let b = if cadr(n).truthy() {
      principal() |> ignore
      cadr(n)
    } else {
      Fix(0L)
    }
    mul2(q_d__pcti, d_rectform(add2_star(a, b)))
  }
}

///|
/// exponentialize sin and cos
fn sconvert(e : Value, ivar : Value) -> Value raise {
  if atom(e) {
    e
  } else if polyinx(e, ivar, Nil).truthy() {
    e
  } else if eq(caar(e), q_p_sin) {
    muln_star([
      defint__rat(-1L, 2L),
      q_d__pcti,
      add2(
        power(q_d__pcte, mul2(q_d__pcti, cadr(e))),
        defint__mneg(power(q_d__pcte, mul2(defint__mneg(q_d__pcti), cadr(e)))),
      ),
    ])
  } else if eq(caar(e), q_p_cos) {
    mul2_star(
      defint__rat(1L, 2L),
      add2(
        power(q_d__pcte, mul2(q_d__pcti, cadr(e))),
        power(q_d__pcte, mul2(defint__mneg(q_d__pcti), cadr(e))),
      ),
    )
  } else {
    simplify(cons(list1(caar(e)), mapcar(ee => sconvert(ee, ivar), cdr(e))))
  }
}

///|
fn polfactors(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let mut poly : Value = Nil
  let mut rest : Value = Nil
  if mplusp(defint__exp()).truthy() {
    Nil
  } else {
    if mtimesp(defint__exp()).truthy() {
      set(q_exp, reverse(cdr(defint__exp()))) |> ignore
    } else {
      set(q_exp, list1(defint__exp())) |> ignore
    }
    for term in defint__exp().iter() {
      if polyinx(term, ivar, Nil).truthy() {
        poly = cons(term, poly)
      } else {
        rest = cons(term, rest)
      }
    }
    list2(muln(poly, Nil), muln(rest, Nil))
  }
}

///|
fn esap(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if !among(q_d__pcte, e).truthy() {
    e
  } else if mexptp(e).truthy() && eq(cadr(e), q_d__pcte) {
    let d = d_imagpart(caddr(e))
    mul2_star(
      power(q_d__pcte, d_realpart(caddr(e))),
      add2_star(mk(q_p_cos, [d]), mul2(q_d__pcti, mk(q_p_sin, [d]))),
    )
  } else {
    simplify(cons(list1(caar(e)), mapcar(x => esap(x), cdr(e))))
  }
}

///|
/// computes integral from minf to inf for expressions of the form
/// exp(%i*m*x)*r(x) by residues on either the upper half plane or the
/// lower half plane, depending on whether m is positive or negative.
/// [wang p. 77]
///
/// exponentializes sin and cos before applying residue method.  can
/// handle some expressions with poles on real line, such as
/// sin(x)*cos(x)/x.
fn mtosc(grand : Value, ivar : Value) -> Value raise {
  let (n0, d0) = numden_var(grand, ivar)
  let mut n = n0
  let mut d = d0
  let mut grand = grand
  let bs = bind_all([(q_ear_bptu, Nil), (q_ear_bptd, Nil)])
  defer unbind_all(bs)
  let mut ratterms : Value = Nil
  let mut ratans : Value = Nil
  let mut upans : Value = Nil
  let mut downans : Value = Nil
  if !(
      polyinx(d, ivar, Nil).truthy() ||
      (
        { grand = p_einvolve_var(d, ivar); grand.truthy() } &&
        among(q_d__pcti, grand).truthy() &&
        {
          d = sratsimp(div_star(d, power(q_d__pcte, grand)))
          polyinx(d, ivar, Nil).truthy()
        } &&
        { n = div_star(n, power(q_d__pcte, grand)); n.truthy() }
      )
    ) {
    return Nil
  }
  let s = deg_var(d, ivar)
  if equal(s, Fix(0L)) {
    return Nil
  }
  // Above tests for applicability of this method.
  let plf = polfactors(n, ivar)
  n = d_expand(
    if car(plf).truthy() {
      mul2(q_x_star, sconvert(cadr(plf), ivar))
    } else {
      sconvert(n, ivar)
    },
  )
  if n is Nil {
    return Nil
  }
  if mplusp(n).truthy() {
    n = cdr(n)
  } else {
    n = list1(n)
  }
  if n is Nil {
    return Nil
  }
  for term in n.iter() {
    if polyinx(term, ivar, Nil).truthy() {
      // call to $expand can create rational terms with no exp(m*%i*x)
      ratterms = cons(term, ratterms)
    } else if rib(term, s, ivar).truthy() {
      ()
    } else {
      return Nil
    }
  }
  // Function RIB sets up the values of BPTU and BPTD
  if car(plf).truthy() {
    set(q_ear_bptu, subst(car(plf), q_x_star, symval(q_ear_bptu))) |> ignore
    set(q_ear_bptd, subst(car(plf), q_x_star, symval(q_ear_bptd))) |> ignore
    ratterms = subst(car(plf), q_x_star, ratterms)
    // CROCK, CROCK. This is TERRIBLE code.
  }
  // If there is BPTU then CSEMIUP must succeed.  Likewise for BPTD.
  ratans = if ratterms.truthy() {
    // The original integrand was already determined to have no poles by
    // initial-analysis.  If individual terms of the expansion have
    // poles, the poles must cancel each other out, so we can ignore
    // them.
    with_special(q_d_intanalysis, Nil, fn() {
      try_defint(div_star(addn(ratterms, Nil), d), ivar, q_d_minf, q_d_inf)
    })
  } else {
    Fix(0L)
  }
  // if integral of ratterms is divergent, ratans is nil, and mtosc
  // returns nil
  if ratans is Nil {
    return Nil
  }
  if symval(q_ear_bptu).truthy() {
    upans = csemiup(addn(symval(q_ear_bptu), Nil), d, ivar)
  } else {
    upans = Fix(0L)
  }
  if upans is Nil {
    return Nil
  }
  if symval(q_ear_bptd).truthy() {
    downans = csemidown(addn(symval(q_ear_bptd), Nil), d, ivar)
  } else {
    downans = Fix(0L)
  }
  if downans is Nil {
    return Nil
  }
  sratsimp(
    add2_star(
      ratans,
      mul2_star(q_d__pctpi, add2_star(upans, defint__mneg(downans))),
    ),
  )
}

///|
fn evenfn(e : Value, ivar : Value) -> Value raise {
  let temp = add2_star(
    defint__mneg(e),
    if atom(ivar) {
      d_substitute(defint__mneg(ivar), ivar, expr=e)
    } else {
      d_ratsubst(defint__mneg(ivar), ivar, e)
    },
  )
  if zerop1(temp).truthy() {
    t
  } else if zerop1(sratsimp(temp)).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn oddfn(e : Value, ivar : Value) -> Value raise {
  let temp = add2_star(
    e,
    if atom(ivar) {
      d_substitute(defint__mneg(ivar), ivar, expr=e)
    } else {
      d_ratsubst(defint__mneg(ivar), ivar, e)
    },
  )
  if zerop1(temp).truthy() {
    t
  } else if zerop1(sratsimp(temp)).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// The SNUMDEN-VAR test of ZTOINF and MTOINF: are all factors of GRAND
/// polynomial powers?  Accumulates into SN and SD.
fn defint__snumden_all(
  grand : Value,
  ivar : Value,
  sn : Ref[Value],
  sd : Ref[Value],
) -> Value raise {
  defint__andmapcar(
    e => {
      let (result, new_sn, new_sd) = snumden_var(e, ivar, sn.val, sd.val)
      if result.truthy() {
        sn.val = new_sn
        sd.val = new_sd
      }
      result
    },
    cdr(grand),
  )
}

///|
fn ztoinf(grand : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  if !(zerop1(ll).truthy() && eq(ul, q_d_inf)) {
    lisp_error("The assertion (AND (ZEROP1 LL) (EQ UL '$INF)) failed.") |> ignore
  }
  let bs = bind_all([
    (q_varlist, Nil),
    (q_d_savefactors, Nil),
    (q_ear_checkfactors, Nil),
  ])
  defer unbind_all(bs)
  let mut grand = grand
  let mut n : Value = Nil
  let mut d : Value = Nil
  let mut s : Value = Nil
  let mut nc : Value = Nil
  let mut dc : Value = Nil
  let mut ans : Value = Nil
  let mut temp : Value = Nil
  let mut nn_var : Value = Nil
  let mut dn_var : Value = Nil
  set(q_d_savefactors, t) |> ignore
  let one = list1(Fix(1L))
  let sn = Ref(one)
  let sd = Ref(one)
  let mut goto_on = false
  if eq(d_sign(add2_star(symval(q_ear_loopstop), Fix(-1L))), q_d_pos) {
    return Nil
  } else {
    temp = scaxn(grand, ivar)
    if temp is Nil {
      temp = ssp(grand, ivar, ll, ul)
    }
    if temp.truthy() {
      return temp
    } else if involve_var(grand, ivar, list([q_p_sin, q_p_cos, q_p_tan])).truthy() {
      grand = sconvert(grand, ivar)
      goto_on = true
    }
  }
  if !goto_on {
    if polyinx(grand, ivar, Nil).truthy() {
      diverg() |> ignore
    } else if ratp(grand, ivar).truthy() &&
      mtimesp(grand).truthy() &&
      defint__snumden_all(grand, ivar, sn, sd).truthy() {
      nn_var = muln(sn.val, Nil)
      sn.val = Nil
      dn_var = muln(sd.val, Nil)
      sd.val = Nil
    } else {
      let (a, b) = numden_var(grand, ivar)
      nn_var = a
      dn_var = b
    }
    // New section.
    n = rmconst1(nn_var, ivar)
    d = rmconst1(dn_var, ivar)
    nc = car(n)
    n = cdr(n)
    dc = car(d)
    d = cdr(d)
    let mut goto_findout = false
    if polyinx(d, ivar, Nil).truthy() {
      s = deg_var(d, ivar)
    } else {
      goto_findout = true
    }
    if !goto_findout {
      let r = findp(n, ivar)
      if r.truthy() && eq(ask_integer(r, q_d_integer), q_d_yes) {
        let test_var = bxm(d, s, ivar)
        if test_var.truthy() {
          ans = fan(
            add2_star(Fix(1L), r),
            nth(0, test_var),
            nth(1, test_var),
            nth(2, test_var),
            nth(3, test_var),
          )
          if ans.truthy() {
            return mul2_star(div_star(nc, dc), sratsimp(ans))
          }
        }
      }
      if ratp(grand, ivar).truthy() {
        ans = zmtorat(
          n,
          if mtimesp(d).truthy() {
            d
          } else {
            d_sqfr(d)
          },
          s,
          lfunc("ztorat-lambda", args => ztorat(
            arg(args, 0),
            arg(args, 1),
            arg(args, 2),
            ivar,
          )),
          ivar,
        )
        if ans.truthy() {
          return mul2_star(div_star(nc, dc), ans)
        }
      }
      if evenfn(d, ivar).truthy() {
        nn_var = p_starlognxp(n, s, ivar)
        if nn_var.truthy() {
          ans = log_starrat(car(nn_var), d, cadr(nn_var), ivar)
          return mul2_star(div_star(nc, dc), ans)
        }
      }
      if involve_var(grand, ivar, list1(q_p_log)).truthy() {
        ans = logquad0(grand, ivar)
        if ans.truthy() {
          return mul2_star(div_star(nc, dc), ans)
        } else {
          return Nil
        }
      }
    }
    // findout
    temp = batapp(grand, ivar, ll, ul)
    if temp.truthy() {
      return temp
    }
  }
  // on
  temp = with_special(q_ear_mtoinf, Nil, fn() { ggr(grand, t, ivar) })
  if temp.truthy() {
    return temp
  } else if mplusp(grand).truthy() {
    ans = with_special(q_ear_nodiverg, t, fn() {
      defint__catch_divergent(fn() {
        defint__andmapcar(g => ztoinf(g, ivar, ll, ul), cdr(grand))
      })
    })
    if ans.truthy() {
      if eq(ans, q_divergent) {
        ()
      } else {
        return sratsimp(addn(ans, Nil))
      }
    }
  }
  if evenfn(grand, ivar).truthy() &&
    set(q_ear_loopstop, add2_star(Fix(1L), symval(q_ear_loopstop))).truthy() &&
    {
      ans = method_by_limits(grand, ivar, q_d_minf, q_d_inf)
      ans.truthy()
    } {
    mul2(defint__rat(1L, 2L), ans)
  } else {
    Nil
  }
}

///|
fn ztorat(n : Value, d : Value, s : Value, ivar : Value) -> Value raise {
  if symval(q_ear_dflag) is Nil {
    let s1 = difapply(
      ivar,
      n,
      d,
      s,
      lfunc("ztorat-lambda", args => ztorat(arg(args, 0), arg(args, 1), arg(args, 2), ivar)),
    )
    if s1.truthy() {
      return s1
    }
  }
  let n1 = with_special(q_plogabs, Nil, fn() {
    keyhole(
      // It's very important here to bind VAR because the PLOG
      // simplifier checks for VAR.  Without this, the simplifier
      // converts plog(-x) to log(x)+%i*%pi, which messes up the keyhole
      // routine.
      with_special(q_var, ivar, fn() {
        mul2_star(mk(q_p_plog, [defint__mneg(ivar)]), n)
      }),
      d,
      ivar,
    )
  })
  if n1.truthy() {
    defint__mneg(n1)
  } else {
    // Let's not signal an error here.  Return nil so that we eventually
    // return a noun form if no other algorithm gives a result.
    Nil
  }
}

///|
fn logquad0(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  set(q_exp, logquad(defint__exp(), ivar)) |> ignore
  if defint__exp().truthy() {
    let e = defint__exp()
    let mut a = car(e)
    let mut b = cadr(e)
    let mut c = caddr(e)
    d_asksign(b) |> ignore // let the data base know about the sign of B.
    if eq(d_asksign(c), q_d_pos) {
      c = power_star(div_star(c, a), defint__rat(1L, 2L))
      b = simplify(
        mk(q_p_acos, [
          add2_star(q_epsilon, div_star(b, muln_star([Fix(2L), a, c]))),
        ]),
      )
      a = div_star(
        mul2_star(b, mk(q_p_log, [c])),
        muln_star([a, simplify(mk(q_p_sin, [b])), c]),
      )
      get_limit(a, q_epsilon, Fix(0L), dir=q_d_plus)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn logquad(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b0 = bind(q_varlist, list1(ivar))
  defer unbind(b0)
  newvar(defint__exp()) |> ignore
  set(q_exp, cdr(ratrep_star(defint__exp()))) |> ignore
  let e = defint__exp()
  if alike1(pdis(car(e)), mk(q_p_log, [ivar])).truthy() &&
    !atom(cdr(e)) &&
    equal(cadr(cdr(e)), Fix(2L)) &&
    !equal(ptterm(cddr(e), Fix(0L)), Fix(0L)) {
    set(q_exp, mapcar(x => pdis(x), cdr(oddelm(cdr(e)))))
  } else {
    Nil
  }
}

///|
fn mtoinf(grand : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  if !(eq(ll, q_d_minf) && eq(ul, q_d_inf)) {
    lisp_error("The assertion (AND (EQ LL '$MINF) (EQ UL '$INF)) failed.")
    |> ignore
  }
  let bs = bind_all([(q_d_savefactors, Nil), (q_ear_checkfactors, Nil)])
  defer unbind_all(bs)
  let mut grand = grand
  let mut ans : Value = Nil
  let mut n : Value = Nil
  let mut d : Value = Nil
  let mut s : Value = Nil
  let mut nc : Value = Nil
  let mut dc : Value = Nil
  let mut temp : Value = Nil
  let mut nn_var : Value = Nil
  let mut dn_var : Value = Nil
  let pp : Ref[Value] = Ref(Nil)
  let pe : Ref[Value] = Ref(Nil)
  set(q_d_savefactors, t) |> ignore
  let one = list1(Fix(1L))
  let sn = Ref(one)
  let sd = Ref(one)
  let mut goto_en = false
  if eq(d_sign(add2_star(symval(q_ear_loopstop), Fix(-1L))), q_d_pos) {
    return Nil
  } else if involve_var(grand, ivar, list([q_p_sin, q_p_cos])).truthy() {
    if evenfn(grand, ivar).truthy() &&
      {
        temp = scaxn(grand, ivar)
        temp.truthy() ||
        {
          temp = ssp(grand, ivar, Fix(0L), ul)
          temp.truthy()
        }
      } {
      return mul2(Fix(2L), temp)
    }
    temp = mtosc(grand, ivar)
    if temp.truthy() {
      return temp
    } else {
      goto_en = true
    }
  } else if among(q_d__pcti, p_einvolve_var(grand, ivar)).truthy() {
    temp = mtosc(grand, ivar)
    if temp.truthy() {
      return temp
    } else {
      goto_en = true
    }
  }
  if !goto_en {
    // exponentializing before numden avoids losing multiplicities
    // [ 1309432 ]
    grand = d_exponentialize(grand)
    if polyinx(grand, ivar, Nil).truthy() {
      diverg() |> ignore
    } else if ratp(grand, ivar).truthy() &&
      mtimesp(grand).truthy() &&
      defint__snumden_all(grand, ivar, sn, sd).truthy() {
      nn_var = muln(sn.val, Nil)
      sn.val = Nil
      dn_var = muln(sd.val, Nil)
      sd.val = Nil
    } else {
      let (a, b) = numden_var(grand, ivar)
      nn_var = a
      dn_var = b
    }
    n = rmconst1(nn_var, ivar)
    d = rmconst1(dn_var, ivar)
    nc = car(n)
    n = cdr(n)
    dc = car(d)
    d = cdr(d)
    if polyinx(d, ivar, Nil).truthy() {
      s = deg_var(d, ivar)
    }
    if !p_einvolve_var(grand, ivar).truthy() &&
      notinvolve_var(
        defint__exp(),
        ivar,
        list([q_p_sinh, q_p_cosh, q_p_tanh]),
      ).truthy() &&
      {
        pp.val = findp(n, ivar)
        pp.val.truthy()
      } &&
      eq(ask_integer(pp.val, q_d_integer), q_d_yes) &&
      {
        pe.val = bxm(d, s, ivar)
        pe.val.truthy()
      } {
      let fan_pe = fn() -> Value raise {
        let pe = pe.val
        fan(add2_star(Fix(1L), pp.val), nth(0, pe), nth(1, pe), nth(2, pe), nth(3, pe))
      }
      if eq(ask_integer(caddr(pe.val), q_d_even), q_d_yes) &&
        eq(ask_integer(pp.val, q_d_even), q_d_yes) {
        ans = fan_pe()
        if ans.truthy() {
          ans = mul2(Fix(2L), ans)
          return mul2_star(div_star(nc, dc), ans)
        }
      } else if equal(car(pe.val), Fix(1L)) {
        ans = fan_pe()
        if ans.truthy() &&
          {
            nn_var = fan(
              add2_star(Fix(1L), pp.val),
              car(pe.val),
              mul2_star(Fix(-1L), cadr(pe.val)),
              caddr(pe.val),
              cadddr(pe.val),
            )
            nn_var.truthy()
          } {
          ans = add2_star(ans, mul2(power_star(Fix(-1L), pp.val), nn_var))
          return mul2_star(div_star(nc, dc), ans)
        }
      }
    }
    // Test to see if exp is of the form p(x)*f(exp(x)).  If so, set pp
    // to be p(x) and set pe to f(exp(x)).
    fn pppin_pctex(nd : Value, ivar : Value) -> Value raise {
      let nd = d_factor(nd)
      if polyinx(nd, ivar, Nil).truthy() {
        pp.val = cons(nd, pp.val)
        t
      } else if defint__catch_pin(nd, ivar).truthy() {
        pe.val = cons(nd, pe.val)
        t
      } else if mtimesp(nd).truthy() {
        defint__andmapcar(ex => pppin_pctex(ex, ivar), cdr(nd))
      } else {
        Nil
      }
    }
    if ratp(grand, ivar).truthy() &&
      {
        let ans1 = zmtorat(
          n,
          if mtimesp(d).truthy() {
            d
          } else {
            d_sqfr(d)
          },
          s,
          lfunc("mtorat-lambda", args => mtorat(
            arg(args, 0),
            arg(args, 1),
            arg(args, 2),
            ivar,
          )),
          ivar,
        )
        if ans1.truthy() {
          ans = mul2(q_d__pctpi, ans1)
          true
        } else {
          false
        }
      } {
      return mul2_star(div_star(nc, dc), ans)
    } else if (
        p_einvolve_var(grand, ivar).truthy() ||
        involve_var(grand, ivar, list([q_p_sinh, q_p_cosh, q_p_tanh])).truthy()
      ) &&
      pppin_pctex(n, ivar).truthy() && // setq's P* and PE*...Barf again.
      {
        ans = defint__catch_pin(d, ivar)
        ans.truthy()
      } {
      // We have an integral of the form p(x)*F(exp(x)), where p(x) is a
      // polynomial.
      if pp.val is Nil {
        // No polynomial
        return dintexp(grand, ivar, ll, ul)
      } else if !(
          zerop1(get_limit(grand, ivar, q_d_inf)).truthy() &&
          zerop1(get_limit(grand, ivar, q_d_minf)).truthy()
        ) {
        // These limits must exist for the integral to converge.
        return diverg()
      } else {
        ans = rectzto_pctpi2(muln(pp.val, Nil), muln(pe.val, Nil), d, ivar)
        if ans.truthy() {
          // This only handles the case when the F(z) is a rational
          // function.
          return mul2_star(div_star(nc, dc), ans)
        }
        ans = log_transform(muln(pp.val, Nil), muln(pe.val, Nil), d, ivar, ul)
        if ans.truthy() {
          // If we get here, F(z) is not a rational function.  We
          // transform it using the substitution x=log(y) which gives us
          // an integral of the form p(log(y))*F(y)/y, which maxima
          // should be able to handle.
          return mul2_star(div_star(nc, dc), ans)
        }
        // Give up.  We don't know how to handle this.
        return Nil
      }
    }
  }
  // en
  ans = ggrm(grand, ivar)
  if ans.truthy() {
    ans
  } else if evenfn(grand, ivar).truthy() &&
    set(q_ear_loopstop, add2_star(Fix(1L), symval(q_ear_loopstop))).truthy() &&
    {
      ans = method_by_limits(grand, ivar, Fix(0L), q_d_inf)
      ans.truthy()
    } {
    mul2(Fix(2L), ans)
  } else {
    Nil
  }
}

///|
fn linpower0(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  set(q_exp, linpower(defint__exp(), ivar)) |> ignore
  if defint__exp().truthy() &&
    eq(ask_integer(caddr(defint__exp()), q_d_even), q_d_yes) &&
    ratgreaterp(Fix(0L), car(defint__exp())).truthy() {
    defint__exp()
  } else {
    Nil
  }
}

///|
/// given (b*x+a)^n+c returns  (a b n c)
fn linpower(exp_ : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b0 = bind(q_varlist, Nil)
  defer unbind(b0)
  let mut linpart : Value = Nil
  let mut deg : Value = Nil
  let mut lc : Value = Nil
  let mut c : Value = Nil
  if !polyp_var(defint__exp(), ivar).truthy() {
    return Nil
  }
  with_special(q_varlist, list1(ivar), fn() {
    newvar(defint__exp()) |> ignore
    linpart = cadr(ratrep_star(defint__exp()))
    if atom(linpart) {
      ()
    } else {
      deg = cadr(linpart)
      // get high degree of poly
      linpart = d_diff(list3(defint__exp(), ivar, add2_star(deg, Fix(-1L))))
      // diff down to linear.
      lc = sdiff(linpart, ivar)
      // all the way to constant.
      linpart = sratsimp(div_star(linpart, lc))
      lc = sratsimp(div_star(lc, mk(q_mfactorial, [deg])))
      // get rid of factorial from differentiation.
      c = sratsimp(
        add2_star(
          defint__exp(),
          mul2_star(defint__mneg(lc), power_star(linpart, deg)),
        ),
      )
    }
    // Sees if can be expressed as (a*x+b)^n + part freeof x.
    if !among(ivar, c).truthy() {
      list([lc, linpart, deg, c])
    } else {
      Nil
    }
  })
}

///|
fn mtorat(n : Value, d : Value, s : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_ear_semirat, t)
  defer unbind(b0)
  if symval(q_ear_dflag) is Nil {
    let s1 = difapply(
      ivar,
      n,
      d,
      s,
      lfunc("mtorat-lambda", args => mtorat(arg(args, 0), arg(args, 1), arg(args, 2), ivar)),
    )
    if s1.truthy() {
      return s1
    }
  }
  csemiup(n, d, ivar)
}

///|
fn zmtorat(
  n : Value,
  d : Value,
  s : Value,
  fn1 : Value,
  ivar : Value,
) -> Value raise {
  let mut n = n
  let mut d = d
  let mut c : Value = Nil
  // The integral can only converge if the degree of the denominator
  // exceeds the degree of the numerator by at least 2.
  let mut goto_on = false
  if eq(
      d_sign(
        add2_star(
          s,
          defint__mneg(add2_star(Fix(2L), set(q_nn_star, deg_var(n, ivar)))),
        ),
      ),
      q_d_neg,
    ) {
    diverg() |> ignore
  } else if eq(d_sign(add2_star(s, Fix(-4L))), q_d_neg) {
    goto_on = true
  }
  if !goto_on {
    d = d_factor(d)
    c = rmconst1(d, ivar)
    d = cdr(c)
    c = car(c)
    if mtimesp(d).truthy() {
      d = cdr(d)
      n = partnum(n, d, ivar)
      let b0 = bind(q_rsn_star, t)
      defer unbind(b0)
      let terms = Collector::new()
      let mut na = n
      let mut db = d
      while na.truthy() && db.truthy() {
        let a = car(na)
        let b = car(db)
        let foo = funcall(fn1, [car(a), b, deg_var(b, ivar)])
        if foo.truthy() {
          terms.add(div_star(foo, cadr(a)))
        } else {
          return Nil
        }
        na = cdr(na)
        db = cdr(db)
      }
      n = d_xthru(addn(terms.result(), Nil))
      return if c.truthy() { div_star(n, c) } else { n }
    }
  }
  // on
  n = funcall(fn1, [n, d, s])
  if n.truthy() {
    sratsimp(if c.truthy() { div_star(n, c) } else { n })
  } else {
    Nil
  }
}

///|
fn pfrnum(f : Value, g : Value, n : Value, n2 : Value, ivar : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(ivar)), (q_genvar, Nil)])
  defer unbind_all(bs)
  let f = polyform(f)
  let g = polyform(g)
  let n = polyform(n)
  let n2 = polyform(n2)
  let ivar = caadr(ratrep_star(ivar))
  let f = resprog0_var(ivar, f, g, n, n2)
  list2(list2(pdis(cadr(f)), pdis(cddr(f))), list2(pdis(caar(f)), pdis(cdar(f))))
}

///|
fn polyform(e : Value) -> Value raise {
  newvar(e) |> ignore
  let f = ratrep_star(e)
  if equal(cddr(f), Fix(1L)) {
    return cadr(f)
  }
  let d = cddr(f)
  if length(d) == 3 && !among(car(d), cadr(f)).truthy() {
    return list3(car(d), num_neg(cadr(d)), ptimes(cadr(f), caddr(d)))
  }
  merr("defint: bug from PFRNUM in RESIDU.", [])
}

///|
fn partnum(n : Value, dl : Value, ivar : Value) -> Value raise {
  let mut n = n
  let mut n2 : Value = Fix(1L)
  let mut ans : Value = Nil
  let mut dl = dl
  while cdr(dl).truthy() {
    let nl = pfrnum(car(dl), muln(cdr(dl), Nil), n, n2, ivar)
    ans = nconc(ans, list1(car(nl)))
    n2 = cadadr(nl)
    n = caadr(nl)
    dl = cdr(dl)
  }
  nconc(ans, list1(list2(n, n2)))
}

///|
fn ggrm(e : Value, ivar : Value) -> Value raise {
  let bs = bind_all([(q_ear_mtoinf, Nil), (q_varlist, Nil), (q_genvar, Nil)])
  defer unbind_all(bs)
  let mut e = e
  set(q_varlist, list1(ivar)) |> ignore
  set(q_ear_mtoinf, t) |> ignore
  let expo0 = p_einvolve_var(e, ivar)
  let mut poly : Value = Nil
  let mut l : Value = Nil
  if expo0.truthy() &&
    {
      poly = sratsimp(div_star(e, power(q_d__pcte, expo0)))
      polyp_var(poly, ivar).truthy()
    } &&
    {
      l = catch_tag(q_ggrm, fn() { ggr(power(q_d__pcte, expo0), Nil, ivar) })
      l.truthy()
    } {
    set(q_ear_mtoinf, Nil) |> ignore
    let mb = defint__mneg(subin_var(Fix(0L), cadr(l), ivar))
    poly = add2_star(
      subin_var(add2(mb, ivar), poly, ivar),
      subin_var(add2(mb, mul2(Fix(-1L), ivar)), poly, ivar),
    )
  } else {
    return Nil
  }
  let expo = caddr(l)
  let c = cadddr(l)
  l = mul2_star(Fix(-1L), car(l))
  e = Nil
  newvar(poly) |> ignore
  poly = cdr(ratrep_star(poly))
  let mb = power_star(pdis(cdr(poly)), Fix(-1L))
  poly = car(poly)
  let gvar = caadr(ratrep_star(ivar))
  if atom(poly) || pointergp(gvar, car(poly)).truthy() {
    poly = list2(Fix(0L), poly)
  } else {
    poly = cdr(poly)
  }
  while poly.truthy() {
    e = cons(ggrm1(car(poly), pdis(cadr(poly)), l, expo), e)
    poly = cddr(poly)
  }
  muln_star([power(q_d__pcte, c), power(expo, Fix(-1L)), mb, addn(e, Nil)])
}

///|
fn ggrm1(d : Value, k : Value, a : Value, b : Value) -> Value raise {
  let b = div_star(add2(Fix(1L), d), b)
  muln_star([k, mk(q_p_gamma, [b]), power_star(a, defint__mneg(b))])
}

///|
/// Compute the integral(n/d,x,0,inf) by computing the negative of the
/// sum of residues of log(-x)*n/d over the poles of n/d inside the
/// keyhole contour.  This contour is basically an disk with a slit along
/// the positive real axis.  n/d must be a rational function.
fn keyhole(n : Value, d : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_ear_semirat, Nil)
  defer unbind(b0)
  let res = res_var(
    ivar,
    n,
    d,
    lfunc("keyhole-region", args => {
      let j = arg(args, 0)
      // Ok if not on the positive real axis.
      lbool(
        !equal(d_imagpart(j), Fix(0L)) || eq(d_asksign(j), q_d_neg),
      )
    }),
    lfunc("keyhole-region1", args => {
      let j = arg(args, 0)
      if eq(d_asksign(j), q_d_pos) {
        t
      } else {
        diverg()
      }
    }),
  )
  if res.truthy() {
    with_special(q_rsn_star, t, fn() {
      d_rectform(
        d_multthru(
          add2_star(
            if car(res).truthy() {
              car(res)
            } else {
              Fix(0L)
            },
            if cadr(res).truthy() {
              cadr(res)
            } else {
              Fix(0L)
            },
          ),
        ),
      )
    })
  } else {
    Nil
  }
}

///|
/// Look at an expression e of the form sin(r*x)^k, where k is an
/// integer.  Return the list (1 r k).
fn skr(e : Value, ivar : Value) -> Value raise {
  if atom(e) {
    return Nil
  }
  let e1 = partition(e, ivar, Fix(1L))
  let m = car(e1)
  let e = cdr(e1)
  let r = sinrx(e, ivar)
  if r.truthy() {
    return list3(m, r, Fix(1L))
  }
  if mexptp(e).truthy() {
    let k = caddr(e)
    if eq(ask_integer(k, q_d_integer), q_d_yes) {
      let r = sinrx(cadr(e), ivar)
      if r.truthy() {
        return list3(m, r, k)
      }
    }
  }
  Nil
}

///|
/// Look at an expression e of the form sin(r*x) and return r.
fn sinrx(e : Value, ivar : Value) -> Value raise {
  if consp(e) && eq(caar(e), q_p_sin) {
    if eq(cadr(e), ivar) {
      Fix(1L)
    } else {
      let e = partition(cadr(e), ivar, Fix(1L))
      if e.truthy() && eq(cdr(e), ivar) {
        car(e)
      } else {
        Nil
      }
    }
  } else {
    Nil
  }
}

///|
/// integrate(a*sc(r*x)^k/x^n,x,0,inf).
fn ssp(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if !(zerop1(ll).truthy() && eq(ul, q_d_inf)) {
    lisp_error("The assertion (AND (ZEROP1 LL) (EQ UL '$INF)) failed.") |> ignore
  }
  // Get the argument of the involved trig function.
  let arg = involve_var(defint__exp(), ivar, list([q_p_sin, q_p_cos]))
  if arg is Nil {
    return Nil
  }
  // Replace (1-cos(arg)^2) with sin(arg)^2.
  set(
    q_exp,
    d_substitute(
      list3(list2(q_mexpt, q_simp), list2(list2(q_p_sin, q_simp), arg), Fix(2L)),
      mk(q_mplus, [
        Fix(1L),
        mk(q_mtimes, [Fix(-1L), mk(q_mexpt, [mk(q_p_cos, [arg]), Fix(2L)])]),
      ]),
      expr=defint__exp(),
    ),
  )
  |> ignore
  let (u, dn) = numden_var(defint__exp(), ivar)
  let n = findp(dn, ivar)
  if n.truthy() && eq(ask_integer(n, q_d_integer), q_d_yes) {
    // n is the power of the denominator.
    let c = skr(u, ivar)
    if c.truthy() {
      // The simple case.
      return scmp(c, n, ivar, ll, ul)
    }
    if mplusp(u).truthy() {
      let c = defint__andmapcar(uu => skr(uu, ivar), cdr(u))
      if c.truthy() {
        // Do this for a sum of such terms.
        return addn(mapcar(j => scmp(j, n, ivar, ll, ul), c), Nil)
      }
    }
  }
  Nil
}

///|
/// We have an integral of the form sin(r*x)^k/x^n.  C is the list
/// (1 r k).
///
/// The substitution y=r*x converts this integral to
///
///   r^(n-1)*integral(sin(y)^k/y^n,y,0,inf)
///
/// (If r is negative, we need to negate the result.)
///
/// The recursion Wang gives on p. 87 has a typo.  The second term should
/// be subtracted from the first.  This formula is given in G&R, 3.82,
/// formula 12.
///
/// integrate(sin(x)^r/x^s,x) =
///    r*(r-1)/(s-1)/(s-2)*integrate(sin(x)^(r-2)/x^(s-2),x)
///    - r^2/(s-1)/(s-2)*integrate(sin(x)^r/x^(s-2),x)
///
/// (Limits are assumed to be 0 to inf.)
///
/// This recursion ends up with integrals with s = 1 or 2 and
///
/// integrate(sin(x)^p/x,x,0,inf) = integrate(sin(x)^(p-1),x,0,%pi/2)
///
/// with p > 0 and odd.  This latter integral is known to maxima, and
/// it's value is beta(p/2,1/2)/2.
///
/// integrate(sin(x)^2/x^2,x,0,inf) = %pi/2*binomial(q-3/2,q-1)
///
/// where q >= 2.
fn scmp(c : Value, n : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  // Compute sign(r)*r^(n-1)*integrate(sin(y)^k/y^n,y,0,inf)
  if !(zerop1(ll).truthy() && eq(ul, q_d_inf)) {
    lisp_error("The assertion (AND (ZEROP1 LL) (EQ UL '$INF)) failed.") |> ignore
  }
  let mult = nth(0, c)
  let r = nth(1, c)
  let k = nth(2, c)
  let recursion = sinsp(k, n)
  if recursion.truthy() {
    muln_star([
      mult,
      power_star(r, add2_star(n, Fix(-1L))),
      mk(q_p_signum, [r]),
      recursion,
    ])
  } else {
    // Recursion failed.  Return the integrand
    let integrand = div(
      power(take(list1(q_p_sin), [mul2(r, ivar)]), k),
      power(ivar, n),
    )
    mul2_star(mult, mk(q_p_integrate, [integrand, ivar, ll, ul]))
  }
}

///|
/// integrate(sin(x)^n/x^2,x,0,inf) = pi/2*binomial(n-3/2,n-1).
/// Express in terms of Gamma functions, though.
fn sevn(n : Value) -> Value raise {
  mul2_star(
    symval(q_half_pctpi),
    d_makegamma(
      mk(q_p_binomial, [
        add2(add2_star(n, Fix(-1L)), defint__rat(-1L, 2L)),
        add2_star(n, Fix(-1L)),
      ]),
    ),
  )
}

///|
/// integrate(sin(x)^n/x,x,0,inf) = beta((n+1)/2,1/2)/2, for n odd and
/// n > 0.
fn sforx(n : Value) -> Value raise {
  if equal(n, Fix(1L)) {
    symval(q_half_pctpi)
  } else {
    bygamma(add2_star(n, Fix(-1L)), Fix(0L))
  }
}

///|
/// This implements the recursion for computing
/// integrate(sin(y)^l/y^k,y,0,inf).  (Note the change in notation from
/// the above!)
fn sinsp(l : Value, k : Value) -> Value raise {
  if eq(d_sign(add2_star(l, defint__mneg(add2_star(k, Fix(-1L))))), q_d_neg) {
    // Integral diverges if l-(k-1) < 0.
    diverg()
  } else if !even1(add2_star(l, k)).truthy() {
    // If l + k is not even, return NIL.  (Is this the right thing to
    // do?)
    Nil
  } else if equal(k, Fix(2L)) {
    // We have integrate(sin(y)^l/y^2).  Use sevn to evaluate.
    sevn(div_star(l, Fix(2L)))
  } else if equal(k, Fix(1L)) {
    // We have integrate(sin(y)^l/y,y)
    sforx(l)
  } else if eq(d_sign(add2_star(k, Fix(-2L))), q_d_pos) {
    let j = add2_star(k, Fix(-2L))
    let i = mul2_star(add2_star(k, Fix(-1L)), j)
    // j = k-2, i = (k-1)*(k-2)
    //
    // The main recursion:
    //
    // i(sin(y)^l/y^k)
    //    = l*(l-1)/(k-1)/(k-2)*i(sin(y)^(l-2)/y^k)
    //      - l^2/(k-1)/(k-1)*i(sin(y)^l/y^(k-2))
    add2_star(
      muln_star([
        l,
        add2_star(l, Fix(-1L)),
        power(i, Fix(-1L)),
        sinsp(add2_star(l, Fix(-2L)), j),
      ]),
      muln_star([
        defint__mneg(power_star(l, Fix(2L))),
        power(i, Fix(-1L)),
        sinsp(l, j),
      ]),
    )
  } else {
    Nil
  }
}

///|
/// Returns the fractional part of a?
fn fpart(a : Value) -> Value raise {
  if a is Nil {
    Fix(0L)
  } else if numberp(a) {
    // Why do we return 0 if a is a number?  Perhaps we really mean
    // integer?
    Fix(0L)
  } else if mnump(a).truthy() {
    // If we're here, this basically assumes a is a rational.  Compute
    // the remainder and return the result.
    list3(car(a), num_rem(cadr(a), caddr(a)), caddr(a))
  } else if atom(a) && abless1(a).truthy() {
    a
  } else if mplusp(a).truthy() && cdddr(a) is Nil && abless1(caddr(a)).truthy() {
    caddr(a)
  } else {
    Nil
  }
}

///|
/// THE FOLLOWING FUNCTION IS FOR TRIG FUNCTIONS OF THE FOLLOWING TYPE:
/// LOWER LIMIT=0 B A MULTIPLE OF %PI SCA FUNCTION OF SIN (X) COS (X)
/// B<=%PI2
fn period(p : Value, e : Value, ivar : Value) -> Value raise {
  let v = no_err_sub_var(ivar, e, ivar)
  let e = no_err_sub_var(add2_star(p, ivar), e, ivar)
  // means there was no error
  lbool(alike1(v, e).truthy() && !eq(e, t))
}

///|
/// returns cons of (integer_part . fractional_part) of a
fn infr(a : Value) -> Value raise {
  // I think we really want to compute how many full periods are in a
  // and the remainder.
  let q = igprt(div(a, mul2(Fix(2L), q_d__pctpi)))
  let r = add2(a, mul2(Fix(-1L), mul3(q, Fix(2L), q_d__pctpi)))
  cons(q, r)
}

///|
/// returns cons of (integer_part . fractional_part) of a
fn lower_infr(a : Value) -> Value raise {
  let q = mfuncall(q_d_ceiling, list1(div(a, mul2(Fix(2L), q_d__pctpi))))
  let r = add2(a, mul2(Fix(-1L), mul3(q, Fix(2L), q_d__pctpi)))
  cons(q, r)
}

///|
/// Return the integer part of r.
fn igprt(r : Value) -> Value raise {
  // r - fpart(r)
  mfuncall(q_d_floor, list1(r))
}

///|
/// Try making exp(%i*ivar) --> yy, if result is rational then do
/// integral around unit circle. Make corrections for limits of
/// integration if possible.
fn scrat(sc : Value, b : Value, ivar : Value) -> Value raise {
  let exp_form = sconvert(sc, ivar) // Exponentialize
  // Try to make Rational fun.
  let rat_form = maxima_substitute(
    q_yy,
    power(q_d__pcte, mul2(q_d__pcti, ivar)),
    exp_form,
  )
  if ratp(rat_form, q_yy).truthy() && !among(ivar, rat_form).truthy() {
    if alike1(b, symval(q_p_pi2)).truthy() {
      let ans = zto_pctpi2(rat_form, q_yy)
      if ans.truthy() {
        ans
      } else {
        Nil
      }
    } else if eq(b, q_d__pctpi) && evenfn(exp_form, ivar).truthy() {
      let ans = zto_pctpi2(rat_form, q_yy)
      if ans.truthy() {
        mul2(defint__rat(1L, 2L), ans)
      } else {
        Nil
      }
    } else if alike1(b, symval(q_half_pctpi)).truthy() &&
      evenfn(exp_form, ivar).truthy() &&
      alike1(
        rat_form,
        no_err_sub_var(
          add2(q_d__pctpi, mul2(Fix(-1L), ivar)),
          rat_form,
          ivar,
        ),
      ).truthy() {
      let ans = zto_pctpi2(rat_form, q_yy)
      if ans.truthy() {
        mul2(defint__rat(1L, 4L), ans)
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Do integrals of sin and cos. this routine makes sure lower limit is
/// zero.
fn intsc1(a : Value, b : Value, e : Value, ivar : Value) -> Value raise {
  // integrate(e,var,a,b)
  let trigarg = find_first_trigarg(e, var_=ivar)
  let bs = bind_all([
    (q_d__pctemode, t),
    (q_d_trigsign, t),
    (q_ear_sin_cos_recur, t), // recursion stopper
  ])
  defer unbind_all(bs)
  let mut a = a
  let mut b = b
  let mut e = e
  let mut ivar = ivar
  let mut ans : Value = Nil
  {
    // pattern match sin(cc*x + bb)
    let arg = simple_trig_arg(trigarg, ivar)
    let cc = cdras(q_c, arg)
    let bb = cdras(q_b, arg)
    let new_var = gensym(prefix="new-var-")
    putprop(new_var, t, q_internal) |> ignore
    if arg is Nil || !every_trigarg_alike(e, trigarg, var_=ivar).truthy() {
      return Nil
    }
    if !(equal(cc, Fix(1L)) && equal(bb, Fix(0L))) {
      e = div(maxima_substitute(div(sub(new_var, bb), cc), ivar, e), cc)
      ivar = new_var // change of variables to get sin(new-var)
      a = add2(bb, mul2(a, cc))
      b = add2(bb, mul2(b, cc))
    }
  }
  let limit_diff = add2_star(b, mul2_star(Fix(-1L), a))
  let pi2 = symval(q_p_pi2)
  if !period(pi2, e, ivar).truthy() ||
    member(a, symval(q_ear_infinities)).truthy() ||
    member(b, symval(q_ear_infinities)).truthy() ||
    !(d_constantp(a).truthy() && d_constantp(b).truthy()) {
    // Exit if b or a is not a constant or if the integrand doesn't
    // appear to have a period of 2 pi.
    return Nil
  }
  // Multiples of 2*%pi in limits.
  let d = with_special(q_d_float, Nil, fn() { div_star(limit_diff, pi2) })
  if integerp(d) {
    ans = intsc(e, pi2, ivar).0
    if ans.truthy() {
      return mul2_star(d, ans)
    } else {
      return Nil
    }
  }
  // The integral is not over a full period (2*%pi) or multiple of a
  // full period.

  // Wang p. 111: The integral integrate(f(x),x,a,b) can be written as:
  //
  //   n * integrate(f,x,0,2*%pi) + integrate(f,x,0,c)
  //     - integrate(f,x,0,d)
  //
  // for some integer n and d >= 0, c < 2*%pi because there exist
  // integers p and q such that a = 2 * p *%pi + d and b = 2 * q * %pi
  // + c.  Then n = q - p.

  // Compute q and c for the upper limit b.
  b = infr(b)
  let mut l = a
  let mut nzp2 : Value = Nil
  let mut int_zero_to_d : Value = Nil
  if l is Nil {
    nzp2 = car(b)
    int_zero_to_d = Fix(0L)
  } else {
    // Compute p and d for the lower limit a.
    l = infr(l)
    // avoid an extra trip around the circle - helps skip principal
    // values
    if ratgreaterp(car(b), car(l)).truthy() {
      // if q > p: p += 1, d -= 2*%pi
      l = cons(add2(Fix(1L), car(l)), add2(mul2(Fix(-1L), pi2), cdr(l)))
    }
    // Compute -integrate(f,x,0,d)
    int_zero_to_d = {
      ans = try_intsc(e, cdr(l), ivar)
      if ans.truthy() {
        mul2(Fix(-1L), ans)
      } else {
        Nil
      }
    }
    // Compute n = q - p (stored in nzp2)
    nzp2 = add2_star(car(b), defint__mneg(car(l)))
  }
  // out
  // Compute n*integrate(f,x,0,2*%pi)
  let int_nzp2 : Value = if zerop1(nzp2).truthy() {
    // n = 0
    Fix(0L)
  } else {
    ans = try_intsc(e, pi2, ivar)
    if ans.truthy() {
      // n is not zero, so compute integrate(f,x,0,2*%pi)
      mul2(nzp2, ans)
    } else {
      // Unable to compute integrate(f,x,0,2*%pi)
      Nil
    }
  }
  // Compute integrate(f,x,0,c)
  let int_zero_to_c = try_intsc(e, cdr(b), ivar)
  if int_zero_to_d.truthy() && int_nzp2.truthy() && int_zero_to_c.truthy() {
    // All three pieces succeeded.
    addn_star([int_zero_to_d, int_nzp2, int_zero_to_c])
  } else if ratgreaterp(pi2, limit_diff).truthy() {
    // Less than 1 full period, so intsc can integrate it.  Apply the
    // substitution to make the lower limit 0.  This is last resort
    // because substitution often causes intsc to fail.
    intsc(maxima_substitute(add2_star(a, ivar), ivar, e), limit_diff, ivar).0
  } else {
    // nothing worked
    Nil
  }
}

///|
/// integrate(sc, var, 0, b), where sc is f(sin(x), cos(x)).  calls
/// intsc with a wrapper to just return nil if integral is divergent,
/// rather than generating an error.
fn try_intsc(sc : Value, b : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_ear_nodiverg, t)
  defer unbind(b0)
  let ans = defint__catch_divergent(fn() { intsc(sc, b, ivar).0 })
  if eq(ans, q_divergent) {
    Nil
  } else {
    ans
  }
}

///|
/// integrate(sc, ivar, 0, b), where sc is f(sin(x), cos(x)).  I (rtoy)
/// think this expects b to be less than 2*%pi.
/// (Returns a single value; the second element is always nil.)
fn intsc(sc : Value, b : Value, ivar : Value) -> (Value, Value) raise {
  if zerop1(b).truthy() {
    return (Fix(0L), Nil)
  }
  let (b, sc) = if eq(d_sign(b), q_d_neg) {
    (
      mul2(Fix(-1L), b),
      mul2_star(Fix(-1L), subin_var(mul2(Fix(-1L), ivar), sc, ivar)),
    )
  } else {
    (b, sc)
  }
  // Partition the integrand SC into the factors that do not contain VAR
  // (the car part) and the parts that do (the cdr part).
  let sc = partition(sc, ivar, Fix(1L))
  let b = intsc0(cdr(sc), b, ivar)
  if b.truthy() {
    (mul2_star(resimplify(car(sc)), b), Nil)
  } else {
    (Nil, Nil)
  }
}

///|
/// The factor (-1)^e in the reflection formulas of INTSC0: 1 or -1 for
/// integer e (the same on every branch), and the simplified (-1)^e for a
/// rational e with an odd denominator. Under the default domain:real the
/// latter is the real branch (e.g. (-1)^(1/3) = -1, so
/// integrate(sin(x)^(1/3)*cos(x)^(1/3),x,0,2*%pi) is 0 and not 4 times
/// the quarter-period integral; with domain:complex it stays symbolic,
/// so the caller's result remains valid under any branch convention.
/// NIL if there is no real branch or we cannot tell.
fn exp_neg_1_real(e : Value) -> Value raise {
  if eq(ask_integer(e, q_d_even), q_d_yes) {
    Fix(1L)
  } else if eq(ask_integer(e, q_d_odd), q_d_yes) {
    Fix(-1L)
  } else if ratnump(e).truthy() && oddp(caddr(e)) {
    power_star(Fix(-1L), e)
  } else {
    Nil
  }
}

///|
/// integrate(sc, ivar, 0, b), where sc is f(sin(x), cos(x)).
fn intsc0(sc : Value, b : Value, ivar : Value) -> Value raise {
  // Determine if sc is a product of sin's and cos's.
  let bs = bind_all([(q_nn_star, scprod(sc, ivar)), (q_dn_star, Nil)])
  defer unbind_all(bs)
  let nn = symval(q_nn_star)
  if nn.truthy() {
    // We have a product of sin's and cos's.  We handle some special
    // cases here.
    if alike1(b, symval(q_half_pctpi)).truthy() {
      // Wang p. 110, formula (1):
      // integrate(sin(x)^m*cos(x)^n, x, 0, %pi/2) =
      //   gamma((m+1)/2)*gamma((n+1)/2)/2/gamma((n+m+2)/2)
      bygamma(car(nn), cadr(nn))
    } else if eq(b, q_d__pctpi) {
      // Wang p. 110, near the bottom, says
      //
      // int(f(sin(x),cos(x)), x, 0, %pi) =
      //   int(f(sin(x),cos(x)) + f(sin(x),-cos(x)),x,0,%pi/2)
      if eq(real_branch(cadr(nn), Fix(-1L)), q_d_yes) {
        mul2_star(
          add2_star(Fix(1L), power_star(Fix(-1L), cadr(nn))),
          bygamma(car(nn), cadr(nn)),
        )
      } else {
        Nil
      }
    } else if alike1(b, symval(q_p_pi2)).truthy() {
      // integrate(sin^m*cos^n, x, 0, 2*%pi)
      // = (1+(-1)^m)*(1+(-1)^n) * integrate(sin^m*cos^n, x, 0, %pi/2)
      let sm = exp_neg_1_real(car(nn))
      let sn = exp_neg_1_real(cadr(nn))
      if sm.truthy() && sn.truthy() {
        muln_star([
          add2_star(Fix(1L), sm),
          add2_star(Fix(1L), sn),
          bygamma(car(nn), cadr(nn)),
        ])
      } else if eq(ask_integer(car(nn), q_d_odd), q_d_yes) ||
        eq(ask_integer(cadr(nn), q_d_odd), q_d_yes) {
        Fix(0L)
      } else {
        Nil
      }
    } else if alike1(b, symval(q_half_pctpi3)).truthy() {
      // Wang, p. 111 says
      //
      // int(f(sin(x),cos(x)),x,0,3*%pi/2) =
      //   int(f(sin(x),cos(x)),x,0,%pi)
      //   + int(f(-sin(x),-cos(x)),x,0,%pi/2)
      mul2_star(
        addn_star([
          Fix(1L),
          power_star(Fix(-1L), cadr(nn)),
          power_star(Fix(-1L), addn(nn, Nil)),
        ]),
        bygamma(car(nn), cadr(nn)),
      )
    } else {
      Nil
    }
  } else if (
      eq(b, q_d__pctpi) ||
      alike1(b, symval(q_p_pi2)).truthy() ||
      alike1(b, symval(q_half_pctpi)).truthy()
    ) &&
    set(q_dn_star, scrat(sc, b, ivar)).truthy() {
    // We don't have a product of sin's and cos's.
    symval(q_dn_star)
  } else {
    let v = intsc_antideriv(sc, b, ivar)
    if v.truthy() {
      v
    } else {
      Nil
    }
  }
}

///|
/// integrate(sc, ivar, 0, b) with an antiderivative. The antiderivative
/// can depend on what is assumed about IVAR, and the assumptions in force
/// can be those of another interval, so assume 0 < IVAR < B meanwhile.
fn intsc_antideriv(sc : Value, b : Value, ivar : Value) -> Value raise {
  let old_assumptions = symval(q_ear_defint_assumptions)
  defint__up(
    fn() {
      make_defint_assumptions(q_noask, ivar, Fix(0L), b) |> ignore
      let f = antideriv(sc, ivar)
      if f.truthy() {
        sin_cos_intsubs(f, ivar, Fix(0L), b)
      } else {
        Nil
      }
    },
    fn() {
      restore_defint_assumptions(
        old_assumptions,
        symval(q_ear_defint_assumptions),
      )
      |> ignore
      set(q_ear_defint_assumptions, old_assumptions) |> ignore
    },
  )
}

///|
/// Is careful about substitution of limits where the denominator may be
/// zero because of various assumptions made.
fn sin_cos_intsubs(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if mplusp(defint__exp()).truthy() {
    let l = mapcar(e => sin_cos_intsubs1(e, ivar, ll, ul), cdr(defint__exp()))
    if !some(x => x is Nil, l) {
      addn(l, Nil)
    } else {
      Nil
    }
  } else {
    sin_cos_intsubs1(defint__exp(), ivar, ll, ul)
  }
}

///|
fn sin_cos_intsubs1(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let rat_exp = d_rat(defint__exp(), Nil)
  let denom = pdis(cddr(rat_exp))
  if equal(d_csign(denom), q_d_zero) {
    q_d_und
  } else {
    try_intsubs(defint__exp(), ll, ul, ivar)
  }
}

///|
fn try_intsubs(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b0 = bind(q_ear_nodiverg, t)
  defer unbind(b0)
  let ans = defint__catch_divergent(fn() { intsubs(defint__exp(), ll, ul, ivar) })
  if eq(ans, q_divergent) {
    Nil
  } else {
    ans
  }
}

///|
fn try_defint(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b0 = bind(q_ear_nodiverg, t)
  defer unbind(b0)
  let ans = defint__catch_divergent(fn() { defint(defint__exp(), ivar, ll, ul) })
  if eq(ans, q_divergent) {
    Nil
  } else {
    ans
  }
}

///|
/// Determine whether E is of the form sin(x)^m*cos(x)^n and return the
/// list (m n).
fn scprod(e : Value, ivar : Value) -> Value raise {
  let great_minus_1 = lfunc("great-minus-1", args => ratgreaterp(
    arg(args, 0),
    Fix(-1L),
  ))
  let mut m : Value = Nil
  let mut n : Value = Nil
  m = powerofx(e, mk(q_p_sin, [ivar]), great_minus_1, ivar)
  if m.truthy() {
    return list2(m, Fix(0L))
  }
  n = powerofx(e, mk(q_p_cos, [ivar]), great_minus_1, ivar)
  if n.truthy() {
    m = Fix(0L)
    return list2(Fix(0L), n)
  }
  if mtimesp(e).truthy() &&
    {
      m = powerofx(cadr(e), mk(q_p_sin, [ivar]), great_minus_1, ivar)
      m.truthy() ||
      {
        n = powerofx(cadr(e), mk(q_p_cos, [ivar]), great_minus_1, ivar)
        n.truthy()
      }
    } &&
    {
      if m is Nil {
        m = powerofx(caddr(e), mk(q_p_sin, [ivar]), great_minus_1, ivar)
        m.truthy()
      } else {
        n = powerofx(caddr(e), mk(q_p_cos, [ivar]), great_minus_1, ivar)
        n.truthy()
      }
    } &&
    cdddr(e) is Nil {
    return list2(m, n)
  }
  Nil
}

///|
/// Says whether (m^t value exponent) has at least one real branch.  Only
/// works for values of 1 and -1 now.  Returns $yes $no $unknown.
fn real_branch(exponent : Value, value : Value) -> Value raise {
  if equal(value, Fix(1L)) {
    q_d_yes
  } else if eq(ask_integer(exponent, q_d_integer), q_d_yes) {
    q_d_yes
  } else if ratnump(exponent).truthy() {
    if eq(d_oddp(caddr(exponent)), t) {
      q_d_yes
    } else {
      q_d_no
    }
  } else {
    q_d_unknown
  }
}

///|
/// Compute beta((m+1)/2,(n+1)/2)/2.
fn bygamma(m : Value, n : Value) -> Value raise {
  let one_half = div(Fix(1L), Fix(2L))
  mul2_star(
    one_half,
    mk(q_p_beta, [
      mul2_star(one_half, add2(Fix(1L), m)),
      mul2_star(one_half, add2(Fix(1L), n)),
    ]),
  )
}

///|
/// Seems like Guys who call this don't agree on what it should return.
fn powerofx(e : Value, x : Value, p : Value, ivar : Value) -> Value raise {
  let e : Value = if !among(ivar, e).truthy() {
    Nil
  } else if alike1(e, x).truthy() {
    Fix(1L)
  } else if atom(e) {
    Nil
  } else if mexptp(e).truthy() &&
    alike1(cadr(e), x).truthy() &&
    !among(ivar, caddr(e)).truthy() {
    caddr(e)
  } else {
    Nil
  }
  if e is Nil {
    Nil
  } else if funcall(p, [e]).truthy() {
    e
  } else {
    Nil
  }
}
