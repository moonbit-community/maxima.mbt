// Port of src/comm2.lisp: more differentiation (integrals, sums, %at,
// noncommutative powers, total differentials), atvalue/at, logcontract,
// rootscontract, nterms, fibtophi, numerval, derivdegree, boxes, scanmap,
// genmatrix, copy*, addrow/addcol, arraymake/arrayinfo, ordergreat,
// orderless, unorder and concat.

// DIFF2

///|
fn diffint(e : Value, x : Value) -> Value raise {
  if cdddr(e) is Nil {
    if alike1(x, caddr(e)).truthy() {
      return cadr(e)
    }
    if !atom(caddr(e)) && atom(x) && !free(caddr(e), x).truthy() {
      return mul2(cadr(e), sdiff(caddr(e), x))
    }
    let a = sdiff(cadr(e), x)
    if d_constantp(a).truthy() || (atom(caddr(e)) && free(a, caddr(e)).truthy()) {
      mul2(a, caddr(e))
    } else {
      simplifya(list3(list1(q_p_integrate), a, caddr(e)), t)
    }
  } else if alike1(x, caddr(e)).truthy() {
    addn(diffint1(cdr(e), x, x), t)
  } else {
    let a = sdiff(cadr(e), x)
    addn(
      cons(
        if equal(a, Fix(0L)) {
          Fix(0L)
        } else {
          simplifya(
            list([
              list1(q_p_integrate),
              a,
              caddr(e),
              cadddr(e),
              car(cddddr(e)),
            ]),
            t,
          )
        },
        diffint1(cdr(e), x, caddr(e)),
      ),
      t,
    )
  }
}

///|
fn diffint1(e : Value, x : Value, y : Value) -> Value raise {
  let u = sdiff(cadddr(e), x)
  let v = sdiff(caddr(e), x)
  list2(
    if pzerop(u).truthy() {
      Fix(0L)
    } else {
      mul2(u, maxima_substitute(cadddr(e), y, car(e)))
    },
    if pzerop(v).truthy() {
      Fix(0L)
    } else {
      mul3(v, maxima_substitute(caddr(e), y, car(e)), Fix(-1L))
    },
  )
}

///|
fn diffsumprod(e : Value, x : Value) -> Value raise {
  if !d_mapatom(x).truthy() ||
    !free(cadddr(e), x).truthy() ||
    !free(car(cddddr(e)), x).truthy() {
    diff_pctderiv(list3(e, x, Fix(1L)))
  } else if eq(caddr(e), x) {
    Fix(0L)
  } else {
    let u = sdiff(cadr(e), x)
    let u = simplifya(
      list([
        list1(q_p_sum),
        if eq(caar(e), q_p_sum) {
          u
        } else {
          div(u, cadr(e))
        },
        caddr(e),
        cadddr(e),
        car(cddddr(e)),
      ]),
      t,
    )
    if eq(caar(e), q_p_sum) {
      u
    } else {
      mul2(e, u)
    }
  }
}

///|
fn difflaplace(e : Value, x : Value) -> Value raise {
  if !atom(x) || eq(cadddr(e), x) {
    diff_pctderiv(list3(e, x, Fix(1L)))
  } else if eq(caddr(e), x) {
    Fix(0L)
  } else {
    d_laplace(sdiff(cadr(e), x), caddr(e), cadddr(e))
  }
}

///|
fn diff__pctat(e : Value, x : Value) -> Value raise {
  if freeof(x, e).truthy() {
    Fix(0L)
  } else if !freeofl(x, hand_side(caddr(e), q_r)).truthy() {
    diff_pctderiv(list3(e, x, Fix(1L)))
  } else {
    d_at(sdiff(cadr(e), x), caddr(e))
  }
}

///|
fn diffncexpt(e : Value, x : Value) -> Value raise {
  let base_star = cadr(e)
  let pow = caddr(e)
  if mnump(pow).truthy() && (!fixnump(pow) || num_lt(pow, Fix(0L))) {
    // POW cannot be 0
    diff_pctderiv(list3(e, x, Fix(1L)))
  } else if atom(base_star) && eq(base_star, x) && free(pow, base_star).truthy() {
    mul2_star(pow, list3(list1(q_mncexpt), base_star, add2(pow, Fix(-1L))))
  } else if fixnump(pow) {
    let deriv = sdiff(base_star, x)
    let mut ans : Value = Nil
    let p = to_int64(pow)
    let mut i = 0L
    while i != p {
      ans = cons(
        list3(
          list1(q_mnctimes),
          list3(list1(q_mncexpt), base_star, int64(i)),
          list3(
            list1(q_mnctimes),
            deriv,
            list3(list1(q_mncexpt), base_star, int64(p - 1L - i)),
          ),
        ),
        ans,
      )
      i += 1L
    }
    addn(ans, Nil)
  } else if !depends(pow, x).truthy() &&
    (atom(pow) || (atom(base_star) && free(pow, base_star).truthy())) {
    let deriv = sdiff(base_star, x)
    let index = gensumindex()
    simplifya(
      list([
        list1(q_p_sum),
        list3(
          list1(q_mnctimes),
          list3(list1(q_mncexpt), base_star, index),
          list3(
            list1(q_mnctimes),
            deriv,
            list3(
              list1(q_mncexpt),
              base_star,
              list4(
                list1(q_mplus),
                pow,
                Fix(-1L),
                list3(list1(q_mtimes), Fix(-1L), index),
              ),
            ),
          ),
        ),
        index,
        Fix(0L),
        list3(list1(q_mplus), pow, Fix(-1L)),
      ]),
      Nil,
    )
  } else {
    diff_pctderiv(list3(e, x, Fix(1L)))
  }
}

///|
fn stotaldiff(e : Value) -> Value raise {
  if mnump(e).truthy() || constant(e).truthy() {
    Fix(0L)
  } else if atom(e) || memq(q_array, cdar(e)).truthy() {
    let w = mget(if atom(e) { e } else { caar(e) }, q_depends)
    if w.truthy() {
      cons(
        list1(q_mplus),
        mapcar(
          x => list3(list1(q_mtimes), chainrule(e, x), list2(list1(q_p_del), x)),
          w,
        ),
      )
    } else {
      list2(list1(q_p_del), e)
    }
  } else if specrepp(e).truthy() {
    stotaldiff(specdisrep(e))
  } else if eq(caar(e), q_mnctimes) {
    with_special(q_d_dotdistrib, t, () => add2(
      ncmuln(cons(stotaldiff(cadr(e)), cddr(e)), t),
      ncmul2(cadr(e), stotaldiff(ncmuln(cddr(e), t))),
    ))
  } else if eq(caar(e), q_mncexpt) {
    if fixnump(caddr(e)) && num_gt(caddr(e), Fix(0L)) {
      stotaldiff(
        list3(
          list1(q_mnctimes),
          cadr(e),
          ncpower(cadr(e), num_sub(caddr(e), Fix(1L))),
        ),
      )
    } else {
      list2(list1(q_p_derivative), e)
    }
  } else {
    addn(
      cons(
        Fix(0L),
        mapcar(
          x => mul2(sdiff(e, x), list2(list2(q_p_del, q_simp), x)),
          extractvars(margs(e)),
        ),
      ),
      t,
    )
  }
}

///|
fn extractvars(e : Value) -> Value raise {
  if e is Nil {
    Nil
  } else if atom(car(e)) {
    if !maxima_constantp(car(e)).truthy() {
      let vars = mget(car(e), q_depends)
      if vars.truthy() {
        // The symbol has dependencies. Put the dependencies on the list of
        // extracted vars.
        union_star(vars, extractvars(cdr(e)))
      } else {
        // Put the symbol on the list of extracted vars.
        union_star(list1(car(e)), extractvars(cdr(e)))
      }
    } else {
      extractvars(cdr(e))
    }
  } else if memq(q_array, cdaar(e)).truthy() {
    union_star(list1(car(e)), extractvars(cdr(e)))
  } else {
    union_star(extractvars(cdar(e)), extractvars(cdr(e)))
  }
}

// AT

///|
fn d_atvalue(exp_ : Value, eqs : Value, val : Value) -> Value raise {
  let mut val = val
  let mut eqs = eqs
  if notloreq(eqs).truthy() {
    improper_arg_err(eqs, q_d_atvalue) |> ignore
  } else if atom(exp_) || (eq(caar(exp_), q_p_derivative) && atom(cadr(exp_))) {
    improper_arg_err(exp_, q_d_atvalue) |> ignore
  }
  let mut fun : Value = Nil
  let mut vl : Value = Nil
  let mut dl : Value = Nil
  if !eq(caar(exp_), q_p_derivative) {
    fun = caar(exp_)
    vl = cdr(exp_)
    let c = Collector::new()
    for _ in vl.iter() {
      c.add(Fix(0L))
    }
    dl = c.result()
  } else {
    fun = caaadr(exp_)
    vl = cdadr(exp_)
    for v in vl.iter() {
      let d = getf(cddr(exp_), v)
      dl = nconc(dl, list1(if d.truthy() { d } else { Fix(0L) }))
    }
  }
  if mopp(fun).truthy() || eq(fun, q_mqapply) {
    improper_arg_err(exp_, q_d_atvalue) |> ignore
  }
  atvarschk(vl) |> ignore
  let mut vl1 = vl
  let mut l = symval(q_atvars)
  while vl1 is Cons(_) {
    if symbolp(car(vl1)) && !kindp(car(vl1), q_d_constant).truthy() {
      val = maxima_substitute(car(l), car(vl1), val)
    } else {
      improper_arg_err(cons(list1(q_mlist), vl), q_d_atvalue) |> ignore
    }
    vl1 = cdr(vl1)
    l = cdr(l)
  }
  eqs = if eq(caar(eqs), q_mequal) { list1(eqs) } else { cdr(eqs) }
  let mut l2 : Value = Nil
  for eqn in eqs.iter() {
    if !memq(cadr(eqn), vl).truthy() {
      improper_arg_err(eqn, q_d_atvalue) |> ignore
    }
    l2 = nconc(l2, list1(cons(cadr(eqn), caddr(eqn))))
  }
  let eqs = l2
  let mut l3 : Value = Nil
  for v in vl.iter() {
    let a = assq(v, eqs)
    l3 = nconc(
      l3,
      list1(
        cdr(
          if a.truthy() {
            a
          } else {
            cons(Nil, symval(q_munbound))
          },
        ),
      ),
    )
  }
  let vl = l3
  let mut atvalues = mget(fun, q_atvalues)
  let mut found = false
  while atvalues is Cons(_) {
    if equal(caar(atvalues), dl) && equal(cadar(atvalues), vl) {
      rplaca(cddar(atvalues), val) |> ignore
      found = true
      break
    }
    atvalues = cdr(atvalues)
  }
  if !found {
    mputprop(fun, cons(list3(dl, vl, val), mget(fun, q_atvalues)), q_atvalues)
    |> ignore
  }
  add2lnc(fun, symval(q_d_props)) |> ignore
  val
}

///|
fn simp__pctat(expr : Value, ignored : Value, simp_flag : Value) -> Value raise {
  ignore(ignored)
  twoargcheck(expr) |> ignore
  let arg = simpcheck(cadr(expr), simp_flag)
  let e = resimplify(caddr(expr))
  let eqn = if d_listp(e).truthy() {
    if num_eq(d_length(e), Fix(1L)) {
      d_first(e)
    } else {
      cons(list2(q_mlist, q_simp), cdr(d_sort(e)))
    }
  } else {
    e
  }
  if d_constantp(arg).truthy() {
    arg
  } else if alike1(eqn, list1(list1(q_mlist))).truthy() {
    arg
  } else {
    let r = at_not_dependent(eqn, arg)
    if r.truthy() {
      r
    } else {
      eqtest(list3(list1(q_p_at), arg, eqn), expr)
    }
  }
}

///|
/// Remove any variable from EQN if ARG is not dependent on it.
fn at_not_dependent(eqn : Value, arg : Value) -> Value raise {
  let eqn = if eq(caar(eqn), q_mequal) {
    list2(list1(q_mlist), eqn)
  } else {
    eqn
  }
  let (e0, e1) = at_not_dependent_find_vars_mv(eqn, arg)
  if e0.truthy() {
    if e1.truthy() {
      let e1 = mapcar(x => list3(list1(q_mequal), x, d_assoc(x, eqn)), e1)
      let eqn1 = if length(e1) == 1 {
        first(e1)
      } else {
        cons(list1(q_mlist), e1)
      }
      ftake_star(q_p_at, [arg, eqn1])
    } else {
      arg
    }
  } else {
    Nil
  }
}

///|
/// Test dependence via derivative to account for declared dependencies.
/// Returns 2 values; the declared function returns the primary one.
fn at_not_dependent_find_vars(eqn : Value, arg : Value) -> Value raise {
  at_not_dependent_find_vars_mv(eqn, arg).0
}

///|
fn at_not_dependent_find_vars_mv(eqn : Value, arg_ : Value) -> (Value, Value) raise {
  let e = mapcar(x => second(x), rest(eqn))
  partition_by(
    lfunc("at-not-dependent-find-vars-1", a => at_not_dependent_find_vars_1(
      arg(a, 0),
      arg_,
    )),
    e,
  )
}

///|
fn at_not_dependent_find_vars_1(x : Value, arg : Value) -> Value raise {
  if d_mapatom(x).truthy() {
    lbool(eql(mfuncall(q_d_diff, list2(arg, x)), Fix(0L)))
  } else {
    // We might be called with something like -1*x as the variable. Try to
    // extract a variable and test for dependence on that. If there are 2
    // or more variables, return NIL (i.e., not at-not-dependent).
    let v = d_listofvars(x)
    if eql(d_length(v), Fix(1L)) {
      at_not_dependent_find_vars_1(d_first(v), arg)
    } else {
      Nil
    }
  }
}

///|
fn d_at(expr : Value, ateqs : Value) -> Value raise {
  if notloreq(ateqs).truthy() {
    improper_arg_err(ateqs, q_d_at) |> ignore
  }
  atscan(with_special(q_ear_atp, t, () => d_psubstitute(ateqs, expr)), ateqs)
}

///|
fn atscan(expr : Value, ateqs : Value) -> Value raise {
  if atom(expr) ||
    eq(caar(expr), q_mrat) ||
    like(ateqs, list1(list1(q_mlist))).truthy() {
    expr
  } else if eq(caar(expr), q_p_derivative) {
    let r = if !atom(cadr(expr)) {
      let vl = cdadr(expr)
      let mut dl : Value = Nil
      for v in vl.iter() {
        let d = getf(cddr(expr), v)
        dl = nconc(dl, list1(if d.truthy() { d } else { Fix(0L) }))
      }
      atfind(
        caaadr(expr),
        cdr(d_psubstitute(ateqs, cons(list1(q_mlist), vl))),
        dl,
      )
    } else {
      Nil
    }
    if r.truthy() {
      r
    } else {
      list3(list1(q_p_at), expr, ateqs)
    }
  } else if memq(caar(expr), symval(q_dummy_variable_operators)).truthy() {
    list3(list1(q_p_at), expr, ateqs)
  } else {
    let r = at1(expr)
    if r.truthy() {
      r
    } else {
      recur_apply(lfunc("atscan", a => atscan(arg(a, 0), ateqs)), expr)
    }
  }
}

///|
fn at1(expr : Value) -> Value raise {
  let c = Collector::new()
  for _ in cdr(expr).iter() {
    c.add(Fix(0L))
  }
  atfind(caar(expr), cdr(expr), c.result())
}

///|
fn atfind(fun : Value, vl : Value, dl : Value) -> Value raise {
  let mut atvalues = mget(fun, q_atvalues)
  while atvalues is Cons(_) {
    if equal(caar(atvalues), dl) {
      let mut l = cadar(atvalues)
      let mut v = vl
      let mut ok = true
      while l is Cons(_) {
        if !equal(car(l), car(v)) && !eq(car(l), symval(q_munbound)) {
          ok = false
          break
        }
        l = cdr(l)
        v = cdr(v)
      }
      if ok {
        atvarschk(vl) |> ignore
        return substitutel(vl, symval(q_atvars), caddar(atvalues))
      }
    }
    atvalues = cdr(atvalues)
  }
  Nil
}

///|
fn d_logcontract(e : Value) -> Value raise {
  // E is assumed to be simplified.
  lgcreciprocal(logcon(e))
}

///|
fn logcon(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    let e = if !lgcsimplep(e).truthy() { lgcsort(e) } else { e }
    if mplusp(e).truthy() {
      lgcplus(e)
    } else if mtimesp(e).truthy() {
      lgctimes(e)
    } else {
      logcon(e)
    }
  } else {
    recur_apply(lfunc("logcon", a => logcon(arg(a, 0))), e)
  }
}

///|
/// The logcontract algorithm for a sum.
///
/// The function accumulates the arguments of things like log(a)+log(b)
/// into a list called LOG. It calls out to lgctimes to deal with things
/// like a*log(b). When all the arguments have been processed, it simplifies
/// all the logarithmic arguments using sratsimp.
fn lgcplus(e : Value) -> Value raise {
  let mut log : Value = Nil
  let mut notlogs : Value = Nil
  for arg in cdr(e).iter() {
    if atom(arg) {
      notlogs = cons(arg, notlogs)
    } else if eq(caar(arg), q_p_log) && !memq(q_array, car(arg)).truthy() {
      // Only gather up log(x), not log[x].
      log = cons(logcon(second(arg)), log)
    } else if eq(caar(arg), q_mtimes) {
      let y = lgctimes(arg)
      if atom(y) || !eq(caar(y), q_p_log) {
        notlogs = cons(y, notlogs)
      } else {
        log = cons(cadr(y), log)
      }
    } else {
      notlogs = cons(logcon(arg), notlogs)
    }
  }
  if log is Nil {
    subst0(cons(list1(q_mplus), nreverse(notlogs)), e)
  } else {
    let l = log
    let simplified_log = lgcsimp(
      with_special(q_d_ratfac, t, () => sratsimp(muln(l, t))),
    )
    addn(cons(simplified_log, notlogs), t)
  }
}

///|
/// The logcontract algorithm for a product
///
/// The main transformation this does is of the form 3*log(x) => log(x^3).
/// To make this work, we find the first %log term and insert any
/// coefficients we find into that. Coefficients are identified by
/// LOGCONCOEFFP, which checks the $LOGCONCOEFFP user variable.
fn lgctimes(e : Value) -> Value raise {
  // Apply logcontract to the arguments. It's possible that the subsequent
  // simplification means that the result isn't a product any more. In
  // that case, just return it.
  let e = subst0(cons(list1(q_mtimes), mapcar(x => logcon(x), cdr(e))), e)
  if !mtimesp(e).truthy() {
    return e
  }
  let mut log : Value = Nil
  let mut notlogs : Value = Nil
  let mut decints : Value = Nil
  for arg in cdr(e).iter() {
    if log is Nil &&
      !atom(arg) &&
      eq(caar(arg), q_p_log) &&
      !equal(cadr(arg), Fix(-1L)) {
      log = cadr(arg)
    } else if logconcoeffp(arg).truthy() {
      decints = cons(arg, decints)
    } else {
      notlogs = cons(arg, notlogs)
    }
  }
  if log is Nil || decints is Nil {
    e
  } else {
    muln(cons(lgcsimp(power(log, muln(decints, t))), notlogs), t)
  }
}

///|
fn lgcsimp(e : Value) -> Value raise {
  if atom(e) {
    // e.g. log(1) -> 0, or log(%e) -> 1
    simplify(list2(list1(q_p_log), e))
  } else if mexptp(e).truthy() && eq(cadr(e), q_d__pcte) {
    // log(%e^expr) -> expr
    simplify(list2(list1(q_p_log), e))
  } else {
    list2(list2(q_p_log, q_simp), e)
  }
}

///|
/// Tests that its argument is a sum of terms that are "simple". A "simple"
/// term is either completely free of logarithms, is a logarithm itself, or
/// is a number times a logarithm. This function assumes that its argument
/// is not an atom.
fn lgcsimplep(e : Value) -> Value raise {
  let lgc_nonsimple_arg_p = (arg : Value) => !(
      atom(arg) ||
      eq(caar(arg), q_p_log) ||
      !isinop(arg, q_p_log).truthy() ||
      // Product of a number with a logarithm e.g. 3*log(x)
      (
        eq(caar(arg), q_mtimes) &&
        cdddr(arg) is Nil &&
        mnump(cadr(arg)).truthy() &&
        !atom(caddr(arg)) &&
        eq(caar(caddr(arg)), q_p_log)
      )
    )
  lbool(eq(caar(e), q_mplus) && !some(lgc_nonsimple_arg_p, cdr(e)))
}

///|
/// Sort the argument so that coefficients come before logarithms and
/// logarithms come before everything else.
fn lgcsort(e : Value) -> Value raise {
  with_special(q_varlist, Nil, () => {
    let mut logs : Value = Nil
    let mut notlogs : Value = Nil
    let mut decints : Value = Nil
    // Split the variables in E into logs, notlogs and coefficients. The
    // list of variables is calculated by NEWVAR (and stored in the special
    // variable VARLIST, which is why we have to bind it above).
    for var_ in newvar(e).iter() {
      if !atom(var_) && eq(caar(var_), q_p_log) {
        logs = cons(var_, logs)
      } else if logconcoeffp(var_).truthy() {
        decints = cons(var_, decints)
      } else {
        notlogs = cons(var_, notlogs)
      }
    }
    let vl = nreconc(
      decints,
      nconc(sort_list(logs, (a, b) => great(a, b).truthy()), nreverse(notlogs)),
    )
    let e1 = ratdisrep(ratrep(e, vl))
    if alike1(e, e1).truthy() {
      e
    } else {
      e1
    }
  })
}

///|
/// lgcreciprocal performs the transformation log(1/x) => -log(x)
fn lgcreciprocal(e : Value) -> Value raise {
  if atom(e) {
    return e
  }
  if eq(caar(e), q_p_log) {
    let num = member_equal(d_num(cadr(e)), list2(Fix(1L), Fix(-1L)))
    if num.truthy() {
      let denom = d_denom(cadr(e))
      if !equal(denom, Fix(1L)) {
        return list3(
          list2(q_mtimes, q_simp),
          Fix(-1L),
          list2(
            list2(q_p_log, q_simp),
            if num_eq(car(num), Fix(1L)) {
              denom
            } else {
              neg(denom)
            },
          ),
        )
      }
    }
  }
  recur_apply(lfunc("lgcreciprocal", a => lgcreciprocal(arg(a, 0))), e)
}

///|
fn logconcoeffp(e : Value) -> Value raise {
  if symval(q_d_logconcoeffp).truthy() {
    is_(list2(list1(q_d_logconcoeffp), e))
  } else {
    maxima_integerp(e)
  }
}

// RTCON

///|
fn d_rootscontract(e : Value) -> Value raise {
  // E is assumed to be simplified
  let radexpand = symval(q_d_radexpand)
  let radpe = radexpand.truthy() &&
    !eq(radexpand, q_d_all) &&
    eq(symval(q_d_domain), q_d_real)
  with_special(q_d_radexpand, Nil, () => rtcon(e, lbool(radpe)))
}

///|
fn rtcon(e : Value, radpe : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mtimes) {
    let mut roots : Value = Nil
    let mut notroots : Value = Nil
    for x in cdr(e).iter() {
      if atom(x) {
        if eq(x, q_d__pcti) {
          roots = rt_separ(list2(Fix(2L), Fix(-1L)), roots)
        } else {
          notroots = cons(x, notroots)
        }
      } else if eq(caar(x), q_mexpt) && ratnump(caddr(x)).truthy() {
        let y = caddr(x)
        roots = rt_separ(
          list2(caddr(y), list3(list1(q_mexpt), rtcon(cadr(x), radpe), cadr(y))),
          roots,
        )
      } else if radpe.truthy() && eq(caar(x), q_mabs) {
        roots = rt_separ(
          list3(
            Fix(2L),
            list3(list1(q_mexpt), rtcon(cadr(x), radpe), Fix(2L)),
            Fix(1L),
          ),
          roots,
        )
      } else {
        notroots = cons(rtcon(x, radpe), notroots)
      }
    }
    if roots is Nil {
      subst0(cons(list1(q_mtimes), nreverse(notroots)), e)
    } else {
      let mode = symval(q_d_rootsconmode)
      if mode.truthy() {
        let (min, gcd_, lcm_) = rtc_getinfo(roots)
        if num_eq(min, gcd_) &&
          !num_eq(gcd_, Fix(1L)) &&
          !num_eq(min, lcm_) &&
          !eq(mode, q_d_all) {
          roots = rt_separ(
            list3(
              gcd_,
              rtcon(rtc_fixitup(rtc_divide_by_gcd(roots, gcd_), Nil), radpe),
              Fix(1L),
            ),
            Nil,
          )
        } else if eq(mode, q_d_all) {
          roots = rt_separ(simp_roots(lcm_, roots), Nil)
        }
      }
      rtc_fixitup(roots, notroots)
    }
  } else if radpe.truthy() && eq(caar(e), q_mabs) {
    power(power(rtcon(cadr(e), radpe), Fix(2L)), mk_simp(q_rat, [Fix(1L), Fix(2L)]))
  } else {
    recur_apply(lfunc("rtcon", a => rtcon(arg(a, 0), radpe)), e)
  }
}

///|
/// RT-SEPAR separates like roots into their appropriate "buckets", where a
/// bucket looks like:
/// ((<denom of power> (<term to be raised> <numer of power>)
///                    (<term> <numer>)) etc)
fn rt_separ(a : Value, roots : Value) -> Value raise {
  let u = assoc_equal(car(a), roots)
  if u.truthy() {
    nconc(u, cdr(a)) |> ignore
    roots
  } else {
    cons(a, roots)
  }
}

///|
fn simp_roots(lcm_ : Value, root_list : Value) -> Value raise {
  let mut root1 : Value = Nil
  for x in root_list.iter() {
    root1 = cons(
      list3(list1(q_mexpt), muln(cdr(x), Nil), num_truncate(lcm_, b=car(x)).0),
      root1,
    )
  }
  cons(lcm_, root1)
}

///|
fn rtc_getinfo(list_ : Value) -> (Value, Value, Value) raise {
  let mut m = caar(list_)
  let mut g = caar(list_)
  let mut l = caar(list_)
  for x in cdr(list_).iter() {
    m = num_min(m, car(x))
    g = num_gcd(g, car(x))
    l = num_lcm(l, car(x))
  }
  (m, g, l)
}

///|
fn rtc_fixitup(roots : Value, notroots : Value) -> Value raise {
  let flag = lbool(!symval(q_d_rootsconmode).truthy())
  for x in roots.iter() {
    rplacd(x, list1(sratsimp(muln(cdr(x), flag)))) |> ignore
  }
  muln(
    nconc(
      mapcar(x => power_star(cadr(x), mk(q_rat, [Fix(1L), car(x)])), roots),
      notroots,
    ),
    flag,
  )
}

///|
fn rtc_divide_by_gcd(llist : Value, gcd_ : Value) -> Value raise {
  for x in llist.iter() {
    rplaca(x, num_truncate(car(x), b=gcd_).0) |> ignore
  }
  llist
}

///|
fn d_nterms(e : Value) -> Value raise {
  if zerop1(e).truthy() {
    Fix(0L)
  } else if atom(e) {
    Fix(1L)
  } else if eq(caar(e), q_mtimes) {
    let e = if equal(Fix(-1L), cadr(e)) { cdr(e) } else { e }
    let mut c : Value = Fix(1L)
    for x in cdr(e).iter() {
      c = num_mul(c, d_nterms(x))
    }
    c
  } else if eq(caar(e), q_mplus) {
    let mut c : Value = Fix(0L)
    for x in cdr(e).iter() {
      c = num_add(c, d_nterms(x))
    }
    c
  } else if eq(caar(e), q_mexpt) && integerp(caddr(e)) && plusp(caddr(e)) {
    ftake(q_p_binomial, [
      num_add(num_add(caddr(e), d_nterms(cadr(e))), Fix(-1L)),
      caddr(e),
    ])
  } else if specrepp(e).truthy() {
    d_nterms(specdisrep(e))
  } else {
    Fix(1L)
  }
}

// ARITHF

///|
fn d_fibtophi(e : Value, lnorecurse? : Value = Nil) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_d_fib) {
    let e = if lnorecurse.truthy() {
      cadr(e)
    } else {
      d_fibtophi(cadr(e), lnorecurse~)
    }
    let phi = meval(q_d__pctphi)
    div(
      add2(power(phi, e), neg(power(add2(Fix(1L), neg(phi)), e))),
      add2(Fix(-1L), mul2(Fix(2L), phi)),
    )
  } else {
    recur_apply(lfunc("$fibtophi", a => d_fibtophi(arg(a, 0), lnorecurse~)), e)
  }
}

///|
fn d_numerval(l : Value) -> Value raise {
  let mut l = cdr(l)
  let x = list1(list2(q_mlist, q_simp))
  while l is Cons(_) {
    if cdr(l) is Nil {
      merr("numerval: expected an even number of arguments.", []) |> ignore
    } else if !symbolp(car(l)) {
      merr("numerval: expected a symbol; found ~M", [car(l)]) |> ignore
    } else if boundp(car(l)) {
      merr("numerval: cannot declare a value because ~M is bound.", [car(l)])
      |> ignore
    }
    mputprop(car(l), cadr(l), q_d_numer) |> ignore
    add2lnc(car(l), symval(q_d_props)) |> ignore
    nconc(x, list1(car(l))) |> ignore
    l = cddr(l)
  }
  x
}

///|
/// MY-POWERS is a special variable bound by $DERIVDEGREE.
fn d_derivdegree(e : Value, depvar : Value, var_ : Value) -> Value raise {
  with_special(q_my_powers, Nil, () => {
    derivdeg1(e, depvar, var_) |> ignore
    if symval(q_my_powers) is Nil {
      Fix(0L)
    } else {
      maximin(symval(q_my_powers), q_d_max)
    }
  })
}

///|
fn derivdeg1(e : Value, depvar : Value, var_ : Value) -> Value raise {
  if atom(e) || specrepp(e).truthy() {
    t
  } else if eq(caar(e), q_p_derivative) {
    if alike1(cadr(e), depvar).truthy() {
      let mut l = cddr(e)
      while l is Cons(_) {
        if alike1(car(l), var_).truthy() {
          return set(q_my_powers, cons(cadr(l), symval(q_my_powers)))
        }
        l = cddr(l)
      }
    }
    Nil
  } else {
    for x in cdr(e).iter() {
      derivdeg1(x, depvar, var_) |> ignore
    }
    cdr(e)
  }
}

// BOX

///|
fn d_dpart(args : Value) -> Value raise {
  mpart(args, Nil, t, Nil, q_d_dpart)
}

///|
fn d_lpart(e : Value, args : Value) -> Value raise {
  mpart(args, Nil, list1(e), Nil, q_d_lpart)
}

///|
fn make_mbox(e : Value, l? : Value) -> Value raise {
  match l {
    Some(l) => list3(list1(q_mlabox), e, box_label(l))
    None => list2(list1(q_mbox), e)
  }
}

///|
fn box_label(x : Value) -> Value raise {
  if atom(x) {
    x
  } else {
    Str(char_list_to_string(mstring(x)))
  }
}

///|
fn d_rembox(e : Value, l? : Value) -> Value raise {
  let label = match l {
    Some(l) => box_label(l)
    None => list1(Nil)
  }
  rembox1(e, label)
}

///|
fn rembox1(e : Value, label : Value) -> Value raise {
  if atom(e) {
    e
  } else if (
      eq(caar(e), q_mbox) &&
      (
        equal(label, list1(Nil)) ||
        eq(label, q_d_unlabelled) ||
        eq(label, q_d_unlabeled)
      )
    ) ||
    (
      eq(caar(e), q_mlabox) &&
      (equal(label, list1(Nil)) || equal(label, caddr(e)))
    ) {
    rembox1(cadr(e), label)
  } else {
    recur_apply(lfunc("rembox1", a => rembox1(arg(a, 0), label)), e)
  }
}

// MAPF

///|
/// defmspec ($scanmap :properties ((evok t)))
fn comm2__d_scanmap(l : Value) -> Value raise {
  with_special(q_scanmapp, t, () => {
    let m = mmapev(l)
    let n = length(m)
    if n < 2 || n > 3 {
      raise LispError::SimpleError(
        "invalid number of arguments to SCANMAP1: " + n.to_string(),
      )
    }
    resimplify(
      if n == 3 {
        scanmap1(car(m), cadr(m), flag=caddr(m))
      } else {
        scanmap1(car(m), cadr(m))
      },
    )
  })
}

///|
fn scanmap1(func : Value, e : Value, flag? : Value) -> Value raise {
  match flag {
    Some(f) =>
      if !(eq(f, q_d_bottomup) || eq(f, q_d_topdown)) {
        merr(
          "scanmap: third argument must be 'bottomup' or 'topdown', if present; found ~M",
          [f],
        )
        |> ignore
      }
    None => ()
  }
  let flag = flag.unwrap_or(Nil)
  let arg2 = specrepcheck(e)
  if eq(func, q_d_rat) {
    merr("scanmap: cannot apply 'rat'.", [])
  } else if eq(flag, q_d_bottomup) {
    if mapatom(arg2).truthy() {
      funcer(func, list1(arg2))
    } else {
      subst0(
        funcer(
          func,
          list1(
            mcons_op_args(
              mop(arg2),
              mapcar(u => scanmap1(func, u, flag=q_d_bottomup), margs(arg2)),
            ),
          ),
        ),
        arg2,
      )
    }
  } else if mapatom(arg2).truthy() {
    funcer(func, list1(arg2))
  } else {
    let newarg2 = specrepcheck(funcer(func, list1(arg2)))
    if mapatom(newarg2).truthy() {
      newarg2
    } else if alike1(cadr(newarg2), arg2).truthy() && cddr(newarg2) is Nil {
      subst0(
        cons(
          list1(caar(newarg2)),
          list1(
            subst0(
              mcons_op_args(mop(arg2), mapcar(u => scanmap1(func, u), margs(arg2))),
              arg2,
            ),
          ),
        ),
        newarg2,
      )
    } else {
      subst0(
        mcons_op_args(
          mop(newarg2),
          mapcar(u => scanmap1(func, u), margs(newarg2)),
        ),
        newarg2,
      )
    }
  }
}

///|
/// This function does mapping of subscripts.
fn subgen(form : Value) -> Value raise {
  let mut ds = if eq(caar(form), q_mqapply) {
    list2(car(form), cadr(form))
  } else {
    list1(car(form))
  }
  let mut sub = reverse(
    if eq(q_mqapply, caar(form)) && cddr(form).truthy() {
      cddr(form)
    } else {
      cdr(form)
    },
  )
  while sub is Cons(_) {
    ds = outermap1(list3(q_dsfunc1, simplify(car(sub)), ds))
    sub = cdr(sub)
  }
  ds
}

///|
fn dsfunc1(dsn : Value, dso : Value) -> Value raise {
  if atom(dso) || atom(car(dso)) {
    dso
  } else if memq(q_array, car(dso)).truthy() {
    if eq(q_mqapply, caar(dso)) {
      nconc(list3(car(dso), cadr(dso), dsn), cddr(dso))
    } else {
      nconc(list2(car(dso), dsn), cdr(dso))
    }
  } else {
    mapcar(d => dsfunc1(dsn, d), dso)
  }
}

// GENMAT

///|
/// GENMATRIX is improved in order to save time when creating a large
/// matrix. see SF bug #4056
fn d_genmatrix(
  a : Value,
  i2 : Value,
  j2? : Value,
  i1? : Value = Fix(1L),
  j1? : Value,
) -> Value raise {
  let j2 = j2.unwrap_or(i2)
  let j1 = j1.unwrap_or(i1)
  let f = if symbolp(a) || hash_table_p(a) || arrayp(a) {
    (i : Value, j : Value) => meval(list3(list2(a, q_array), i, j))
  } else {
    (i : Value, j : Value) => mfuncall(a, list2(i, j))
  }
  if !(fixnump(i2) && fixnump(j2) && fixnump(i1) && fixnump(j1)) {
    merr("genmatrix: bounds must be integers; found ~M, ~M, ~M, ~M", [
      i2, j2, i1, j1,
    ])
    |> ignore
  }
  if num_gt(i1, i2) || num_gt(j1, j2) {
    merr(
      "genmatrix: upper bounds must be greater than or equal to lower bounds; found ~M, ~M, ~M, ~M",
      [i2, j2, i1, j1],
    )
    |> ignore
  }
  let rows = Collector::new()
  let mut i = to_int64(i1)
  while i <= to_int64(i2) {
    let row = Collector::new()
    let mut j = to_int64(j1)
    while j <= to_int64(j2) {
      row.add(f(int64(i), int64(j)))
      j += 1L
    }
    rows.add(cons(list1(q_mlist), row.result()))
    i += 1L
  }
  cons(list1(q_d_matrix), rows.result())
}

///|
/// Execute deep copy for copymatrix and copylist.
fn d_copymatrix(x : Value) -> Value raise {
  if !d_matrixp(x).truthy() {
    merr("copymatrix: argument must be a matrix; found ~M", [x]) |> ignore
  }
  copy_tree(x)
}

///|
fn d_copylist(x : Value) -> Value raise {
  if !d_listp(x).truthy() {
    merr("copylist: argument must be a list; found ~M", [x]) |> ignore
  }
  copy_tree(x)
}

///|
fn d_copy(x : Value) -> Value raise {
  copy_tree(x)
}

// ADDROW

///|
fn d_addrow(m : Value, rows : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("addrow: first argument must be a matrix; found ~M", [m])
  } else if rows is Nil {
    m
  } else {
    let mut m = copy_tree(m)
    for r in rows.iter() {
      m = addrow(m, r)
    }
    m
  }
}

///|
fn d_addcol(m : Value, cols : Value) -> Value raise {
  if !d_matrixp(m).truthy() {
    merr("addcol: first argument must be a matrix; found ~M", [m])
  } else if cols is Nil {
    m
  } else if cdr(m) is Nil {
    d_addcol(ensure_matrix_column(first(cols)), rest(cols))
  } else {
    let mut m = d_transpose(m)
    for c in cols.iter() {
      m = addrow(m, d_transpose(c))
    }
    d_transpose(m)
  }
}

///|
fn ensure_matrix_column(a : Value) -> Value raise {
  if d_matrixp(a).truthy() {
    a
  } else {
    // otherwise must be a MLIST.
    cons(list1(q_d_matrix), mapcar(e => list2(list1(q_mlist), e), cdr(a)))
  }
}

///|
fn addrow(m : Value, r : Value) -> Value raise {
  let mut r = r
  if !mxorlistp(r).truthy() {
    merr("addrow or addcol: argument must be a matrix or list; found ~M", [r])
    |> ignore
  } else if cdr(m).truthy() &&
    (
      (eq(caar(r), q_mlist) && length(cadr(m)) != length(r)) ||
      (
        eq(caar(r), q_d_matrix) &&
        length(cadr(m)) != length(cadr(r)) &&
        {
          r = d_transpose(r)
          length(cadr(m)) != length(cadr(r))
        }
      )
    ) {
    merr("addrow or addcol: incompatible structure.", []) |> ignore
  }
  append(
    m,
    if eq(caar(r), q_d_matrix) {
      cdr(r)
    } else {
      list1(r)
    },
  )
}

// ARRAYF

///|
fn my_nonatomic_expr_p(e : Value) -> Value raise {
  lbool(consp(e) && consp(car(e)) && symbolp(caar(e)))
}

///|
fn my_lambda_expr_p(e : Value) -> Value raise {
  lbool(consp(e) && consp(car(e)) && eq(q_lambda, caar(e)))
}

///|
fn d_arraymake(ary : Value, subs : Value) -> Value raise {
  // We go through some gyrations here to allow as wide a range of inputs
  // as possible.
  if !(
      symbolp(ary) ||
      d_subvarp(ary).truthy() ||
      (
        my_nonatomic_expr_p(ary).truthy() &&
        !my_lambda_expr_p(ary).truthy()
      )
    ) {
    merr(
      "arraymake: first argument must be a symbol, subscripted symbol, or nonatomic expression (but not a lambda expression); found: ~M",
      [ary],
    )
  } else if !d_listp(subs).truthy() || cdr(subs) is Nil {
    merr(
      "arraymake: second argument must be a list of one or more elements; found ~M",
      [subs],
    )
  } else if symbolp(ary) {
    cons(cons(getopr(ary), list1(q_array)), cdr(subs))
  } else {
    cons(list2(q_mqapply, q_array), cons(ary, cdr(subs)))
  }
}

///|
fn d_arrayinfo(e : Value) -> Value raise {
  let ary = second(e)
  let ary_value = if arrayp(ary) || hash_table_p(ary) {
    ary
  } else {
    getvalue(ary)
  }
  arrayinfo_aux(ary, ary_value)
}

///|
fn arrayinfo_aux(sym_ : Value, val : Value) -> Value raise {
  let arra = val
  let ary = sym_
  if arra.truthy() &&
    (
      hash_table_p(arra) ||
      arrayp(arra) ||
      eq(marray_type(arra), q_d_functional)
    ) {
    if hash_table_p(arra) {
      let dim1 = gethash(q_dim1, arra)
      let keys = Collector::new()
      maphash(
        (u, _) => if !eq(u, q_dim1) {
          keys.add(
            if dim1.truthy() {
              u
            } else {
              cons(list2(q_mlist, q_simp), u)
            },
          )
        },
        arra,
      )
      return list_star([
        list1(q_mlist),
        q_d_hash_table,
        if dim1.truthy() {
          Fix(1L)
        } else {
          t
        },
        keys.result(),
      ])
    } else if arrayp(arra) {
      let dims = array_dimensions(arra)
      return list4(
        list1(q_mlist),
        q_d_declared,
        int(length(dims)),
        cons(list1(q_mlist), mapcar(d => one_minus(d), dims)),
      )
    } else {
      return arrayinfo_aux(sym_, struct_ref(arra, 5))
    }
  }
  let gen = safe_mgetl(sym_, list2(q_hashar, q_array))
  if gen is Nil {
    merr("arrayinfo: ~M is not an array.", [ary]) |> ignore
  }
  let ary1 = cadr(gen)
  if eq(car(gen), q_hashar) {
    let ary1 = get(ary1, q_array)
    let mut l : Value = Nil
    let n = to_int(cadr(arraydims(ary1)))
    for i in 3..<n {
      for l1 in aref1(ary1, i).iter() {
        l = cons(cons(list2(q_mlist, q_simp), car(l1)), l)
      }
    }
    append(
      list2(list2(q_mlist, q_simp), q_d_hashed),
      cons(aref1(ary1, 2), sort_list(l, (x, y) => great(y, x).truthy())),
    )
  } else {
    let ary1 = arraydims(ary1)
    list4(
      list2(q_mlist, q_simp),
      if safe_get(ary, q_array).truthy() {
        let et = car(ary1)
        if eq(et, t) {
          q_d_complete
        } else if eq(et, q_fixnum) {
          q_d_integer
        } else if eq(et, q_flonum) {
          q_d_float
        } else {
          Nil
        }
      } else {
        q_d_declared
      },
      int(length(cdr(ary1))),
      cons(list2(q_mlist, q_simp), mapcar(d => one_minus(d), cdr(ary1))),
    )
  }
}

// ALIAS

///|
fn d_ordergreat(l : Value) -> Value raise {
  if symval(q_greatorder).truthy() {
    merr("ordergreat: reordering is not allowed.", []) |> ignore
  }
  makorder(set(q_greatorder, reverse(cdr(l))), q_op_u_)
}

///|
fn d_orderless(l : Value) -> Value raise {
  if symval(q_lessorder).truthy() {
    merr("orderless: reordering is not allowed.", []) |> ignore
  }
  makorder(set(q_lessorder, cdr(l)), q_op_hash)
}

///|
fn makorder(l : Value, char_ : Value) -> Value raise {
  let mut n = 101
  for x in l.iter() {
    alias(
      x,
      implode(
        nconc_n([list1(char_), mexploden(int(n)), exploden(stripdollar(x))]),
      ),
    )
    |> ignore
    n += 1
  }
  q_d_done
}

///|
fn d_unorder() -> Value raise {
  let l = delete(
    Nil,
    cons(
      list2(q_mlist, q_simp),
      nconc(
        mapcar(x => remalias(getalias(x)), symval(q_lessorder)),
        mapcar(x => remalias(getalias(x)), symval(q_greatorder)),
      ),
    ),
  )
  set(q_lessorder, Nil) |> ignore
  set(q_greatorder, Nil) |> ignore
  l
}

// CONCAT

///|
/// Concatenates its arguments. The arguments must evaluate to atoms. The
/// return value is a symbol if the first argument is a symbol and a string
/// otherwise.
fn d_concat(l : Value) -> Value raise {
  if l is Nil {
    merr("concat: there must be at least one argument.", []) |> ignore
  }
  let result_is_a_string = numberp(car(l)) || stringp(car(l))
  let l = mapcan(
    x => {
      if !atom(x) {
        merr("concat: argument must be an atom; found ~M", [x]) |> ignore
      }
      copy_list(string_star(x))
    },
    l,
  )
  if result_is_a_string {
    Str(char_list_to_string(l))
  } else {
    getalias(implode(cons(Char('$'), l)))
  }
}

///|
fn init_comm2() -> Unit raise {
  putprop(q_p_at, q_simp__pctat, q_operators) |> ignore
  putprop(q_d_logcontract, t, q_evfun) |> ignore
  putprop(q_d_rootscontract, t, q_evfun) |> ignore
  // Alias makes `box` in input parse to symbol MBOX.
  putprop(q_d_box, q_mbox, q_alias) |> ignore
  // Reverse alias makes MBOX and MLABOX display as box in 1-d output.
  putprop(q_mbox, q_d_box, q_reversealias) |> ignore
  putprop(q_mlabox, q_d_box, q_reversealias) |> ignore
  putprop(
    q_mbox,
    lfunc("mbox-simp", args => {
      let x = arg(args, 0)
      let z = arg(args, 2)
      let mbox_args = if z.truthy() {
        cdr(x)
      } else {
        mapcar(a => simplify(a), cdr(x))
      }
      let r = if cdr(mbox_args).truthy() {
        if cddr(mbox_args).truthy() {
          raise LispError::SimpleError("invalid number of arguments to MAKE-MBOX")
        }
        make_mbox(car(mbox_args), l=cadr(mbox_args))
      } else {
        make_mbox(car(mbox_args))
      }
      eqtest(r, x)
    }),
    q_operators,
  )
  |> ignore
  register_mspec(q_d_scanmap, comm2__d_scanmap)
  putprop(q_d_scanmap, t, q_evok) |> ignore
  defun(q_d_derivdegree, args => {
    check_arity("$derivdegree", args, 3)
    d_derivdegree(arg(args, 0), arg(args, 1), arg(args, 2))
  })
  defun(comm2__q_derivdeg1, args => derivdeg1(arg(args, 0), arg(args, 1), arg(args, 2)))
}

///|
let comm2__q_derivdeg1 : Value = sym("derivdeg1")
