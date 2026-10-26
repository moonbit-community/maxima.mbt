// Port of src/hayat.lisp, part 3: the TAYLOR entry points, argument
// parsing, TAYLOR1/TAYLOR2 and expansion of functions (try-expansion).

///|
fn taylor_star(arg : Value, l : Value) -> Value raise {
  // We must bind $MAXTAYORDER to () below because of the problem of
  // constants not retaining their truncation level. This means that when we
  // add a series which has more terms than the user-specified truncation to
  // a constant we must truncate the series with more terms down to the user
  // specified level because, in the worst case, the constant could be a
  // series no better than to the user-specified level. Hence $MAXTAYORDER is
  // essentially useless until the constant problem is fixed.
  let exact = if l.truthy() {
    lbool(!symval(q_d_taylor_truncate_polynomials).truthy())
  } else {
    q_user_specified
  }
  with_specials(
    [
      (q_tlist, Nil),
      (q_d_maxtayorder, Nil),
      (q_ear_within_srf_q, Nil),
      (q_exact_poly, exact),
    ],
    () => {
      parse_tay_args(l) |> ignore
      taylor1(arg, list1(symval(q_tlist)))
    },
  )
}

///|
fn tay_order(n : Value) -> Value raise {
  with_specials([(q_d_float, Nil), (q_modulus, Nil)], () => if eq(n, q_d_inf) {
    list1(inf())
  } else if n is Nil {
    wna_err(q_d_taylor)
  } else if !mnump(n).truthy() {
    merr("taylor: expansion order must be a number; found: ~:M", [n])
  } else {
    list1(prep1(n))
  })
}

///|
fn re_erat(head : Value, exp_ : Value) -> Value raise {
  taylor1(exp_, list1(cadddr(cdr(head))))
}

///|
fn parse_tay_args(l : Value) -> Value raise {
  if l is Nil {
    t
  } else if numberp(car(l)) {
    merr("taylor: variable of expansion cannot be a number: ~M", [car(l)])
  } else if symbolp(car(l)) || !eq(caaar(l), q_mlist) {
    parse_tay_args1(list3(car(l), d_ratdisrep(cadr(l)), caddr(l))) |> ignore
    parse_tay_args(cdddr(l))
  } else if {
      let mut ll = cddar(l)
      let mut found = false
      while !(ll is Nil) {
        if mnump(car(ll)).truthy() || eq(car(ll), q_d_inf) {
          found = true
          break
        }
        ll = cdr(ll)
      }
      found
    } {
    parse_tay_args1(cdar(l)) |> ignore
    parse_tay_args(cdr(l))
  } else {
    parse_tay_args2(list3(car(l), cadr(l), caddr(l))) |> ignore
    parse_tay_args(cdddr(l))
  }
}

///|
fn parse_tay_args1(l : Value) -> Value raise {
  if d_listp(car(l)).truthy() {
    parse_tay_args2(l)
  } else {
    let v = car(l)
    let pt = canonicalize_plus_inf(d_ratdisrep(cadr(l)))
    let ord = tay_order(caddr(l))
    let switches = make_switch_list(cdddr(l))
    push_special(list4(v, ord, pt, switches), q_tlist)
  }
}

///|
fn parse_tay_args2(l : Value) -> Value raise {
  let label = gensym()
  let vs = cdar(l)
  let pts = make_long_list(
    if d_listp(cadr(l)).truthy() {
      copy_list(cdadr(l))
    } else {
      list1(ratdisrep(cadr(l)))
    },
  )
  let mut ord = caddr(l)
  let switches = make_switch_list(cdddr(l))
  let mut lcm : Value = Fix(1L)
  let mut max : Value = Fix(0L)
  if atom(ord) {
    lcm = ord
    max = ord
    ord = make_long_list(list1(ord))
  } else {
    let mut a = vs
    let mut ll = cdr(ord)
    while true {
      if a is Nil {
        ord = cdr(ord)
        break
      }
      if ll is Nil {
        merr("PARSE-TAY-ARGS2: ran out of truncation levels.", []) |> ignore
      } else {
        lcm = num_lcm(lcm, car(ll))
        max = num_max(max, car(ll))
      }
      a = cdr(a)
      ll = cdr(ll)
    }
  }
  push_special(
    list4(label, tay_order(max), Fix(0L), list1(list3(q_multivar, lcm, vs))),
    q_tlist,
  )
  |> ignore
  let mut vl = vs
  let mut ordl = ord
  let mut ptl = pts
  while !(vl is Nil) {
    if ptl is Nil {
      merr("PARSE-TAY-ARGS2: ran out of matching points of expansion.", [])
      |> ignore
    } else {
      push_special(
        list4(
          car(vl),
          tay_order(car(ordl)),
          canonicalize_plus_inf(car(ptl)),
          cons(
            list3(q_multi, label, timesk(lcm, expta(car(ordl), Fix(-1L)))),
            switches,
          ),
        ),
        q_tlist,
      )
      |> ignore
    }
    vl = cdr(vl)
    ordl = cdr(ordl)
    ptl = cdr(ptl)
  }
  Nil
}

///|
fn make_switch_list(l : Value) -> Value raise {
  mapcar(q => cons(q, t), l)
}

///|
fn make_long_list(q : Value) -> Value raise {
  nconc(q, q)
}

///|
/// This checks to ensure that there isn't more than one set of multi-
/// dependent variables with different orders of expansion, e.g.
/// taylor(u+v+x+y,[u,v],0,[2,3],[x,y],0,[5,7]) is one.
fn ratwtsetup(l : Value) -> Value raise {
  let mut l = l
  let mut sw = false
  while !(l is Nil) {
    let a = switch(q_multivar, car(l))
    if a.truthy() {
      let mut ll = cadr(a)
      while !(ll is Nil) {
        if equal(cadr(switch(q_multi, get_datum(car(ll)))), Fix(1L)) {
          ()
        } else if sw {
          merr(
            "taylor: multiple dependent variables must all have the same order of expansion.",
            [],
          )
          |> ignore
        } else {
          sw = true
          break
        }
        ll = cdr(ll)
      }
    }
    l = cdr(l)
  }
  Nil
}

///|
fn taylor1(e : Value, tlist : Value) -> Value raise {
  let b = bind(q_tlist, tlist)
  defer unbind(b)
  set(q_tlist, tlist_merge(nconc(find_tlists(e), symval(q_tlist)))) |> ignore
  with_specials(
    [
      (q_d_zerobern, Nil),
      (q_d_simp, Nil),
      (q_d_algebraic, Nil),
      (q_genpairs, Nil),
      (q_varlist, Nil),
      (q_tvars, Nil),
      (q_log_1, Nil),
      (q_log_pcti, Nil),
      (q_ivars, Nil),
      (q_key_vars, Nil),
      (q_full_log, Nil),
      (q_last_exp, Nil),
      (q_mainvar_datum, Nil),
      (q_zerolist, Nil),
      (q_taylor_simplifier, Nil),
      (q_least_term_q, Nil),
      (q_tvar_limits, Nil),
      (q_genvar, Nil),
    ],
    () => {
      let mut sing_tvars : Value = Nil
      set(
        q_tlist,
        mapcan(
          d => if tvar_q(datum_var(d)).truthy() {
            list1(d)
          } else {
            sing_tvars = cons(d, sing_tvars)
            Nil
          },
          symval(q_tlist),
        ),
      )
      |> ignore
      set(q_d_zerobern, t) |> ignore
      set(q_d_simp, t) |> ignore
      set(q_d_algebraic, t) |> ignore
      set(q_last_exp, e) |> ignore
      set(q_least_term_q, t) |> ignore
      set(q_log_1, list2(list2(q_p_log, q_simp), Fix(-1L))) |> ignore
      set(q_log_pcti, list2(list2(q_p_log, q_simp), q_d__pcti)) |> ignore
      set(q_tvars, mapcar(x => car(x), symval(q_tlist))) |> ignore
      set(q_varlist, copy_list(symval(q_tvars))) |> ignore
      let ts = symval(q_d_taylor_simplifier)
      if ts.truthy() {
        // This symbolp/fboundp check is presumably for efficiency (so it can
        // be directly funcalled).
        set(
          q_taylor_simplifier,
          if symbolp(ts) && fboundp(ts) {
            ts
          } else {
            q_taylor_simplifier_caller
          },
        )
        |> ignore
      }
      // Ensure that the expansion points don't depend on the expansion vars.
      // This could cause an infinite loop, e.g. taylor(x,x,x,1).
      let mut tl = symval(q_tlist)
      while !(tl is Nil) {
        if !mfree(exp_pt(car(tl)), symval(q_tvars)).truthy() {
          merr("taylor: attempt to expand ~M at a point depending on ~M.", [
            e,
            caar(tl),
          ])
          |> ignore
        }
        tl = cdr(tl)
      }
      // This drastic initialization ensures that ALGEBRAIC, TELLRAT, DISREP,
      // etc. prop's are removed from our gensyms.
      mapc(g => set_symbol_plist(g, Nil) |> ignore, symval(q_genvar)) |> ignore
      ratsetup(symval(q_varlist), symval(q_genvar)) |> ignore
      if symval(q_d_taylor_order_coefficients).truthy() &&
        !symval(q_ear_within_srf_q).truthy() {
        newvar(e) |> ignore
      }
      orderpointer(symval(q_varlist)) |> ignore
      let first_tvar = car(symval(q_tvars))
      let vtail = {
        let mut v = symval(q_varlist)
        while !eq(car(v), first_tvar) && !(v is Nil) {
          v = cdr(v)
        }
        v
      }
      let gtail = {
        let mut v = symval(q_varlist)
        let mut g = symval(q_genvar)
        while !eq(car(v), first_tvar) && !(v is Nil) {
          v = cdr(v)
          g = cdr(g)
        }
        g
      }
      let mut q = vtail
      let mut g = gtail
      while !(q is Nil) && !(g is Nil) {
        push_special(cons(car(g), car(q)), q_key_vars) |> ignore
        let data = get_datum(car(q))
        rplaca(q, transform_tvar(car(q), data)) |> ignore
        push_special(cons(car(g), car(q)), q_ivars) |> ignore
        rplacd(cdddr(data), cons(car(g), valget(car(g)))) |> ignore
        q = cdr(q)
        g = cdr(g)
      }
      set(
        q_genpairs,
        mapcar2(
          (y, z) => {
            putprop(z, y, q_disrep) |> ignore
            cons(y, cons(pget(z), Fix(1L)))
          },
          symval(q_varlist),
          symval(q_genvar),
        ),
      )
      |> ignore
      ratwtsetup(symval(q_tlist)) |> ignore
      setup_multivar_disrep(Nil) |> ignore
      set(q_mainvar_datum, car(last(symval(q_tlist)))) |> ignore
      mapc(d => adjoin_sing_datum(d) |> ignore, sing_tvars)
      |> ignore
      let ans = catch_tag(q_tay_err, () => taylor3(e))
      if atom(car(ans)) {
        tay_error(car(ans), cadr(ans))
      } else {
        ans
      }
    },
  )
}

///|
fn transform_tvar(var2 : Value, data : Value) -> Value raise {
  if !tvar_q(var2).truthy() {
    var2
  } else {
    let pt = exp_pt(data)
    if numberp(pt) && zerop(pt) && switch(q_d_asymp, data) is Nil {
      // Simple case
      var2
    } else if hayat__memq_arr(pt, [q_d_inf, q_infinity]) {
      power_star(var2, Fix(-1L))
    } else if eq(pt, q_d_minf) {
      mul2_star(Fix(-1L), power_star(var2, Fix(-1L)))
    } else {
      let temp = sub_star(var2, pt)
      if switch(q_d_asymp, data).truthy() {
        power_star(temp, Fix(-1L))
      } else {
        temp
      }
    }
  }
}

///|
fn taylor_simplifier_caller(exp_ : Value) -> Value raise {
  mcall(symval(q_d_taylor_simplifier), list1(exp_))
}

///|
fn taylor_simplify_recurse(ps : Value) -> Value raise {
  if pscoefp(ps).truthy() {
    return taylor2(
      funcall(symval(q_taylor_simplifier), [rcdisrep(ps)]),
    )
  }
  let mut datum = ps_data(ps)
  // We must treat multivars like 1, since they'll reappear again when we
  // call taylor2 on their disrep'd coeff's.
  if switch(q_multivar, datum).truthy() {
    datum = Nil
  } else {
    // Don't push pw's < 0, else constants will be truncated
    push_pw(datum, emax(trunc_lvl(ps), rczero())) |> ignore
  }
  let mut terms = terms(ps)
  let mut ans = rczero()
  while !(terms is Nil) {
    ans = psplus(
      if datum is Nil {
        taylor_simplify_recurse(lc(terms))
      } else {
        // Don't do (taylor2 (funcall taylor_simplifier (m^ var ...)))
        // since this causes terms to be lost when inverting.
        pstimes(
          taylor_simplify_recurse(lc(terms)),
          if ezerop(le(terms)).truthy() {
            rcone()
          } else {
            make_ps(ps, list1(term(le(terms), rcone())))
          },
        )
      },
      ans,
    )
    terms = n__term(terms)
  }
  if datum.truthy() {
    pop_pw(datum) |> ignore
  }
  ans
}

///|
fn push_pw(datum : Value, pw : Value) -> Value raise {
  rplaca(cdr(datum), cons(pw, cadr(datum))) |> ignore
  // When changing the truncation on an internal multivar we must also
  // propagate the change to all var's which depend upon it.
  let datum = switch(q_multivar, datum)
  if datum.truthy() {
    let mut vars = cadr(datum)
    while !(vars is Nil) {
      let d = get_datum(car(vars))
      rplaca(cdr(d), cons(pw, cadr(d))) |> ignore
      vars = cdr(vars)
    }
  }
  Nil
}

///|
fn pop_pw(datum : Value) -> Value raise {
  rplaca(cdr(datum), cdadr(datum)) |> ignore
  // See the comment above in push-pw; here we must undo the propagation.
  let datum = switch(q_multivar, datum)
  if datum.truthy() {
    let mut vars = cadr(datum)
    while !(vars is Nil) {
      let d = get_datum(car(vars))
      rplaca(cdr(d), cdadr(d)) |> ignore
      vars = cdr(vars)
    }
  }
  Nil
}

///|
fn setup_multivar_disrep(mrat_q : Value) -> Value raise {
  with_specials(
    [(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))],
    () => {
      let mut multivars : Value = Nil
      if mrat_q.truthy() {
        set(q_varlist, mrat_varlist(mrat_q)) |> ignore
        set(q_genvar, mrat_genvar(mrat_q)) |> ignore
      }
      mapc(
        datum => if switch(q_multivar, datum).truthy() {
          multivars = cons(car(datum), multivars)
          // All genvar's corresponding to internally generated multivars
          // must "disappear" when disrep'd.
          putprop(int_gvar(datum), Fix(1L), q_disrep) |> ignore
        },
        if mrat_q.truthy() {
          mrat_tlist(mrat_q)
        } else {
          symval(q_tlist)
        },
      )
      |> ignore
      // Here we must substitute 1 for any genvars which depend on
      // multivars. For example, taylor(x^n,[x],0,0) generates a multivar^n.
      if multivars.truthy() {
        let mut expl = symval(q_varlist)
        let mut gvarl = symval(q_genvar)
        while !(expl is Nil) {
          if !mfree(car(expl), multivars).truthy() {
            putprop(car(gvarl), Fix(1L), q_disrep) |> ignore
          }
          expl = cdr(expl)
          gvarl = cdr(gvarl)
        }
      }
      Nil
    },
  )
}

// An example showing why the flag trunc-constants? is needed is given by
// taylor(-exp(exp(-1/x)+2/x),x,0,-1). Without it, tstimes and
// taylor_simplify_recurse end up trunc'ing the -1.

///|
fn taylor3(e : Value) -> Value raise {
  if mbagp(e).truthy() {
    cons(car(e), mapcar(x => taylor3(x), cdr(e)))
  } else if symval(q_tlist) is Nil &&
    !eq(symval(q_exact_poly), q_user_specified) {
    xcons(
      prep1(e),
      list([q_mrat, q_simp, symval(q_varlist), symval(q_genvar)]),
    )
  } else {
    xcons(
      if symval(q_taylor_simplifier) is Nil {
        taylor2(e)
      } else {
        let e = taylor2(e)
        with_specials([(q_exact_poly, Nil), (q_trunc_constants_q, Nil)], () => taylor_simplify_recurse(
          e,
        ))
      },
      list([
        q_mrat,
        q_simp,
        symval(q_varlist),
        symval(q_genvar),
        symval(q_tlist),
        q_trunc,
      ]),
    )
  }
}

///|
fn find_tlists(e : Value) -> Value raise {
  with_special(q_ear_a, Nil, () => {
    findtl1(e) |> ignore
    symval(q_ear_a)
  })
}

///|
fn findtl1(e : Value) -> Value raise {
  if atom(e) || mnump(e).truthy() {
    t
  } else if eq(caar(e), q_mrat) {
    if memq(q_trunc, car(e)).truthy() {
      push_special(mapcar(x => copy_tree(x), mrat_tlist(e)), q_ear_a)
    } else {
      Nil
    }
  } else {
    mapc(x => findtl1(x) |> ignore, cdr(e))
  }
}

///|
fn tlist_merge(tlists : Value) -> Value raise {
  let mut tlists = tlists
  let mut tlist : Value = Nil
  while !(tlists is Nil) {
    let mut a_tlist = car(tlists)
    while !(a_tlist is Nil) {
      let mut temp = get_datum(datum_var(car(a_tlist)), not_canonicalized_q=t)
      if temp is Nil {
        temp = car(a_tlist)
        if tvar_q(datum_var(temp)).truthy() ||
          hayat__memq_arr(caar(datum_var(temp)), [q_mexpt, q_p_log]) {
          tlist = cons(
            list4(datum_var(temp), trunc_stack(temp), exp_pt(temp), switches(temp)),
            tlist,
          )
        } else {
          merr("taylor: ~M cannot be a variable.", [datum_var(temp)]) |> ignore
        }
      } else {
        if symval(q_d_maxtayorder).truthy() {
          // We must take the max truncation level when $maxtayorder is T,
          // cf. JPG's bug of 9/15/82.
          if e_gt(current_trunc(car(a_tlist)), current_trunc(temp)).truthy() {
            rplaca(cadr(temp), current_trunc(car(a_tlist))) |> ignore
          }
        } else if !e_gt(current_trunc(car(a_tlist)), current_trunc(temp)).truthy() {
          rplaca(cadr(temp), current_trunc(car(a_tlist))) |> ignore
        }
        if !alike1(exp_pt(temp), exp_pt(car(a_tlist))).truthy() {
          merr(
            "taylor: cannot combine expressions expanded at different points.",
            [],
          )
          |> ignore
        }
        rplaca(cdddr(temp), union_star(switches(temp), switches(car(a_tlist))))
        |> ignore
      }
      a_tlist = cdr(a_tlist)
    }
    tlists = cdr(tlists)
  }
  nreverse(tlist)
}

///|
fn compattlist(list_ : Value) -> Value raise {
  let mut l = list_
  while !(l is Nil) {
    if !alike1(exp_pt(get_datum(datum_var(car(l)))), exp_pt(car(l))).truthy() {
      return Nil
    }
    l = cdr(l)
  }
  t
}

///|
fn taylor2(e : Value) -> Value raise {
  // lexp-non0 should be bound here when needed
  with_special(q_last_exp, e, () => hayat__taylor2(e))
}

///|
fn hayat__taylor2(e : Value) -> Value raise {
  if assolike(e, symval(q_tlist)).truthy() {
    return var_expand(e, Fix(1L), Nil)
  }
  if mnump(e).truthy() || atom(e) || mfree(e, symval(q_tvars)).truthy() {
    let mvd = symval(q_mainvar_datum)
    return if e_gt(rczero(), current_trunc(mvd)).truthy() ||
      lim_zerop(e).truthy() {
      pszero(data_gvar_o(mvd), current_trunc(mvd))
    } else if symval(q_taylor_simplifier).truthy() && !atom(e) {
      let e_simp = prep1(funcall(symval(q_taylor_simplifier), [e]))
      if rczerop(e_simp).truthy() && memq(e_simp, symval(q_zerolist)) is Nil {
        push_special(e, q_zerolist) |> ignore
      }
      e_simp
    } else {
      prep1(e)
    }
  }
  if !atom(caar(e)) {
    return merr("TAYLOR2: internal error.", [])
  }
  if d_taylorp(e).truthy() {
    return if compatvarlist(
        symval(q_varlist),
        mrat_varlist(e),
        symval(q_genvar),
        mrat_genvar(e),
      ).truthy() &&
      compattlist(mrat_tlist(e)).truthy() {
      pstrunc(cdr(e))
    } else {
      with_special(q_exact_poly, Nil, () => re_taylor(e))
    }
  }
  let op = caar(e)
  if eq(op, q_mplus) {
    return tsplus(cdr(e))
  }
  if eq(op, q_mtimes) {
    return tstimes(cdr(e))
  }
  if eq(op, q_mexpt) {
    return tsexpt(cadr(e), caddr(e))
  }
  if eq(op, q_p_log) {
    return tslog(cadr(e))
  }
  if (known_ps(op).truthy() || get(op, q_tay_trans).truthy()) &&
    memq(q_array, cdar(e)) is Nil {
    let r = try_expansion(if cddr(e).truthy() { cdr(e) } else { cadr(e) }, op)
    if r.truthy() {
      return r
    }
  }
  if mqapplyp(e).truthy() {
    let r = if get(subfunname(e), q_spec_trans).truthy() {
      funcall(get(subfunname(e), q_spec_trans), [e])
    } else if known_ps(subfunname(e)).truthy() {
      try_expansion(caddr(e), cadr(e))
    } else {
      Nil
    }
    if r.truthy() {
      return r
    }
  }
  if hayat__memq_arr(op, [q_p_sum, q_p_product]) &&
    mfreel(cddr(e), symval(q_tvars)).truthy() {
    return tsprsum(cadr(e), cddr(e), op)
  }
  // If TSDIFF returns NIL, it means that the derivative is wrt to some
  // variable other than one of the taylor variables. If so, keep going and
  // handle E as if it were a general expression.
  if eq(op, q_p_derivative) {
    let r = tsdiff(cadr(e), cddr(e))
    if r.truthy() {
      return r
    }
  }
  if eq(op, q_p_at) ||
    {
      let mut l = mapcar(x => car(x), symval(q_tlist))
      let mut all_free = true
      while !(l is Nil) {
        if !free(e, car(l)).truthy() {
          all_free = false
          break
        }
        l = cdr(l)
      }
      all_free
    } {
    return newsym(e)
  }
  // Taylor series aren't exact
  with_special(q_exact_poly, Nil, () => {
    let ee = diff_expand(e, symval(q_tlist))
    if equal(sratsimp(e), sratsimp(ee)) {
      prep1(ee)
    } else {
      taylor2(ee)
    }
  })
}

///|
fn compatvarlist(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  if a is Nil {
    t
  } else if b is Nil || c is Nil || d is Nil {
    Nil
  } else if alike1(car(a), car(b)).truthy() {
    if !eq(car(c), car(d)) {
      Nil
    } else {
      compatvarlist(cdr(a), cdr(b), cdr(c), cdr(d))
    }
  } else {
    compatvarlist(a, cdr(b), c, cdr(d))
  }
}

///|
fn re_taylor(mrat : Value) -> Value raise {
  let old_varlist = mrat_varlist(mrat)
  let old_genvar = mrat_genvar(mrat)
  with_specials([(q_old_tlist, mrat_tlist(mrat)), (q_old_ivars, Nil)], () => {
    // Put back the old disreps so rcdisrep's will work correctly.
    mapcar2(
      (g, v) => {
        putprop(g, v, q_disrep) |> ignore
        Nil
      },
      old_genvar,
      old_varlist,
    )
    |> ignore
    setup_multivar_disrep(mrat) |> ignore
    // Singular exponentials (such as those adjoined during expansion at
    // infinity) are not placed on GENVAR or VARLIST, meaning they will be
    // missing from OLD-GENVAR and OLD-VARLIST. We extract their
    // internal-to-external variable mappings from OLD-TLIST and append them
    // to OLD-IVARS.
    set(
      q_old_ivars,
      nconc(
        mapcar2((g, v) => cons(g, v), old_genvar, old_varlist),
        mapcar(d => cons(data_gvar(d), datum_var(d)), symval(q_old_tlist)),
      ),
    )
    |> ignore
    let r = re_taylor_recurse(mrat_ps(mrat))
    // Restore the correct disreps.
    mapcar2(
      (g, v) => {
        putprop(g, v, q_disrep) |> ignore
        Nil
      },
      symval(q_genvar),
      symval(q_varlist),
    )
    |> ignore
    setup_multivar_disrep(Nil) |> ignore
    r
  })
}

///|
fn re_taylor_recurse(ps : Value) -> Value raise {
  if !psp(ps).truthy() {
    return taylor2(rcdisrep(ps))
  }
  let mut var2 = cdr(assq(gvar(ps), symval(q_old_ivars)))
  let mut datum : Value = Nil
  // We must treat multivars like 1, since they'll reappear again when we
  // call taylor2 or var-expand below.
  if switch(q_multivar, assoc_equal(var2, symval(q_old_tlist))).truthy() {
    var2 = Nil
  } else {
    datum = var_data(var2)
    if datum.truthy() {
      push_pw(datum, trunc_lvl(ps)) |> ignore
    }
  }
  let mut terms = terms(ps)
  let mut ans = rczero()
  while !(terms is Nil) {
    ans = psplus(
      if var2 is Nil {
        re_taylor_recurse(lc(terms))
      } else {
        pstimes(
          re_taylor_recurse(lc(terms)),
          if datum.truthy() {
            var_expand(car(datum), edisrep(le(terms)), Nil)
          } else {
            taylor2(power(var2, edisrep(le(terms))))
          },
        )
      },
      ans,
    )
    terms = n__term(terms)
  }
  if datum.truthy() {
    pop_pw(datum) |> ignore
  }
  ans
}

///|
fn var_expand(var2 : Value, exp_ : Value, dont_truncate_q : Value) -> Value raise {
  // exp must be a rational integer
  let mut exp_ = with_specials(
    [(q_d_keepfloat, Nil), (q_d_float, Nil), (q_modulus, Nil)],
    () => prep1(exp_),
  )
  let temp = get_datum(var2, not_canonicalized_q=t)
  if temp is Nil {
    merr("VAR-EXPAND: invalid call.", [])
  } else if hayat__memq_arr(exp_pt(temp), [q_d_inf, q_d_minf, q_d_infinity]) {
    if switch(q_d_asymp, temp).truthy() {
      merr("taylor: cannot create an asymptotic expansion at infinity.", [])
    } else if {
        exp_ = rcminus(exp_)
        e_gt(exp_, current_trunc(temp)).truthy()
      } {
      rczero()
    } else {
      make_ps(
        int_var(temp),
        list1(
          if symval(q_exact_poly).truthy() {
            inf()
          } else {
            current_trunc(temp)
          },
        ),
        terms=list1(
          term(
            exp_,
            if eq(exp_pt(temp), q_d_minf) {
              rcmone()
            } else {
              rcone()
            },
          ),
        ),
      )
    }
    // multivar expansion does not work at infinity, so expansion at infinity
    // is handled by above clause even if doing multivar.
  } else if switch(q_multi, temp).truthy() {
    // The reason we call var-expand below instead of taylor2 is that we must
    // be sure the call is not truncated to 0 which would cause an error in
    // psexpt if exp < 0. For example, this occurred in
    // TAYLOR(X^2/Y,[X,Y],0,2).
    // Must ensure that we get back a series truncated to at least what is
    // specified by tlist. This means we'll have to push-pw unless exp>0
    // since psexpt'n kills (exp-1) terms.
    let first = if !e_gt(exp_, rczero()).truthy() {
      mhayat__let_pw(
        get_datum(car(switch(q_multi, temp))),
        e_plus(current_trunc(temp), e_(e1_(exp_))),
        () => var_expand(car(switch(q_multi, temp)), Fix(1L), t),
      )
    } else {
      var_expand(car(switch(q_multi, temp)), Fix(1L), t)
    }
    psexpt(
      psplus(
        pstimes(
          first,
          cons(list3(int_gvar(temp), Fix(1L), Fix(1L)), Fix(1L)),
        ),
        taylor2(exp_pt(temp)),
      ),
      exp_,
    )
  } else if numberp(exp_pt(temp)) && zerop(exp_pt(temp)) {
    let mut exp_gt_trunc_q = false
    if e_gt(exp_, current_trunc(temp)).truthy() &&
      {
        exp_gt_trunc_q = true
        true
      } &&
      !dont_truncate_q.truthy() {
      rczero()
    } else {
      make_ps(
        int_var(temp),
        list1(
          if symval(q_exact_poly).truthy() {
            inf()
          } else if exp_gt_trunc_q {
            exp_
          } else {
            current_trunc(temp)
          },
        ),
        terms=list1(
          term(
            if switch(q_d_asymp, temp).truthy() {
              rcminus(exp_)
            } else {
              exp_
            },
            rcone(),
          ),
        ),
      )
    }
  } else {
    psexpt(
      psplus(
        make_ps(
          int_var(temp),
          list1(
            if symval(q_exact_poly).truthy() {
              inf()
            } else {
              current_trunc(temp)
            },
          ),
          terms=list1(
            term(
              if switch(q_d_asymp, temp).truthy() {
                rcmone()
              } else {
                rcone()
              },
              rcone(),
            ),
          ),
        ),
        taylor2(exp_pt(temp)),
      ),
      exp_,
    )
  }
}

///|
fn expand(arg : Value, func : Value) -> Value raise {
  let r = try_expansion(arg, func)
  if r.truthy() {
    r
  } else {
    exp_pt_err()
  }
}

///|
fn try_expansion(arg : Value, func : Value) -> Value raise {
  // We bind exact-poly to () since we don't want psexpt retaining higher
  // order terms when subst'ing into series (which aren't exact).
  with_special(q_exact_poly, Nil, () => hayat__try_expansion(arg, func))
}

///|
fn hayat__try_expansion(arg : Value, func : Value) -> Value raise {
  let atrig_funs = [q_p_atan, q_p_asin, q_p_asinh, q_p_atanh]
  // Try diff-expanding unknown subscripted functions.
  if !(atom(func) || known_ps(caar(func)).truthy()) {
    taylor2(diff_expand(mk(q_mqapply, [func, arg]), symval(q_tlist))) |> ignore
  }
  let funame = oper_name(func)
  let mut temp = get(funame, q_tay_trans)
  if temp.truthy() {
    return funcall(temp, [arg, func])
  }
  let lterm = getfun_lt(func)
  let funord = e(lterm)
  let fun_lc = c(lterm)
  let mut psarg : Value = Nil
  let mut argord : Value = Nil
  while true {
    // begin-expansion
    if !psarg.truthy() {
      psarg = get_lexp(arg, rcone(), Nil)
    }
    if rczerop(psarg).truthy() {
      if e_gt(rczero(), funord).truthy() {
        psarg = get_lexp(arg, rcone(), t)
        if rczerop(psarg).truthy() {
          tay_depth_err() |> ignore
        } else {
          continue
        }
      } else {
        temp = assq(funame, symval(q_tay_pole_expand))
        return if temp.truthy() {
          funcall(cdr(temp), [arg, psarg, func])
        } else if rczerop(funord).truthy() {
          fun_lc
        } else {
          rczero()
        }
      }
    }
    if pscoefp(psarg).truthy() {
      psarg = taylor2(arg)
    }
    if pscoefp(psarg).truthy() {
      return if !mfree(rdis(psarg), symval(q_tvars)).truthy() {
        symbolic_expand(arg, psarg, func)
      } else {
        temp = assq(funame, symval(q_tay_pole_expand))
        if temp.truthy() {
          funcall(cdr(temp), [arg, psarg, func])
        } else {
          prep1(
            simplify(
              if atom(func) {
                list2(list1(func), rcdisrep(psarg))
              } else {
                list3(list1(q_mqapply), func, rcdisrep(psarg))
              },
            ),
          )
        }
      }
    }
    argord = ps_le(psarg)
    if e_gt(rczero(), argord).truthy() {
      if !hayat__memq_arr(funame, atrig_funs) {
        psarg = get_lexp(arg, rcone(), t)
        if e_gt(rczero(), ps_le_star(psarg)).truthy() {
          essen_sing_err() |> ignore
        } else {
          continue
        }
      } else {
        // ATRIGH expands the LOGARC form. For ATAN at a pole of the
        // argument, the constant of that expansion comes out as %pi/2 or
        // -%pi/2 depending on how the internal log(-1)s fall out for the
        // particular form of ARG. So read off the constant actually produced
        // and force it to the sign of the leading series term of ARG.
        let mut ans = atrigh(arg, func)
        let mut sgn : Value = Nil
        if eq(funame, q_p_atan) &&
          {
            sgn = ps_lt_sign(psarg)
            hayat__memq_arr(sgn, [q_d_pos, q_d_neg])
          } {
          let c0 = rcdisrep(
            if psp(ans).truthy() {
              psterm(terms(ans), rczero())
            } else {
              ans
            },
          )
          // force the constant term to sgn * %pi/2
          ans = psplus(
            ans,
            taylor2(
              sub_star(
                if eq(sgn, q_d_neg) {
                  mul2_star(Fix(-1L), symval(q_half_pctpi))
                } else {
                  symval(q_half_pctpi)
                },
                c0,
              ),
            ),
          )
        }
        return ans
      }
    }
    temp = t_o_var(gvar(psarg))
    if e_gt(e_star(funord, argord), temp).truthy() {
      return rczero()
    }
    // The following form need not be executed if psarg is really exact.
    // The constant problem does not allow one to determine this now, so we
    // always have to execute this currently.
    let arg_trunc = if !(trunc_lvl(psarg) is Nil) && e_eq(funord, rcone()).truthy() {
      temp
    } else {
      e_(temp, e2=e_star(e1_(funord), argord))
    }
    let ps0 = psarg
    psarg = mhayat__let_pw(
      get_datum(get_key_var(gvar(ps0))),
      arg_trunc,
      () => if trunc_lvl(ps0) is Nil || e_gt(arg_trunc, trunc_lvl(ps0)).truthy() {
        taylor2(arg)
      } else {
        pstrunc(ps0)
      },
    )
    // We must recalculate argord since pstrunc may have "picked" a coeff
    // out of a constant monomial; e.g. this occurs in
    // taylor(sin(x+y),x,0,0,y,0,1) where psarg is (Y+...)*X^0+... which
    // truncates to Y+... of order 1.
    argord = ps_le_star(psarg)
    if rczerop(argord).truthy() {
      if hayat__memq_arr(funame, atrig_funs) {
        // Only convert these to logarithmic form (done by ATRIGH) when
        // DIFF-EXPAND would fail (singularity at the expansion point).
        let r = with_special(q_silent_taylor_flag, t, () => {
          let ans = catch_tag(q_tay_err, () => diff_expand(
            ftake(funame, [arg]),
            symval(q_tlist),
          ))
          // Objects thrown to the TAY-ERR tag have an atomic CAR, that's
          // how we can detect that we caught an error.
          if !(consp(ans) && atom(car(ans))) {
            Some(taylor2(ans))
          } else {
            None
          }
        })
        match r {
          Some(v) => return v
          None => ()
        }
        return atrigh(arg, func)
      } else {
        temp = assq(funame, symval(q_const_exp_funs))
        if temp.truthy() {
          return funcall(cdr(temp), [arg, psarg, func])
        }
        psarg = get_lexp(arg, rcone(), t)
        if rczerop(ps_le_star(psarg)).truthy() {
          // Don't know an addition formula
          return Nil
        }
        continue
      }
    } else {
      return if mono_term_q(terms(psarg)).truthy() {
        get_series(
          func,
          current_trunc(get_datum(get_key_var(gvar(psarg)))),
          gvar_o(psarg),
          ps_le(psarg),
          ps_lc(psarg),
        )
      } else {
        temp = get_series(
          func,
          e_sl_sl(temp, e2=argord),
          gvar_o(psarg),
          rcone(),
          rcone(),
        )
        if !psp(temp).truthy() {
          temp
        } else {
          pscsubst1(psarg, temp)
        }
      }
    }
  }
  Nil
}

///|
/// Should be much stronger.
fn symbolic_expand(ign : Value, psarg : Value, func : Value) -> Value raise {
  ignore(ign)
  prep1(
    simplifya(
      if atom(func) {
        list2(list1(func), rcdisrep(psarg))
      } else {
        list3(list1(q_mqapply), func, rcdisrep(psarg))
      },
      Nil,
    ),
  )
}

///|
fn expand_sing_trig_q(arg : Value, func : Value) -> Value raise {
  if memq(func, symval(q_n_starpscirc)).truthy() {
    tay_exponentialize(arg, func)
  } else if memq(func, symval(q_n_starpsacirc)).truthy() {
    atrigh(arg, func)
  } else {
    essen_sing_err()
  }
}

///|
fn trig_const(a : Value, arg : Value, func : Value) -> Value raise {
  let mut const_ = ps_lc_star(arg)
  let temp = cdr(assq(func, symval(q_trigdisp)))
  if pscoefp(const_).truthy() && hayat__memq_arr(func, [q_p_tan, q_p_cot]) {
    let r = multiple__pctpi(a, srdis(const_), func)
    if r.truthy() {
      return r
    }
  }
  if temp.truthy() {
    const_ = psdisrep(const_)
    funcall(temp, [const_, sub_star(a, const_)])
  } else {
    tsexpt(list2(list1(get(func, q_recip)), srdis(arg)), Fix(-1L))
  }
}

///|
fn multiple__pctpi(a : Value, const_ : Value, func : Value) -> Value raise {
  if !multiplep(const_, q_d__pctpi).truthy() {
    return Nil
  }
  let coef = d_ratcoef(const_, q_d__pctpi, n=Fix(1L))
  if !d_ratnump(coef).truthy() {
    return Nil
  }
  if numberp(coef) {
    expand(sub_star(a, const_), func)
  } else if equal(caddr(coef), Fix(2L)) {
    psminus(
      expand(
        sub_star(a, const_),
        if eq(func, q_p_tan) {
          q_p_cot
        } else if eq(func, q_p_cot) {
          q_p_tan
        } else {
          merr("MULTIPLE-%PI: internal error in Taylor expansion.", [])
        },
      ),
    )
  } else {
    Nil
  }
}

///|
/// Evaluates the asymptotic sign of the power series PS' leading term.
fn ps_lt_sign(ps : Value) -> Value raise {
  if pscoefp(ps).truthy() {
    coef_sign(rcdisrep(ps))
  } else {
    // recursively get coefficient sign
    let c_sign = ps_lt_sign(ps_lc(ps))
    // limit of v^e
    let v_lim = lim_power(gvar_lim(gvar(ps)), ps_le(ps))
    if hayat__memq_arr(v_lim, [q_d_minf, q_d_zerob, q_d_neg]) {
      // v^e is negative, so flip the coefficient's sign.
      if eq(c_sign, q_d_pos) {
        q_d_neg
      } else if eq(c_sign, q_d_neg) {
        q_d_pos
      } else {
        c_sign
      }
    } else {
      // otherwise, retain coefficient's sign
      c_sign
    }
  }
}

///|
fn atan2_trans(args : Value, func : Value) -> Value raise {
  ignore(func)
  let y = first(args)
  let x = second(args)
  // GET-LEXP finds the first non-zero term.
  let lexp_y = get_lexp(y, Nil, Nil)
  let lexp_x = get_lexp(x, Nil, Nil)
  // Get their signs.
  let sign_y = ps_lt_sign(lexp_y)
  let sign_x = ps_lt_sign(lexp_x)
  if eq(sign_x, q_d_zero) {
    if eq(sign_y, q_d_pos) {
      taylor2(div(q_d__pctpi, Fix(2L)))
    } else if eq(sign_y, q_d_neg) {
      taylor2(div(q_d__pctpi, Fix(-2L)))
    } else {
      tay_error(Str("atan2: atan2(0, 0) is undefined."), Nil)
    }
  } else if eq(sign_y, q_d_zero) {
    taylor2(if eq(sign_x, q_d_pos) { Fix(0L) } else { q_d__pctpi })
  } else {
    let ord_y = if psp(lexp_y).truthy() { ps_le(lexp_y) } else { rczero() }
    let ord_x = if psp(lexp_x).truthy() { ps_le(lexp_x) } else { rczero() }
    // Compare relative growth rates to avoid atan(inf) or atan(minf).
    // If x approaches 0 faster than y (ORD-X > ORD-Y), atan(y/x) has an
    // essential singularity; use the identity:
    // atan2(y, x) = sign(y)*%pi/2 - atan(x/y).
    // Otherwise, rewrite as atan(y/x) + offset, depending on quadrant.
    if e_gt(ord_x, ord_y).truthy() {
      let offset = div(
        q_d__pctpi,
        if eq(sign_y, q_d_pos) {
          Fix(2L)
        } else {
          Fix(-2L)
        },
      )
      taylor2(sub(offset, ftake(q_p_atan, [div(x, y)])))
    } else {
      let offset : Value = if eq(sign_x, q_d_pos) {
        Fix(0L)
      } else if eq(sign_y, q_d_neg) {
        neg(q_d__pctpi)
      } else {
        q_d__pctpi
      }
      taylor2(add2(offset, ftake(q_p_atan, [div(y, x)])))
    }
  }
}

///|
fn factorial_trans(arg : Value, func : Value) -> Value raise {
  ignore(func)
  taylor2(list2(list1(q_p_gamma), add2_star(Fix(1L), arg)))
}

///|
/// signum(x) => x/abs(x); this gives an error at x=0 and a derivative of 0
/// elsewhere.
fn signum_trans(arg : Value, func : Value) -> Value raise {
  ignore(func)
  taylor2(mk(q_mtimes, [arg, mk(q_mexpt, [mk(q_mabs, [arg]), Fix(-1L)])]))
}

///|
/// For gamma_incomplete(s,z): translate into gamma_incomplete_lower if s>0
/// and z=0. The call to $limit is surrounded with errcatch (with $errormsg
/// set to nil) to work around a bug elsewhere.
fn gamma_upper_trans(arg : Value, func : Value) -> Value raise {
  let s = car(arg)
  let z = cadr(arg)
  let tl = symval(q_tlist)
  if eq(d_sign(s), q_d_pos) &&
    with_special(q_d_errormsg, Nil, () => {
      let r = errset(() => d_limit(list3(z, caar(tl), exp_pt(car(tl)))))
      let v = match r {
        Some(v) => v
        None => Nil
      }
      zerop1(v).truthy()
    }) {
    taylor2(
      mk(q_mplus, [
        mk(q_p_gamma, [s]),
        mk(q_mtimes, [Fix(-1L), mk(q_p_gamma_incomplete_lower, [s, z])]),
      ]),
    )
  } else {
    taylor2(diff_expand(cons(list1(func), arg), symval(q_tlist)))
  }
}

///|
/// For gamma_incomplete_lower(s,z): if z=0, use A&S 6.5.29
///   gamma_incomplete_lower(s,z) = z^s * sum((-z)^k/((s+k) k!), k, 0, inf)
fn gamma_lower_trans(arg : Value, func : Value) -> Value raise {
  let s = car(arg)
  let z = cadr(arg)
  let tl = symval(q_tlist)
  if zerop1(d_limit(list3(z, caar(tl), exp_pt(car(tl))))).truthy() {
    taylor2(
      mk(q_mtimes, [
        mk(q_mexpt, [z, s]),
        mk(q_p_sum, [
          mk(q_mtimes, [
            mk(q_mexpt, [mk(q_mtimes, [Fix(-1L), z]), q_k]),
            mk(q_mexpt, [
              mk(q_mtimes, [mk(q_mfactorial, [q_k]), mk(q_mplus, [s, q_k])]),
              Fix(-1L),
            ]),
          ]),
          q_k,
          Fix(0L),
          q_d_inf,
        ]),
      ]),
    )
  } else {
    taylor2(diff_expand(cons(list1(func), arg), symval(q_tlist)))
  }
}

///|
fn psina_plusb(a : Value, b : Value) -> Value raise {
  psplus(
    pstimes(expand(a, q_p_sin), expand(b, q_p_cos)),
    pstimes(expand(a, q_p_cos), expand(b, q_p_sin)),
  )
}

///|
fn pscosa_plusb(a : Value, b : Value) -> Value raise {
  psdiff(
    pstimes(expand(a, q_p_cos), expand(b, q_p_cos)),
    pstimes(expand(a, q_p_sin), expand(b, q_p_sin)),
  )
}

///|
fn pstana_plusb(a : Value, b : Value) -> Value raise {
  let a = expand(a, q_p_tan)
  let b = expand(b, q_p_tan)
  pstimes(psplus(a, b), psexpt(psdiff(rcone(), pstimes(a, b)), rcmone()))
}

///|
fn psinha_plusb(a : Value, b : Value) -> Value raise {
  psplus(
    pstimes(expand(a, q_p_sinh), expand(b, q_p_cosh)),
    pstimes(expand(a, q_p_cosh), expand(b, q_p_sinh)),
  )
}

///|
fn pscosha_plusb(a : Value, b : Value) -> Value raise {
  psplus(
    pstimes(expand(a, q_p_cosh), expand(b, q_p_cosh)),
    pstimes(expand(a, q_p_sinh), expand(b, q_p_sinh)),
  )
}

///|
fn pstanha_plusb(a : Value, b : Value) -> Value raise {
  let a = expand(a, q_p_tanh)
  let b = expand(b, q_p_tanh)
  pstimes(psplus(a, b), psexpt(psplus(rcone(), pstimes(a, b)), rcmone()))
}

///|
fn atrig_trans(arg : Value, func : Value) -> Value raise {
  let half_pi = symval(q_half_pctpi)
  taylor2(
    if eq(func, q_p_acos) {
      mk(q_mplus, [half_pi, mk(q_mtimes, [Fix(-1L), mk(q_p_asin, [arg])])])
    } else if eq(func, q_p_acosh) {
      mk(q_mtimes, [
        Fix(-1L),
        q_d__pcti,
        mk(q_mplus, [half_pi, mk(q_mtimes, [Fix(-1L), mk(q_p_asin, [arg])])]),
      ])
    } else {
      mk(
        hayat__assq_arr(func, [
          (q_p_acsc, q_p_asin),
          (q_p_asec, q_p_acos),
          (q_p_acot, q_p_atan),
          (q_p_acsch, q_p_asinh),
          (q_p_asech, q_p_acosh),
          (q_p_acoth, q_p_atanh),
        ]),
        [power_star(arg, Fix(-1L))],
      )
    },
  )
}

///|
fn atrigh(arg : Value, func : Value) -> Value raise {
  with_specials(
    [
      (q_full_log, t),
      (q_d_logarc, t),
      (q_log_1, mk(q_mtimes, [q_d__pcti, q_d__pctpi])),
      (
        q_log_pcti,
        mk(q_mtimes, [mk(q_rat, [Fix(1L), Fix(2L)]), q_d__pcti, q_d__pctpi]),
      ),
    ],
    () => taylor2(simplify(list2(list1(func), arg))),
  )
}

///|
/// This should be in symbolic-expand!
fn tay_exponentialize(arg : Value, fun : Value) -> Value raise {
  let arg = with_specials([(q_d_exponentialize, t), (q_d_logarc, t)], () => meval(
    list2(list1(fun), arg),
  ))
  taylor2(arg)
}

///|
fn tsplus(l : Value) -> Value raise {
  let mut ans = taylor2(car(l))
  let mut l = cdr(l)
  while !(l is Nil) {
    ans = psplus(ans, taylor2(car(l)))
    l = cdr(l)
  }
  ans
}

///|
fn ts_formula(form : Value, var2 : Value, pw : Value) -> Value raise {
  let datum = get_datum(get_key_var(car(var2)))
  mhayat__let_pw(datum, pw, () => taylor2(
    subst(get_inverse(car(var2)), q_sp2var, form),
  ))
}
