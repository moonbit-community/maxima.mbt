// Port of src/hayat.lisp, part 2: exponentials and logarithms of series,
// singular kernels and their limits, the expansion table for known
// functions.

///|
/// Destructive CL `delete` with an explicit test.
fn hayat__delete(
  item : Value,
  l : Value,
  pred : (Value, Value) -> Bool,
) -> Value raise {
  let mut head = l
  // drop leading matches
  while head is Cons(c) && pred(item, c.car) {
    head = c.cdr
  }
  let mut prev = head
  while prev is Cons(pc) && pc.cdr is Cons(nc) {
    if pred(item, nc.car) {
      pc.cdr = nc.cdr
    } else {
      prev = pc.cdr
    }
  }
  head
}

///|
/// `(member x '(syms...) :test #'eq)` as a Bool.
fn hayat__memq_arr(x : Value, syms : Array[Value]) -> Bool {
  for s in syms {
    if eq(x, s) {
      return true
    }
  }
  false
}

///|
/// `(cdr (assoc x '((a . b) ...) :test #'eq))`.
fn hayat__assq_arr(x : Value, pairs : Array[(Value, Value)]) -> Value {
  for p in pairs {
    if eq(x, p.0) {
      return p.1
    }
  }
  Nil
}

///|
fn psexpt_fn(p : Value) -> Value raise {
  let mut ans : Value = Nil
  let mut ord_lt0 = false
  if pscoefp(p).truthy() {
    return psexpt_fn2(rcdisrep(p))
  }
  if ps_lim_infp(p).truthy() {
    return psexpt_fn_sing(p)
  }
  ord_lt0 = e_gt(rczero(), ps_le(p)).truthy()
  if n__term(terms(p)) is Nil {
    ans = get_series(
      q_p_exp,
      psexpt_log_ord(p),
      gvar_o(p),
      if ord_lt0 {
        e_(ps_le(p))
      } else {
        ps_le(p)
      },
      ps_lc(p),
    )
    return if ord_lt0 { ps_invert_var(ans) } else { ans }
  }
  let r = if ord_lt0 {
    ans = ps_gt(p)
    if e_eq(rczero(), e(ans)).truthy() {
      pstimes(
        psexpt_fn(
          pscheck(
            gvar_o(p),
            list1(trunc_lvl(p)),
            hayat__delete(ans, terms(p), eq),
          ),
        ),
        psexpt_fn2(srdis(c(ans))),
      )
    } else {
      Nil
    }
  } else if e_eq(rczero(), ps_le(p)).truthy() {
    pstimes(
      psexpt_fn2(srdis(lc(terms(p)))),
      psexpt_fn(
        pscheck(gvar_o(p), list1(trunc_lvl(p)), n__term(terms(p))),
      ),
    )
  } else {
    Nil
  }
  if r.truthy() {
    return r
  }
  let mut l = terms(p)
  if ord_lt0 {
    l = invert_terms(l)
  }
  let mut trunc = trunc_lvl(p)
  let inc = psexpon_gcd(l)
  let ea0 = rcone()
  if !e_gt(le(l), rczero()).truthy() {
    // MEANING OF FOLLOWING MESSAGE IS OBSCURE
    merr("PSEXPT-FN: unreachable point.", []) |> ignore
  }
  ans = if pscoefp(ea0).truthy() || !eq(gvar(p), gvar(ea0)) {
    list2(Fix(0L), term(rczero(), ea0))
  } else {
    cons(Fix(0L), terms(ea0))
  }
  if !symval(q_d_maxtayorder).truthy() {
    trunc = emin(trunc, t_o_var(gvar(p)))
  }
  if trunc is Nil {
    trunc = t_o_var(gvar(p))
  }
  ans = psexpt_fn1(gvar_o(p), trunc, l, inc, Fix(1L), inc, ans)
  if ord_lt0 {
    ps_invert_var(ans)
  } else {
    ans
  }
}

///|
fn psexpt_fn_sing(p : Value) -> Value raise {
  let inf_var_q = hayat__memq_arr(gvar_lim(gvar(p)), [q_d_inf, q_d_minf])
  let clogs = c_starlogs(lt_poly(p))
  // Must pull out out logs here: exp(ci*log(ui)+x) -> ui^ci*exp(x)
  // since its much harder for adjoin-tvar to do this transformation
  // below after things have been disrepped.
  let mut cc = exp_c_starlogs(clogs)
  let p = psdiff(p, sum_c_starlogs(clogs))
  if !ps_lim_infp(p).truthy() {
    // Here we just subtracted the only infinite term, e.g.
    // p = 1/2*log(x)+1/log(x)+...
    pstimes(cc, psexpt_fn(p))
  } else {
    let strongest_term = if inf_var_q { ps_gt(p) } else { ps_lt(p) }
    // If the strongest term has degree 0 in the mainvar then the singular
    // terms occur in some other weaker var. There may be terms in this coef
    // which are not singular (e.g. 1 in (1/x+1+...)+exp(-1/x)+...) so we
    // must recursively psexpt-fn this term to get only what we need.
    if rczerop(e(strongest_term)).truthy() {
      cc = pstimes(cc, psexpt_fn(c(strongest_term)))
    } else {
      for exp_ in expand_and_disrep(strongest_term, p).iter() {
        cc = pstimes(cc, adjoin_tvar(power_star(q_d__pcte, exp_)))
      }
    }
    pstimes(
      cc,
      psexpt_fn(
        pscheck(
          gvar_o(p),
          list1(trunc_lvl(p)),
          if inf_var_q {
            hayat__delete(strongest_term, terms(p), eq)
          } else {
            n__term(terms(p))
          },
        ),
      ),
    )
  }
}

///|
fn gvar_logp(gvar : Value) -> Value raise {
  let mut var2 = get_inverse(gvar)
  if consp(var2) &&
    eq(caar(var2), q_mexpt) &&
    equal(caddr(var2), Fix(-1L)) &&
    {
      var2 = cadr(var2)
      consp(var2)
    } &&
    eq(caar(var2), q_p_log) {
    var2
  } else {
    Nil
  }
}

///|
fn c_starlogs(p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    Nil
  } else {
    let log = gvar_logp(gvar(p))
    if !log.truthy() {
      Nil
    } else {
      let c = psconst(psterm(terms(p), rcmone()))
      // We don't want e.g. exp(x^a*log(x)) -> x^x^a
      if !mfree(rcdisrep(c), symval(q_tvars)).truthy() {
        Nil
      } else {
        cons(cons(c, cons(log, p)), c_starlogs(psterm(terms(p), rczero())))
      }
    }
  }
}

///|
fn psconst(p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    p
  } else {
    psconst(psterm(terms(p), rczero()))
  }
}

///|
fn exp_c_starlogs(c_starlogs : Value) -> Value raise {
  if c_starlogs is Nil {
    rcone()
  } else {
    pstimes(
      taylor2(
        mk(q_mexpt, [cadr(cadr(car(c_starlogs))), rcdisrep(caar(c_starlogs))]),
      ),
      exp_c_starlogs(cdr(c_starlogs)),
    )
  }
}

///|
fn sum_c_starlogs(c_starlogs : Value) -> Value raise {
  if c_starlogs is Nil {
    rczero()
  } else {
    let ps = cddr(car(c_starlogs))
    psplus(
      make_ps(ps, list1(term(ps_le(ps), caar(c_starlogs)))),
      sum_c_starlogs(cdr(c_starlogs)),
    )
  }
}

// Calculates the limit of a series at the expansion point. Returns one of
// {$zeroa, $zerob, $pos, $neg, $inf, $minf}.
// TVAR-LIMITS is a list of the form ((gvar . limit(gvar)) ...).

///|
fn ps_lim_infp(ps : Value) -> Value raise {
  if pscoefp(ps).truthy() {
    Nil
  } else {
    // Assume taylor vars at 0+ for now. Should handle the cases when the
    // expansion point is INF, MINF,etc.
    let mut lim = gvar_lim(gvar(ps))
    let strongest_term = if hayat__memq_arr(lim, [q_d_inf, q_d_minf]) {
      ps_gt(ps)
    } else {
      ps_lt(ps)
    }
    if ezerop(e(strongest_term)).truthy() {
      ps_lim_infp(c(strongest_term))
    } else {
      lim = lim_power(lim, e(strongest_term))
      lbool(lim_infp(lim).truthy() && !eq(lim, q_d_infinity))
    }
  }
}

///|
fn lim_zerop(lim : Value) -> Value raise {
  lbool(hayat__memq_arr(lim, [q_d_zeroa, q_d_zerob, q_d_zeroim]))
}

///|
fn lim_plusp(lim : Value) -> Value raise {
  lbool(hayat__memq_arr(lim, [q_d_zeroa, q_d_pos, q_d_inf, q_d_finite]))
}

///|
fn lim_finitep(lim : Value) -> Value raise {
  lbool(hayat__memq_arr(lim, [q_d_pos, q_d_neg, q_d_im, q_d_finite]))
}

///|
fn lim_infp(lim : Value) -> Value raise {
  lbool(hayat__memq_arr(lim, [q_d_inf, q_d_minf, q_d_infinity]))
}

///|
fn lim_imagp(lim : Value) -> Value raise {
  lbool(hayat__memq_arr(lim, [q_d_im, q_d_infinity]))
}

///|
fn lim_minus(lim : Value) -> Value raise {
  hayat__assq_arr(lim, [
    (q_d_zeroa, q_d_zerob),
    (q_d_zerob, q_d_zeroa),
    (q_d_pos, q_d_neg),
    (q_d_zero, q_d_zero),
    (q_d_neg, q_d_pos),
    (q_d_inf, q_d_minf),
    (q_d_minf, q_d_inf),
    (q_d_im, q_d_im),
    (q_d_infinity, q_d_infinity),
    (q_d_finite, q_d_finite),
  ])
}

///|
fn lim_abs(lim : Value) -> Value raise {
  let r = hayat__assq_arr(lim, [
    (q_d_zerob, q_d_zeroa),
    (q_d_neg, q_d_pos),
    (q_d_minf, q_d_inf),
  ])
  if r.truthy() {
    r
  } else {
    lim
  }
}

///|
fn lim_times(lim1 : Value, lim2 : Value) -> Value raise {
  let mut lim1 = lim1
  let mut lim2 = lim2
  let mut lim : Value = Nil
  if eq(lim1, q_d_zero) || eq(lim2, q_d_zero) {
    lim = q_d_zero
  } else if lim_infp(lim1).truthy() && lim_infp(lim2).truthy() {
    lim = q_d_inf
  } else if lim_zerop(lim1).truthy() && lim_zerop(lim2).truthy() {
    lim = q_d_pos
  } else if (if lim_finitep(lim2).truthy() {
               let tmp = lim1
               lim1 = lim2
               lim2 = tmp
               true
             } else {
               false
             }) ||
    lim_finitep(lim1).truthy() {
    // After the ROTATEF above, LIM1 is the finite one, so the infinity test
    // must look at LIM2.
    if eq(lim1, q_d_finite) && lim_infp(lim2).truthy() {
      tay_error(Str("Undefined finite*inf in lim-times"), lim2) |> ignore
    }
    lim = lim_abs(lim2)
  } else {
    tay_error(
      Str("Undefined limit product in lim-times"),
      list3(list1(q_mtimes), lim1, lim2),
    )
    |> ignore
  }
  if lim_imagp(lim1).truthy() || lim_imagp(lim2).truthy() {
    if lim_infp(lim).truthy() {
      q_d_infinity
    } else {
      q_d_im
    }
  } else if lim_plusp(lim1).truthy() && lim_plusp(lim2).truthy() {
    lim
  } else {
    lim_minus(lim)
  }
}

///|
fn lim_power(lim : Value, power : Value) -> Value raise {
  if ezerop(power).truthy() {
    q_d_pos
  } else if e_gt(rczero(), power).truthy() {
    lim_recip(lim_power(lim, e_(power)))
  } else if !oddp(car(power)) {
    if lim_plusp(lim).truthy() {
      lim
    } else {
      lim_minus(lim)
    }
  } else {
    lim
  }
}

///|
fn lim_recip(lim : Value) -> Value raise {
  let r = hayat__assq_arr(lim, [
    (q_d_zeroa, q_d_inf),
    (q_d_zerob, q_d_minf),
    (q_d_inf, q_d_zeroa),
    (q_d_minf, q_d_zerob),
  ])
  if r.truthy() {
    r
  } else if eq(lim, q_d_finite) {
    raise LispError::SimpleError("inverting $finite?")
  } else {
    lim
  }
}

///|
fn lim_exp(lim : Value) -> Value raise {
  if hayat__memq_arr(lim, [
      q_d_zeroa, q_d_zerob, q_d_zero, q_d_pos, q_d_neg, q_d_minf,
    ]) {
    q_d_zeroa
  } else if hayat__memq_arr(lim, [q_d_inf, q_d_finite]) {
    lim
  } else if eq(lim, q_d_infinity) {
    // actually only if Re lim = inf
    q_d_infinity
  } else {
    raise LispError::SimpleError("Unhandled limit in lim-exp")
  }
}

///|
fn lim_log(lim : Value) -> Value raise {
  if eq(lim, q_d_zeroa) {
    q_d_minf
  } else if eq(lim, q_d_inf) {
    q_d_inf
  } else if eq(lim, q_d_minf) {
    q_d_infinity
  } else if eq(lim, q_d_zerob) {
    q_d_infinity
  } else {
    raise LispError::SimpleError("Unhandled limit in lim-log")
  }
}

///|
fn expand_and_disrep(term : Value, p : Value) -> Value raise {
  let x_n = list3(list1(q_mexpt), get_inverse(gvar(p)), edisrep(e(term)))
  let a = c(term)
  if pscoefp(a).truthy() {
    list1(mul2_star(srdis(a), x_n))
  } else {
    mapcar(
      subterm => mul2_star(
        cons(list1(q_mtimes), expand_and_disrep(subterm, a)),
        x_n,
      ),
      terms(a),
    )
  }
}

///|
fn adjoin_sing_datum(d : Value) -> Value raise {
  let r = prep1(datum_var(d))
  let g = gensym()
  let kernel = datum_var(d)
  let mut pg : Value = Nil
  let no = one_plus(cdr(int_var(car(last(symval(q_tlist))))))
  let one_one = list2(Fix(1L), Fix(1L))
  if equal(cdr(r), Fix(1L)) && consp(car(r)) && equal(cdar(r), one_one) {
    // Direct polynomial case: ((G 1 1) . 1)
    pg = caar(r)
  } else if equal(car(r), Fix(1L)) && consp(cdr(r)) && equal(cddr(r), one_one) {
    // Reciprocal case: (1 . (G 1 1))
    pg = cadr(r)
  } else {
    raise LispError::SimpleError("bad singular datum")
  }
  putprop(g, kernel, q_disrep) |> ignore
  rplacd(cdddr(d), cons(g, no)) |> ignore
  adjoin_datum(d) |> ignore
  push_special(cons(pg, kernel), q_key_vars) |> ignore
  push_special(cons(g, kernel), q_key_vars) |> ignore
  push_special(car(symval(q_key_vars)), q_ivars) |> ignore
  push_special(cons(g, exp_pt(d)), q_tvar_limits)
}

///|
fn adjoin_tvar(exp_ : Value) -> Value raise {
  rat__gtps(prep1(exp_))
}

///|
fn rat__gtps(rat : Value) -> Value raise {
  pstimes(poly__gtps(car(rat)), psexpt(poly__gtps(cdr(rat)), rcmone()))
}

///|
fn poly__gtps(poly : Value) -> Value raise {
  let polyd = pdis(poly)
  if mfree(polyd, symval(q_tvars)).truthy() {
    return prep1(polyd)
  }
  let mut g = p__var(poly)
  let mut datum = key_var_pow(g)
  let mut pow = rcone()
  if datum.truthy() {
    g = car(datum)
    pow = cdr(datum)
  } else {
    let r = adjoin_pvar(g)
    g = car(r)
    pow = cdr(r)
  }
  if consp(g) {
    // G is an evaluated PSCOEF or PS. Evaluate POLY(G) mathematically.
    let mut po_terms = p__terms(poly)
    let mut ans = rczero()
    while !(po_terms is Nil) {
      ans = psplus(
        ans,
        pstimes(
          poly__gtps(pt_lc(po_terms)),
          psexpt(g, e_star(pow, prep1(pt_le(po_terms)))),
        ),
      )
      po_terms = p__red(po_terms)
    }
    ans
  } else {
    // Normal case: G is a GENSYM. Build the PS structurally.
    datum = gvar_data(g)
    let mut po_terms = p__terms(poly)
    let mut ps_terms : Value = Nil
    while !(po_terms is Nil) {
      ps_terms = cons(
        term(e_star(pow, prep1(pt_le(po_terms))), poly__gtps(pt_lc(po_terms))),
        ps_terms,
      )
      po_terms = p__red(po_terms)
    }
    // This must be exact so that when we invert in rat-ps above we don't
    // lose any terms. E.g. try taylor(log(1+exp(-1/x)),x,0,5).
    make_ps(
      int_var(datum),
      list1(current_trunc(datum)),
      terms=if eq(g, data_gvar(datum)) {
        ps_terms
      } else {
        invert_terms(ps_terms)
      },
    )
  }
}

///|
fn key_var_pow(g : Value) -> Value raise {
  let var2 = get_key_var(g)
  if var2.truthy() {
    let datum = get_datum(var2)
    let g2 = data_gvar(datum)
    if eq(g, g2) {
      cons(g2, rcone())
    } else {
      cons(g2, rcmone())
    }
  } else {
    Nil
  }
}

///|
fn adjoin_pvar(g : Value) -> Value raise {
  let mut g = g
  let mut kernel = get(g, q_disrep)
  let mut lim : Value = Nil
  let no = one_plus(cdr(int_var(car(last(symval(q_tlist))))))
  let mut pow = rcone()
  let mut expt : Value = Nil
  if assol(kernel, symval(q_tlist)).truthy() {
    raise LispError::SimpleError("bad1")
  }
  if eq(caar(kernel), q_mexpt) &&
    eq(cadr(kernel), q_d__pcte) &&
    {
      expt = caddr(kernel)
      !atom(expt)
    } &&
    eq(caar(expt), q_mtimes) &&
    !mfree(expt, list1(q_d__pcti)).truthy() {
    let rp = trisplit(expt)
    let rpart = car(rp)
    let ipart = cdr(rp)
    return cons(
      pstimes(
        prep1(power_star(q_d__pcte, rpart)),
        psplus(
          adjoin_tvar(ftake(q_p_cos, [ipart])),
          pstimes(prep1(q_d__pcti), adjoin_tvar(ftake(q_p_sin, [ipart]))),
        ),
      ),
      pow,
    )
  }
  if eq(caar(kernel), q_mexpt) {
    expt = caddr(kernel)
    if !atom(expt) &&
      eq(caar(expt), q_mtimes) &&
      d_ratnump(cadr(expt)).truthy() {
      pow = cadr(expt)
      kernel = power_star(kernel, inv_star(pow))
      g = prep1(kernel)
      pow = prep1(pow)
      if !(equal(cdr(g), Fix(1L)) && equal(cdar(g), list2(Fix(1L), Fix(1L)))) {
        raise LispError::SimpleError("Illegal kernel in `adjoin-pvar'")
      }
      g = caar(g)
      kernel = get(g, q_disrep)
    }
  }
  let ans = key_var_pow(g)
  if ans.truthy() {
    return cons(car(ans), e_star(pow, cdr(ans)))
  }
  if lim_infp(
      if lim.truthy() {
        lim
      } else {
        lim = tvar_lim(kernel)
        lim
      },
    ).truthy() {
    let g_star = g
    g = gensym()
    kernel = inv_star(kernel)
    lim = lim_recip(lim)
    pow = e_star(rcmone(), pow)
    putprop(g, kernel, q_disrep) |> ignore
    push_special(cons(g_star, kernel), q_key_vars) |> ignore
  }
  if assol(kernel, symval(q_tlist)).truthy() {
    raise LispError::SimpleError("bad2")
  }
  let datum = list_star([
    kernel,
    copy_list(trunc_stack(car(symval(q_tlist)))),
    lim,
    Nil,
    g,
    no,
  ])
  adjoin_datum(datum) |> ignore
  push_special(cons(g, kernel), q_key_vars) |> ignore
  push_special(car(symval(q_key_vars)), q_ivars) |> ignore
  push_special(cons(g, lim), q_tvar_limits) |> ignore
  cons(g, pow)
}

///|
fn adjoin_datum(datum : Value) -> Value raise {
  let mut tl1 = symval(q_tlist)
  let mut tl2 : Value = Nil
  while !(tl1 is Nil) {
    if stronger_var_q(datum_var(car(tl1)), datum_var(datum)).truthy() {
      if tl2 is Nil {
        push_special(datum, q_tlist) |> ignore
        return renumber_tlist(symval(q_tlist))
      } else {
        rplacd(tl2, cons(datum, tl1)) |> ignore
        return renumber_tlist(cdr(tl2))
      }
    }
    tl2 = tl1
    tl1 = cdr(tl1)
  }
  set(q_tlist, nconc(symval(q_tlist), list1(datum)))
}

///|
/// Maybe this should just permute the numbering in case it isn't
/// sequential?
fn renumber_tlist(tlist : Value) -> Value raise {
  rplacd(data_gvar_o(car(tlist)), cdr(data_gvar_o(cadr(tlist)))) |> ignore
  let mut tl = cdr(tlist)
  while !(tl is Nil) {
    rplacd(data_gvar_o(car(tl)), one_plus(cdr(data_gvar_o(car(tl))))) |> ignore
    tl = cdr(tl)
  }
  Nil
}

///|
fn tvar_q(var2 : Value) -> Value raise {
  if atom(var2) {
    t
  } else {
    memq(q_array, cdar(var2))
  }
}

///|
/// Needs to be extended to handle singular tvars in > 1 var's.
fn stronger_var_q(v1 : Value, v2 : Value) -> Value raise {
  let mut v1 = v1
  let mut v2 = v2
  let mut e1 = rcone()
  let mut e2 = rcone()
  let mut reverse_q = false
  if alike1(v1, v2).truthy() {
    tay_err(Str("taylor: stronger-var? called on equal vars.")) |> ignore
  }
  if mexptp(v1).truthy() && d_ratnump(caddr(v1)).truthy() {
    e1 = prep1(caddr(v1))
    v1 = cadr(v1)
  }
  if mexptp(v2).truthy() && d_ratnump(caddr(v2)).truthy() {
    e2 = prep1(caddr(v2))
    v2 = cadr(v2)
  }
  if alike1(v1, v2).truthy() {
    return if equal(e1, e2) {
      tay_err(Str("taylor: stronger-var? called on equal vars."))
    } else {
      e_gt(e1, e2)
    }
  }
  if eq(tvar_lim(v2), q_d_finite) {
    let tv = v1
    v1 = v2
    v2 = tv
    let te = e1
    e1 = e2
    e2 = te
    reverse_q = !reverse_q
  }
  if eq(tvar_lim(v1), q_d_finite) {
    return if eq(tvar_lim(v2), q_d_finite) {
      great(v1, v2)
    } else {
      lbool(reverse_q)
    }
  }
  if mtimesp(v2).truthy() {
    let tv = v1
    v1 = v2
    v2 = tv
    let te = e1
    e1 = e2
    e2 = te
    reverse_q = !reverse_q
  }
  let ans = if mtimesp(v1).truthy() {
    stronger_vars_q(
      order_vars_by_strength(cdr(v1)),
      order_vars_by_strength(
        if mtimesp(v2).truthy() {
          cdr(v2)
        } else {
          list1(power_star(v2, edisrep(e2)))
        },
      ),
    )
  } else {
    if tvar_q(v2).truthy() {
      let tv = v1
      v1 = v2
      v2 = tv
      let te = e1
      e1 = e2
      e2 = te
      reverse_q = !reverse_q
    }
    if tvar_q(v1).truthy() {
      if tvar_q(v2).truthy() {
        let n1 = cdr(data_gvar_o(get_datum(v1, not_canonicalized_q=t)))
        let n2 = cdr(data_gvar_o(get_datum(v2, not_canonicalized_q=t)))
        lbool(num_gt(n1, n2))
      } else if mfree(v2, list1(v1)).truthy() {
        tay_err(Str("taylor: Unhandled multivar datum comparison."))
      } else if eq(caar(v2), q_p_log) {
        t
      } else if eq(caar(v2), q_mexpt) && eq(cadr(v2), q_d__pcte) {
        stronger_var_q(list2(list1(q_p_log), v1), caddr(v2))
      } else {
        tay_err(Str("taylor: Unhandled var in stronger-var?."))
      }
    } else {
      if eq(caar(v2), q_p_log) {
        let tv = v1
        v1 = v2
        v2 = tv
        let te = e1
        e1 = e2
        e2 = te
        reverse_q = !reverse_q
      }
      if eq(caar(v1), q_p_log) {
        if eq(caar(v2), q_p_log) {
          stronger_var_q(cadr(v1), cadr(v2))
        } else if eq(caar(v2), q_mexpt) && eq(cadr(v2), q_d__pcte) {
          stronger_var_q(list2(list1(q_p_log), v1), caddr(v2))
        } else {
          tay_err(Str("taylor: Unhandled var in stronger-var?"))
        }
      } else if eq(caar(v1), q_mexpt) &&
        eq(cadr(v1), q_d__pcte) &&
        eq(caar(v2), q_mexpt) &&
        eq(cadr(v2), q_d__pcte) {
        stronger_var_q(caddr(v1), caddr(v2))
      } else {
        tay_err(Str("taylor: Unhandled var in stronger-var?"))
      }
    }
  }
  if reverse_q {
    lbool(ans is Nil)
  } else {
    ans
  }
}

///|
fn neg_monom_q(exp_ : Value) -> Value raise {
  if mtimesp(exp_).truthy() &&
    equal(cadr(exp_), Fix(-1L)) &&
    cdddr(exp_) is Nil {
    caddr(exp_)
  } else {
    Nil
  }
}

///|
fn order_vars_by_strength(vars : Value) -> Value raise {
  let mut ordvars : Value = Nil
  let mut vs = vars
  while !(vs is Nil) {
    // ignore constants
    if !mfree(car(vs), symval(q_tvars)).truthy() {
      let mut ov = ordvars
      while true {
        if ov is Nil {
          if ordvars is Nil {
            ordvars = list1(car(vs))
          } else {
            rplacd(last(ordvars), list1(car(vs))) |> ignore
          }
          break
        }
        if stronger_var_q(car(vs), car(ov)).truthy() {
          rplacd(ov, cons(car(ov), cdr(ov))) |> ignore
          rplaca(ov, car(vs)) |> ignore
          break
        }
        ov = cdr(ov)
      }
    }
    vs = cdr(vs)
  }
  ordvars
}

///|
fn stronger_vars_q(vars1 : Value, vars2 : Value) -> Value raise {
  let mut v1 = vars1
  let mut v2 = vars2
  while true {
    if v1 is Nil {
      if v2 is Nil {
        // two equal vars generated
        return t
      } else {
        let lim = tvar_lim(car(v2))
        return if lim_infp(lim).truthy() {
          Nil
        } else if lim_zerop(lim).truthy() {
          t
        } else {
          raise LispError::SimpleError("var with non-zero finite lim?")
        }
      }
    } else if v2 is Nil {
      let lim = tvar_lim(car(v1))
      return if lim_infp(lim).truthy() {
        t
      } else if lim_zerop(lim).truthy() {
        Nil
      } else {
        raise LispError::SimpleError("var with non-zero finite lim?")
      }
    } else if alike1(car(v1), car(v2)).truthy() {
      ()
    } else {
      return stronger_var_q(car(v1), car(v2))
    }
    v1 = cdr(v1)
    v2 = cdr(v2)
  }
  Nil
}

///|
fn stronger_datum_q(d1 : Value, d2 : Value) -> Value raise {
  let d1 = datum_var(d1)
  let d2 = datum_var(d2)
  let mut end_flag = false
  let mut answer : Value = Nil
  while !end_flag {
    answer = retrieve(
      list([list1(q_mtext), sym("Is  "), d1, sym(" stronger than "), d2, sym("?")]),
      Nil,
    )
    if hayat__memq_arr(answer, [q_d_yes, q_d_y, q_d_no, q_d_n]) {
      end_flag = true
    } else {
      mtell(list1(Str("~%Acceptable answers are: yes, y, no, n~%"))) |> ignore
    }
  }
  memq(answer, list2(q_d_yes, q_d_y))
}

///|
fn datum_lim(datum : Value) -> Value raise {
  if !tvar_q(datum_var(datum)).truthy() {
    exp_pt(datum)
  } else {
    let pt = exp_pt(datum)
    if hayat__memq_arr(pt, [q_d_inf, q_d_minf]) {
      pt
    } else {
      q_d_zeroa
    }
  }
}

///|
fn tvar_lim(kernel : Value) -> Value raise {
  if mfree(kernel, symval(q_tvars)).truthy() {
    return coef_sign(kernel)
  }
  let mut datum = get_datum(kernel, not_canonicalized_q=t)
  if datum.truthy() {
    let r = datum_lim(datum)
    if r.truthy() {
      return r
    }
  }
  datum = get_datum(inv_star(kernel), not_canonicalized_q=t)
  if datum.truthy() {
    let lim = datum_lim(datum)
    if lim.truthy() {
      let r = lim_recip(lim)
      if r.truthy() {
        return r
      }
    }
  }
  if eq(caar(kernel), q_mexpt) {
    datum = get_datum(cadr(kernel), not_canonicalized_q=t)
    if datum.truthy() && d_ratnump(caddr(kernel)).truthy() {
      lim_power(datum_lim(datum), prep1(caddr(kernel)))
    } else if d_ratnump(caddr(kernel)).truthy() {
      lim_power(tvar_lim(cadr(kernel)), prep1(caddr(kernel)))
    } else if eq(cadr(kernel), q_d__pcte) {
      lim_exp(tvar_lim(caddr(kernel)))
    } else {
      tay_error(Str("Unhandled case in tvar-lim"), kernel)
    }
  } else if eq(caar(kernel), q_mtimes) {
    let mut ans = tvar_lim(cadr(kernel))
    let mut facs = cddr(kernel)
    while !(facs is Nil) {
      ans = lim_times(ans, tvar_lim(car(facs)))
      facs = cdr(facs)
    }
    ans
  } else if eq(caar(kernel), q_p_log) {
    lim_log(datum_lim(get_datum(cadr(kernel), not_canonicalized_q=t)))
  } else if hayat__memq_arr(caar(kernel), [q_p_sin, q_p_cos]) {
    if !lim_infp(tvar_lim(cadr(kernel))).truthy() {
      tay_error(Str("Invalid trig kernel in tvar-lim"), kernel) |> ignore
    }
    q_d_finite
  } else {
    tay_error(Str("Unhandled kernel in tvar-lim"), kernel)
  }
}

///|
/// Determine the sign of COEF. First, find the sign using `$csign`. If
/// `$csign` returns `$complex` or `$imaginary`, return `$im`; if the sign is
/// `$neg` or `$pos`, return those values.
fn coef_sign(coef : Value) -> Value raise {
  let sgn = d_csign(coef)
  if eq(sgn, q_d_complex) || eq(sgn, q_d_imaginary) {
    q_d_im
  } else if hayat__memq_arr(sgn, [q_d_neg, q_d_zero, q_d_pos]) {
    sgn
  } else {
    d_asksign(coef)
  }
}

///|
fn gvar_lim(gvar : Value) -> Value raise {
  let r = cdr(assq(gvar, symval(q_tvar_limits)))
  if r.truthy() {
    r
  } else if memq(gvar__gtvar(gvar), symval(q_tvars)).truthy() {
    // user tvars assumed 0+ now
    q_d_zeroa
  } else {
    raise LispError::SimpleError("Invalid gvar")
  }
}

///|
fn psexpt_fn1(
  varh : Value,
  trunc : Value,
  l : Value,
  inc : Value,
  m : Value,
  mr : Value,
  ans : Value,
) -> Value raise {
  let mut m = to_int64(m)
  let mut mr = mr
  let mut a = last(ans)
  while true {
    // tag B
    if e_gt(mr, trunc).truthy() {
      break
    }
    let mut kr = inc
    let mut ak = l
    let mut k = 1L
    let mut sum = rczero()
    let lim = m
    while true {
      // tag A
      if k > lim {
        break
      }
      let cm_k = psterm(cdr(ans), e_(mr, e2=kr))
      if cm_k is Nil {
        break
      }
      let ak1 = pstrim_terms(ak, kr)
      if ak1 is Nil {
        break
      }
      ak = ak1
      let c = pstimes(ereduce(Fix(k), Fix(m)), pstimes(psterm1(ak, kr), cm_k))
      sum = psplus(sum, c)
      k = k + 1
      kr = e_plus(kr, inc)
    }
    // tag ADD-TERM
    if !rczerop(sum).truthy() {
      add_term(a, term_or_e=mr, c=sum) |> ignore
      a = n__term(a)
    }
    m = m + 1
    mr = e_plus(mr, inc)
  }
  pscheck(varh, list1(trunc), cdr(ans))
}

// PSEXPT-FN2 and RED-MONO-LOG are needed to reduce exponentials of logs.

///|
fn psexpt_fn2(p : Value) -> Value raise {
  if atom(p) {
    if get_datum(p).truthy() {
      psexpt_fn(taylor2(p))
    } else {
      prep1(mk(q_mexpt, [q_d__pcte, p]))
    }
  } else if eq(caar(p), q_p_log) {
    if get_datum(cadr(p)).truthy() {
      taylor2(cadr(p))
    } else {
      prep1(cadr(p))
    }
  } else if eq(caar(p), q_mplus) || eq(caar(p), q_mtimes) {
    let e = d_ratexpand(p)
    if !(consp(e) && hayat__memq_arr(caar(e), [q_mplus, q_mtimes])) {
      psexpt_fn2(e)
    } else if eq(caar(e), q_mplus) {
      let mut log_facs : Value = Nil
      let mut l : Value = Nil
      let mut sumnds = cdr(e)
      while !(sumnds is Nil) {
        let temp = red_mono_log(car(sumnds))
        if temp.truthy() {
          log_facs = cons(temp, log_facs)
        } else {
          l = cons(car(sumnds), l)
        }
        sumnds = cdr(sumnds)
      }
      if !log_facs.truthy() {
        tsexpt(q_d__pcte, p)
      } else {
        tstimes(cons(power(q_d__pcte, addn(l, Nil)), log_facs))
      }
    } else {
      let temp = red_mono_log(e)
      if temp.truthy() {
        taylor2(temp)
      } else {
        prep1(power(q_d__pcte, p))
      }
    }
  } else {
    prep1(power(q_d__pcte, p))
  }
}

///|
fn red_mono_log(e : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if eq(caar(e), q_p_log) {
    cadr(e)
  } else if mtimesp(e).truthy() {
    let mut facs = cdr(e)
    let mut log_term : Value = Nil
    while !(facs is Nil) {
      if !atom(car(facs)) && eq(caaar(facs), q_p_log) {
        if log_term.truthy() {
          return Nil
        } else {
          log_term = car(facs)
        }
      } else if !mfree(car(facs), symval(q_tvars)).truthy() {
        return Nil
      }
      facs = cdr(facs)
    }
    if log_term.truthy() {
      power(cadr(log_term), muln(remove(log_term, cdr(e)), Nil))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn pslog(p : Value) -> Value raise {
  if pscoefp(p).truthy() {
    return pslog2(rcdisrep(p))
  }
  let mut terms = terms(p)
  if mono_term_q(terms).truthy() {
    // log(c x^n) = log(c) + n log(x); do this always for now
    return pslog_monom(p)
  }
  // expand log(1+ax^n) directly by series substitution
  terms = cdddr(psplus(p, rcmone()))
  if !(n__term(terms).truthy() || ps_lim_infp(p).truthy()) {
    let p = get_series(
      q_p_log,
      psexpt_log_ord(p),
      gvar_o(p),
      if e_gt(rczero(), le(terms)).truthy() {
        e_(le(terms))
      } else {
        le(terms)
      },
      lc(terms),
    )
    return if e_gt(rczero(), le(terms)).truthy() { ps_invert_var(p) } else { p }
  }
  with_special(q_d_maxtayorder, Nil, () => {
    let mut p = p
    // log(lt+y) = log(lt) + log(1 + y/lt) = lterm + p
    let mut trunc = trunc_lvl(p)
    let gvar_lim = gvar_lim(gvar(p))
    let mut lt : Value = Nil
    let mut gt : Value = Nil
    if !hayat__memq_arr(gvar_lim, [q_d_zeroa, q_d_zerob, q_d_inf, q_d_minf]) {
      tay_error(Str("bad gvar lim"), gvar_lim) |> ignore
    } else if hayat__memq_arr(gvar_lim, [q_d_inf, q_d_minf]) {
      lt = ps_gt(p)
      gt = lt
    } else {
      lt = ps_lt(p)
      gt = Nil
    }
    lt = pscheck(gvar_o(p), list1(trunc), list1(lt))
    let lterm = pslog(lt)
    p = pstimes(p, with_special(q_d_maxtayorder, t, () => psexpt(lt, rcmone())))
    if hayat__memq_arr(gvar_lim, [q_d_inf, q_d_minf]) &&
      e_gt(le(terms), rczero()).truthy() {
      return psplus(lterm, pslog(p))
    }
    if pscoefp(p).truthy() {
      if !equal(p, rcone()) {
        merr("PSLOG: internal error.", []) |> ignore
      }
      return lterm
    }
    let mut l = cdddr(p)
    let mut inc = psexpon_gcd(l)
    if gt.truthy() {
      l = hayat__delete(last(l), l, equal)
    } else {
      l = n__term(l)
    }
    let mut ans = list1(Fix(0L))
    if !symval(q_d_maxtayorder).truthy() {
      trunc = emin(trunc, t_o_var(gvar(p)))
    }
    // When we've divided by the greatest term, all terms have non-positive
    // exponents and we must perform the transformation x -> 1/x before
    // calling pslog1 and then perform the inverse afterwards.
    if gt.truthy() {
      l = invert_terms(l)
    }
    if e_gt(rczero(), inc).truthy() {
      inc = e_(inc)
    }
    ans = psplus(lterm, pslog1(gvar_o(p), trunc, l, inc, Fix(1L), inc, ans))
    if gt.truthy() && psp(ans).truthy() && eq(gvar(ans), gvar(p)) {
      ps_invert_var(ans)
    } else {
      ans
    }
  })
}

///|
fn invert_terms(terms : Value) -> Value raise {
  nreverse(
    mapc(x => rplaca(x, e_(e(x))) |> ignore, terms),
  )
}

///|
fn ps_invert_var(ps : Value) -> Value raise {
  if psp(ps).truthy() {
    rplacd(cddr(ps), invert_terms(terms(ps))) |> ignore
  }
  ps
}

///|
fn ps_gt(ps : Value) -> Value raise {
  if pscoefp(ps).truthy() {
    term(rczero(), ps)
  } else {
    lt(last(terms(ps)))
  }
}

///|
fn pslog1(
  varh : Value,
  trunc : Value,
  l : Value,
  inc : Value,
  m : Value,
  mr : Value,
  ans : Value,
) -> Value raise {
  let mut m = to_int64(m)
  let mut mr = mr
  let mut a = last(ans)
  while true {
    // tag B
    if e_gt(mr, trunc).truthy() {
      break
    }
    let mut kr = inc
    let mut ak = l
    let mut k = 1L
    let mut sum = rczero()
    while true {
      // tag A
      if k == m {
        break
      }
      let m_kr = e_(mr, e2=kr)
      let cm_k = psterm(cdr(ans), m_kr)
      if cm_k is Nil {
        break
      }
      let ak1 = pstrim_terms(ak, kr)
      if ak1 is Nil {
        break
      }
      ak = ak1
      let c = pstimes(m_kr, pstimes(psterm1(ak, kr), cm_k))
      sum = psplus(sum, c)
      k = k + 1
      kr = e_plus(kr, inc)
    }
    // tag ADD-TERM
    let c = {
      let c0 = pstrim_terms(ak, mr)
      if c0.truthy() {
        psterm1(c0, mr)
      } else {
        rczero()
      }
    }
    sum = psdiff(c, pstimes(sum, e_sl_sl(mr)))
    if !rczerop(sum).truthy() {
      add_term(a, term_or_e=mr, c=sum) |> ignore
      a = n__term(a)
    }
    m = m + 1
    mr = e_plus(mr, inc)
  }
  pscheck(varh, list1(trunc), cdr(ans))
}

///|
/// Computes log(monom), where monom = c x^n. Is extra careful trying to
/// keep singular logs going to INF and not generating log(-1)'s unless it
/// is necessary to transform a log at MINF to INF.
fn pslog_monom(monom : Value) -> Value raise {
  let gvar = gvar(monom)
  let datum = gvar_data(gvar)
  let mut logvar : Value = Nil
  let mut c : Value = Nil
  if switch(q_multivar, datum).truthy() {
    return pslog(ps_lc(monom))
  }
  let var2 = datum_var(datum)
  if tvar_q(var2).truthy() {
    let pt = exp_pt(datum)
    if !hayat__memq_arr(pt, [q_d_inf, q_d_minf]) {
      logvar = adjoin_tvar(list2(list1(q_p_log), sub_star(var2, pt)))
    } else {
      // At x = inf: log(c (1/x)^n) -> log(c) - n log(x)
      // At x = minf: log(c (-1/x)^n) -> log(c (-1)^n) - n log(x)
      logvar = psminus(adjoin_tvar(list2(list1(q_p_log), var2)))
      if eq(pt, q_d_minf) {
        c = rcexpt(rcmone(), ps_le(monom))
      }
    }
  } else if eq(caar(var2), q_mexpt) {
    if equal(caddr(var2), Fix(-1L)) {
      // var2 must be 1/log(y). Try to keep inf's real. Here we want
      // log(c (1/log(x))^n) -> log(c (-1)^n) - n log(-log(x))
      if equal(tvar_lim(cadr(var2)), q_d_minf) {
        c = rcexpt(rcmone(), ps_le(monom))
        logvar = psminus(
          adjoin_tvar(
            list2(list1(q_p_log), mul2_star(Fix(-1L), cadr(var2))),
          ),
        )
      } else {
        logvar = psminus(adjoin_tvar(list2(list1(q_p_log), cadr(var2))))
      }
    } else if equal(cadr(var2), q_d__pcte) {
      logvar = taylor2(caddr(var2))
    } else {
      raise LispError::SimpleError("Unhandled gvar in `pslog-of-gvar'")
    }
  }
  psplus(
    pslog(
      if c.truthy() {
        pstimes(c, ps_lc(monom))
      } else {
        ps_lc(monom)
      },
    ),
    pstimes(ps_le(monom), logvar),
  )
}

///|
/// Computes log(p), where p is an rcdisrep'd pscoef.
fn pslog2(p : Value) -> Value raise {
  with_special(q_d_logarc, Nil, () => pslog3(p))
}

///|
fn pslog3(p : Value) -> Value raise {
  if atom(p) {
    prep1(
      if equal(p, Fix(1L)) {
        Fix(0L)
      } else if equal(p, Fix(-1L)) {
        symval(q_log_1)
      } else if eq(p, q_d__pcti) {
        symval(q_log_pcti)
      } else if eq(p, q_d__pcte) {
        Fix(1L)
      } else if equal(p, Fix(0L)) {
        merr("taylor: log(0) encountered while processing ~:M", [
          symval(q_last_exp),
        ])
      } else {
        list2(list1(q_p_log), p)
      },
    )
  } else if eq(caar(p), q_rat) {
    prep1(
      if !symval(q_d_taylor_logexpand).truthy() {
        list2(list1(q_p_log), p)
      } else {
        sub_star(list2(list1(q_p_log), cadr(p)), list2(list1(q_p_log), caddr(p)))
      },
    )
  } else if symval(q_full_log).truthy() && !free(p, q_d__pcti).truthy() {
    with_special(q_full_log, Nil, () => pslog3(d_polarform(p)))
  } else if eq(caar(p), q_mexpt) {
    // Must handle things like x^a, %e^(a*x), etc. which are pscoef's.
    pstimes(taylor2(caddr(p)), pslog(taylor2(cadr(p))))
  } else if eq(caar(p), q_mtimes) && symval(q_d_taylor_logexpand).truthy() {
    let mut l = cddr(p)
    let mut ans = pslog3(cadr(p))
    while !(l is Nil) {
      ans = psplus(ans, pslog3(car(l)))
      l = cdr(l)
    }
    ans
  } else {
    prep1(list2(list1(q_p_log), p))
  }
}

// Subtitle Extending Routines

///|
fn getfun_lt(fun : Value) -> Value raise {
  let mut exp_datum = get(oper_name(fun), q_exp_form)
  if exp_datum.truthy() {
    exp_datum_lt(fun, exp_datum)
  } else {
    exp_datum = get(oper_name(fun), q_sp2)
    if exp_datum.truthy() {
      exp_datum = get_lexp(subst(dummy_var(), q_sp2var, exp_datum), rcone(), Nil)
      if psp(exp_datum).truthy() {
        ps_lt(exp_datum)
      } else {
        term(rczero(), exp_datum)
      }
    } else {
      merr("GETFUN-LT: unknown function ~A", [fun])
    }
  }
}

///|
fn getexp_fun(fun : Value, var_ : Value, pw : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  let mut exp_datum = copy_tree(get(oper_name(fun), q_exp_form))
  if pw is Nil {
    infin_ord_err()
  } else if exp_datum is Nil {
    exp_datum = get_ps_form(if atom(fun) { fun } else { caar(fun) })
    if exp_datum is Nil {
      merr("taylor: power series unavailable for function ~A", [fun])
    } else {
      if !atom(fun) {
        let mut subvals = cdr(fun)
        let mut subs = safe_get(caar(fun), q_sp2subs)
        while true {
          if subvals is Nil || subs is Nil {
            if subvals.truthy() || subs.truthy() {
              merr(
                "taylor: incorrect number of subscripts to the deftaylor'd function ~A",
                [caar(fun)],
              )
              |> ignore
            }
            break
          }
          exp_datum = maxima_substitute(car(subvals), car(subs), exp_datum)
          subvals = cdr(subvals)
          subs = cdr(subs)
        }
      }
      ts_formula(exp_datum, var_, pw)
    }
  } else if e_gt(exp_datum_le(fun, exp_datum), pw).truthy() {
    pszero(var_, pw)
  } else {
    exp_datum = apply(
      exp_fun(exp_datum),
      if atom(fun) {
        cons(pw, cdr(exp_datum))
      } else {
        cons(pw, cons(cdr(fun), cdr(exp_datum)))
      },
    )
    if exp_datum.truthy() {
      if psp(exp_datum).truthy() {
        exp_datum
      } else {
        make_ps(var_, list1(pw), terms=exp_datum)
      }
    } else {
      Nil
    }
  }
}

///|
fn expexp_funs(
  pw : Value,
  l : Value,
  sign : Value,
  chng : Value,
  inc : Value,
) -> Value raise {
  let mut sign = sign
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  while true {
    e = e_plus(e, inc)
    if e_gt(e, pw).truthy() {
      return l
    }
    let coef = rctimes(
      e_sl_sl(
        sign,
        e2=if e_eq(inc, rcone()).truthy() {
          e
        } else {
          e_star(e, e1_(e))
        },
      ),
      cons(Fix(1L), cdr(lc(lt_l))),
    )
    add_term(lt_l, term_or_e=e, c=coef) |> ignore
    lt_l = n__term(lt_l)
    sign = e_star(sign, chng)
  }
  Nil
}

///|
/// Returns series expansion of %expintegral_si from term x^i to term x^max;
/// sign is sign of term x^i (1 or -1); ifac is i! (to avoid repeated
/// computation).
fn expsi_series(i : Value, sign : Value, ifac : Value, max_ : Value) -> Value raise {
  if num_gt(i, max_) {
    // we have all powers up to max
    Nil
  } else {
    cons(
      cons(cons(i, Fix(1L)), cons(sign, num_mul(i, ifac))),
      expsi_series(
        num_add(Fix(2L), i),
        num_mul(Fix(-1L), sign),
        num_mul(num_mul(num_add(Fix(2L), i), num_add(Fix(1L), i)), ifac),
        max_,
      ),
    )
  }
}

///|
/// Returns series expansion of %expintegral_si up to term with x^pw.
fn exp__pctexpintegral_si(pw : Value, l : Value) -> Value raise {
  ignore(l)
  expsi_series(
    Fix(1L),
    Fix(1L),
    Fix(1L),
    num_div(lfloat(car(pw)), lfloat(cdr(pw))),
  )
}

///|
fn explog_funs(
  pw : Value,
  l : Value,
  sign : Value,
  chng : Value,
  inc : Value,
) -> Value raise {
  let mut sign = sign
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  while true {
    e = e_plus(e, inc)
    if e_gt(e, pw).truthy() {
      return l
    }
    add_term(lt_l, term_or_e=e, c=e_sl_sl(sign, e2=e)) |> ignore
    lt_l = n__term(lt_l)
    sign = e_star(sign, chng)
  }
  Nil
}

///|
fn exptan_funs(pw : Value, l : Value, chng : Value) -> Value raise {
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  let mut sign = rcone()
  let mut fact = cons(Fix(1L), Fix(2L))
  let mut pow = cons(Fix(4L), Fix(1L))
  while true {
    e = e_plus(rctwo(), e)
    if e_gt(e, pw).truthy() {
      return l
    }
    fact = e_sl_sl(fact, e2=e_star(e, e1_plus(e)))
    pow = e_star(cons(Fix(4L), Fix(1L)), pow)
    sign = e_star(chng, sign)
    add_term(
      lt_l,
      term_or_e=e,
      c=e_star(
        e_star(sign, fact),
        e_star(
          prep1(ftake(q_p_bern, [rcdisrep(e1_plus(e))])),
          e_star(pow, e1_(pow)),
        ),
      ),
    )
    |> ignore
    lt_l = n__term(lt_l)
  }
  Nil
}

///|
fn expcot_funs(
  pw : Value,
  l : Value,
  sign : Value,
  chng : Value,
  plus : Value,
) -> Value raise {
  let mut sign = sign
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  let mut fact = rcone()
  let mut pow = rcone()
  while true {
    e = e_plus(rctwo(), e)
    if e_gt(e, pw).truthy() {
      return l
    }
    fact = e_sl_sl(fact, e2=e_star(e, e1_plus(e)))
    pow = e_star(cons(Fix(4L), Fix(1L)), pow)
    sign = e_star(chng, sign)
    add_term(
      lt_l,
      term_or_e=e,
      c=e_star(
        e_star(sign, fact),
        e_star(
          prep1(ftake(q_p_bern, [rcdisrep(e1_plus(e))])),
          e_plus(pow, plus),
        ),
      ),
    )
    |> ignore
    lt_l = n__term(lt_l)
  }
  Nil
}

///|
fn expsec_funs(pw : Value, l : Value, chng : Value) -> Value raise {
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  let mut sign = rcone()
  let mut fact = rcone()
  while true {
    e = e_plus(rctwo(), e)
    if e_gt(e, pw).truthy() {
      return l
    }
    fact = e_sl_sl(fact, e2=e_star(e, e1_(e)))
    sign = e_star(chng, sign)
    add_term(
      lt_l,
      term_or_e=e,
      c=e_star(e_star(sign, fact), prep1(ftake(q_p_euler, [rcdisrep(e)]))),
    )
    |> ignore
    lt_l = n__term(lt_l)
  }
  Nil
}

///|
fn expasin_funs(pw : Value, l : Value, chng : Value) -> Value raise {
  let mut e = e(l)
  let l = list1(l)
  let mut lt_l = l
  let mut sign : Value = Fix(1L)
  let mut n : Value = Fix(1L)
  let mut d : Value = Fix(1L)
  while true {
    e = e_plus(rctwo(), e)
    if e_gt(e, pw).truthy() {
      return l
    }
    n = num_mul(n, car(e_(e, e2=rctwo())))
    d = num_mul(d, car(e1_(e)))
    sign = num_mul(sign, chng)
    // need to reduce here ? - check this.
    let x = n_starred(num_mul(n, sign), num_mul(d, car(e)))
    add_term(
      lt_l,
      term_or_e=e,
      c=if atom(x) {
        x
      } else {
        cons(cadr(x), caddr(x))
      },
    )
    |> ignore
    lt_l = n__term(lt_l)
  }
  Nil
}

// This is the table of expansion data for known functions. The format of
// the EXP-FORM property is as follows:
//	(<name of the expanding routine for the function or
//	  (name . le of n-term) if expansion is of order 0>
//      <first term in the expansion or the name of a routine which
//	  computes the order when it may depend on parameters (e.g subscripts)>
//      <data for the expanding routine>)

///|
let hayat__exp_form_table : String =
  #|(%exp    ((expexp-funs 1 . 1) ((0 . 1) 1 . 1) (1 . 1) (1 . 1) (1 . 1))
  #| %sin   (expexp-funs ((1 . 1) 1 . 1) (-1 . 1) (-1 . 1) (2 . 1))
  #| %cos   ((expexp-funs 2 . 1) ((0 . 1) 1 . 1) (-1 . 1) (-1 . 1) (2 . 1))
  #| %sinh  (expexp-funs ((1 . 1) 1 . 1) (1 . 1) (1 . 1) (2 . 1))
  #| %cosh  ((expexp-funs 2 . 1) ((0 . 1) 1 . 1) (1 . 1) (1 . 1) (2 . 1))
  #| %log   (explog-funs ((1 . 1) 1 . 1) (-1 . 1) (-1 . 1) (1 . 1))
  #| %atan  (explog-funs ((1 . 1) 1 . 1) (-1 . 1) (-1 . 1) (2 . 1))
  #| %atanh (explog-funs ((1 . 1) 1 . 1) (1 . 1) (1 . 1) (2 . 1))
  #| %cot   (expcot-funs ((-1 . 1) 1 . 1) (1 . 1) (-1 . 1) (0 . 1))
  #| %csc   (expcot-funs ((-1 . 1) 1 . 1) (-1 . 1) (-1 . 1) (-2 . 1))
  #| %csch  (expcot-funs ((-1 . 1) 1 . 1) (-1 . 1) (1 . 1) (-2 . 1))
  #| %coth  (expcot-funs ((-1 . 1) 1 . 1) (1 . 1) (1 . 1) (0 . 1))
  #| %tan   (exptan-funs ((1 . 1) 1 . 1) (-1 . 1))
  #| %tanh  (exptan-funs ((1 . 1) 1 . 1) (1 . 1))
  #| %sec   ((expsec-funs 2 . 1) ((0 . 1) 1 . 1) (-1 . 1))
  #| %sech  ((expsec-funs 2 . 1) ((0 . 1) 1 . 1) (1 . 1))
  #| %asin  (expasin-funs ((1 . 1) 1 . 1) 1)
  #| %asinh (expasin-funs ((1 . 1) 1 . 1) -1)
  #| %gamma (expgam-fun ((-1 . 1) 1 . 1))
  #| $li    (exp$li-fun li-ord)
  #| %expintegral_si (exp_%expintegral_si ((1 . 1) 1 . 1))
  #| $psi   (expplygam-funs plygam-ord))

///|
fn hayat__init_exp_forms() -> Unit raise {
  let mut l = lread(hayat__exp_form_table)
  while !(l is Nil) {
    putprop(car(l), cadr(l), q_exp_form) |> ignore
    l = cddr(l)
  }
}

///|
fn known_ps(fun : Value) -> Value raise {
  getl(fun, list2(q_exp_form, q_sp2))
}

// Taylor series expansion routines

///|
/// SRF is only called externally; by RATF and SIMPEXPT.
fn srf(x : Value) -> Value raise {
  with_specials(
    [(q_exact_poly, t), (q_tlist, Nil), (q_ear_within_srf_q, t)],
    () => {
      let x = taylor1(x, Nil)
      set(q_tlist, mrat_tlist(x)) |> ignore
      // Set trunc levels in the local tlist to correspond to the maximum
      // level occurring in any series.
      let mut data = symval(q_tlist)
      let mut truncs = trunc_vector(mrat_ps(x), Nil)
      while !(data is Nil) {
        if car(truncs).truthy() &&
          e_gt(car(truncs), current_trunc(car(data))).truthy() {
          rplaca(cadr(car(data)), car(truncs)) |> ignore
        }
        data = cdr(data)
        truncs = cdr(truncs)
      }
      x
    },
  )
}

///|
/// [var, pt, order, asymp]
fn d_taylor(e : Value, args : Value) -> Value raise {
  let mut e = e
  if !d_taylorp(e).truthy() {
    // Not a taylor expression. Remove the special representation.
    e = specrepcheck(e)
  }
  taylor_star(e, args)
}
