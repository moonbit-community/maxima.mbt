// Port of src/risch.lisp: the Risch integration algorithm.
//
// Internal representation of risch expressions: a list with a canonical
// rational expression (CRE) as first element and standard maxima
// expressions as remaining elements.  A risch expression is the sum of the
// CRE and the remaining elements.

// ---------------------------------------------------------------------------
// Expansions of the ratmac.lisp macros R+, R*, R- (two-argument forms).

///|
fn risch__rp(a : Value, b : Value) -> Value raise {
  ratpl(a, b)
}

///|
fn risch__rt(a : Value, b : Value) -> Value raise {
  ratti(a, b, t)
}

///|
/// `(r- a b)`
fn risch__rm(a : Value, b : Value) -> Value raise {
  ratdif(ratfix(a), b)
}

///|
/// `(r- a)`
fn risch__rneg(a : Value) -> Value raise {
  ratminus(ratfix(a))
}

///|
fn risch__i(n : Int) -> Value {
  int(n)
}

///|
/// `(cons (list v e 1) 1)`-style helper: the CRE v^e.
fn risch__vpow(v : Value, e : Value) -> Value {
  cons(list3(v, e, Fix(1L)), Fix(1L))
}

///|
/// The Lisp ERRCATCH macro: `(list value)` on success, nil after an error.
fn risch__errcatch(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let r = risch__errcatch_tags(f) catch {
      LispError::Throw(_, _) as e => raise e
      LispError::ReturnFrom(_, _) as e => raise e
      LispError::Go(_) as e => raise e
      e => {
        if !is_maxima_error(e) {
          let msg = match e {
            LispError::SimpleError(m) => m
            LispError::Condition(_, m, _) => m
            _ => e.to_string()
          }
          set(q_d_error, list2(list2(q_mlist, q_simp), Str(msg))) |> ignore
          if symval(q_d_errormsg).truthy() {
            d_errormsg() |> ignore
          }
        }
        errlfun1(symval(q_errcatch)) |> ignore
        return Nil
      }
    }
    list1(r)
  })
}

///|
/// WITH-ERRCATCH-TAG-$ERRORS: throws to the errcatch tags become Maxima
/// errors.
fn risch__errcatch_tags(f : () -> Value raise) -> Value raise {
  f() catch {
    LispError::Throw(tag, v) if eq(tag, q_rat_err) => merror(car(v), cdr(v))
    LispError::Throw(tag, _) if eq(tag, q_macsyma_quit) || eq(tag, q_errorsw) =>
      with_special(q_ear_merror_signals__dolerror_p, t, () => merr(
        "An error was caught by errcatch.",
        [],
      ))
    e => raise e
  }
}

///|
/// Remove the first element of L that is EQ to ITEM (CL REMOVE :COUNT 1).
fn risch__remove_once_eq(item : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut x = l
  while x is Cons(cell) {
    if eq(cell.car, item) {
      c.append_list(cell.cdr)
      return c.result()
    }
    c.add(cell.car)
    x = cell.cdr
  }
  c.result()
}

// ---------------------------------------------------------------------------

///|
fn pair(al : Value, bl : Value) -> Value raise {
  mapcar2((a, b) => cons(a, b), al, bl)
}

///|
fn rischzero() -> Value raise {
  list2(cons(Fix(0L), Fix(1L)), Fix(0L))
}

///|
fn rischnoun(
  exp1 : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  exp2? : Value,
) -> Value raise {
  let (e1, e2) = match exp2 {
    Some(v) => (exp1, v)
    None => (rzero(), exp1)
  }
  list2(
    e1,
    list3(list1(q_p_integrate), disrep(e2, risch_ratform), risch_intvar),
  )
}

///|
fn getrischvar() -> Value raise {
  let mut vl = symval(q_varlist)
  let mut gl = symval(q_genvar)
  while cdr(vl) is Cons(_) {
    vl = cdr(vl)
    gl = cdr(gl)
  }
  car(gl)
}

///|
/// Test whether CRE p is constant with respect to the variable of
/// integration.  Requires variables in varlist and genvar to be ordered as
/// by intsetup.
fn risch_pconstp(p : Value, risch_mainvar : Value) -> Value raise {
  let v = pcoefp(p)
  if v.truthy() {
    v
  } else {
    pointergp(risch_mainvar, car(p))
  }
}

///|
fn risch_constp(r : Value, risch_mainvar : Value) -> Value raise {
  let r = ratfix(r)
  if risch_pconstp(car(r), risch_mainvar).truthy() {
    risch_pconstp(cdr(r), risch_mainvar)
  } else {
    Nil
  }
}

///|
/// Adds two risch expressions.
fn rischadd(x : Value, y : Value) -> Value raise {
  let a = car(x)
  let b = cdr(x)
  let c = car(y)
  let d = cdr(y)
  cons(ratpl(a, c), append(b, d))
}

///|
fn d_risch(exp_ : Value, risch_var : Value) -> Value raise {
  with_special(q_ear_integrator_level, Fix(0L), () => {
    let my_context = gensym(prefix="$ctxt")
    d_supcontext(list2(my_context, symval(q_context))) |> ignore
    let r = rischint(exp_, risch_var) catch {
      e => {
        d_killcontext(list1(my_context)) |> ignore
        raise e
      }
    }
    d_killcontext(list1(my_context)) |> ignore
    r
  })
}

///|
fn spderivative(p : Value, risch_var : Value) -> Value raise {
  if pcoefp(p).truthy() {
    cons(Fix(0L), Fix(1L))
  } else if cdr(p) is Nil {
    cons(Fix(0L), Fix(1L))
  } else if !atom(car(p)) || numberp(car(p)) {
    // P IS A RATFORM
    let denprime = spderivative(cdr(p), risch_var)
    if rzerop(denprime).truthy() {
      ratqu(spderivative(car(p), risch_var), cdr(p))
    } else {
      ratqu(
        risch__rm(
          risch__rt(spderivative(car(p), risch_var), cdr(p)),
          risch__rt(car(p), denprime),
        ),
        risch__rt(cdr(p), cdr(p)),
      )
    }
  } else {
    risch__rp(
      spderivative1(car(p), cadr(p), caddr(p), risch_var),
      spderivative(cons(car(p), cdddr(p)), risch_var),
    )
  }
}

///|
fn spderivative1(
  var1 : Value,
  deg : Value,
  coeff : Value,
  risch_var : Value,
) -> Value raise {
  if eq(var1, risch_var) {
    risch__rt(
      ratexpt(risch__vpow(risch_var, Fix(1L)), one_minus(deg)),
      pctimes(deg, coeff),
    )
  } else if pointergp(risch_var, var1).truthy() {
    cons(Fix(0L), Fix(1L))
  } else if equal(deg, Fix(0L)) {
    spderivative(coeff, risch_var)
  } else {
    risch__rp(
      risch__rt(
        ratexpt(risch__vpow(var1, Fix(1L)), deg),
        spderivative(coeff, risch_var),
      ),
      risch__rt(
        if equal(deg, Fix(1L)) {
          coeff
        } else {
          risch__rt(
            deg,
            risch__rt(
              coeff,
              ratexpt(risch__vpow(var1, Fix(1L)), one_minus(deg)),
            ),
          )
        },
        get(var1, q_rischdiff),
      ),
    )
  }
}

///|
fn polylogp(exp_ : Value, sub? : Value = Nil) -> Value raise {
  lbool(
    mqapplyp(exp_).truthy() &&
    eq(subfunname(exp_), q_d_li) &&
    (sub is Nil || equal(sub, car(subfunsubs(exp_)))),
  )
}

///|
fn rischint(exp_ : Value, risch_intvar : Value) -> Value raise {
  with_specials(
    [
      (q_d_logarc, Nil),
      (q_d_exponentialize, Nil),
      (q_d_gcd, q_d_algebraic),
      (q_d_algebraic, t),
      (q_implicit_real, t),
      (q_d_float, Nil),
      (q_d_numer, Nil),
      // The risch integrator expects $logexpand T. Otherwise, the
      // integrator hangs for special types of integrals.
      (q_d_logexpand, t),
      (q_d__pcte_to_numlog, Nil),
      (q_d_logsimp, Nil),
      (q_varlist, Nil),
      (q_genvar, Nil),
      (q_d_ratfac, Nil),
      (q_d_ratalgdenom, Nil),
    ],
    () => {
      let mut exp_ = exp_
      let mut risch_intvar = risch_intvar
      let noun = () => list3(list1(q_p_integrate), exp_, risch_intvar)
      if specrepp(exp_).truthy() {
        exp_ = specdisrep(exp_)
      }
      if specrepp(risch_intvar).truthy() {
        risch_intvar = specdisrep(risch_intvar)
      }
      if mnump(risch_intvar).truthy() {
        merr("risch: attempt to integrate wrt a number: ~:M", [risch_intvar])
        |> ignore
      }
      if atom(risch_intvar) && isinop(exp_, risch_intvar).truthy() {
        return noun()
      }
      let (_, risch_trigint, risch_hypertrigint, risch_operator) = rischform_mv(
        exp_, risch_intvar,
      )
      if risch_trigint.truthy() {
        return trigin1(exp_, risch_intvar)
      } else if risch_hypertrigint.truthy() {
        return hypertrigint1(exp_, risch_intvar, t)
      } else if risch_operator.truthy() {
        return noun()
      }
      let (risch_y, risch_operator) = intsetup(exp_, risch_intvar)
      if risch_operator.truthy() {
        return noun()
      }
      let risch_ratform = car(risch_y)
      set(q_varlist, caddr(risch_ratform)) |> ignore
      let risch_mainvar = caadr(ratf(risch_intvar))
      set(q_genvar, cadddr(risch_ratform)) |> ignore
      if !some(v => algpget(v).truthy(), symval(q_varlist)) {
        set(q_d_algebraic, Nil) |> ignore
        set(q_d_gcd, car(symval(q_ear_gcdl))) |> ignore
      }
      let risch_var = getrischvar()
      let z = tryrisch(
        cdr(risch_y),
        risch_mainvar,
        risch_ratform,
        risch_intvar,
        Nil,
        Nil,
        risch_var,
      )
      rplaca(cddr(risch_ratform), symval(q_varlist)) |> ignore
      rplaca(cdddr(risch_ratform), symval(q_genvar)) |> ignore
      if atom(cdr(z)) {
        disrep(car(z), risch_ratform)
      } else {
        with_specials([(q_d_logsimp, t), (q_d__pcte_to_numlog, t)], () => simplify(
          cons(list1(q_mplus), cons(disrep(car(z), risch_ratform), cdr(z))),
        ))
      }
    },
  )
}

///|
fn rischform(l : Value, risch_intvar : Value) -> Value raise {
  rischform_mv(l, risch_intvar).0
}

///|
/// RISCHFORM returns four values: the result of the walk, and whether
/// trigonometric, hyperbolic or unknown operators (the last one's name)
/// were found.
fn rischform_mv(
  l : Value,
  risch_intvar : Value,
) -> (Value, Value, Value, Value) raise {
  let trigint : Ref[Value] = Ref(Nil)
  let hypertrigint : Ref[Value] = Ref(Nil)
  let operator : Ref[Value] = Ref(Nil)
  fn impl_(l : Value) -> Value raise {
    if atom(l) ||
      alike1(risch_intvar, l).truthy() ||
      freeof(risch_intvar, l).truthy() {
      Nil
    } else if polylogp(l).truthy() {
      let s = car(subfunsubs(l))
      if integerp(s) && num_gt(s, Fix(0L)) {
        impl_(car(subfunargs(l)))
      } else {
        operator.val = t
        t
      }
    } else if atom(caar(l)) {
      let op = caar(l)
      if eq(op, q_p_sin) ||
        eq(op, q_p_cos) ||
        eq(op, q_p_tan) ||
        eq(op, q_p_cot) ||
        eq(op, q_p_sec) ||
        eq(op, q_p_csc) {
        trigint.val = t
        set(q_d_exponentialize, t) |> ignore
        impl_(cadr(l))
      } else if eq(op, q_p_asin) ||
        eq(op, q_p_acos) ||
        eq(op, q_p_atan) ||
        eq(op, q_p_acot) ||
        eq(op, q_p_asec) ||
        eq(op, q_p_acsc) {
        trigint.val = t
        set(q_d_logarc, t) |> ignore
        impl_(cadr(l))
      } else if eq(op, q_p_sinh) ||
        eq(op, q_p_cosh) ||
        eq(op, q_p_tanh) ||
        eq(op, q_p_coth) ||
        eq(op, q_p_sech) ||
        eq(op, q_p_csch) {
        hypertrigint.val = t
        set(q_d_exponentialize, t) |> ignore
        impl_(cadr(l))
      } else if eq(op, q_p_asinh) ||
        eq(op, q_p_acosh) ||
        eq(op, q_p_atanh) ||
        eq(op, q_p_acoth) ||
        eq(op, q_p_asech) ||
        eq(op, q_p_acsch) {
        hypertrigint.val = t
        set(q_d_logarc, t) |> ignore
        impl_(cadr(l))
      } else if eq(op, q_mtimes) ||
        eq(op, q_mplus) ||
        eq(op, q_mexpt) ||
        eq(op, q_rat) ||
        eq(op, q_p_erf) ||
        eq(op, q_p_log) {
        mapc(e => impl_(e) |> ignore, cdr(l))
      } else {
        operator.val = op
        op
      }
    } else {
      operator.val = caar(l)
      caar(l)
    }
  }

  let v = impl_(l)
  (v, trigint.val, hypertrigint.val, operator.val)
}

///|
fn hypertrigint1(
  exp_ : Value,
  risch_var : Value,
  hyperfunc : Value,
) -> Value raise {
  let result = if hyperfunc.truthy() {
    sinint(resimplify(exp_), risch_var)
  } else {
    rischint(resimplify(exp_), risch_var)
  }
  // The result can contain solvable integrals. Look for this case.
  if isinop(result, q_p_integrate).truthy() {
    // Found an integral. Evaluate the result again.  *IN-RISCH-P* makes
    // sure that we do not call rischint again from the integrator.
    with_special(q_ear_in_risch_p, t, () => meval(
      list3(list1(q_d_ev), result, q_d_nouns),
    ))
  } else {
    result
  }
}

///|
fn trigin1(risch__starexp : Value, risch_var : Value) -> Value raise {
  let yyy0 = hypertrigint1(risch__starexp, risch_var, Nil)
  let (num, denom) = with_specials(
    [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
    () => num_denom_split(yyy0),
  )
  let yyy = div(d_expand(num), d_expand(denom))
  with_specials(
    [
      (q_rischp, risch_var),
      (q_rp_polylogp, t),
      (q_d_logarc, Nil),
      (q_d_exponentialize, Nil),
    ],
    () => {
      // Split into real and imaginary part. This automatically converts
      // back to trigonometric functions.  RISPLIT can ask sign() about an
      // expression that is not real, which throws to SIGN-IMAG-ERR here.
      // The integral is then left unevaluated.
      let s = with_special(q_sign_imag_errp, Nil, () => catch_tag(
        q_sign_imag_err,
        () => risplit(yyy),
      ))
      if !(s is Cons(_)) {
        return list3(list1(q_p_integrate), risch__starexp, risch_var)
      }
      let yyy_re0 = car(s)
      let yyy_im0 = cdr(s)
      // E is locally constant iff its derivative vanishes.
      fn locally_const_p(e : Value) -> Value raise {
        let e = with_specials([(q_d_exponentialize, t), (q_d_logarc, t)], () => radcan1(
          resimplify(e),
          risch_var,
        ))
        lbool(
          freeof(risch_var, e).truthy() ||
          zerop1(radcan1(sdiff(e, risch_var), risch_var)).truthy(),
        )
      }

      // Strip locally constant parts (unsolved integrals survive this).
      let yyy_re : Value = if car(risch__errcatch(() => locally_const_p(yyy_re0))).truthy() {
        Fix(0L)
      } else {
        yyy_re0
      }
      let yyy_im : Value = if car(risch__errcatch(() => locally_const_p(yyy_im0))).truthy() {
        Fix(0L)
      } else {
        yyy_im0
      }
      let result = sratsimp(
        if freeof(q_p_realpart, yyy_re).truthy() &&
          freeof(q_p_imagpart, yyy_im).truthy() {
          addn_([yyy_re, muln_([q_d__pcti, yyy_im])])
        } else {
          yyy
        },
      )
      // The result can contain solvable integrals. Look for this case.
      if isinop(result, q_p_integrate).truthy() {
        with_special(q_ear_in_risch_p, t, () => sratsimp(
          meval(list3(list1(q_d_ev), result, q_d_nouns)),
        ))
      } else {
        result
      }
    },
  )
}

///|
fn tryrisch(
  exp_ : Value,
  risch_mainvar : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_var : Value,
) -> Value raise {
  let mut risch_expflag : Value = Nil
  let mut risch_expstuff = cons(Fix(0L), Fix(1L))
  let risch_expint : Value = Nil
  if eq(risch_mainvar, risch_var) {
    return rischfprog(exp_, risch_ratform, risch_var)
  } else if eq(get(risch_var, q_leadop), q_mexpt) {
    risch_expflag = t
  }
  let (y0, risch_logptdx, ei) = rischlogdprog(
    exp_, risch_ratform, risch_intvar, risch_liflag, risch_var, risch_expflag,
    risch_mainvar, risch_expint, risch_degree,
  )
  let mut risch_y = y0
  let mut risch_expint = ei
  for rat in risch_logptdx.iter() {
    let (v, ei2, es2) = rischlogeprog_mv(
      rat, risch_ratform, Nil, risch_intvar, risch_expstuff, risch_var, risch_expflag,
      risch_mainvar, risch_expint,
    )
    risch_expint = ei2
    risch_expstuff = es2
    risch_y = rischadd(v, risch_y)
  }
  if symval(q_varlist).truthy() {
    risch_y = rischadd(
      tryrisch1(
        risch_expstuff, risch_mainvar, risch_ratform, risch_intvar, risch_liflag,
        risch_degree,
      ),
      risch_y,
    )
  }
  if risch_expint.truthy() {
    rischadd(
      rischexppoly(
        risch_expint, risch_var, risch_ratform, risch_intvar, risch_liflag, risch_degree,
        risch_mainvar,
      ),
      risch_y,
    )
  } else {
    risch_y
  }
}

///|
fn tryrisch1(
  exp_ : Value,
  risch_mainvar : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
) -> Value raise {
  with_special(q_varlist, reverse(cdr(reverse(symval(q_varlist)))), () => {
    let risch_var = getrischvar()
    tryrisch(
      exp_, risch_mainvar, risch_ratform, risch_intvar, risch_liflag, risch_degree,
      risch_var,
    )
  })
}

///|
fn rischfprog(
  rat : Value,
  risch_ratform : Value,
  risch_var : Value,
) -> Value raise {
  let (dprog_ret, risch_logptdx) = dprog(rat, risch_ratform, risch_var)
  let a = cdr(ratrep_star(dprog_ret))
  let vl = symval(q_varlist)
  let b = with_specials(
    [
      (q_varlist, vl),
      (q_genvar, subseq(symval(q_genvar), 0, end=length(vl))),
    ],
    () => mapcar(p => eprog(p, risch_ratform, risch_var, Nil), risch_logptdx),
  )
  cons(a, b)
}

///|
fn rischlogdprog(
  ratarg : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_var : Value,
  risch_expflag : Value,
  risch_mainvar : Value,
  risch_expint : Value,
  risch_degree : Value,
) -> (Value, Value, Value) raise {
  let mut risch_expint = risch_expint
  let mut ans = cons(Fix(0L), Fix(1L))
  let mut risch_logptdx : Value = Nil
  if pcoefp(cdr(ratarg)).truthy() ||
    pointergp(risch_var, cadr(ratarg)).truthy() {
    let (v, ei) = rischlogpoly(
      ratarg, risch_ratform, risch_intvar, risch_liflag, risch_var, risch_expflag,
      risch_mainvar, risch_expint, risch_degree,
    )
    return (v, risch_logptdx, ei)
  }
  let (risch_rootfactor, risch_pardenom) = aprog(
    ratdenominator(ratarg),
    risch_var,
  )
  let (risch_parnumer, risch_wholepart) = cprog(
    ratnumerator(ratarg),
    ratdenominator(ratarg),
    risch_var,
    risch_pardenom,
  )
  let mut rf = reverse(risch_rootfactor)
  let mut pn = reverse(risch_parnumer)
  let mut klth = length(risch_rootfactor)
  while klth != 1 {
    let arootf = car(rf)
    if pcoefp(arootf).truthy() {
      ()
    } else if eq(get(car(arootf), q_leadop), q_mexpt) && cdddr(arootf) is Nil {
      risch_expint = append(
        if !atom(car(pn)) && !atom(caar(pn)) && eq(caaar(pn), car(arootf)) {
          gennegs(arootf, cdaar(pn), cdar(pn), int(klth))
        } else {
          list1(list([q_neg, car(pn), car(arootf), int(klth), cadr(arootf)]))
        },
        risch_expint,
      )
    } else if !zerop(pdegree(arootf, risch_var)) {
      let deriv = spderivative(arootf, risch_mainvar)
      let thebpg = bprog(arootf, ratnumerator(deriv), risch_var)
      let mut thetop = car(pn)
      let mut kx = klth - 1
      while kx != 0 {
        let kxv = int(kx)
        let prod1 = risch__rt(thetop, car(thebpg))
        let prod2 = risch__rt(
          thetop,
          risch__rt(cdr(thebpg), ratdenominator(deriv)),
        )
        let thebot = pexpt(arootf, kxv)
        ans = risch__rp(
          ans,
          ratqu(risch__rneg(prod2), risch__rt(kxv, thebot)),
        )
        thetop = risch__rp(
          prod1,
          ratqu(spderivative(prod2, risch_mainvar), kxv),
        )
        thetop = cdr(ratdivide(thetop, thebot))
        kx = kx - 1
      }
      risch_logptdx = cons(ratqu(thetop, arootf), risch_logptdx)
    }
    rf = cdr(rf)
    pn = cdr(pn)
    klth = klth - 1
  }
  risch_logptdx = cons(
    ratqu(car(risch_parnumer), car(risch_rootfactor)),
    risch_logptdx,
  )
  if pzerop(ans).truthy() || pzerop(car(ans)).truthy() {
    let (v, ei) = rischlogpoly(
      risch_wholepart, risch_ratform, risch_intvar, risch_liflag, risch_var, risch_expflag,
      risch_mainvar, risch_expint, risch_degree,
    )
    return (v, risch_logptdx, ei)
  }
  let thetop = cadr(pdivide(ratnumerator(ans), ratdenominator(ans)))
  let (v, ei) = rischlogpoly(
    risch_wholepart, risch_ratform, risch_intvar, risch_liflag, risch_var, risch_expflag,
    risch_mainvar, risch_expint, risch_degree,
  )
  (
    rischadd(list1(ratqu(thetop, ratdenominator(ans))), v),
    risch_logptdx,
    ei,
  )
}

///|
fn gennegs(
  denom : Value,
  num : Value,
  numdenom : Value,
  risch_klth : Value,
) -> Value raise {
  if num is Nil {
    Nil
  } else {
    cons(
      list([
        q_neg,
        cadr(num),
        car(denom),
        num_sub(risch_klth, car(num)),
        risch__rt(numdenom, caddr(denom)),
      ]),
      gennegs(denom, cddr(num), numdenom, risch_klth),
    )
  }
}

///|
fn rischlogeprog(
  p : Value,
  risch_ratform : Value,
  risch_switch1 : Value,
  risch_intvar : Value,
  risch_expstuff : Value,
  risch_var : Value,
  risch_expflag : Value,
  risch_mainvar : Value,
  risch_expint : Value,
) -> Value raise {
  rischlogeprog_mv(
    p, risch_ratform, risch_switch1, risch_intvar, risch_expstuff, risch_var, risch_expflag,
    risch_mainvar, risch_expint,
  ).0
}

///|
/// RISCHLOGEPROG returns three values: the risch expression and the
/// updated RISCH-EXPINT and RISCH-EXPSTUFF.
fn rischlogeprog_mv(
  p : Value,
  risch_ratform : Value,
  risch_switch1 : Value,
  risch_intvar : Value,
  risch_expstuff : Value,
  risch_var : Value,
  risch_expflag : Value,
  risch_mainvar : Value,
  risch_expint : Value,
) -> (Value, Value, Value) raise {
  let expint : Ref[Value] = Ref(risch_expint)
  let expstuff : Ref[Value] = Ref(risch_expstuff)
  fn impl_(p : Value, risch_switch1 : Value) -> Value raise {
    let mut risch_switch1 = risch_switch1
    if pzerop(p).truthy() || pzerop(car(p)).truthy() {
      return rischzero()
    }
    let mut p1e = ratnumerator(p)
    let oc = oldcontent(ratdenominator(p))
    let dcc = car(oc)
    let mut p2e = cadr(oc)
    if !risch_switch1.truthy() {
      let risch_pardenom = intfactor(p2e)
      if cdr(risch_pardenom).truthy() {
        risch_switch1 = t
        let oc2 = oldcontent(p1e)
        let ncc = car(oc2)
        p1e = cadr(oc2)
        let risch_parnumer = cprog(p1e, p2e, risch_var, risch_pardenom).0
        let allcc = ratqu(ncc, dcc)
        let mut pnum = risch_parnumer
        let mut pden = risch_pardenom
        let mut ans = rischzero()
        while !(pnum is Nil || pden is Nil) {
          ans = rischadd(
            impl_(risch__rt(allcc, ratqu(car(pnum), car(pden))), risch_switch1),
            ans,
          )
          pnum = cdr(pnum)
          pden = cdr(pden)
        }
        return ans
      }
    }
    if risch_expflag.truthy() && cdddr(p2e) is Nil {
      expint.val = cons(cons(q_neg, p), expint.val)
      return rischzero()
    }
    let mut expcoef : Value = Nil
    if risch_expflag.truthy() {
      expcoef = risch__rt(
        cadr(p2e),
        ratqu(
          get(risch_var, q_rischdiff),
          cons(risch_var, list2(Fix(1L), Fix(1L))),
        ),
      )
    }
    p1e = ratqu(p1e, ptimes(dcc, caddr(p2e)))
    p2e = ratqu(p2e, caddr(p2e)) // MAKE DENOM MONIC
    let p2deriv = spderivative(p2e, risch_mainvar)
    let my_divisor = if risch_expflag.truthy() {
      risch__rm(p2deriv, risch__rt(p2e, expcoef))
    } else {
      p2deriv
    }
    if equal(my_divisor, cons(Fix(0L), Fix(1L))) {
      return rischnoun(p, risch_ratform, risch_intvar)
    }
    let logcoef = ratqu(p1e, my_divisor)
    if risch_constp(logcoef, risch_mainvar).truthy() {
      if risch_expflag.truthy() {
        expstuff.val = risch__rm(expstuff.val, risch__rt(expcoef, logcoef))
      }
      return list2(
        cons(Fix(0L), Fix(1L)),
        list3(
          list1(q_mtimes),
          disrep(logcoef, risch_ratform),
          logmabs(disrep(p2e, risch_ratform)),
        ),
      )
    }
    if risch_expflag.truthy() &&
      symval(q_d_liflag).truthy() &&
      symval(q_ear_changevp).truthy() {
      let newvar = gensym()
      let new_int = d_changevar(
        list3(
          list1(q_p_integrate),
          simplify(disrep(p, risch_ratform)),
          risch_intvar,
        ),
        sub(newvar, get(risch_var, q_rischexpr)),
        newvar,
        risch_intvar,
      )
      // *CHANGEVP* NIL prevents recursive changevar
      let r = with_special(q_ear_changevp, Nil, () => {
        if freeof(risch_intvar, new_int).truthy() {
          let new_int2 = rischint(sdiff(new_int, newvar), newvar)
          if freeof(q_p_integrate, new_int2).truthy() {
            return Some(
              list2(
                rzero(),
                maxima_substitute(get(risch_var, q_rischexpr), newvar, new_int2),
              ),
            )
          }
        }
        None
      })
      if r is Some(v) {
        return v
      }
    }
    rischnoun(p, risch_ratform, risch_intvar)
  }

  let v = impl_(p, risch_switch1)
  (v, expint.val, expstuff.val)
}

///|
fn findint(exp_ : Value) -> Value raise {
  let mut e = exp_
  while true {
    if atom(e) {
      return Nil
    } else if atom(car(e)) {
      e = cdr(e)
    } else if eq(caaar(e), q_p_integrate) {
      return t
    } else {
      e = cdr(e)
    }
  }
  Nil
}

///|
fn logequiv(fn1 : Value, fn2 : Value, risch_intvar : Value) -> Value raise {
  freeof(
    risch_intvar,
    d_ratsimp(div_star(remabs(leadarg(fn1)), remabs(leadarg(fn2))), Nil),
  )
}

///|
fn remabs(exp_ : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if eq(caar(exp_), q_mabs) {
    cadr(exp_)
  } else {
    exp_
  }
}

///|
fn getfnsplit(l : Value, risch_intvar : Value) -> (Value, Value) raise {
  let mut coef : Value = Nil
  let mut fn_ : Value = Nil
  for x in l.iter() {
    if free(x, risch_intvar).truthy() {
      coef = cons(x, coef)
    } else {
      fn_ = cons(x, fn_)
    }
  }
  (muln(coef, Nil), muln(fn_, Nil))
}

///|
fn getfncoeff(
  a : Value,
  form : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_cary : Value,
  risch_nogood : Value,
  risch_lians : Value,
) -> Value raise {
  getfncoeff_mv(
    a, form, risch_intvar, risch_liflag, risch_degree, risch_cary, risch_nogood,
    risch_lians,
  ).0
}

///|
/// GETFNCOEFF returns four values: the coefficient and the updated
/// RISCH-CARY, RISCH-NOGOOD and RISCH-LIANS.
fn getfncoeff_mv(
  a : Value,
  form : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_cary : Value,
  risch_nogood : Value,
  risch_lians : Value,
) -> (Value, Value, Value, Value) raise {
  let cary : Ref[Value] = Ref(risch_cary)
  let nogood : Ref[Value] = Ref(risch_nogood)
  let lians : Ref[Value] = Ref(risch_lians)
  fn impl_(a : Value) -> Value raise {
    if a is Nil {
      return Fix(0L)
    }
    if equal(car(a), Fix(0L)) {
      return impl_(cdr(a))
    }
    if listp(car(a)) && eq(caaar(a), q_mplus) {
      let v = ratpl(impl_(cdar(a)), impl_(cdr(a)))
      if v.truthy() {
        return v
      }
    }
    if listp(car(a)) && eq(caaar(a), q_mtimes) {
      let (coef, newfn) = getfnsplit(cdar(a), risch_intvar)
      // Insert a complete mtimes expression without simpflag.
      // Nested mtimes expressions simplify further.
      setf_car(a, list3(list1(q_mtimes), coef, newfn)) |> ignore
      setf_cdr(car(a), list2(coef, newfn)) |> ignore
      if zerop1(coef).truthy() {
        return impl_(cdr(a))
      }
      if matanp(newfn).truthy() && memq(q_d__pcti, symval(q_varlist)).truthy() {
        with_specials([(q_d_logarc, t), (q_d_logexpand, q_d_all)], () => rplaca(
          a,
          d_expand(resimplify(car(a))),
        ))
        |> ignore
        return impl_(a)
      }
      if alike1(leadop(newfn), leadop(form)).truthy() &&
        (
          alike1(leadarg(newfn), leadarg(form)).truthy() ||
          (
            mlogp(newfn).truthy() &&
            logequiv(form, newfn, risch_intvar).truthy()
          )
        ) {
        let rc = rform(coef)
        rplaca(a, Fix(0L)) |> ignore
        return ratpl(rc, impl_(cdr(a)))
      }
      let mut vl = symval(q_varlist)
      while vl is Cons(_) {
        if !atom(car(vl)) &&
          alike1(leadop(car(vl)), leadop(newfn)).truthy() &&
          (
            if mlogp(newfn).truthy() {
              logequiv(car(vl), newfn, risch_intvar).truthy()
            } else {
              alike1(car(vl), newfn).truthy()
            }
          ) {
          rplaca(cddar(a), car(vl)) |> ignore
          break
        }
        vl = cdr(vl)
      }
      let novars = with_special(q_vlist, Nil, () => {
        // newvar1 accesses the special var vlist.
        newvar1(car(a)) |> ignore
        symval(q_vlist) is Nil
      })
      if novars {
        cary.val = ratpl(cdr(ratrep_star(car(a))), cary.val)
        rplaca(a, Fix(0L)) |> ignore
        return impl_(cdr(a))
      }
      if risch_liflag.truthy() && mlogp(form).truthy() && mlogp(newfn).truthy() {
        let (res, ng) = dilog(
          cons(car(a), form),
          risch_intvar,
          risch_degree,
          nogood.val,
        )
        nogood.val = ng
        lians.val = cons(res, lians.val)
        rplaca(a, Fix(0L)) |> ignore
        return impl_(cdr(a))
      }
      if risch_liflag.truthy() &&
        polylogp(form).truthy() &&
        mlogp(newfn).truthy() &&
        logequiv(form, newfn, risch_intvar).truthy() {
        lians.val = cons(
          mul_star(
            list([
              cadar(a),
              make_li(one_plus(car(subfunsubs(form))), leadarg(form)),
            ]),
          ),
          lians.val,
        )
        rplaca(a, Fix(0L)) |> ignore
        return impl_(cdr(a))
      }
      nogood.val = t
      return Fix(0L)
    }
    rplaca(a, list3(list1(q_mtimes), Fix(1L), car(a))) |> ignore
    impl_(a)
  }

  let v = impl_(a)
  (v, cary.val, nogood.val, lians.val)
}

///|
fn rischlogpoly(
  exp_ : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_var : Value,
  risch_expflag : Value,
  risch_mainvar : Value,
  risch_expint : Value,
  risch_degree : Value,
) -> (Value, Value) raise {
  let mut risch_expint = risch_expint
  let mut risch_liflag = risch_liflag
  let result = if equal(exp_, cons(Fix(0L), Fix(1L))) {
    rischzero()
  } else if risch_expflag.truthy() {
    risch_expint = cons(cons(q_poly, exp_), risch_expint)
    rischzero()
  } else if !among(risch_var, exp_).truthy() {
    tryrisch1(
      exp_, risch_mainvar, risch_ratform, risch_intvar, risch_liflag, risch_degree,
    )
  } else {
    let mut risch_degree = pdegree(car(exp_), risch_var)
    let mut p = car(exp_)
    let den = cdr(exp_)
    let mut risch_lians : Value = Nil
    let mut sum = rzero()
    let mut risch_cary = rzero()
    let mut risch_y : Value = Nil
    let mut risch_nogood : Value = Nil
    let mut res : Value = Nil
    while true {
      if minusp(risch_degree) {
        res = cons(sum, append(risch_lians, cdr(risch_y)))
        break
      }
      let ak = risch__rm(
        ratqu(polcoef(p, risch_degree, risch_var), den),
        risch__rt(
          cons(one_plus(risch_degree), Fix(1L)),
          risch__rt(risch_cary, get(risch_var, q_rischdiff)),
        ),
      )
      if !pzerop(polcoef(p, risch_degree, risch_var)).truthy() {
        p = if pcoefp(p).truthy() {
          pzero()
        } else {
          psimp(risch_var, cdddr(p))
        }
      }
      risch_y = tryrisch1(
        ak, risch_mainvar, risch_ratform, risch_intvar, risch_liflag, risch_degree,
      )
      risch_cary = car(risch_y)
      if num_gt(risch_degree, Fix(0L)) {
        risch_liflag = symval(q_d_liflag)
      }
      let lians_prev = risch_lians
      let (z, c2, ng2, l2) = getfncoeff_mv(
        cdr(risch_y),
        get(risch_var, q_rischexpr),
        risch_intvar,
        risch_liflag,
        risch_degree,
        risch_cary,
        risch_nogood,
        risch_lians,
      )
      risch_cary = c2
      risch_nogood = ng2
      risch_lians = l2
      risch_liflag = Nil
      if num_gt(risch_degree, Fix(0L)) &&
        (risch_nogood.truthy() || findint(cdr(risch_y)).truthy()) {
        res = rischadd(
          rischnoun(
            sum,
            risch_ratform,
            risch_intvar,
            exp2=risch__rp(
              risch__rt(ak, list3(risch_var, risch_degree, Fix(1L))),
              ratqu(p, den),
            ),
          ),
          cons(rzero(), lians_prev),
        )
        break
      }
      let lbkpl1 = ratqu(z, cons(one_plus(risch_degree), Fix(1L)))
      sum = risch__rp(
        risch__rt(lbkpl1, list3(risch_var, one_plus(risch_degree), Fix(1L))),
        risch__rp(
          risch__rt(
            risch_cary,
            if zerop(risch_degree) {
              Fix(1L)
            } else {
              list3(risch_var, risch_degree, Fix(1L))
            },
          ),
          sum,
        ),
      )
      risch_degree = one_minus(risch_degree)
    }
    res
  }
  (result, risch_expint)
}

///|
fn make_li(sub : Value, arg : Value) -> Value raise {
  subfunmake(q_d_li, list1(sub), list1(arg))
}

///|
/// Integrates log(ro)^risch-degree*log(rn)' in terms of polylogs: finds
/// constants c,d and integers j,k such that c*ro^j+d=rn^k.  If ro and rn
/// are polys then we can assume either j=1 or k=1.
fn dilog(
  l : Value,
  risch_intvar : Value,
  risch_degree : Value,
  risch_nogood : Value,
) -> (Value, Value) raise {
  let mut coef = cadr(car(l))
  let nlog = caddr(car(l))
  let mut olog = cdr(l)
  let mut narg = remabs(cadr(nlog))
  with_specials(
    [(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))],
    () => {
      let mut rn = rform(narg) // can add new vars to varlist
      let mut ro = rform(cadr(olog))
      let risch_var = caar(ro)
      let jk = ratreduce(
        pdegree(car(rn), risch_var),
        pdegree(car(ro), risch_var),
      )
      let j = car(jk)
      let k = cdr(jk)
      let idx = gensym()
      if num_eq(j, Fix(1L)) && num_gt(k, Fix(1L)) {
        rn = ratexpt(rn, k)
        coef = div(coef, k)
        narg = rdis(rn)
      } else if num_eq(k, Fix(1L)) && num_gt(j, Fix(1L)) {
        ro = ratexpt(ro, j)
        coef = div(coef, power(j, risch_degree))
        olog = muln_([j, olog])
      }
      let rcd = ratdivide(rn, ro)
      let rc = car(rcd)
      let rd = cdr(rcd)
      let mut risch_nogood = risch_nogood
      // RN must be a polynomial in RISCH-VAR as RO is, as RATDIVIDE divides
      // by their main variables.
      let result = if !pcoefp(car(rn)).truthy() &&
        eq(car(car(rn)), risch_var) &&
        freeof(risch_intvar, rdis(rc)).truthy() &&
        freeof(risch_intvar, rdis(rd)).truthy() {
        narg = d_ratsimp(sub(Fix(1L), div(narg, rdis(rd))), Nil)
        mul_star(
          list([
            coef,
            power(Fix(-1L), one_plus(risch_degree)),
            mk(q_mfactorial, [risch_degree]),
            dosum(
              mul_star(
                list([
                  power(Fix(-1L), idx),
                  div_star(power(olog, idx), mk(q_mfactorial, [idx])),
                  make_li(addn_([risch_degree, neg(idx), Fix(1L)]), narg),
                ]),
              ),
              idx,
              Fix(0L),
              risch_degree,
              t,
            ),
          ]),
        )
      } else {
        risch_nogood = t
        Fix(0L)
      }
      (result, risch_nogood)
    },
  )
}

///|
fn exppolycontrol(
  flag : Value,
  f : Value,
  a : Value,
  expg : Value,
  n : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_mainvar : Value,
) -> Value raise {
  with_specials(
    [(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))],
    () => {
      set(q_varlist, reverse(cdr(reverse(symval(q_varlist))))) |> ignore
      let risch_var = getrischvar()
      let risch_y = get(risch_var, q_leadop)
      if !pzerop(ratnumerator(f)).truthy() {
        let l = ratqu(a, f)
        if risch_constp(l, risch_mainvar).truthy() {
          return if flag.truthy() {
            // multiply in expg^n - n may be negative
            list2(risch__rt(l, ratexpt(risch__vpow(expg, Fix(1L)), n)), Fix(0L))
          } else {
            l
          }
        }
      }
      if eq(risch_y, risch_intvar) {
        rischexpvar(
          flag,
          list4(f, a, expg, n),
          risch_ratform,
          risch_intvar,
          risch_y,
          risch_var,
          risch_mainvar,
        )
      } else {
        rischexplog(
          lbool(eq(risch_y, q_mexpt)),
          flag,
          f,
          a,
          list([
            expg,
            n,
            get(risch_var, q_rischarg),
            risch_var,
            get(risch_var, q_rischdiff),
          ]),
          risch_ratform,
          risch_intvar,
          risch_liflag,
          risch_degree,
          risch_y,
          risch_var,
          risch_mainvar,
        )
      }
    },
  )
}

///|
fn rischexppoly(
  risch_expint : Value,
  risch_var : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_mainvar : Value,
) -> Value raise {
  let mut ans = rischzero()
  let expdiff = ratqu(
    get(risch_var, q_rischdiff),
    list3(risch_var, Fix(1L), Fix(1L)),
  )
  let mut ei = risch_expint
  while ei is Cons(_) {
    let type_ = car(car(ei))
    let risch_y = cdr(car(ei))
    let nd = ratfix(risch_y)
    let num = car(nd)
    let denom = cdr(nd)
    let mut w : Value = Nil
    if eq(type_, q_neg) {
      w = exppolycontrol(
        t,
        risch__rt(num_neg(cadr(denom)), expdiff),
        ratqu(num, caddr(denom)),
        risch_var,
        num_neg(cadr(denom)),
        risch_ratform,
        risch_intvar,
        risch_liflag,
        risch_degree,
        risch_mainvar,
      )
    } else if numberp(num) || !eq(car(num), risch_var) {
      w = tryrisch1(
        risch_y, risch_mainvar, risch_ratform, risch_intvar, risch_liflag, risch_degree,
      )
    } else {
      w = rischzero()
      let mut nm = cdr(num)
      while nm is Cons(_) {
        if equal(car(nm), Fix(0L)) {
          w = rischadd(
            tryrisch1(
              ratqu(cadr(nm), denom),
              risch_mainvar,
              risch_ratform,
              risch_intvar,
              risch_liflag,
              risch_degree,
            ),
            w,
          )
        } else {
          w = rischadd(
            exppolycontrol(
              t,
              risch__rt(car(nm), expdiff),
              ratqu(cadr(nm), denom),
              risch_var,
              car(nm),
              risch_ratform,
              risch_intvar,
              risch_liflag,
              risch_degree,
              risch_mainvar,
            ),
            w,
          )
        }
        nm = cddr(nm)
      }
    }
    ans = rischadd(w, ans)
    ei = cdr(ei)
  }
  ans
}

///|
fn rischexpvar(
  flag : Value,
  l : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_y : Value,
  risch_var : Value,
  risch_mainvar : Value,
) -> Value raise {
  let mut risch_y = risch_y
  let f = car(l)
  let a = cadr(l)
  let expg = caddr(l)
  let n = cadddr(l)
  if pzerop(a).truthy() || pzerop(car(a)).truthy() {
    return if flag is Nil { rzero() } else { rischzero() }
  }
  let _ = ratdenominator(f)
  let (p, _) = findpr(
    cdr(partfrac(a, risch_mainvar)),
    cdr(partfrac(f, risch_mainvar)),
    risch_y,
    risch_mainvar,
  )
  let mut lcm = plcm(ratdenominator(a), p)
  risch_y = ratpl(spderivative(cons(Fix(1L), p), risch_mainvar), ratqu(f, p))
  lcm = plcm(lcm, ratdenominator(risch_y))
  let r = pquotient(lcm, p)
  let s = ptimes(ratnumerator(risch_y), pquotient(lcm, ratdenominator(risch_y)))
  let mut tt = ptimes(ratnumerator(a), pquotient(lcm, ratdenominator(a)))
  let risch_beta = pdegree(r, risch_mainvar)
  let risch_gamma = pdegree(s, risch_mainvar)
  let delta = pdegree(tt, risch_mainvar)
  let mut risch_alphar = num_max(
    num_sub(one_plus(delta), risch_beta),
    num_sub(delta, risch_gamma),
  )
  let mut risch_m : Value = Fix(0L)
  if equal(one_minus(risch_beta), risch_gamma) {
    risch_y = risch__rt(
      Fix(-1L),
      ratqu(
        polcoef(s, risch_gamma, risch_var),
        polcoef(r, risch_beta, risch_var),
      ),
    )
    if equal(cdr(risch_y), Fix(1L)) && numberp(car(risch_y)) {
      risch_m = car(risch_y)
    }
  }
  risch_alphar = num_max(risch_alphar, risch_m)
  if minusp(risch_alphar) {
    return if flag.truthy() {
      cxerfarg(rzero(), expg, n, a, risch_ratform, risch_intvar, risch_mainvar)
    } else {
      Nil
    }
  }
  let mut fromlsa = false
  let mut k : Value = Nil
  if equal(risch_alphar, risch_m) && !zerop(risch_m) {
    k = num_sum([risch_alphar, risch_beta, Fix(-1L)])
    let mut wl : Value = Nil
    while true {
      // l2
      let mut wv = list1(cons(polcoef(tt, k, risch_var), Fix(1L)))
      let mut i = risch_alphar
      while true {
        // l1
        wv = cons(
          risch__rp(
            risch__rt(
              cons(i, Fix(1L)),
              polcoef(r, num_sub(num_add(k, Fix(1L)), i), risch_var),
            ),
            cons(polcoef(s, num_sub(k, i), risch_var), Fix(1L)),
          ),
          wv,
        )
        i = one_minus(i)
        if !num_gt(i, Fix(-1L)) {
          break
        }
      }
      wl = cons(wv, wl)
      k = one_minus(k)
      if !num_gt(k, Fix(-1L)) {
        break
      }
    }
    let (ly, lm) = lsa(wl)
    risch_y = ly
    risch_m = lm
    // LSA calls the system singular when it has more than one solution.
    // Here the antiderivatives those solutions give differ only by a
    // constant, so any one of them will do, and the DOWN2 walk finds one.
    // The walk answers only when it solves the equation exactly, so it is
    // also safe to let it try when LSA calls the system inconsistent.
    if eq(risch_y, q_singular) || eq(risch_y, q_inconsistent) {
      fromlsa = true
    } else {
      k = Fix(0L)
      lcm = Fix(0L)
      risch_y = cdr(risch_y)
      while true {
        // l3
        lcm = risch__rp(
          risch__rt(car(risch_y), pexpt(list3(risch_mainvar, Fix(1L), Fix(1L)), k)),
          lcm,
        )
        k = one_plus(k)
        risch_y = cdr(risch_y)
        if risch_y is Nil {
          return if flag is Nil {
            ratqu(lcm, p)
          } else {
            list2(
              risch__rt(ratqu(lcm, p), ratexpt(risch__vpow(expg, Fix(1L)), n)),
              Fix(0L),
            )
          }
        }
      }
    }
  }
  // down2
  let mut denom_mode = 0
  if pzerop(s).truthy() || num_gt(one_minus(risch_beta), risch_gamma) {
    k = num_add(risch_alphar, one_minus(risch_beta))
    denom_mode = 0
  } else if num_lt(one_minus(risch_beta), risch_gamma) {
    k = num_add(risch_alphar, risch_gamma)
    denom_mode = 1
  } else {
    k = num_add(risch_alphar, risch_gamma)
    denom_mode = 2
  }
  risch_y = rzero()
  while true {
    // loop
    let yn = polcoef(
      ratnumerator(tt),
      if zerop(risch_alphar) {
        risch_gamma
      } else {
        k
      },
      risch_var,
    )
    // DENOM MAY BE 0
    let yd = risch__rt(ratdenominator(tt), if zerop(risch_alphar) {
      polcoef(s, risch_gamma, risch_var)
    } else {
      match denom_mode {
        0 => ratti(risch_alphar, polcoef(r, risch_beta, risch_var), t)
        1 => polcoef(s, risch_gamma, risch_var)
        _ =>
          ratpl(
            ratti(risch_alphar, polcoef(r, risch_beta, risch_var), t),
            polcoef(s, risch_gamma, risch_var),
          )
      }
    })
    let mut yalpha : Value = Nil
    if rzerop(yd).truthy() {
      if pzerop(yn).truthy() {
        k = one_minus(k)
        risch_alphar = one_minus(risch_alphar)
        continue // need more constraints?
      } else if flag is Nil {
        return Nil
      } else {
        return cxerfarg(
          rzero(),
          expg,
          n,
          a,
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      }
    } else {
      yalpha = ratqu(yn, yd)
    }
    let ytemp = risch__rp(
      risch_y,
      risch__rt(yalpha, risch__vpow(risch_mainvar, risch_alphar)),
    )
    let mut ttemp = risch__rm(
      tt,
      risch__rt(
        yalpha,
        risch__rp(
          risch__rt(s, risch__vpow(risch_mainvar, risch_alphar)),
          risch__rt(
            r,
            risch__rt(
              risch_alphar,
              list3(risch_mainvar, one_minus(risch_alphar), Fix(1L)),
            ),
          ),
        ),
      ),
    )
    k = one_minus(k)
    risch_alphar = one_minus(risch_alphar)
    if num_lt(risch_alphar, Fix(0L)) {
      if rzerop(ttemp).truthy() {
        if flag is Nil {
          return ratqu(ytemp, p)
        } else {
          return list2(
            ratqu(risch__rt(ytemp, ratexpt(risch__vpow(expg, Fix(1L)), n)), p),
            Fix(0L),
          )
        }
      } else if flag is Nil {
        return Nil
      } else if fromlsa {
        // The LSA branch returns either a complete answer or none. A walk
        // entered from there does the same.
        return cxerfarg(
          rzero(),
          expg,
          n,
          a,
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      }
      ttemp = ratqu(ttemp, lcm)
      if risch_constp(ttemp, risch_mainvar).truthy() &&
        symval(q_d_erfflag).truthy() &&
        equal(pdegree(car(get(expg, q_rischarg)), risch_mainvar), Fix(2L)) &&
        equal(pdegree(cdr(get(expg, q_rischarg)), risch_mainvar), Fix(0L)) {
        return list2(
          ratqu(risch__rt(ytemp, ratexpt(risch__vpow(expg, Fix(1L)), n)), p),
          erfarg2(
            risch__rt(n, get(expg, q_rischarg)),
            ttemp,
            risch_ratform,
            risch_intvar,
            risch_mainvar,
          ),
        )
      } else if rzerop(risch_y).truthy() {
        // With nothing accumulated in RISCH-Y, the last step alone is a
        // single integration by parts, which usually leaves an integral no
        // easier than the one it started from.  Hand it back unevaluated.
        return cxerfarg(
          rzero(),
          expg,
          n,
          a,
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      } else {
        // YTEMP and TTEMP are the pair the last step reached.  TTEMP is
        // already divided by LCM.
        return cxerfarg(
          ratqu(risch__rt(ytemp, ratexpt(risch__vpow(expg, Fix(1L)), n)), p),
          expg,
          n,
          ttemp,
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      }
    }
    risch_y = ytemp
    tt = ttemp
  }
  Nil
}

///|
fn lsa(mm : Value) -> (Value, Value) raise {
  with_special(q_n_starmosesflag, Nil, () => {
    let d = length(car(mm))
    // MTOA stands for MATRIX-TO-ARRAY.  An array is created and associated
    // with the symbol *JM*.
    mtoa(q_ear_jm, int(length(mm)), int(d), mm) |> ignore
    let risch_m = tfgeli(q_ear_jm, int(length(mm)), int(d))
    if (
        car(risch_m) is Nil &&
        cadr(risch_m) is Nil &&
        length(mm) < d - 1
      ) ||
      (
        car(risch_m).truthy() &&
        length(car(risch_m)) > length(mm) - (d - 1)
      ) {
      return (q_singular, risch_m)
    } else if cadr(risch_m).truthy() {
      return (q_inconsistent, risch_m)
    }
    set(q_n_starmosesflag, t) |> ignore
    ptorat(q_ear_jm, int(d - 1), int(d)) |> ignore
    let m2 = xrutout(q_ear_jm, int(d - 1), int(d), Nil, Nil)
    let m2 = lsafix(cdr(m2), caddr(risch_m))
    (m2, risch_m)
  })
}

///|
fn lsafix(l : Value, n : Value) -> Value raise {
  let mut nn = n
  let mut ll = l
  while ll is Cons(_) {
    aset(symval(q_ear_jm), [1, to_int(car(nn))], car(ll)) |> ignore
    nn = cdr(nn)
    ll = cdr(ll)
  }
  let mut ans : Value = Nil
  let mut s = length(l)
  while s != 0 {
    ans = cons(aref(symval(q_ear_jm), [1, s]), ans)
    s = s - 1
  }
  cons(list1(q_list), ans)
}

///|
fn findpr(
  alist : Value,
  flist : Value,
  risch_y : Value,
  risch_mainvar : Value,
) -> (Value, Value) raise {
  let mut p : Value = Fix(1L)
  let mut flist = flist
  let mut risch_alphar : Value = Nil
  let mut al = alist
  while al is Cons(_) {
    let fterm = findflist(cadar(al), flist)
    if fterm.truthy() {
      flist = risch__remove_once_eq(risch_y, flist)
    }
    risch_alphar = if fterm is Nil {
      caddar(al)
    } else if equal(caddr(fterm), Fix(1L)) {
      fpr_dif(car(flist), caddar(al), risch_mainvar)
    } else {
      num_max(num_sub(caddar(al), caddr(fterm)), Fix(0L))
    }
    if !zerop(risch_alphar) {
      p = ptimes(p, pexpt(cadar(al), risch_alphar))
    }
    al = cdr(al)
  }
  let mut fl = flist
  while fl is Cons(_) {
    if equal(caddar(fl), Fix(1L)) {
      risch_alphar = fpr_dif(car(fl), Fix(0L), risch_mainvar)
      p = ptimes(p, pexpt(cadar(fl), risch_alphar))
    }
    fl = cdr(fl)
  }
  (p, risch_alphar)
}

///|
fn fpr_dif(fterm : Value, alpha : Value, risch_mainvar : Value) -> Value raise {
  let num = car(fterm)
  let den = cadr(fterm)
  let risch_m = spderivative(den, risch_mainvar)
  if rzerop(risch_m).truthy() {
    alpha
  } else {
    let n = ratqu(cdr(ratdivide(num, den)), risch_m)
    if equal(cdr(n), Fix(1L)) && numberp(car(n)) {
      num_max(car(n), alpha)
    } else {
      alpha
    }
  }
}

///|
fn findflist(a : Value, llist : Value) -> Value raise {
  let mut l = llist
  while l is Cons(_) {
    if equal(cadar(l), a) {
      return car(l)
    }
    l = cdr(l)
  }
  Nil
}

///|
fn rischexplog(
  expexpflag : Value,
  flag : Value,
  f : Value,
  a : Value,
  l : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_liflag : Value,
  risch_degree : Value,
  risch_y : Value,
  risch_var : Value,
  risch_mainvar : Value,
) -> Value raise {
  let mut risch_y = risch_y
  let mut f = f
  let expg = car(l)
  let n = cadr(l)
  let eta = caddr(l)
  let logeta = cadddr(l)
  let logdiff = car(cddddr(l))
  if pzerop(a).truthy() || pzerop(car(a)).truthy() {
    return if flag is Nil { rzero() } else { rischzero() }
  }
  let p = findpr(
    cdr(partfrac(a, risch_var)),
    cdr(partfrac(f, risch_var)),
    risch_y,
    risch_mainvar,
  ).0
  let mut lcm = plcm(ratdenominator(a), p)
  risch_y = ratpl(spderivative(cons(Fix(1L), p), risch_mainvar), ratqu(f, p))
  lcm = plcm(lcm, ratdenominator(risch_y))
  let r = pquotient(lcm, p)
  let s = ptimes(ratnumerator(risch_y), pquotient(lcm, ratdenominator(risch_y)))
  let mut tt = ptimes(ratnumerator(a), pquotient(lcm, ratdenominator(a)))
  let risch_beta = pdegree(r, risch_var)
  let risch_gamma = pdegree(s, risch_var)
  let delta = pdegree(tt, risch_var)
  let mut mu : Value = Nil
  let mut yy : Value = Nil
  let mut risch_cary : Value = Nil
  let mut risch_nogood : Value = Nil
  let mut risch_lians : Value = Nil
  let mut denom : Value = Nil
  let mut ymu : Value = Nil
  let mut rbeta : Value = Nil
  let mut temp : Value = Nil
  let mut vector : Value = Nil
  let mut aarray : Value = Nil
  let mut rmu : Value = Nil
  let mut rrmu : Value = Nil
  let mut rarray : Value = Nil
  let mut constmu : Value = Nil
  let mut secondpass = false
  let mut firsty : Value = Nil
  let mut firsttt : Value = Nil
  let mut startmu : Value = Nil
  let mut starttt : Value = Nil
  let mut fromlsa = false
  let rexpg_n = () => ratexpt(risch__vpow(expg, Fix(1L)), n)
  let logeta_poly = () => list3(logeta, Fix(1L), Fix(1L))
  // states
  let s_start = 0
  let s_expcase = 1
  let s_down1 = 2
  let s_back = 3
  let s_linearloop = 4
  let s_recurse = 5
  let s_recurseloop = 6
  let s_recursefail = 7
  let s_recursedone = 8
  let s_lsacall = 9
  let s_muloop = 10
  let s_mu1 = 11
  let s_rmuloop = 12
  let s_skipmu = 13
  let s_arrayloop = 14
  let s_array1loop = 15
  let s_array2loop = 16
  let s_l3 = 17
  let mut st = s_start
  while true {
    if st == s_start {
      if expexpflag.truthy() {
        mu = num_max(num_sub(delta, risch_beta), num_sub(delta, risch_gamma))
        st = s_expcase
        continue
      }
      mu = num_max(
        num_sub(one_plus(delta), risch_beta),
        num_sub(one_plus(delta), risch_gamma),
      )
      if num_lt(risch_beta, risch_gamma) {
        st = s_back
        continue
      } else if num_eq(one_minus(risch_beta), risch_gamma) {
        st = s_down1
        continue
      }
      risch_y = tryrisch1(
        ratqu(
          risch__rm(
            risch__rt(
              polcoef(r, one_minus(risch_beta), risch_var),
              polcoef(s, risch_gamma, risch_var),
            ),
            risch__rt(
              polcoef(r, risch_beta, risch_var),
              polcoef(s, one_minus(risch_gamma), risch_var),
            ),
          ),
          risch__rt(
            polcoef(r, risch_beta, risch_var),
            polcoef(r, risch_beta, risch_var),
          ),
        ),
        risch_mainvar,
        risch_ratform,
        risch_intvar,
        risch_liflag,
        risch_degree,
      )
      risch_cary = car(risch_y)
      let (y1, c1, n1, l1) = getfncoeff_mv(
        cdr(risch_y),
        get(risch_var, q_rischexpr),
        risch_intvar,
        risch_liflag,
        risch_degree,
        risch_cary,
        risch_nogood,
        risch_lians,
      )
      yy = y1
      risch_cary = c1
      risch_nogood = n1
      risch_lians = l1
      if !findint(cdr(risch_y)).truthy() &&
        !risch_nogood.truthy() &&
        !atom(yy) &&
        equal(cdr(yy), Fix(1L)) &&
        numberp(car(yy)) &&
        num_gt(car(yy), mu) {
        mu = car(yy)
      }
      st = s_back
    } else if st == s_expcase {
      if !equal(risch_beta, risch_gamma) {
        st = s_back
        continue
      }
      risch_y = tryrisch1(
        ratqu(
          polcoef(s, risch_gamma, risch_var),
          polcoef(r, risch_beta, risch_var),
        ),
        risch_mainvar,
        risch_ratform,
        risch_intvar,
        risch_liflag,
        risch_degree,
      )
      if findint(cdr(risch_y)).truthy() {
        st = s_back
        continue
      }
      yy = ratqu(risch__rt(Fix(-1L), car(risch_y)), eta)
      if !atom(yy) &&
        equal(cdr(yy), Fix(1L)) &&
        numberp(car(yy)) &&
        num_gt(car(yy), mu) {
        mu = car(yy)
      }
      st = s_back
    } else if st == s_down1 {
      risch_y = tryrisch1(
        ratqu(
          polcoef(s, risch_gamma, risch_var),
          polcoef(r, risch_beta, risch_var),
        ),
        risch_mainvar,
        risch_ratform,
        risch_intvar,
        risch_liflag,
        risch_degree,
      )
      risch_cary = car(risch_y)
      let (y1, c1, n1, l1) = getfncoeff_mv(
        cdr(risch_y),
        get(risch_var, q_rischexpr),
        risch_intvar,
        risch_liflag,
        risch_degree,
        risch_cary,
        risch_nogood,
        risch_lians,
      )
      yy = y1
      risch_cary = c1
      risch_nogood = n1
      risch_lians = l1
      if !findint(cdr(risch_y)).truthy() &&
        !risch_nogood.truthy() &&
        !atom(yy) &&
        equal(cdr(yy), Fix(1L)) &&
        numberp(car(yy)) &&
        num_gt(num_neg(car(yy)), mu) {
        mu = num_neg(car(yy))
      }
      st = s_back
    } else if st == s_back {
      if minusp(mu) {
        return if flag.truthy() {
          cxerfarg(rzero(), expg, n, a, risch_ratform, risch_intvar, risch_mainvar)
        } else {
          Nil
        }
      }
      if num_gt(risch_beta, risch_gamma) {
        st = s_lsacall
        continue
      } else if num_eq(risch_beta, risch_gamma) {
        st = s_recurse
        continue
      }
      denom = polcoef(s, risch_gamma, risch_var)
      risch_y = cons(Fix(0L), Fix(1L))
      st = s_linearloop
    } else if st == s_linearloop {
      ymu = ratqu(
        polcoef(ratnumerator(tt), num_add(mu, risch_gamma), risch_var),
        risch__rt(ratdenominator(tt), denom),
      )
      ymu = risch__rt(ymu, pexpt(logeta_poly(), mu))
      risch_y = risch__rp(risch_y, ymu)
      tt = risch__rm(
        tt,
        risch__rp(
          risch__rt(s, ymu),
          risch__rt(r, spderivative(ymu, risch_mainvar)),
        ),
      )
      mu = one_minus(mu)
      if !num_lt(mu, Fix(0L)) {
        continue
      } else if !flag.truthy() {
        return if rzerop(tt).truthy() { ratqu(risch_y, p) } else { Nil }
      } else if rzerop(tt).truthy() {
        return cons(ratqu(risch__rt(risch_y, rexpg_n()), p), list1(Fix(0L)))
      } else {
        return cxerfarg(
          ratqu(risch__rt(risch_y, rexpg_n()), p),
          expg,
          n,
          ratqu(tt, lcm),
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      }
    } else if st == s_recurse {
      rbeta = polcoef(r, risch_beta, risch_var)
      risch_y = cons(Fix(0L), Fix(1L))
      startmu = mu
      starttt = tt
      st = s_recurseloop
    } else if st == s_recurseloop {
      // The equation for the coefficient of the MU-th power only involves
      // the term of S of the same degree as the leading term of R.
      f = risch__rp(
        ratqu(polcoef(s, risch_beta, risch_var), rbeta),
        if expexpflag.truthy() {
          risch__rt(mu, spderivative(eta, risch_mainvar))
        } else {
          Fix(0L)
        },
      )
      // F is affine in MU with slope ETA', so for an exponential over an
      // exponential it vanishes at no more than one MU.
      if expexpflag.truthy() && constmu is Nil && rzerop(f).truthy() {
        constmu = mu
      }
      ymu = exppolycontrol(
        Nil,
        f,
        ratqu(
          polcoef(ratnumerator(tt), num_add(risch_beta, mu), risch_var),
          risch__rt(ratdenominator(tt), rbeta),
        ),
        expg,
        n,
        risch_ratform,
        risch_intvar,
        risch_liflag,
        risch_degree,
        risch_mainvar,
      )
      if ymu is Nil {
        st = s_recursefail
        continue
      }
      if secondpass && eql(mu, constmu) {
        ymu = risch__rp(ymu, cons(Fix(1L), Fix(1L)))
      }
      ymu = risch__rt(ymu, pexpt(logeta_poly(), mu))
      risch_y = risch__rp(risch_y, ymu)
      tt = risch__rm(
        tt,
        risch__rp(
          risch__rt(s, ymu),
          risch__rt(r, spderivative(ymu, risch_mainvar)),
        ),
      )
      mu = one_minus(mu)
      if !num_lt(mu, Fix(0L)) {
        continue
      } else if rzerop(tt).truthy() {
        st = s_recursedone
        continue
      } else if constmu.truthy() && !secondpass {
        // The constant left open at CONSTMU is fixed by one of the
        // coefficient equations below it.  Walk again with that constant
        // one higher.
        firsty = risch_y
        firsttt = tt
        secondpass = true
        risch_y = cons(Fix(0L), Fix(1L))
        mu = startmu
        tt = starttt
        continue
      } else if secondpass {
        // Both walks keep R*Y' + S*Y + TT equal to STARTTT, so the
        // combination with a constant CC leaves FIRSTTT - CC*SPREAD = 0.
        let spread = risch__rm(firsttt, tt)
        let cc = if !rzerop(spread).truthy() {
          ratqu(firsttt, spread)
        } else {
          Nil
        }
        if cc.truthy() && risch_constp(cc, risch_mainvar).truthy() {
          risch_y = risch__rp(firsty, risch__rt(cc, risch__rm(risch_y, firsty)))
          st = s_recursedone
          continue
        }
      }
      st = s_recursefail
    } else if st == s_recursefail {
      // A second walk that came to nothing leaves the first walk's answer.
      if secondpass {
        risch_y = firsty
        tt = firsttt
      }
      return if flag is Nil {
        Nil
      } else if fromlsa {
        cxerfarg(rzero(), expg, n, a, risch_ratform, risch_intvar, risch_mainvar)
      } else {
        cxerfarg(
          ratqu(risch__rt(risch_y, rexpg_n()), p),
          expg,
          n,
          ratqu(tt, lcm),
          risch_ratform,
          risch_intvar,
          risch_mainvar,
        )
      }
    } else if st == s_recursedone {
      return if flag is Nil {
        ratqu(risch_y, p)
      } else {
        cons(ratqu(risch__rt(risch_y, rexpg_n()), p), list1(Fix(0L)))
      }
    } else if st == s_lsacall {
      rrmu = mu
      st = s_muloop
    } else if st == s_muloop {
      temp = risch__rt(
        ratexpt(risch__vpow(logeta, Fix(1L)), one_minus(mu)),
        risch__rp(
          risch__rt(s, risch__vpow(logeta, Fix(1L))),
          risch__rt(mu, risch__rt(r, logdiff)),
        ),
      )
      st = s_mu1
    } else if st == s_mu1 {
      vector = Nil
      rmu = num_add(rrmu, risch_beta)
      st = s_rmuloop
    } else if st == s_rmuloop {
      vector = cons(
        ratqu(
          polcoef(ratnumerator(temp), rmu, risch_var),
          ratdenominator(temp),
        ),
        vector,
      )
      rmu = one_minus(rmu)
      if !num_lt(rmu, Fix(0L)) {
        continue
      }
      mu = one_minus(mu)
      aarray = append(aarray, list1(reverse(vector)))
      if !num_lt(mu, Fix(0L)) {
        st = s_muloop
        continue
      } else if equal(mu, Fix(-2L)) {
        st = s_skipmu
        continue
      }
      temp = tt
      st = s_mu1
    } else if st == s_skipmu {
      rarray = Nil
      st = s_arrayloop
    } else if st == s_arrayloop {
      vector = Nil
      vector = mapcar(x => car(x), aarray)
      aarray = mapcar(x => cdr(x), aarray)
      rarray = append(rarray, list1(vector))
      if !(car(aarray) is Nil) {
        continue
      }
      rmu = one_plus(rrmu)
      vector = Nil
      st = s_array1loop
    } else if st == s_array1loop {
      vector = cons(cons(Fix(0L), Fix(1L)), vector)
      rmu = one_minus(rmu)
      if !num_lt(rmu, Fix(0L)) {
        continue
      }
      aarray = Nil
      st = s_array2loop
    } else if st == s_array2loop {
      if !equal(car(rarray), vector) {
        aarray = cons(car(rarray), aarray)
      }
      rarray = cdr(rarray)
      if rarray.truthy() {
        continue
      }
      rarray = reverse(aarray)
      temp = lsa(rarray).0
      // LSACALL only looks for coefficients that are constants. When LSA
      // finds no single such solution, let the RECURSE walk try.
      if eq(temp, q_singular) || eq(temp, q_inconsistent) {
        mu = rrmu
        fromlsa = true
        st = s_recurse
        continue
      }
      temp = reverse(cdr(temp))
      rmu = Fix(0L)
      risch_y = Fix(0L)
      st = s_l3
    } else {
      // l3
      risch_y = risch__rp(
        risch_y,
        risch__rt(car(temp), pexpt(logeta_poly(), rmu)),
      )
      temp = cdr(temp)
      rmu = one_plus(rmu)
      if !num_gt(rmu, rrmu) {
        continue
      }
      // LSA solves these equations over a field that contains the variable
      // of integration, but they hold only for coefficients that are
      // constants.  A solution that depends on that variable does not solve
      // the differential equation, so walk for coefficients that are
      // functions.
      if !rzerop(
          risch__rm(
            tt,
            risch__rp(
              risch__rt(s, risch_y),
              risch__rt(r, spderivative(risch_y, risch_mainvar)),
            ),
          ),
        ).truthy() {
        mu = rrmu
        fromlsa = true
        st = s_recurse
        continue
      }
      return if flag is Nil {
        ratqu(risch_y, p)
      } else {
        cons(risch__rt(rexpg_n(), ratqu(risch_y, p)), list1(Fix(0L)))
      }
    }
  }
  Nil
}

///|
fn erfarg(
  exparg : Value,
  coef : Value,
  risch_ratform : Value,
  risch_mainvar : Value,
) -> Value raise {
  let exparg = risch__rneg(exparg)
  let num = pnthrootp(ratnumerator(exparg), Fix(2L))
  if num is Nil {
    return Nil
  }
  let denom = pnthrootp(ratdenominator(exparg), Fix(2L))
  if denom is Nil {
    return Nil
  }
  let erfarg = cons(num, denom)
  let coef = ratqu(coef, spderivative(erfarg, risch_mainvar))
  if risch_constp(coef, risch_mainvar).truthy() {
    return simplify(
      list([
        list1(q_mtimes),
        mk(q_rat, [Fix(1L), Fix(2L)]),
        mk(q_mexpt, [q_d__pctpi, mk(q_rat, [Fix(1L), Fix(2L)])]),
        disrep(coef, risch_ratform),
        mk(q_p_erf, [disrep(erfarg, risch_ratform)]),
      ]),
    )
  }
  Nil
}

///|
fn erfarg2(
  exparg : Value,
  coeff : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_mainvar : Value,
) -> Value raise {
  let risch_var = risch_mainvar
  if num_eq(pdegree(car(exparg), risch_var), Fix(2L)) &&
    eq(caar(exparg), risch_var) &&
    risch_pconstp(cdr(exparg), risch_mainvar).truthy() &&
    risch_constp(coeff, risch_mainvar).truthy() {
    let mut a = ratqu(risch__rt(Fix(-1L), caddar(exparg)), cdr(exparg))
    let b = disrep(
      ratqu(
        risch__rt(Fix(-1L), polcoef(car(exparg), Fix(1L), risch_var)),
        cdr(exparg),
      ),
      risch_ratform,
    )
    let c = disrep(
      ratqu(polcoef(car(exparg), Fix(0L), risch_var), cdr(exparg)),
      risch_ratform,
    )
    let d = ratsqrt(a, risch_ratform)
    a = disrep(a, risch_ratform)
    simplify(
      mk(q_mtimes, [
        mk(q_mtimes, [
          mk(q_mexpt, [
            q_d__pcte,
            mk(q_mplus, [
              c,
              mk(q_mquotient, [
                mk(q_mexpt, [b, Fix(2L)]),
                mk(q_mtimes, [Fix(4L), a]),
              ]),
            ]),
          ]),
          mk(q_rat, [Fix(1L), Fix(2L)]),
          disrep(coeff, risch_ratform),
          mk(q_mexpt, [d, Fix(-1L)]),
          mk(q_mexpt, [q_d__pctpi, mk(q_rat, [Fix(1L), Fix(2L)])]),
        ]),
        mk(q_p_erf, [
          mk(q_mplus, [
            mk(q_mtimes, [d, risch_intvar]),
            mk(q_mtimes, [
              b,
              mk(q_rat, [Fix(1L), Fix(2L)]),
              mk(q_mexpt, [d, Fix(-1L)]),
            ]),
          ]),
        ]),
      ]),
    )
  } else {
    Nil
  }
}

///|
fn cxerfarg(
  ans : Value,
  expg : Value,
  n : Value,
  numdenom : Value,
  risch_ratform : Value,
  risch_intvar : Value,
  risch_mainvar : Value,
) -> Value raise {
  let mut arg = risch__rt(n, get(expg, q_rischarg))
  let mut fails : Value = Fix(0L)
  let num = car(numdenom)
  let mut denom = cdr(numdenom)
  let mut erfans : Value = Nil
  if !symval(q_d_erfflag).truthy() {
    fails = num
  } else {
    erfans = erfarg(arg, numdenom, risch_ratform, risch_mainvar)
    if erfans.truthy() {
      return list2(ans, erfans)
    }
    // again
    while !pcoefp(denom).truthy() &&
          cdddr(denom) is Nil &&
          eq(get(car(denom), q_leadop), q_mexpt) {
      arg = risch__rp(
        arg,
        risch__rt(num_neg(cadr(denom)), get(car(denom), q_rischarg)),
      )
      denom = caddr(denom)
    }
    for x in explist(num, arg, Fix(1L)).iter() {
      let coef = ratqu(car(x), denom)
      let exparg = cadr(x)
      let exppoly = caddr(x)
      let nerf = {
        let v = erfarg2(exparg, coef, risch_ratform, risch_intvar, risch_mainvar)
        if v.truthy() {
          v
        } else {
          erfarg(exparg, coef, risch_ratform, risch_mainvar)
        }
      }
      if nerf.truthy() {
        erfans = cons(nerf, erfans)
      } else {
        fails = pplus(fails, exppoly)
      }
    }
  }
  // lose
  if pzerop(fails).truthy() {
    cons(ans, erfans)
  } else {
    rischadd(
      cons(ans, erfans),
      rischnoun(
        risch__rt(
          ratexpt(cons(cons(expg, list2(Fix(1L), Fix(1L))), Fix(1L)), n),
          ratqu(fails, cdr(numdenom)),
        ),
        risch_ratform,
        risch_intvar,
      ),
    )
  }
}

///|
fn explist(p : Value, oarg : Value, exps : Value) -> Value raise {
  if pcoefp(p).truthy() || !eq(q_mexpt, get(car(p), q_leadop)) {
    list1(list3(p, oarg, ptimes(p, exps)))
  } else {
    let narg = get(car(p), q_rischarg)
    let c = Collector::new()
    let mut terms = cdr(p)
    while terms is Cons(_) {
      let exp_ = car(terms)
      let coef = cadr(terms)
      c.append_list(
        explist(
          coef,
          risch__rp(oarg, risch__rt(exp_, narg)),
          ptimes(exps, list3(car(p), exp_, Fix(1L))),
        ),
      )
      terms = cddr(terms)
    }
    c.result()
  }
}

///|
fn intsetup(exp_ : Value, risch__starvar : Value) -> (Value, Value) raise {
  with_specials(
    [
      (q_varlist, Nil),
      (q_d_factorflag, Nil),
      (q_d_ratfac, Nil),
      (q_d_keepfloat, Nil),
      (q_n_starfnewvarsw, Nil),
    ],
    () => {
      let mut exp_ = exp_
      let mut do_y = true
      while true {
        if do_y {
          // y
          exp_ = radcan1(exp_, risch__starvar)
          fnewvar(exp_) |> ignore
          set(q_n_starfnewvarsw, t) |> ignore
          do_y = false
        }
        // a
        let mut clist : Value = Nil
        let mut dlist : Value = Nil
        let mut z = symval(q_varlist)
        let mut restart = false
        while true {
          // up
          let risch_y = car(z)
          z = cdr(z)
          if freeof(risch__starvar, risch_y).truthy() {
            clist = cons(risch_y, clist)
          } else if eq(risch_y, risch__starvar) {
            ()
          } else if mexptp(risch_y).truthy() && !eq(cadr(risch_y), q_d__pcte) {
            if !freeof(risch__starvar, caddr(risch_y)).truthy() {
              dlist = list3(
                list2(q_mexpt, q_simp),
                q_d__pcte,
                mul2_star(caddr(risch_y), mk(q_p_log, [cadr(risch_y)])),
              )
              exp_ = maxima_substitute(dlist, risch_y, exp_)
              set(q_varlist, Nil) |> ignore
              restart = true
              break
            } else if atom(caddr(risch_y)) {
              if numberp(caddr(risch_y)) {
                dlist = cons(risch_y, dlist)
              } else {
                return (Nil, t)
              }
            } else {
              dlist = cons(risch_y, dlist)
            }
          } else {
            dlist = cons(risch_y, dlist)
          }
          if z is Nil {
            break
          }
        }
        if restart {
          do_y = true
          continue
        }
        if memq(q_d__pcti, clist).truthy() {
          clist = cons(q_d__pcti, delete(q_d__pcti, clist))
        }
        set(
          q_varlist,
          append(
            clist,
            cons(
              risch__starvar,
              nreverse(
                sort_list(append(dlist, Nil), (a, b) => intgreat(
                    a, b, risch__starvar,
                  ).truthy()),
              ),
            ),
          ),
        )
        |> ignore
        orderpointer(symval(q_varlist)) |> ignore
        let old = symval(q_varlist)
        mapc(
          b => intset1(b, risch__starvar) |> ignore,
          cons(risch__starvar, dlist),
        )
        |> ignore
        if alike(old, symval(q_varlist)).truthy() {
          return (ratrep_star(exp_), Nil)
        }
      }
      (Nil, Nil)
    },
  )
}

///|
fn leadop(exp_ : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if mqapplyp(exp_).truthy() {
    cadr(exp_)
  } else {
    caar(exp_)
  }
}

///|
fn leadarg(exp_ : Value) -> Value raise {
  if atom(exp_) {
    Fix(0L)
  } else if mexptp(exp_).truthy() && eq(cadr(exp_), q_d__pcte) {
    caddr(exp_)
  } else if mqapplyp(exp_).truthy() {
    car(subfunargs(exp_))
  } else {
    cadr(exp_)
  }
}

///|
fn intset1(b : Value, risch__starvar : Value) -> Value raise {
  let d0 = if mexptp(b).truthy() {
    // needed for radicals
    list3(
      list2(q_mtimes, q_simp),
      b,
      radcan1(sdiff(simplify(caddr(b)), risch__starvar), risch__starvar),
    )
  } else {
    radcan1(sdiff(simplify(b), risch__starvar), risch__starvar)
  }
  fnewvar(d0) |> ignore
  let d = ratrep_star(d0)
  let c = ratrep_star(leadarg(b))
  let e = cdr(assoc_equal(b, pair(symval(q_varlist), symval(q_genvar))))
  putprop(e, leadop(b), q_leadop) |> ignore
  putprop(e, b, q_rischexpr) |> ignore
  putprop(e, cdr(d), q_rischdiff) |> ignore
  putprop(e, cdr(c), q_rischarg)
}

///|
/// Order of expressions for risch: expressions containing erf and li last,
/// then order by size of expression to guarantee that any subexpressions
/// are considered smaller.
fn intgreat(a : Value, b : Value, risch__starvar : Value) -> Value raise {
  if !atom(a) && !atom(b) {
    if !freeof(q_p_erf, a).truthy() && freeof(q_p_erf, b).truthy() {
      t
    } else if !freeof(q_d_li, a).truthy() && freeof(q_d_li, b).truthy() {
      t
    } else if freeof(q_d_li, a).truthy() && !freeof(q_d_li, b).truthy() {
      Nil
    } else if freeof(q_p_erf, a).truthy() && !freeof(q_p_erf, b).truthy() {
      Nil
    } else if num_gt(conssize(a), conssize(b)) {
      t
    } else if num_lt(conssize(a), conssize(b)) {
      Nil
    } else {
      great(
        resimplify(fixintgreat(a, risch__starvar)),
        resimplify(fixintgreat(b, risch__starvar)),
      )
    }
  } else {
    great(
      resimplify(fixintgreat(a, risch__starvar)),
      resimplify(fixintgreat(b, risch__starvar)),
    )
  }
}

///|
fn fixintgreat(a : Value, risch__starvar : Value) -> Value raise {
  subst(q_n_sl_101x, risch__starvar, a)
}

///|
fn init_risch() -> Unit raise {
  ()
}
