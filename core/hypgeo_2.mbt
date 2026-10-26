// Port of src/hypgeo.lisp (part 2): $specint, the drivers DEFINTEGRATE,
// DEFEXEC and LT-EXEC, Algorithm 1 (c*t^v*exp(-s*t+e*f)) and the dispatcher
// LT-SF-LOG of Algorithm 2.

///|
/// $specint is the Maxima User function
fn d_specint(expr : Value, var2 : Value) -> Value raise {
  with_specials([(q_d_radexpand, Nil), (q_ear_checkcoefsignlist, Nil)], () => {
    set(q_d_radexpand, q_d_all) |> ignore
    defintegrate(expr, var2)
  })
}

///|
/// int_0^inf f(x) dx = int_0^inf f(sqrt(u))/(2 sqrt(u)) du
/// Only called when the direct route returned a noun form.
fn defint_sqrt_subst(form : Value, var2 : Value) -> Value raise {
  with_special(q_ear_specint_sqrt_subst_active, t, () => {
    let u = gensym(prefix="u")
    let r = power(u, hypgeo__r(1, 2))
    let new = d_ratsimp(
      div(maxima_substitute(r, var2, form), mul2(int(2), r)),
      Nil,
    )
    if freeof(var2, new).truthy() {
      let res = defintegrate(new, u)
      if freeof(u, res).truthy() && !among(q_p_specint, res).truthy() {
        res
      } else {
        Nil
      }
    } else {
      Nil
    }
  })
}

///|
fn defintegrate(expr : Value, var2 : Value) -> Value raise {
  // Expand the form with $exponentialize to convert trig and hyperbolic
  // functions to exponential functions that we can handle.  At first
  // factor the integrand.
  let form = with_special(q_d_exponentialize, t, () => d_factor(
    resimplify(expr),
  ))

  // Because we call defintegrate recursively, we add code to end the
  // recursion safely.
  if atom(form) {
    if numberp(form) && zerop(form) {
      return int(0)
    } else {
      return mk_simp(q_p_specint, [form, var2])
    }
  }

  // We try to find a constant denominator. This is necessary to get results
  // for integrands like u(t)/(a+b+c+...).
  let den = with_specials(
    [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
    () => d_denom(form),
  )
  if !equal(int(1), den) && d_freeof(list2(var2, den)).truthy() {
    return div(defintegrate(mul2(den, form), var2), den)
  }

  // We search for a sum of Exponential functions which we can integrate.
  // This code finds result for Trigonometric or Hyperbolic functions with
  // a factor t^-1 or t^-2 e.g. t^-1*sin(a*t).
  let l = m2_defltep(form, var2)
  let s = mul2(int(-1), cdras(q_a, l))
  let u = d_expand(cdras(q_u, l))
  let e_st = () => power(q_d__pcte, muln_([int(-1), s, var2]))
  let mut l1 = m2_sum_with_exp_case1(u, var2)
  if l1.truthy() {
    //  c * t^-1 * (%e^(-a*t) - %e^(-b*t)) + d
    let c = cdras(q_c, l1)
    let a = mul2(int(-1), cdras(q_a, l1))
    let b = mul2(int(-1), cdras(q_b, l1))
    let d = cdras(q_d, l1)
    return add2(
      mul2(c, hypgeo__take(q_p_log, [div(add2(s, b), add2(s, a))])),
      defintegrate(mul2(d, e_st()), var2),
    )
  }
  l1 = m2_sum_with_exp_case2(u, var2)
  if l1.truthy() {
    //  c * t^(-3/2) * (%e^(-a*t) - %e^(-b*t)) + d
    let c = cdras(q_c, l1)
    let a = mul2(int(-1), cdras(q_a, l1))
    let b = mul2(int(-1), cdras(q_b, l1))
    let d = cdras(q_d, l1)
    return add2(
      muln_([
        int(2),
        c,
        power(q_d__pctpi, hypgeo__r(1, 2)),
        sub(
          power(add2(s, b), hypgeo__r(1, 2)),
          power(add2(s, a), hypgeo__r(1, 2)),
        ),
      ]),
      defintegrate(mul2(d, e_st()), var2),
    )
  }
  l1 = m2_sum_with_exp_case3(u, var2)
  if l1.truthy() {
    // c * t^-2 * (1 - 2 * %e^(-a*t) + %e^(2*a*t)) + d
    let c = cdras(q_c, l1)
    let a = div(cdras(q_a, l1), int(-2))
    let d = cdras(q_d, l1)
    return add2(
      mul2(
        c,
        addn_([
          mul2(
            addn_([s, a, a]),
            hypgeo__take(q_p_log, [addn_([s, a, a])]),
          ),
          mul2(s, hypgeo__take(q_p_log, [s])),
          mul3(int(-2), add2(s, a), hypgeo__take(q_p_log, [add2(s, a)])),
        ]),
      ),
      defintegrate(mul2(d, e_st()), var2),
    )
  }
  l1 = m2_sum_with_exp_case4(u, var2)
  if l1.truthy() {
    // c * t^-1 * (1 - 2 * %e^(-a*t) + %e^(2*a*t)) + d
    let c = cdras(q_c, l1)
    let a = div(cdras(q_a, l1), mul2(int(4), q_d__pcti))
    let d = cdras(q_d, l1)
    return add2(
      mul3(
        int(-1),
        c,
        hypgeo__take(q_p_log, [
          add2(
            int(1),
            div(
              mul3(int(4), a, a),
              mul2(
                sub(s, mul3(int(2), q_d__pcti, a)),
                sub(s, mul3(int(2), q_d__pcti, a)),
              ),
            ),
          ),
        ]),
      ),
      defintegrate(mul2(d, e_st()), var2),
    )
  }
  l1 = m2_sum_with_exp_case5(u, var2)
  if l1.truthy() {
    // c * t^-1 * (1 - %e^(2*a*t)) + d
    let c = cdras(q_c, l1)
    let a = cdras(q_a, l1)
    let d = cdras(q_d, l1)
    return add2(
      mul2(c, hypgeo__take(q_p_log, [div(sub(s, a), s)])),
      defintegrate(mul2(d, e_st()), var2),
    )
  }
  // At this point we expand the integrand.
  let res = distrdefexecinit(d_expand(form), var2)
  // If that failed, try the substitution x = sqrt(u).
  if among(q_p_specint, res).truthy() &&
    !symval(q_ear_specint_sqrt_subst_active).truthy() {
    let r = defint_sqrt_subst(form, var2)
    if r.truthy() {
      return r
    }
  }
  res
}

// Test functions for the pattern m2-sum-with-exp-case<n>

///|
fn equal_times_minus_one(a : Value, b : Value) -> Value raise {
  lbool(equal(a, mul2(int(-1), b)))
}

///|
fn equal_times_minus_two(a : Value, b : Value) -> Value raise {
  lbool(equal(a, mul2(int(-2), b)))
}

///|
fn equal_div_two(a : Value, b : Value) -> Value raise {
  lbool(equal(a, div(b, int(2))))
}

// Called by defintegrate.
// Call for every term of a sum defexec and add up the results.

///|
/// Evaluate the transform of a sum as sum of transforms.
fn distrdefexecinit(expr : Value, var2 : Value) -> Value raise {
  if eq(caar(expr), q_mplus) {
    distrdefexec(cdr(expr), var2)
  } else {
    defexec(expr, var2)
  }
}

///|
/// EXPR is a list of addends. Compute the transform of each addend and
/// add them up.
fn distrdefexec(expr : Value, var2 : Value) -> Value raise {
  if expr is Nil {
    int(0)
  } else {
    add2(defexec(car(expr), var2), distrdefexec(cdr(expr), var2))
  }
}

// Called after transformation of a integrand to a new representation.
// Evaluate the transform of a sum as sum of transforms.

///|
fn sendexec(r : Value, a : Value) -> Value raise {
  distrexecinit(d_expand(mul2(init_(r), a)))
}

///|
/// Compute r*exp(-p*t), where t is the variable of integration and
/// p is the parameter of the Laplace transform.
fn init_(r : Value) -> Value raise {
  mul2(r, power(q_d__pcte, mul3(int(-1), hypgeo__var(), hypgeo__par())))
}

///|
fn distrexecinit(expr : Value) -> Value raise {
  if consp(expr) && consp(car(expr)) && eq(caar(expr), q_mplus) {
    distrexec(cdr(expr))
  } else {
    hypgeo_exec(expr)
  }
}

///|
fn distrexec(expr : Value) -> Value raise {
  if expr is Nil {
    int(0)
  } else {
    add2(hypgeo_exec(car(expr)), distrexec(cdr(expr)))
  }
}

///|
/// It dispatches according to the kind of transform it matches.
fn hypgeo_exec(expr : Value) -> Value raise {
  let l = m2_ltep(expr, hypgeo__var(), hypgeo__par())
  if l.truthy() {
    let u = cdras(q_u, l)
    let a = cdras(q_a, l)
    let c = cdras(q_c, l)
    let e = cdras(q_e, l)
    let f = cdras(q_f, l)
    return ltscale(u, c, a, e, f)
  }
  hypgeo__flag(q_other_trans_to_follow)
}

///|
/// Compute transform of EXPR wrt the variable of integration VAR2.
fn defexec(expr : Value, var2 : Value) -> Value raise {
  with_specials(
    [
      (q_ear_hypgeo_par, q_psey), // Set parameter of Laplace transform
      (q_ear_hypgeo_var, var2), // Set variable of integration
      (q_ear_hyp_return_noun_flag, Nil),
    ], // Reset the flag
    () => {
      let form = expr
      let mut l = m2_defltep(expr, var2)
      let mut s = cdras(q_a, l) // Get the parameter of the Laplace transform.
      // If we have not found a parameter, we try to factor the integrand.
      if numberp(s) && equal(s, int(0)) {
        l = m2_defltep(d_factor(form), hypgeo__var())
        s = cdras(q_a, l)
      }
      if l.truthy() {
        // EXPR is an expression of the form u*%e^(s*t+e*f+c).  So s
        // is basically the parameter of the Laplace transform.
        let result = negtest(l, s)
        // At this point we construct the noun form if one of the
        // called routines set the global flag. If the global flag
        // is not set, the noun form has been already constructed.
        if symval(q_ear_hyp_return_noun_form_p).truthy() &&
          symval(q_ear_hyp_return_noun_flag).truthy() {
          mk_simp(q_p_specint, [expr, hypgeo__var()])
        } else {
          result
        }
      } else if symval(q_ear_hyp_return_noun_form_p).truthy() {
        // If necessary we construct the noun form.
        mk_simp(q_p_specint, [expr, hypgeo__var()])
      } else {
        q_other_defint_to_follow_defexec
      }
    },
  )
}

///|
/// L is the integrand of the transform, after pattern matching.  S is
/// the parameter (p) of the transform.
fn negtest(l : Value, s : Value) -> Value raise {
  if eq(d_asksign(d_realpart(s)), q_d_neg) {
    // The parameter of transform must have a negative realpart.  Break out
    // the integrand into its various components.
    let u = cdras(q_u, l)
    let e = cdras(q_e, l)
    let mut f = cdras(q_f, l)
    let c = cdras(q_c, l)
    if equal(e, int(0)) {
      f = int(1)
    }
    // To compute the transform, we replace A with PSEY for simplicity.
    // After the transform is computed, replace PSEY with A.  We know psey
    // must be positive, so we add a rule for the sign of psey.
    mfuncall(q_d_assume, list1(mk(q_mgreaterp, [hypgeo__par(), int(0)])))
    |> ignore
    let f0 = f
    return hypgeo__unwind(
      () => {
        let result = ltscale(u, c, int(0), e, f0)
        // $SPECINT binds $RADEXPAND to '$ALL, which would split
        // (-%i)^(-psey) into (-1)^(-3*psey/2) and leave the principal branch.
        with_special(q_d_radexpand, t, () => maxima_substitute(
          mul2(int(-1), s),
          hypgeo__par(),
          result,
        ))
      },
      // We forget the rule after the calculation, even after an error.
      () => mfuncall(
        q_d_forget,
        list1(mk(q_mgreaterp, [hypgeo__par(), int(0)])),
      )
      |> ignore,
    )
  }
  hypgeo__flag(q_other_defint_to_follow_negtest)
}

///|
/// Compute the transform of
///
///  U * %E^(-VAR * (*PAR* - PAR0) + E*F + C)
fn ltscale(
  u : Value,
  c : Value,
  par0 : Value,
  e : Value,
  f : Value,
) -> Value raise {
  let p1 = power(q_d__pcte, c)
  let p2 = sub(hypgeo__par(), par0)
  mul2(p1, substl(p2, hypgeo__par(), lt_exec(u, e, f)))
}

///|
/// Compute the transform of u*%e^(-p*t+e*f)
fn lt_exec(u0 : Value, e : Value, f : Value) -> Value raise {
  let mut u = u0
  let mut l = m2_sum(u, hypgeo__var())
  if l.truthy() {
    // We have found a summation.
    // Temporarily assume lo <= summation index <= hi so that
    // Maxima doesn't ask about the sign of the summation index.
    let ls = l
    return hypgeo__with_new_context(() => {
      let mut i = cdras(q_i, ls)
      let lo = cdras(q_l, ls)
      let hi = cdras(q_h, ls)
      let mut v = cdras(q_u, ls)
      let ef = if equal(e, int(0)) {
        int(1)
      } else {
        power(q_d__pcte, mul2(e, f))
      }
      // The integrand is u*%e^(e*f), and %e^(e*f) goes into the sum.
      // Rename the summation index if it would capture a free
      // variable of the same name in %e^(e*f).
      if !free(ef, i).truthy() {
        let mut j = gensumindex()
        while !free(list([Nil, v, ef]), j).truthy() {
          j = gensumindex()
        }
        v = maxima_substitute(j, i, v)
        i = j
      }
      if !eq(t, csign(lo)) {
        assume(ftake(q_mgeqp, [i, lo])) |> ignore
      }
      if !eq(t, csign(hi)) {
        assume(ftake(q_mleqp, [i, hi])) |> ignore
      }
      mul2(
        cdras(q_c, ls),
        hypgeo__take(q_p_sum, [sendexec(ef, v), i, lo, hi]),
      )
    })
  }
  l = m2_unit_step(u, hypgeo__var())
  if l.truthy() &&
    {
      let sgn = d_csign(cdras(q_a, l))
      // Ask for an unknown sign of a real shift, as LAPHSTEP does.
      member(sgn, list([q_d_pos, q_d_pz, q_d_zero])).truthy() ||
      (
        member(sgn, list([q_d_pn, q_d_pnz])).truthy() &&
        member(d_asksign(cdras(q_a, l)), list([q_d_pos, q_d_zero])).truthy()
      )
    } {
    // unit_step(t+a) with a >= 0 is 1 for t > 0, so drop it.
    return sendexec(cdras(q_u, l), if equal(e, int(0)) {
      int(1)
    } else {
      power(q_d__pcte, mul2(e, f))
    })
  }
  l = m2_unit_step(u, hypgeo__var())
  if l.truthy() {
    // We have found the Unit Step function.
    u = cdras(q_u, l)
    let a = cdras(q_a, l)
    // The integrand is u*%e^(e*f). Keep that factor.
    if !equal(e, int(0)) {
      u = mul2(u, power(q_d__pcte, mul2(e, f)))
    }
    return mul2(
      power(q_d__pcte, mul2(a, hypgeo__par())),
      sendexec(
        if d_freeof(list2(hypgeo__var(), u)).truthy() {
          u
        } else {
          maxima_substitute(sub(hypgeo__var(), a), hypgeo__var(), u)
        },
        int(1),
      ),
    )
  }
  let r = lt_unitstep_exp(
    if equal(e, int(0)) {
      u
    } else {
      mul2(u, power(q_d__pcte, mul2(e, f)))
    },
  )
  if r.truthy() {
    return r
  }
  if equal(e, int(0)) {
    // The simple case of u*%e^(-p*t)
    return lt_sf_log(u)
  }
  if !equal(e, int(0)) {
    l = m2_c_start_hatv(u, hypgeo__var())
    if l.truthy() {
      // We have u*%e^(-p*t+e*f).  Try to see if U is of the form
      // c*t^v.  If so, we can handle it here.
      return lt_exp(l, e, f)
    }
  }
  // The complicated case.  Remove the e*f term and move it to u.
  lt_sf_log(mul2(u, power(q_d__pcte, mul2(e, f))))
}

///|
/// True unless $CSIGN finds X complex or imaginary. $ASKSIGN signals an
/// error for such an X.
fn lt_real_p(x : Value) -> Value raise {
  lbool(!member(d_csign(x), list2(q_d_complex, q_d_imaginary)).truthy())
}

///|
/// True if X is positive. Asks for the sign of a real X if unknown.
fn lt_pos_p(x : Value) -> Value raise {
  if lt_real_p(x).truthy() {
    lbool(eq(d_asksign(x), q_d_pos))
  } else {
    Nil
  }
}

///|
/// Laplace transform of v(t)*unit_step(%e^(b*t)-c), b and c free of t.
/// Returns NIL for anything else so that LT-EXEC can go on.
fn lt_unitstep_exp(u : Value) -> Value raise {
  if freeof(q_d_unit_step, u).truthy() {
    return Nil
  }
  let l = m2(u, subst(hypgeo__var(), hypgeo__ph_var2, hypgeo__p_unitstep_exp))
  let bc = if l.truthy() {
    split_exp_minus_const(cdras(q_w, l), hypgeo__var())
  } else {
    Nil
  }
  let v = cdras(q_v, l)
  let b = car(bc)
  let c = cdr(bc)
  if bc.truthy() && lt_real_p(b).truthy() && lt_real_p(c).truthy() {
    let full = () => sendexec(v, int(1))
    // v(t)*unit_step(t-t0) with t0 = log(c)/b
    let shifted = () => mul2(
      power(c, div(mul2(int(-1), hypgeo__par()), b)),
      sendexec(
        maxima_substitute(
          add2(hypgeo__var(), div(hypgeo__take(q_p_log, [c]), b)),
          hypgeo__var(),
          v,
        ),
        int(1),
      ),
    )
    // c <= 0, or b > 0 and c <= 1: the step is 1 for t > 0.
    if !eq(d_asksign(c), q_d_pos) ||
      (
        eq(d_asksign(b), q_d_pos) &&
        !eq(d_asksign(sub(c, int(1))), q_d_pos)
      ) {
      return full()
    }
    // b < 0 and c >= 1: the step is 0 for t > 0.
    if eq(d_asksign(b), q_d_neg) && !eq(d_asksign(sub(int(1), c)), q_d_pos) {
      return int(0)
    }
    // b > 0 and c > 1: the step is unit_step(t-t0).
    if eq(d_asksign(b), q_d_pos) {
      return shifted()
    }
    // b < 0 and 0 < c < 1: the step is 1-unit_step(t-t0).
    if eq(d_asksign(b), q_d_neg) {
      return sub(full(), shifted())
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// Algorithm 1: Laplace transform of c*t^v*exp(-s*t+e*f)
//
// L contains the pattern for c*t^v.

///|
fn lt_exp(l : Value, e0 : Value, f : Value) -> Value raise {
  let c = cdras(q_c, l)
  let mut v = cdras(q_v, l)
  let mut e = e0
  if m2_t_hat2(f, hypgeo__var()).truthy() {
    e = inv(mul2(int(-8), e))
    v = add2(v, int(1))
    return f24p146test(c, v, e)
  }
  if m2_sqroott(f, hypgeo__var()).truthy() {
    // We don't do the transformation at this place. Because we take the
    // square of e we lost the sign and get wrong results.
    return f35p147test(c, v, e)
  }
  if m2_t_hat_1(f, hypgeo__var()).truthy() {
    e = mul2(int(-4), e)
    v = add2(v, int(1))
    return f29p146test(c, v, e) // We have to call with the constant c.
  }
  if equal(v, int(0)) && m2_e_hat_t(f, hypgeo__var()).truthy() {
    return f36p147(c, e) // with the constant c.
  }
  if equal(v, int(0)) && m2_e_hatt(f, hypgeo__var()).truthy() {
    return f37p147(c, mul2(int(-1), e))
  }
  hypgeo__flag(q_other_lt_exponential_to_follow)
}

///|
/// Recognize w = %e^(b*hv) - c, b and c free of hv. Returns (b . c) or nil.
fn split_exp_minus_const(w : Value, var2 : Value) -> Value raise {
  if consp(w) && eq(caar(w), q_mplus) && length(cdr(w)) == 2 {
    let terms = cdr(w)
    let c0 = find_if(x => d_freeof(list2(var2, x)).truthy(), terms)
    let ex = find_if(x => !d_freeof(list2(var2, x)).truthy(), terms)
    if c0.truthy() &&
      ex.truthy() &&
      consp(ex) &&
      eq(caar(ex), q_mexpt) &&
      eq(cadr(ex), q_d__pcte) {
      let l = m2_a_start(caddr(ex), var2)
      if l.truthy() {
        return cons(cdras(q_a, l), mul2(int(-1), c0))
      }
    }
  }
  Nil
}

// Algorithm 1.1: Laplace transform of c*t^v*exp(-a*t^2)
//
// Table of Integral Transforms, p. 146, formula 24:
//
// t^(v-1)*exp(-t^2/8/a)
//   -> gamma(v)*2^v*a^(v/2)*exp(a*p^2)*D[-v](2*p*sqrt(a))
//
// Re(a) > 0, Re(v) > 0

///|
fn f24p146test(c : Value, v : Value, a : Value) -> Value raise {
  if eq(d_asksign(a), q_d_pos) && eq(d_asksign(v), q_d_pos) {
    // Both a and v must be positive
    f24p146(c, v, a)
  } else {
    hypgeo__flag(q_fail_on_f24p146test)
  }
}

///|
fn f24p146(c : Value, v : Value, a : Value) -> Value raise {
  muln_([
    c,
    hypgeo__take(q_p_gamma, [v]),
    power(int(2), v),
    power(a, div(v, int(2))),
    power(q_d__pcte, mul3(a, hypgeo__par(), hypgeo__par())),
    dtford(
      mul3(int(2), hypgeo__par(), power(a, hypgeo__r(1, 2))),
      mul2(int(-1), v),
    ),
  ])
}

// Algorithm 1.2: Laplace transform of c*t^v*exp(-a*sqrt(t))
//
// Table of Integral Transforms, p. 147, formula 35:
//
// (2*t)^(v-1)*exp(-2*sqrt(a)*sqrt(t))
//    -> gamma(2*v)*p^(-v)*exp(a/p/2)*D[-2*v](sqrt(2*a/p))
//
// Re(v) > 0, Re(p) > 0

///|
/// Check if conditions for f35p147 hold
fn f35p147test(c : Value, v : Value, a : Value) -> Value raise {
  if eq(d_asksign(add2(v, int(1))), q_d_pos) {
    // v must be positive
    f35p147(c, v, a)
  } else {
    // Set a global flag. When *hyp-return-noun-form-p* is T the noun
    // form will be constructed in the routine DEFEXEC.
    hypgeo__flag(q_fail_on_f35p147test)
  }
}

///|
fn f35p147(c : Value, v0 : Value, a : Value) -> Value raise {
  // We have not done the calculation v->v+1 and a-> a^2/4
  // and substitute here accordingly.
  let v = add2(v0, int(1))
  muln_([
    c,
    hypgeo__take(q_p_gamma, [add2(v, v)]),
    power(int(2), sub(int(1), v)), // Is this supposed to be here?
    power(hypgeo__par(), mul2(int(-1), v)),
    power(
      q_d__pcte,
      muln_([a, a, hypgeo__r(1, 8), inv(hypgeo__par())]),
    ),
    // We need an additional factor -1 to get the expected results.
    dtford(
      mul3(
        int(-1),
        a,
        inv(power(mul2(int(2), hypgeo__par()), hypgeo__r(1, 2))),
      ),
      mul2(int(-2), v),
    ),
  ])
}

///|
/// Express a parabolic cylinder function as either a parabolic
/// cylinder function or as hypergeometric function.
///
/// Tables of Integral Transforms, p. 386 gives this definition:
///
/// D[v](z) = 2^(v/2+1/4)*z^(-1/2)*W[v/2+1/4,1/4](z^2/2)
fn dtford(z : Value, v : Value) -> Value raise {
  let inv4 = inv(int(4))
  if symval(q_d_prefer_d).truthy() ||
    whittindtest(add2(div(v, int(2)), inv4), inv4).truthy() {
    // At this time the Parabolic Cylinder D function is not implemented
    // as a simplifying function. We call nevertheless the simplifier
    // to simplify the arguments.
    hypgeo__take(q_d_parabolic_cylinder_d, [v, z])
  } else {
    simpdtf(z, v)
  }
}

///|
fn whittindtest(i1 : Value, i2 : Value) -> Value raise {
  let r1 = maxima_integerp(add2(i2, i2))
  if r1.truthy() {
    return r1
  }
  let r2 = neginp(sub(sub(hypgeo__r(1, 2), i2), i1))
  if r2.truthy() {
    return r2
  }
  neginp(sub(add2(hypgeo__r(1, 2), i2), i1))
}

///|
/// Return T if a is a non-positive integer.
fn neginp(a : Value) -> Value raise {
  if maxima_integerp(a).truthy() {
    let z = zerop1(a)
    if z.truthy() {
      z
    } else {
      lbool(eq(d_sign(a), q_d_neg))
    }
  } else {
    Nil
  }
}

///|
/// Express parabolic cylinder function as a hypergeometric function.
///
/// D[v](z) = U(-v-1/2,z)
///         = sqrt(%pi)*2^(v/2+1/2)*x*exp(-x^2/4)
///                    *M(1/2-v/2,3/2,x^2/2)/gamma(-v/2)
///             + sqrt(%pi)*2^(v/2)*exp(-x^2/4)/gamma(1/2-v/2)
///                        *M(-v/2,1/2,x^2/2)
fn simpdtf(z : Value, v : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  let pow = power(q_d__pcte, mul3(z, z, hypgeo__r(-1, 4)))
  add2(
    muln_([
      power(int(2), div(sub(v, int(1)), int(2))),
      z,
      int(-2),
      power(q_d__pctpi, inv2), // gamma(-1/2)
      inv(hypgeo__take(q_p_gamma, [mul3(v, int(-1), inv2)])),
      pow,
      hgfsimp_exec(
        list1(sub(inv2, div(v, int(2)))),
        list1(hypgeo__r(3, 2)),
        mul3(z, z, inv2),
      ),
    ]),
    muln_([
      power(int(2), div(v, int(2))),
      power(q_d__pctpi, inv2), // gamma(1/2)
      pow,
      inv(hypgeo__take(q_p_gamma, [sub(inv2, mul2(v, inv2))])),
      hgfsimp_exec(list1(mul3(v, int(-1), inv2)), list1(inv2), mul3(z, z, inv2)),
    ]),
  )
}

// Algorithm 1.3: Laplace transform of t^v*exp(1/t)
//
// Table of Integral Transforms, p. 146, formula 29:
//
// t^(v-1)*exp(-a/t/4)
//    -> 2*(a/p/4)^(v/2)*bessel_k(v, sqrt(a)*sqrt(p))
//
// Re(a) > 0

///|
/// Check if conditions for f29p146test hold
fn f29p146test(c : Value, v : Value, a : Value) -> Value raise {
  if eq(d_asksign(a), q_d_pos) {
    f29p146(c, v, a)
  } else {
    hypgeo__flag(q_fail_on_f29p146test)
  }
}

///|
fn f29p146(c : Value, v : Value, a : Value) -> Value raise {
  muln_([
    int(2),
    c,
    power(mul3(a, hypgeo__r(1, 4), inv(hypgeo__par())), div(v, int(2))),
    ktfork(a, v),
  ])
}

///|
/// bessel_k(v, sqrt(a)*sqrt(p)) in terms of bessel_k or in terms of
/// hypergeometric functions.
///
/// Choose bessel_k if the order v is an integer.
fn ktfork(a : Value, v : Value) -> Value raise {
  let z = power(mul2(a, hypgeo__par()), hypgeo__r(1, 2))
  if maxima_integerp(v).truthy() {
    hypgeo__take(q_p_bessel_k, [v, z])
  } else {
    simpktf(z, v)
  }
}

///|
/// Express the Bessel K function in terms of hypergeometric functions.
///
/// K[v](z) = %pi/2*(bessel_i(-v,z)-bessel(i,z))/sin(v*%pi)
///
/// and
///
/// bessel_i(v,z) = (z/2)^v/gamma(v+1)*0F1(;v+1;z^2/4)
fn simpktf(z : Value, v : Value) -> Value raise {
  let dz2 = div(z, int(2))
  muln_([
    q_d__pctpi,
    hypgeo__r(1, 2),
    inv(hypgeo__take(q_p_sin, [mul2(v, q_d__pctpi)])),
    sub(
      mul3(
        power(dz2, mul2(int(-1), v)),
        inv(hypgeo__take(q_p_gamma, [sub(int(1), v)])),
        hgfsimp_exec(
          Nil,
          list1(sub(int(1), v)),
          mul3(z, z, hypgeo__r(1, 4)),
        ),
      ),
      mul3(
        power(dz2, v),
        inv(hypgeo__take(q_p_gamma, [add2(v, int(1))])),
        hgfsimp_exec(
          Nil,
          list1(add2(v, int(1))),
          mul3(z, z, hypgeo__r(1, 4)),
        ),
      ),
    ),
  ])
}

///|
/// Compute Z^P on the principal branch. A numeric complex Z gives
/// |Z|^P*%e^(%i*P*arg(Z)), so that conjugate bases such as %i and -%i give
/// matching factors (%i^P itself simplifies to (-1)^(P/2)). Any other Z gives
/// the power built with $RADEXPAND = T, because the binding of $RADEXPAND to
/// '$ALL by $SPECINT splits (-b)^P into (-1)^P*b^P, which is wrong for b < 0.
fn principal_power(z : Value, p : Value) -> Value raise {
  let (cnum, re, im) = hypgeo__complex_number_p_mv(z)
  if cnum && !zerop1(im).truthy() {
    mul2(
      power(power(add2(mul2(re, re), mul2(im, im)), hypgeo__r(1, 2)), p),
      power(q_d__pcte, mul3(q_d__pcti, p, ftake(q_p_atan2, [im, re]))),
    )
  } else {
    with_special(q_d_radexpand, t, () => power(z, p))
  }
}

// Algorithm 1.4: Laplace transform of exp(exp(-t))
//
// Table of Integral Transforms, p. 147, formula 36:
//
// exp(-a*exp(-t))
//   -> a^(-p)*gamma_incomplete_lower(p,a)

///|
fn f36p147(c : Value, a : Value) -> Value raise {
  let na = mul2(int(-1), a)
  mul3(
    c,
    principal_power(na, mul2(int(-1), hypgeo__par())),
    mk_simp(q_p_gamma_incomplete_lower, [hypgeo__par(), na]),
  )
}

// Algorithm 1.5: Laplace transform of exp(exp(t))
//
// Table of Integral Transforms, p. 147, formula 36:
//
// exp(-a*exp(t))
//   -> a^(-p)*gamma_incomplete(-p,a)

///|
fn f37p147(c : Value, a : Value) -> Value raise {
  mul3(
    c,
    principal_power(a, hypgeo__par()),
    hypgeo__take(q_p_gamma_u_incomplete, [mul2(int(-1), hypgeo__par()), a]),
  )
}

// ---------------------------------------------------------------------------
// Algorithm 2: Laplace transform of u(t)*%e^(-p*t).
//
// u contains one or more special functions. Dispatches according to the
// special functions involved in the Laplace transformable expression.
// The ordering of the calls to match a pattern is important.

///|
/// c*atan(a*t) with a > 0
/// -> c*(Ci(p)*sin(p) + (%pi/2 - Si(p))*cos(p))/s with p = s/a
fn lt_atan(rest_ : Value, arg : Value) -> Value raise {
  let l = m2_a_start(arg, hypgeo__var())
  if l.truthy() &&
    freeof(hypgeo__var(), rest_).truthy() &&
    lt_pos_p(cdras(q_a, l)).truthy() {
    let p = div(hypgeo__par(), cdras(q_a, l))
    mul3(
      rest_,
      inv(hypgeo__par()),
      add2(
        mul2(
          hypgeo__take(q_p_expintegral_ci, [p]),
          hypgeo__take(q_p_sin, [p]),
        ),
        mul2(
          sub(
            div(q_d__pctpi, int(2)),
            hypgeo__take(q_p_expintegral_si, [p]),
          ),
          hypgeo__take(q_p_cos, [p]),
        ),
      ),
    )
  } else {
    hypgeo__flag(q_lt_atan_failed)
  }
}

///|
/// rest*%i^(-index) as used for the Bessel I cases: I[v](w)=%i^-v*J[v](%i*w).
fn hypgeo__i_rest(index : Value, u : Value) -> Value raise {
  mul2(power(q_d__pcti, neg(index)), u)
}

///|
fn lt_sf_log(u : Value) -> Value raise {
  let hv = hypgeo__var()
  let mut l : Value = Nil

  // Laplace transform of asin(w)
  l = m2_asin(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt_ltp(q_asin, rest_, arg1, Nil)
  }

  // Laplace transform of atan(w)
  l = m2_atan(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt_atan(rest_, arg1)
  }

  // Laplace transform of atanh(w) = (log(1+w) - log(1-w))/2
  l = m2_atanh(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return sendexec(
      rest_,
      mul2(
        hypgeo__r(1, 2),
        sub(
          hypgeo__take(q_p_log, [add2(int(1), arg1)]),
          hypgeo__take(q_p_log, [sub(int(1), arg1)]),
        ),
      ),
    )
  }

  // Laplace transform of two Bessel J functions
  l = m2_twoj(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return lt2j(rest_, arg1, arg2, index1, index2)
  }

  // Laplace transform of two hankel_1 functions
  l = m2_two_hankel_1(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    // Call the code for the symbol %h.
    return fractest(
      rest_,
      arg1,
      arg2,
      index1,
      int(1),
      index2,
      int(1),
      q_n2htjory,
    )
  }

  // Laplace transform of two hankel_2 functions
  l = m2_two_hankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest(
      rest_,
      arg1,
      arg2,
      index1,
      int(2),
      index2,
      int(2),
      q_n2htjory,
    )
  }

  // Laplace transform of hankel_1 * hankel_2
  l = m2_hankel_1_starhankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest(
      rest_,
      arg1,
      arg2,
      index1,
      int(1),
      index2,
      int(2),
      q_n2htjory,
    )
  }

  // Laplace transform of two Bessel Y functions
  l = m2_twoy(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest(rest_, arg1, arg2, index1, Nil, index2, Nil, q_n2ytj)
  }

  // Laplace transform of two Bessel K functions
  l = m2_twok(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest(rest_, arg1, arg2, index1, Nil, index2, Nil, q_n2kti)
  }

  // Laplace transform of Bessel K and Bessel Y functions
  l = m2_onekoney(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest(rest_, arg1, arg2, index1, Nil, index2, Nil, q_ktiytj)
  }

  // Laplace transform of Bessel I and Bessel J functions
  l = m2_oneionej(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = cdras(q_w2, l)
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return lt2j(rest_, arg1, arg2, index1, index2)
  }

  // Laplace transform of Bessel I and Hankel 1 functions
  l = m2_bessel_i_starhankel_1(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = cdras(q_w2, l)
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return fractest1(rest_, arg1, arg2, index1, index2, int(1), q_besshtjory)
  }

  // Laplace transform of Bessel I and Hankel 2 functions
  l = m2_bessel_i_starhankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = cdras(q_w2, l)
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return fractest1(rest_, arg1, arg2, index1, index2, int(2), q_besshtjory)
  }

  // Laplace transform of Bessel Y and Bessel J functions
  l = m2_oneyonej(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, Nil, q_bessytj)
  }

  // Laplace transform of Bessel K and Bessel J functions
  l = m2_onekonej(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, Nil, q_besskti)
  }

  // Laplace transform of Hankel 1 and Bessel J functions
  l = m2_hankel_1_starbessel_j(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(1), q_besshtjory)
  }

  // Laplace transform of Hankel 2 and Bessel J functions
  l = m2_hankel_2_starbessel_j(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(2), q_besshtjory)
  }

  // Laplace transform of Bessel Y and Hankel 1 functions
  l = m2_bessel_y_starhankel_1(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(1), q_htjoryytj)
  }

  // Laplace transform of Bessel Y and Hankel 2 functions
  l = m2_bessel_y_starhankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(2), q_htjoryytj)
  }

  // Laplace transform of Bessel K and Hankel 1 functions
  l = m2_bessel_k_starhankel_1(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(1), q_htjorykti)
  }

  // Laplace transform of Bessel K and Hankel 2 functions
  l = m2_bessel_k_starhankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest1(rest_, arg2, arg1, index2, index1, int(2), q_htjorykti)
  }

  // Laplace transform of Bessel I and Bessel Y functions
  l = m2_oneioney(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = cdras(q_w2, l)
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return fractest1(rest_, arg1, arg2, index1, index2, Nil, q_bessytj)
  }

  // Laplace transform of Bessel I and Bessel K functions
  l = m2_oneionek(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = cdras(q_w2, l)
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return fractest1(rest_, arg1, arg2, index1, index2, Nil, q_besskti)
  }

  // Laplace transform of Struve H function
  l = m2_struve_h(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1hstruve(rest_, arg1, index1)
  }

  // Laplace transform of Struve L function
  l = m2_struve_l(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1lstruve(rest_, arg1, index1)
  }

  // Laplace transform of little Lommel s function
  l = m2_ones(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1s(rest_, arg1, index1, index2)
  }

  // Laplace transform of Lommel S function
  l = m2_oneslommel(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, index1, index2, q_slommel)
  }

  // Laplace transform of Bessel Y function
  l = m2_oney(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1yref(rest_, arg1, index1)
  }

  // Laplace transform of Bessel K function
  l = m2_onek(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    if zerop1(index1).truthy() {
      // Special case for a zero index
      return lt_bessel_k0(rest_, arg1)
    } else {
      return fractest2(rest_, arg1, index1, Nil, q_kti)
    }
  }

  // Laplace transform of Parabolic Cylinder function
  l = m2_parabolic_cylinder_d(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, index1, Nil, q_d)
  }

  // Laplace transform of Incomplete Gamma function
  l = m2_onegammaincomplete(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, arg2, Nil, q_gamma_u_incomplete)
  }

  // Laplace transform of Batemann function
  l = m2_onekbateman(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, index1, Nil, q_kbateman)
  }

  // Laplace transform of Bessel J function
  l = m2_onej(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1j(rest_, arg1, index1)
  }

  // Laplace transform of lower incomplete Gamma function
  l = m2_onegamma_incomplete_lower(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w1, l)
    let arg2 = cdras(q_w2, l)
    let rest_ = cdras(q_u, l)
    return lt1gamma_incomplete_lower(rest_, arg1, arg2)
  }

  // Laplace transform of Hankel 1 function
  l = m2_hankel_1(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, index1, int(1), q_htjory)
  }

  // Laplace transform of Hankel 2 function
  l = m2_hankel_2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, index1, int(2), q_htjory)
  }

  // Laplace transform of Whittaker M function
  l = m2_onem(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1m(rest_, arg1, index1, index11)
  }

  // Laplace transform of Whittaker M function
  l = m2_whittaker_m(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1m(rest_, arg1, index1, index2)
  }

  // Laplace transform of the Generalized Laguerre function, %l[v1,v2](w)
  l = m2_onel(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, index11, q_l)
  }

  // Laplace transform for the Generalized Laguerre function
  // We call the routine for %l[v1,v2](w).
  l = m2_one_gen_laguerre(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, index2, q_l)
  }

  // Laplace transform for the Laguerre function
  // We call the routine for %l[v1,0](w).
  l = m2_one_laguerre(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, int(0), q_l)
  }

  // Laplace transform of Gegenbauer function
  l = m2_onec(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, index11, q_c)
  }

  // Laplace transform of Chebyshev function of the first kind
  l = m2_onet(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, Nil, t)
  }

  // Laplace transform of Chebyshev function of the second kind
  l = m2_oneu(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return integertest(rest_, arg1, index1, Nil, q_u)
  }

  // Laplace transform for the Hermite function, hermite(index1,arg1)
  l = m2_one_hermite(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    if maxima_integerp(index1).truthy() &&
      (mevenp(index1).truthy() || moddp(index1).truthy()) {
      // When index1 is an even or odd integer, we transform
      // directly to a hypergeometric function. For this case we
      // get a Laplace transform when the arg is the
      // square root of the variable.
      return sendexec(rest_, hermite_to_hypergeometric(index1, arg1))
    } else {
      return integertest(rest_, arg1, index1, Nil, q_he)
    }
  }

  // Laplace transform of %p[v1,v2](w), Associated Legendre P function
  l = m2_hyp_onep(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1p(rest_, arg1, index1, index11)
  }

  // Laplace transform of Associated Legendre P function
  l = m2_assoc_legendre_p(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1p(rest_, arg1, index1, index2)
  }

  // Laplace transform of %p[v1,v2,v3](w), Jacobi function
  l = m2_onepjac(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let index21 = cdras(q_v3, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return pjactest(rest_, arg1, index1, index2, index21)
  }

  // Laplace transform of Jacobi P function
  l = m2_jacobi_p(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let index21 = cdras(q_v3, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return pjactest(rest_, arg1, index1, index2, index21)
  }

  // Laplace transform of Associated Legendre function of the second kind
  l = m2_oneq(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1q(rest_, arg1, index1, index11)
  }

  // Laplace transform of Associated Legendre function of the second kind
  l = m2_assoc_legendre_q(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1q(rest_, arg1, index1, index2)
  }

  // Laplace transform of %p[v1](w), Legendre P function
  l = m2_onep0(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = int(0)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1p(rest_, arg1, index1, index11)
  }

  // Laplace transform of Legendre P function
  l = m2_legendre_p(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1p(rest_, arg1, index1, int(0))
  }

  // Laplace transform of Whittaker W function
  l = m2_onew(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index11 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return whittest(rest_, arg1, index1, index11)
  }

  // Laplace transform of Whittaker W function
  l = m2_whittaker_w(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return whittest(rest_, arg1, index1, index2)
  }

  // Laplace transform of square of Bessel J function
  l = m2_onej_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1j_hat2(rest_, arg1, index1)
  }

  // Laplace transform of square of Hankel 1 function
  l = m2_hankel_1_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest(
      rest_,
      arg1,
      arg1,
      index1,
      int(1),
      index1,
      int(1),
      q_n2htjory,
    )
  }

  // Laplace transform of square of Hankel 2 function
  l = m2_hankel_2_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest(
      rest_,
      arg1,
      arg1,
      index1,
      int(2),
      index1,
      int(2),
      q_n2htjory,
    )
  }

  // Laplace transform of square of Bessel Y function
  l = m2_oney_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest(rest_, arg1, arg1, index1, Nil, index1, Nil, q_n2ytj)
  }

  // Laplace transform of square of Bessel K function
  l = m2_onek_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest(rest_, arg1, arg1, index1, Nil, index1, Nil, q_n2kti)
  }

  // Laplace transform of two Bessel I functions
  l = m2_twoi(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v1, l)
    let index2 = cdras(q_v2, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w1, l))
    let arg2 = mul2(q_d__pcti, cdras(q_w2, l))
    let rest_ = mul3(
      power(q_d__pcti, neg(index1)),
      power(q_d__pcti, neg(index1)),
      cdras(q_u, l),
    )
    return lt2j(rest_, arg1, arg2, index1, index2)
  }

  // Laplace transform of Bessel I. We use I[v](w)=%i^n*J[n](%i*w).
  l = m2_onei(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w, l))
    let rest_ = hypgeo__i_rest(index1, cdras(q_u, l))
    return lt1j(rest_, arg1, index1)
  }

  // Laplace transform of square of Bessel I function
  l = m2_onei_hat2(u, hv)
  if l.truthy() {
    let index1 = cdras(q_v, l)
    let arg1 = mul2(q_d__pcti, cdras(q_w, l))
    let rest_ = mul3(
      power(q_d__pcti, neg(index1)),
      power(q_d__pcti, neg(index1)),
      cdras(q_u, l),
    )
    return lt1j_hat2(rest_, arg1, index1)
  }

  // Laplace transform of Erf function
  l = m2_onerf(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1erf(rest_, arg1)
  }

  // Laplace transform of the logarithmic function.
  l = m2_onelog(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt_log(rest_, arg1)
  }

  // Laplace transform of Erfc function
  l = m2_onerfc(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return fractest2(rest_, arg1, Nil, Nil, q_erfc)
  }

  // Laplace transform of expintegral_ei.
  // Maxima uses the build in transformation to the gamma_incomplete
  // function and simplifies the log functions of the transformation. We do
  // not use the dispatch mechanism of fractest2, but call sendexec directly
  // with the transformed function.
  l = m2_oneexpintegral_ei(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return with_specials(
      [(q_d_expintrep, q_p_gamma_u_incomplete), (q_d_logexpand, q_d_all)],
      () => sratsimp(sendexec(rest_, ftake(q_p_expintegral_ei, [arg1]))),
    )
  }

  // Laplace transform of expintegral_e1
  l = m2_oneexpintegral_e1(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return with_specials(
      [(q_d_expintrep, q_p_gamma_u_incomplete), (q_d_logexpand, q_d_all)],
      () => sratsimp(sendexec(rest_, ftake(q_p_expintegral_e1, [arg1]))),
    )
  }

  // Laplace transform of expintegral_e
  l = m2_oneexpintegral_e(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_v, l)
    let arg2 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return with_specials(
      [(q_d_expintrep, q_p_gamma_u_incomplete), (q_d_logexpand, q_d_all)],
      () => sratsimp(sendexec(rest_, ftake(q_p_expintegral_e, [arg1, arg2]))),
    )
  }

  // Laplace transform of expintegral_si
  l = m2_oneexpintegral_si(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    // We transform to the hypergeometric representation.
    return sendexec(rest_, expintegral_si_to_hypergeometric(arg1))
  }

  // Laplace transform of expintegral_shi
  l = m2_oneexpintegral_shi(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    // We transform to the hypergeometric representation.
    return sendexec(rest_, expintegral_shi_to_hypergeometric(arg1))
  }

  // Laplace transform of expintegral_ci
  l = m2_oneexpintegral_ci(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    // We transform to the hypergeometric representation.
    // Because we have Logarithmic terms in the transformation,
    // we switch on the flag $logexpand and do a ratsimp.
    return with_special(q_d_logexpand, q_d_super, () => sratsimp(
      sendexec(rest_, expintegral_ci_to_hypergeometric(arg1)),
    ))
  }

  // Laplace transform of expintegral_chi
  l = m2_oneexpintegral_chi(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return with_special(q_d_logexpand, q_d_super, () => sratsimp(
      sendexec(rest_, expintegral_chi_to_hypergeometric(arg1)),
    ))
  }

  // Laplace transform of Complete elliptic integral of the first kind
  l = m2_onekelliptic(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1kelliptic(rest_, arg1)
  }

  // Laplace transform of Complete elliptic integral of the first kind
  l = m2_elliptic_kc(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1kelliptic(rest_, arg1)
  }

  // Laplace transform of Complete elliptic integral of the second kind
  l = m2_onee(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1e(rest_, arg1)
  }

  // Laplace transform of Complete elliptic integral of the second kind
  l = m2_elliptic_ec(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_w, l)
    let rest_ = cdras(q_u, l)
    return lt1e(rest_, arg1)
  }

  // Laplace transform of %f[v1,v2](w1,w2,w3), Hypergeometric function
  // We support the Laplace transform of the build in symbol %f. We do
  // not use the mechanism of defining an "Expert on Laplace transform",
  // the expert function does a call to lt-ltp. We do this call directly.
  l = m2_onef(u, hv)
  if l.truthy() {
    let rest_ = cdras(q_u, l)
    let arg1 = cdras(q_w3, l)
    let index1 = list2(cdras(q_w1, l), cdras(q_w2, l))
    return lt_ltp(q_f, rest_, arg1, index1)
  }

  // Laplace transform of Hypergeometric function
  l = m2_hypergeometric(u, hv)
  if l.truthy() {
    let rest_ = cdras(q_u, l)
    let arg1 = cdras(q_w3, l)
    let index1 = list2(cdras(q_w1, l), cdras(q_w2, l))
    return lt_ltp(q_f, rest_, arg1, index1)
  }

  // Laplace transform of c * t^v * (a+t)^w
  // It is possible to combine arbpow2 and arbpow.
  l = m2_arbpow2(u, hv)
  if l.truthy() {
    let rest_ = cdras(q_c, l)
    let arg1 = cdras(q_a, l)
    let arg2 = cdras(q_b, l)
    let index1 = cdras(q_v, l)
    let index2 = cdras(q_w, l)
    return lt_arbpow2(rest_, arg1, arg2, index1, index2)
  }

  // Laplace transform of c * t^v
  l = m2_arbpow1(u, hv)
  if l.truthy() {
    let arg1 = cdras(q_u, l)
    let arg2 = cdras(q_c, l)
    let index1 = cdras(q_v, l)
    return mul2(arg2, lt_arbpow(arg1, index1))
  }

  // We have specialized the pattern for arbpow1. Now a lot of integrals
  // will fail correctly and we have to return a noun form.
  hypgeo__flag(q_other_j_cases_next)
}
