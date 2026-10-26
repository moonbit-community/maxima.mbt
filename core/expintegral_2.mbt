// Port of src/expintegral.lisp, part 2: the Exponential Integrals E1, Ei,
// Li, Si, Shi, Ci, Chi, the deprecated $expint, and the top-level forms.

///|
fn expintegral__log(x : Value) -> Value raise {
  take(list1(q_p_log), [x])
}

///|
fn expintegral__f(op : Value, x : Value) -> Value raise {
  take(list1(op), [x])
}

///|
fn expintegral__gi0(x : Value) -> Value raise {
  take(list1(q_p_gamma_u_incomplete), [Fix(0L), x])
}

///|
/// `(member $expintrep *expintflag*)` and not `(eq $expintrep self)`.
fn expintegral__rep_other(self_ : Value) -> Bool {
  let rep = symval(q_d_expintrep)
  rep.truthy() &&
  memq(rep, symval(q_ear_expintflag)).truthy() &&
  !eq(rep, self_)
}

///|
fn expintegral__neg1(x : Value) -> Value raise {
  mul2(Fix(-1L), x)
}

///|
fn expintegral__wna(form : Value, noun : Value) -> Unit raise {
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(noun), expintegral__q_d_arg),
    )
    |> ignore
  }
}

// ---------------------------------------------------------------------------
// Part 2: The implementation of the Exponential Integral E1

///|
/// Exponential Integral E1 has mirror symmetry, but not on the real
/// negative axis.
fn conjugate_expintegral_e1(args : Value) -> Value raise {
  let z = first(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    take(list1(q_p_expintegral_e1), [take(list1(q_d_conjugate), [z])])
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_expintegral_e1), [z]))
  }
}

///|
fn simplim_pctexpintegral_e1(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    // limit is inf from both sides
    q_d_inf
  } else {
    // All other cases are handled by the simplifier of the function.
    let value = take(list1(q_p_expintegral_e1), [z])
    if !on_negative_real_axisp(z).truthy() {
      value
    } else {
      let r = expintegral_cut_limit(value, cadr(expr), var_, val, Nil)
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, Nil)
      }
    }
  }
}

///|
/// Exponential Integral E1 is a simplifying function
/// (def-simplifier expintegral_e1 (arg)).
fn simp__pctexpintegral_e1(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_e1)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_e1), list1(arg)), form)
  // Check for special values
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    return Fix(0L)
  }
  if zerop1(arg).truthy() {
    return simp_domain_error(
      list([Str("expintegral_e1: expintegral_e1(~:M) is undefined."), arg]),
    )
  }
  // Check for numerical evaluation
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    // For E1 we call En(z) with n=1 directly.
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_e(Fix(1L), carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    // For E1 we call En(z) with n=1 directly.
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_e(Fix(1L), carg)
      expintegral__rect(result)
    })
  }
  // Check argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_p_expintegral_e1) {
    let rep = symval(q_d_expintrep)
    return if eq(rep, q_p_gamma_u_incomplete) {
      expintegral__gi0(arg)
    } else if eq(rep, q_p_expintegral_ei) {
      addn_([
        expintegral__neg1(
          expintegral__f(q_p_expintegral_ei, expintegral__neg1(arg)),
        ),
        mul2(
          inv(Fix(2L)),
          sub(
            expintegral__log(expintegral__neg1(arg)),
            expintegral__log(expintegral__neg1(inv(arg))),
          ),
        ),
        expintegral__neg1(expintegral__log(arg)),
      ])
    } else if eq(rep, q_p_expintegral_li) {
      addn_([
        expintegral__neg1(
          expintegral__f(
            q_p_expintegral_li,
            power(q_d__pcte, expintegral__neg1(arg)),
          ),
        ),
        expintegral__neg1(expintegral__log(arg)),
        mul2(
          inv(Fix(2L)),
          sub(
            expintegral__log(expintegral__neg1(arg)),
            expintegral__log(expintegral__neg1(inv(arg))),
          ),
        ),
      ])
    } else if eq(rep, q_d_expintegral_trig) {
      addn_([
        muln_([
          Fix(-1L),
          q_d__pcti,
          expintegral__f(q_p_expintegral_si, mul2(q_d__pcti, arg)),
        ]),
        expintegral__neg1(
          expintegral__f(q_p_expintegral_ci, mul2(q_d__pcti, arg)),
        ),
        expintegral__log(mul2(q_d__pcti, arg)),
        expintegral__neg1(expintegral__log(arg)),
      ])
    } else if eq(rep, q_d_expintegral_hyp) {
      sub(
        expintegral__f(q_p_expintegral_shi, arg),
        expintegral__f(q_p_expintegral_chi, arg),
      )
    } else {
      give_up()
    }
  }
  give_up()
}

// ---------------------------------------------------------------------------
// Part 3: The implementation of the Exponential Integral Ei

///|
fn simplim_pctexpintegral_ei(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the arguments.
  let z = limit(cadr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    q_d_minf
  } else {
    // All other cases are handled by the simplifier of the function.
    let value = take(list1(q_p_expintegral_ei), [z])
    if !on_negative_real_axisp(z).truthy() {
      value
    } else {
      let r = expintegral_cut_limit(value, cadr(expr), var_, val, t)
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, Nil)
      }
    }
  }
}

///|
/// Exponential Integral Ei is a simplifying function
/// (def-simplifier expintegral_ei (arg)).
fn simp__pctexpintegral_ei(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_ei)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_ei), list1(arg)), form)
  // Check special values
  if zerop1(arg).truthy() {
    return simp_domain_error(
      list([Str("expintegral_ei: expintegral_ei(~:M) is undefined."), arg]),
    )
  }
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    return q_d_inf
  }
  if eq(arg, q_d_minf) || expintegral__alike(arg, [Fix(-1L), q_d_inf]) {
    return Fix(0L)
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_inf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_minf]) {
    return mul2(q_d__pcti, q_d__pctpi)
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_minf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_inf]) {
    return muln_([Fix(-1L), q_d__pcti, q_d__pctpi])
  }
  // Check numerical evaluation
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_ei(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_ei(carg)
      expintegral__rect(result)
    })
  }
  // Check argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_p_expintegral_ei) {
    let rep = symval(q_d_expintrep)
    return if eq(rep, q_p_gamma_u_incomplete) {
      addn_([
        expintegral__neg1(expintegral__gi0(expintegral__neg1(arg))),
        mul2(
          inv(Fix(2L)),
          sub(expintegral__log(arg), expintegral__log(inv(arg))),
        ),
        expintegral__neg1(expintegral__log(expintegral__neg1(arg))),
      ])
    } else if eq(rep, q_p_expintegral_e1) {
      addn_([
        expintegral__neg1(
          expintegral__f(q_p_expintegral_e1, expintegral__neg1(arg)),
        ),
        mul2(
          inv(Fix(2L)),
          sub(expintegral__log(arg), expintegral__log(inv(arg))),
        ),
        expintegral__neg1(expintegral__log(expintegral__neg1(arg))),
      ])
    } else if eq(rep, q_p_expintegral_li) {
      expintegral__f(q_p_expintegral_li, power(q_d__pcte, arg))
    } else if eq(rep, q_d_expintegral_trig) {
      addn_([
        expintegral__f(q_p_expintegral_ci, mul2(q_d__pcti, arg)),
        muln_([
          Fix(-1L),
          q_d__pcti,
          expintegral__f(q_p_expintegral_si, mul2(q_d__pcti, arg)),
        ]),
        mul2(
          inv(Fix(-2L)),
          sub(expintegral__log(inv(arg)), expintegral__log(arg)),
        ),
        expintegral__neg1(expintegral__log(mul2(q_d__pcti, arg))),
      ])
    } else if eq(rep, q_d_expintegral_hyp) {
      addn_([
        expintegral__f(q_p_expintegral_chi, arg),
        expintegral__f(q_p_expintegral_shi, arg),
        mul2(
          inv(Fix(-2L)),
          add2(expintegral__log(inv(arg)), expintegral__log(arg)),
        ),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.35.26.0001.01
    //
    // expintegral_ei(z) = z*hypergeometric([1,1],[2,2],z)
    //   + 1/2*(log(z) - log(1/z)) + %gamma
    //
    // But note that Maxima expands log(1/z) to -log(z), but this is not
    // true when z is on the negative real axis.
    return addn_([
      mul2(
        arg,
        ftake(q_p_hypergeometric, [
          make_mlist(list2(Fix(1L), Fix(1L))),
          make_mlist(list2(Fix(2L), Fix(2L))),
          arg,
        ]),
      ),
      mul2(
        symval(q_n1_sl_sl2),
        sub(ftake(q_p_log, [arg]), ftake(q_p_log, [div(Fix(1L), arg)])),
      ),
      q_d__pctgamma,
    ])
  }
  give_up()
}

///|
/// Numerical evaluation of the Exponential Integral Ei(z):
///
///   Ei(z) = -E1(-z) + 0.5*(log(z)-log(1/z))-log(-z)
///
/// z is a CL Complex number.
fn expintegral_ei(z : Value) -> Value raise {
  num_add(
    num_neg(expintegral_e(Fix(1L), num_neg(z))),
    // Carefully compute 1/2*(log(z)-log(1/z))-log(-z), using the branch
    // cuts that we want, not the one that Lisp wants.
    if num_gt(imagpart(z), Fix(0L)) {
      // Positive imaginary part. Add phase %i*%pi.
      complex(Fix(0L), i=Flo(@math.PI))
    } else if num_lt(imagpart(z), Fix(0L)) {
      // Negative imaginary part. Add phase -%i*%pi.
      complex(Fix(0L), i=num_neg(Flo(@math.PI)))
    } else if num_gt(realpart(z), Fix(0L)) {
      // Positive real value. Add phase -%i*pi.
      complex(Fix(0L), i=num_neg(Flo(@math.PI)))
    } else {
      // Negative real value. No phase factor.
      Fix(0L)
    },
  )
}

///|
fn bfloat_expintegral_ei(z : Value) -> Value raise {
  let one = symval(q_ear_bigfloatone)
  let mz = mul2(Fix(-1L), z)
  add2(
    cmul(mul2(Fix(-1L), one), bfloat_expintegral_e(Fix(1L), mz)),
    sub(
      cmul(
        div(one, Fix(2L)),
        sub(
          take(list1(q_p_log), [z]),
          take(list1(q_p_log), [cdiv(one, z)]),
        ),
      ),
      take(list1(q_p_log), [mz]),
    ),
  )
}

// ---------------------------------------------------------------------------
// Part 4: The implementation of the Logarithmic integral li(z)

///|
fn conjugate_expintegral_li(args : Value) -> Value raise {
  let z = first(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    take(list1(q_p_expintegral_li), [take(list1(q_d_conjugate), [z])])
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_expintegral_li), [z]))
  }
}

///|
fn simplim_pctexpintegral_li(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if onep1(z).truthy() {
    // Handle an argument 1 at this place
    return q_d_minf
  }
  // All other cases are handled by the simplifier of the function.
  let value = take(list1(q_p_expintegral_li), [z])
  // Below zero the value on the cut is the one from above it, between
  // zero and one it is the principal value.
  if on_negative_real_axisp(z).truthy() {
    let r = expintegral_cut_limit(value, cadr(expr), var_, val, Nil)
    if r.truthy() {
      r
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if on_negative_real_axisp(sub(z, Fix(1L))).truthy() &&
    eql(t, mgrp(z, Fix(0L))) {
    let r = expintegral_cut_limit(value, cadr(expr), var_, val, t)
    if r.truthy() {
      r
    } else {
      throw_tag(q_limit, Nil)
    }
  } else {
    value
  }
}

///|
/// Exponential Integral Li is a simplifying function
/// (def-simplifier expintegral_li (arg)).
fn simp__pctexpintegral_li(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_li)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_li), list1(arg)), form)
  if zerop1(arg).truthy() {
    return arg
  }
  if onep1(arg).truthy() {
    return simp_domain_error(
      list([Str("expintegral_li: expintegral_li(~:M) is undefined."), arg]),
    )
  }
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    return q_d_inf
  }
  if eq(arg, q_d_infinity) {
    return q_d_infinity
  }
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_li(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_li(carg)
      expintegral__rect2(result)
    })
  }
  // Check for argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_p_expintegral_li) {
    let logarg = take(list1(q_p_log), [arg])
    let rep = symval(q_d_expintrep)
    return if eq(rep, q_p_gamma_u_incomplete) {
      addn_([
        expintegral__neg1(expintegral__gi0(expintegral__neg1(logarg))),
        mul2(
          inv(Fix(2L)),
          sub(expintegral__log(logarg), expintegral__log(inv(logarg))),
        ),
        expintegral__neg1(expintegral__log(expintegral__neg1(logarg))),
      ])
    } else if eq(rep, q_p_expintegral_e1) {
      addn_([
        expintegral__neg1(
          expintegral__f(q_p_expintegral_e1, expintegral__neg1(logarg)),
        ),
        mul2(
          inv(Fix(2L)),
          sub(expintegral__log(logarg), expintegral__log(inv(logarg))),
        ),
        expintegral__neg1(expintegral__log(expintegral__neg1(logarg))),
      ])
    } else if eq(rep, q_p_expintegral_ei) {
      expintegral__f(q_p_expintegral_ei, logarg)
    } else if eq(rep, q_d_expintegral_trig) {
      addn_([
        expintegral__f(q_p_expintegral_ci, mul2(q_d__pcti, logarg)),
        muln_([
          Fix(-1L),
          q_d__pcti,
          expintegral__f(q_p_expintegral_si, mul2(q_d__pcti, logarg)),
        ]),
        mul2(
          inv(Fix(-2L)),
          sub(expintegral__log(inv(logarg)), expintegral__log(logarg)),
        ),
        expintegral__neg1(expintegral__log(mul2(q_d__pcti, logarg))),
      ])
    } else if eq(rep, q_d_expintegral_hyp) {
      addn_([
        expintegral__f(q_p_expintegral_chi, logarg),
        expintegral__f(q_p_expintegral_shi, logarg),
        mul2(
          inv(Fix(-2L)),
          add2(expintegral__log(inv(logarg)), expintegral__log(logarg)),
        ),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See  http://functions.wolfram.com/06.36.26.0001.01
    //
    // expintegral_li(z) = log(z)*hypergeometric([1,1],[2,2],log(z))
    //   + 1/2*(log(log(z)) - log(1/log(z))) + %gamma
    return addn_([
      mul2(
        ftake(q_p_log, [arg]),
        ftake(q_p_hypergeometric, [
          make_mlist(list2(Fix(1L), Fix(1L))),
          make_mlist(list2(Fix(2L), Fix(2L))),
          ftake(q_p_log, [arg]),
        ]),
      ),
      mul2(
        symval(q_n1_sl_sl2),
        sub(
          ftake(q_p_log, [ftake(q_p_log, [arg])]),
          ftake(q_p_log, [div(Fix(1L), ftake(q_p_log, [arg]))]),
        ),
      ),
      q_d__pctgamma,
    ])
  }
  give_up()
}

///|
/// Numerical evaluation of the Expintegral Li: Li(z) = Ei(log(z))
fn expintegral_li(z : Value) -> Value raise {
  expintegral_ei(llog(z))
}

///|
fn bfloat_expintegral_li(z : Value) -> Value raise {
  bfloat_expintegral_ei(ftake(q_p_log, [z]))
}

// ---------------------------------------------------------------------------
// Part 5: The implementation of the Exponential Integral Si

///|
fn simplim_pctexpintegral_si(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if eq(lim, q_d_infinity) {
    throw_tag(q_limit, t)
  } else if eq(lim, q_d_ind) {
    q_d_ind
  } else if eq(lim, q_d_zerob) {
    q_d_zerob
  } else if eq(lim, q_d_zeroa) {
    q_d_zeroa
  } else if eq(lim, q_d_und) {
    throw_tag(q_limit, Nil)
  } else {
    // The expintegral_si simplifier handles expintegral_si(minf & inf)
    ftake(q_p_expintegral_si, [lim])
  }
}

///|
/// Exponential Integral Si is a simplifying function
/// (def-simplifier expintegral_si (arg)).
fn simp__pctexpintegral_si(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_si)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_si), list1(arg)), form)
  // Check for special values
  if zerop1(arg).truthy() {
    return arg
  }
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    return div(q_d__pctpi, Fix(2L))
  }
  if eq(arg, q_d_minf) || expintegral__alike(arg, [Fix(-1L), q_d_inf]) {
    return mul2(Fix(-1L), div(q_d__pctpi, Fix(2L)))
  }
  // Check for numerical evaluation
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_si(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_si(carg)
      expintegral__rect2(result)
    })
  }
  // Check for argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  let r = apply_reflection_simp(mop(form), arg, b=symval(q_d_trigsign))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_d_expintegral_trig) {
    let rep = symval(q_d_expintrep)
    let iarg = mul2(q_d__pcti, arg)
    return if eq(rep, q_p_gamma_u_incomplete) {
      mul2(
        div(q_d__pcti, Fix(2L)),
        addn_([
          expintegral__gi0(muln_([Fix(-1L), q_d__pcti, arg])),
          expintegral__neg1(expintegral__gi0(iarg)),
          expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
          expintegral__neg1(expintegral__log(iarg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_e1) {
      mul2(
        div(q_d__pcti, Fix(2L)),
        addn_([
          expintegral__f(
            q_p_expintegral_e1,
            muln_([Fix(-1L), q_d__pcti, arg]),
          ),
          expintegral__neg1(expintegral__f(q_p_expintegral_e1, iarg)),
          expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
          expintegral__neg1(expintegral__log(iarg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_ei) {
      mul2(
        div(q_d__pcti, Fix(4L)),
        addn_([
          mul2(
            Fix(2L),
            sub(
              expintegral__f(
                q_p_expintegral_ei,
                muln_([Fix(-1L), q_d__pcti, arg]),
              ),
              expintegral__f(q_p_expintegral_ei, iarg),
            ),
          ),
          expintegral__log(div(q_d__pcti, arg)),
          expintegral__neg1(
            expintegral__log(expintegral__neg1(div(q_d__pcti, arg))),
          ),
          expintegral__neg1(
            expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
          ),
          expintegral__log(iarg),
        ]),
      )
    } else if eq(rep, q_p_expintegral_li) {
      mul2(
        inv(mul2(Fix(2L), q_d__pcti)),
        addn_([
          expintegral__f(q_p_expintegral_li, power(q_d__pcte, iarg)),
          expintegral__neg1(
            expintegral__f(
              q_p_expintegral_li,
              power(q_d__pcte, muln_([Fix(-1L), q_d__pcte, arg])),
            ),
          ),
          mul2(
            div(q_d__pctpi, Fix(-2L)),
            take(list1(q_p_signum), [d_realpart(arg)]),
          ),
        ]),
      )
    } else if eq(rep, q_d_expintegral_hyp) {
      muln_([
        Fix(-1L),
        q_d__pcti,
        expintegral__f(q_p_expintegral_shi, iarg),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See  http://functions.wolfram.com/06.37.26.0001.01
    //
    // expintegral_si(z) = z*hypergeometric([1/2],[3/2,3/2],-z^2/4)
    return mul2(
      arg,
      ftake(q_p_hypergeometric, [
        make_mlist(list1(symval(q_n1_sl_sl2))),
        make_mlist(list2(symval(q_n3_sl_sl2), symval(q_n3_sl_sl2))),
        div(mul2(arg, arg), Fix(-4L)),
      ]),
    )
  }
  give_up()
}

///|
/// `(coerce z '(complex flonum))`
fn expintegral__coerce_cflonum(z : Value) -> Value raise {
  match z {
    Cplx(_, _) => lfloat(z)
    _ => Cplx(Flo(to_double(z)), Flo(0.0))
  }
}

///|
/// Numerical evaluation of the Exponential Integral Si:
///
///   Si(z) = %i/2 * (E1(-%i*z) - E1(*%i*z) + log(%i*z) - log(-%i*z))
fn expintegral_si(z : Value) -> Value raise {
  let z = expintegral__coerce_cflonum(z)
  let miz = real_if_real(num_mul(complex(Flo(0.0), i=Flo(-1.0)), z))
  let piz = real_if_real(num_mul(complex(Flo(0.0), i=Flo(1.0)), z))
  num_mul(
    complex(Fix(0L), i=Flo(0.5)),
    num_add(
      num_add(
        num_add(
          expintegral_e(Fix(1L), miz),
          num_neg(expintegral_e(Fix(1L), piz)),
        ),
        llog(miz),
      ),
      num_neg(llog(piz)),
    ),
  )
}

///|
fn bfloat_expintegral_si(z : Value) -> Value raise {
  let z_star_pcti = cmul(q_d__pcti, z)
  let mz_star_pcti = cmul(mul2(Fix(-1L), q_d__pcti), z)
  cmul(
    mul2(Flo(0.5), q_d__pcti),
    addn_([
      bfloat_expintegral_e(Fix(1L), mz_star_pcti),
      mul2(Fix(-1L), bfloat_expintegral_e(Fix(1L), z_star_pcti)),
      ftake(q_p_log, [mz_star_pcti]),
      mul2(Fix(-1L), ftake(q_p_log, [z_star_pcti])),
    ]),
  )
}

// ---------------------------------------------------------------------------
// Part 6: The implementation of the Exponential Integral Shi

///|
fn simplim_pctexpintegral_shi(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    q_d_inf
  } else if eq(z, q_d_minf) {
    q_d_minf
  } else {
    // All other cases are handled by the simplifier of the function.
    take(list1(q_p_expintegral_shi), [z])
  }
}

///|
/// Exponential Integral Shi is a simplifying function
/// (def-simplifier expintegral_shi (arg)).
fn simp__pctexpintegral_shi(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_shi)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_shi), list1(arg)), form)
  // Check for special values
  if zerop1(arg).truthy() {
    return arg
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_inf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_minf]) {
    return div(mul2(q_d__pcti, q_d__pctpi), Fix(2L))
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_minf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_inf]) {
    return div(muln_([Fix(-1L), q_d__pcti, q_d__pctpi]), Fix(2L))
  }
  // Check for numrical evaluation
  if float_numerical_eval_p(list1(arg)).truthy() {
    return realpart(expintegral_shi(arg))
  }
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_shi(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_shi(carg)
      expintegral__rect2(result)
    })
  }
  // Check for argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  let r = apply_reflection_simp(mop(form), arg, b=symval(q_d_trigsign))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_d_expintegral_hyp) {
    let rep = symval(q_d_expintrep)
    return if eq(rep, q_p_gamma_u_incomplete) {
      mul2(
        inv(Fix(2L)),
        addn_([
          expintegral__gi0(arg),
          expintegral__neg1(expintegral__gi0(expintegral__neg1(arg))),
          expintegral__neg1(expintegral__log(expintegral__neg1(arg))),
          expintegral__log(arg),
        ]),
      )
    } else if eq(rep, q_p_expintegral_e1) {
      mul2(
        inv(Fix(2L)),
        addn_([
          expintegral__f(q_p_expintegral_e1, arg),
          expintegral__neg1(
            expintegral__f(q_p_expintegral_e1, expintegral__neg1(arg)),
          ),
          expintegral__neg1(expintegral__log(expintegral__neg1(arg))),
          expintegral__log(arg),
        ]),
      )
    } else if eq(rep, q_p_expintegral_ei) {
      mul2(
        inv(Fix(4L)),
        addn_([
          mul2(
            Fix(2L),
            sub(
              expintegral__f(q_p_expintegral_ei, arg),
              expintegral__f(q_p_expintegral_ei, expintegral__neg1(arg)),
            ),
          ),
          expintegral__log(inv(arg)),
          expintegral__neg1(expintegral__log(expintegral__neg1(inv(arg)))),
          expintegral__log(expintegral__neg1(arg)),
          expintegral__neg1(expintegral__log(arg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_li) {
      add2(
        mul2(
          inv(Fix(2L)),
          sub(
            expintegral__f(q_p_expintegral_li, power(q_d__pcte, arg)),
            expintegral__f(
              q_p_expintegral_li,
              power(q_d__pcte, expintegral__neg1(arg)),
            ),
          ),
        ),
        mul2(
          div(mul2(q_d__pcti, q_d__pctpi), Fix(-2L)),
          take(list1(q_p_signum), [d_imagpart(arg)]),
        ),
      )
    } else if eq(rep, q_d_expintegral_trig) {
      muln_([
        Fix(-1L),
        q_d__pcti,
        expintegral__f(q_p_expintegral_si, mul2(q_d__pcti, arg)),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.39.26.0001.01
    //
    // expintegral_shi(z) = z*hypergeometric([1/2],[3/2,3/2],z^2/4)
    return mul2(
      arg,
      ftake(q_p_hypergeometric, [
        make_mlist(list1(symval(q_n1_sl_sl2))),
        make_mlist(list2(symval(q_n3_sl_sl2), symval(q_n3_sl_sl2))),
        div(mul2(arg, arg), Fix(4L)),
      ]),
    )
  }
  give_up()
}

///|
/// Numerical evaluation of the Exponential Integral Shi:
///
///   Shi(z) = 1/2 * (E1(z) - E1(-z) - log(-z) + log(z))
fn expintegral_shi(z : Value) -> Value raise {
  num_mul(
    Flo(0.5),
    num_add(
      num_add(
        num_add(
          expintegral_e(Fix(1L), z),
          num_neg(expintegral_e(Fix(1L), num_neg(z))),
        ),
        num_neg(llog(num_neg(z))),
      ),
      llog(z),
    ),
  )
}

///|
fn bfloat_expintegral_shi(z : Value) -> Value raise {
  let mz = mul2(Fix(-1L), z)
  mul2(
    Flo(0.5),
    addn_([
      bfloat_expintegral_e(Fix(1L), z),
      mul2(Fix(-1L), bfloat_expintegral_e(Fix(1L), mz)),
      mul2(Fix(-1L), ftake(q_p_log, [mz])),
      ftake(q_p_log, [z]),
    ]),
  )
}

// ---------------------------------------------------------------------------
// Part 7: The implementation of the Exponential Integral Ci

///|
fn conjugate_expintegral_ci(args : Value) -> Value raise {
  let z = first(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    take(list1(q_p_expintegral_ci), [take(list1(q_d_conjugate), [z])])
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_expintegral_ci), [z]))
  }
}

///|
fn simplim_pctexpintegral_ci(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if eq(lim, q_d_infinity) {
    // Is the limit +/- %i x inf?
    let lim = limit(div(cadr(e), q_d__pcti), x, pt, q_think)
    if eq(lim, q_d_inf) {
      q_d_inf
    } else if eq(lim, q_d_minf) {
      q_d_inf
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if eq(lim, q_d_ind) {
    if eq(t, mgrp(cadr(e), Fix(0L))) {
      q_d_ind
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if eq(lim, q_d_zerob) {
    q_d_minf
  } else if eq(lim, q_d_zeroa) {
    q_d_minf
  } else if eql(lim, Fix(0L)) {
    q_d_minf
  } else if eq(lim, q_d_und) {
    throw_tag(q_limit, Nil)
  } else {
    // The general simplifier for expintegral_ci handles inputs minf & inf
    let value = ftake(q_p_expintegral_ci, [lim])
    if !on_negative_real_axisp(lim).truthy() {
      value
    } else {
      let r = expintegral_cut_limit(value, cadr(e), x, pt, Nil)
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, Nil)
      }
    }
  }
}

///|
/// Exponential Integral Ci is a simplifying function
/// (def-simplifier expintegral_ci (arg)).
fn simp__pctexpintegral_ci(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_ci)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_ci), list1(arg)), form)
  // Check for special values
  if zerop1(arg).truthy() {
    return simp_domain_error(
      list([Str("expintegral_ci: expintegral_ci(~:M) is undefined."), arg]),
    )
  }
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    return Fix(0L)
  }
  if eq(arg, q_d_minf) || expintegral__alike(arg, [Fix(-1L), q_d_inf]) {
    return mul2(q_d__pcti, q_d__pctpi)
  }
  // Check for numerical evaluation
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_ci(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_ci(carg)
      expintegral__rect2(result)
    })
  }
  // Check for argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_d_expintegral_trig) {
    let rep = symval(q_d_expintrep)
    let iarg = mul2(q_d__pcti, arg)
    return if eq(rep, q_p_gamma_u_incomplete) {
      sub(
        expintegral__log(arg),
        mul2(
          inv(Fix(2L)),
          addn_([
            expintegral__gi0(muln_([Fix(-1L), q_d__pcti, arg])),
            expintegral__gi0(iarg),
            expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
            expintegral__log(iarg),
          ]),
        ),
      )
    } else if eq(rep, q_p_expintegral_e1) {
      add2(
        muln_([
          inv(Fix(-2L)),
          add2(
            expintegral__f(
              q_p_expintegral_e1,
              muln_([Fix(-1L), q_d__pcti, arg]),
            ),
            expintegral__f(q_p_expintegral_e1, iarg),
          ),
          expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
          expintegral__log(iarg),
        ]),
        expintegral__log(arg),
      )
    } else if eq(rep, q_p_expintegral_ei) {
      add2(
        mul2(
          inv(Fix(4L)),
          addn_([
            mul2(
              Fix(2L),
              add2(
                expintegral__f(
                  q_p_expintegral_ei,
                  muln_([Fix(-1L), q_d__pcti, arg]),
                ),
                expintegral__f(q_p_expintegral_ei, iarg),
              ),
            ),
            expintegral__log(div(q_d__pcti, arg)),
            expintegral__log(muln_([Fix(-1L), q_d__pcti, inv(arg)])),
            expintegral__neg1(
              expintegral__log(muln_([Fix(-1L), q_d__pcti, arg])),
            ),
            expintegral__neg1(expintegral__log(iarg)),
          ]),
        ),
        expintegral__log(arg),
      )
    } else if eq(rep, q_p_expintegral_li) {
      addn_([
        mul2(
          inv(Fix(2L)),
          add2(
            expintegral__f(
              q_p_expintegral_li,
              power(q_d__pcte, muln_([Fix(-1L), q_d__pcti, arg])),
            ),
            expintegral__f(q_p_expintegral_li, power(q_d__pcte, iarg)),
          ),
        ),
        mul2(
          div(mul2(q_d__pcti, q_d__pctpi), Fix(2L)),
          take(list1(q_p_signum), [d_imagpart(arg)]),
        ),
        sub(Fix(1L), take(list1(q_p_signum), [d_realpart(arg)])),
      ])
    } else if eq(rep, q_d_expintegral_hyp) {
      addn_([
        expintegral__f(q_p_expintegral_chi, iarg),
        expintegral__neg1(expintegral__log(iarg)),
        expintegral__log(arg),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.38.26.0001.01
    //
    // expintegral_ci(z) = -z^2/4*hypergeometric([1,1],[2,2,3/2],-z^2/4)
    //   + log(z) + %gamma
    return addn_([
      mul2(
        div(mul2(arg, arg), Fix(-4L)),
        ftake(q_p_hypergeometric, [
          make_mlist(list2(Fix(1L), Fix(1L))),
          make_mlist(list3(Fix(2L), Fix(2L), symval(q_n3_sl_sl2))),
          div(mul2(arg, arg), Fix(-4L)),
        ]),
      ),
      ftake(q_p_log, [arg]),
      q_d__pctgamma,
    ])
  }
  give_up()
}

///|
/// Numerical evaluation of the Exponential Integral Ci:
///
///   Ci(z) = -1/2 * (E1(-%i*z) + E1(%i*z) + log(-%i*z) + log(%i*z)) + log(z)
fn expintegral_ci(z : Value) -> Value raise {
  let z = expintegral__coerce_cflonum(z)
  let miz = real_if_real(num_mul(complex(Fix(0L), i=Fix(-1L)), z))
  let piz = real_if_real(num_mul(complex(Fix(0L), i=Fix(1L)), z))
  num_add(
    num_mul(
      Flo(-0.5),
      num_add(
        num_add(
          num_add(expintegral_e(Fix(1L), miz), expintegral_e(Fix(1L), piz)),
          llog(miz),
        ),
        llog(piz),
      ),
    ),
    llog(z),
  )
}

///|
fn bfloat_expintegral_ci(z : Value) -> Value raise {
  let z_star_pcti = cmul(q_d__pcti, z)
  let mz_star_pcti = cmul(mul2(Fix(-1L), q_d__pcti), z)
  add2(
    cmul(
      Flo(-0.5),
      addn_([
        bfloat_expintegral_e(Fix(1L), mz_star_pcti),
        bfloat_expintegral_e(Fix(1L), z_star_pcti),
        ftake(q_p_log, [mz_star_pcti]),
        ftake(q_p_log, [z_star_pcti]),
      ]),
    ),
    ftake(q_p_log, [z]),
  )
}

// ---------------------------------------------------------------------------
// Part 8: The implementation of the Exponential Integral Chi

///|
fn conjugate_expintegral_chi(args : Value) -> Value raise {
  let z = first(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    take(list1(q_p_expintegral_chi), [take(list1(q_d_conjugate), [z])])
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_expintegral_chi), [z]))
  }
}

///|
fn simplim_pctexpintegral_chi(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    q_d_minf
  } else if eq(z, q_d_inf) || eq(z, q_d_minf) {
    q_d_inf
  } else {
    // All other cases are handled by the simplifier of the function.
    let value = take(list1(q_p_expintegral_chi), [z])
    if !on_negative_real_axisp(z).truthy() {
      value
    } else {
      let r = expintegral_cut_limit(value, cadr(expr), var_, val, Nil)
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, Nil)
      }
    }
  }
}

///|
/// Exponential Integral Chi is a simplifying function
/// (def-simplifier expintegral_chi (arg)).
fn simp__pctexpintegral_chi(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  expintegral__wna(form, q_p_expintegral_chi)
  let arg = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_expintegral_chi), list1(arg)), form)
  // Check for special values
  if zerop1(arg).truthy() {
    // First check for zero argument. Throw Maxima error.
    return simp_domain_error(
      list([Str("expintegral_chi: expintegral_chi(~:M) is undefined."), arg]),
    )
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_inf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_minf]) {
    return div(mul2(q_d__pctpi, q_d__pcti), Fix(2L))
  }
  if expintegral__alike(arg, [q_d__pcti, q_d_minf]) ||
    expintegral__alike(arg, [Fix(-1L), q_d__pcti, q_d_inf]) {
    return div(muln_([Fix(-1L), q_d__pctpi, q_d__pcti]), Fix(2L))
  }
  // Check for numerical evaluation
  if complex_float_numerical_eval_p(list1(arg)).truthy() {
    let carg = expintegral__cfloat(arg)
    return complexify(expintegral_chi(carg))
  }
  if complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    return with_special(q_d_ratprint, Nil, () => {
      let carg = expintegral__cbfloat(arg)
      let result = bfloat_expintegral_chi(carg)
      expintegral__rect2(result)
    })
  }
  // Check for argument simplifications and transformations
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  if expintegral__rep_other(q_d_expintegral_hyp) {
    let rep = symval(q_d_expintrep)
    return if eq(rep, q_p_gamma_u_incomplete) {
      mul2(
        inv(Fix(-2L)),
        addn_([
          expintegral__gi0(expintegral__neg1(arg)),
          expintegral__gi0(arg),
          expintegral__log(expintegral__neg1(arg)),
          expintegral__neg1(expintegral__log(arg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_e1) {
      mul2(
        inv(Fix(-2L)),
        addn_([
          expintegral__f(q_p_expintegral_e1, expintegral__neg1(arg)),
          expintegral__f(q_p_expintegral_e1, arg),
          expintegral__log(expintegral__neg1(arg)),
          expintegral__neg1(expintegral__log(arg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_ei) {
      mul2(
        inv(Fix(4L)),
        addn_([
          mul2(
            Fix(2L),
            add2(
              expintegral__f(q_p_expintegral_ei, expintegral__neg1(arg)),
              expintegral__f(q_p_expintegral_ei, arg),
            ),
          ),
          expintegral__log(inv(arg)),
          expintegral__log(expintegral__neg1(inv(arg))),
          expintegral__neg1(expintegral__log(expintegral__neg1(arg))),
          mul2(Fix(3L), expintegral__log(arg)),
        ]),
      )
    } else if eq(rep, q_p_expintegral_li) {
      addn_([
        mul2(
          inv(Fix(2L)),
          add2(
            expintegral__f(
              q_p_expintegral_li,
              power(q_d__pcte, expintegral__neg1(arg)),
            ),
            expintegral__f(q_p_expintegral_li, power(q_d__pcte, arg)),
          ),
        ),
        mul2(
          div(mul2(q_d__pcti, q_d__pctpi), Fix(2L)),
          take(list1(q_p_signum), [d_imagpart(arg)]),
        ),
        mul2(
          inv(Fix(2L)),
          add2(expintegral__log(inv(arg)), expintegral__log(arg)),
        ),
      ])
    } else if eq(rep, q_d_expintegral_trig) {
      addn_([
        expintegral__f(q_p_expintegral_ci, mul2(q_d__pcti, arg)),
        expintegral__log(arg),
        expintegral__neg1(expintegral__log(mul2(q_d__pcti, arg))),
      ])
    } else {
      Nil
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.40.26.0001.01
    //
    // expintegral_chi(z) = z^2/4*hypergeometric([1,1],[2,2,3/2],z^2/4)
    //   + log(z) + %gamma
    return addn_([
      mul2(
        div(mul2(arg, arg), Fix(4L)),
        ftake(q_p_hypergeometric, [
          make_mlist(list2(Fix(1L), Fix(1L))),
          make_mlist(list3(Fix(2L), Fix(2L), symval(q_n3_sl_sl2))),
          div(mul2(arg, arg), Fix(4L)),
        ]),
      ),
      ftake(q_p_log, [arg]),
      q_d__pctgamma,
    ])
  }
  give_up()
}

///|
/// Numerical evaluation of the Exponential Integral Chi:
///
///   Chi(z) = -1/2 * (E1(-z) + E1(z) + log(-z) - log(z))
fn expintegral_chi(z : Value) -> Value raise {
  let z = real_if_real(z)
  num_mul(
    Flo(-0.5),
    num_add(
      num_add(
        num_add(
          expintegral_e(Fix(1L), z),
          expintegral_e(Fix(1L), num_neg(z)),
        ),
        llog(num_neg(z)),
      ),
      num_neg(llog(z)),
    ),
  )
}

///|
fn bfloat_expintegral_chi(z : Value) -> Value raise {
  let mz = mul2(Fix(-1L), z)
  mul2(
    Flo(-0.5),
    addn_([
      bfloat_expintegral_e(Fix(1L), z),
      bfloat_expintegral_e(Fix(1L), mz),
      ftake(q_p_log, [mz]),
      mul2(Fix(-1L), ftake(q_p_log, [z])),
    ]),
  )
}

///|
/// Exponential integral E1(x).  The Cauchy principal value is used for
/// negative x.  (Moved from bessel.lisp; uses SLATEC DE1.)
fn d_expint(x : Value) -> Value raise {
  if numberp(x) {
    Flo(@slatec.de1(to_double(x)))
  } else {
    mk_simp(q_d_expint, [x])
  }
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn expintegral__bags() -> Value {
  list([q_mlist, q_d_matrix, q_mequal])
}

///|
/// `(defgrad name args derivs...)`
fn expintegral__defgrad(
  name : Value,
  args : Array[Value],
  derivs : Array[Value],
) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  setf_get(name, q_grad, cons(list(args), list(derivs))) |> ignore
}

///|
fn init_expintegral() -> Unit raise {
  // *expintflag*: allowed flags to transform the Exponential Integral.
  defvar_init(
    q_ear_expintflag,
    list([
      q_p_expintegral_e1,
      q_p_expintegral_ei,
      q_p_expintegral_li,
      q_d_expintegral_trig,
      q_d_expintegral_hyp,
      q_p_gamma_u_incomplete,
    ]),
  )
  // (defmvar $expintexpand nil ... :setting-list (t nil %erf))
  let possible_values = list([t, Nil, q_p_erf])
  putprop(
    q_d_expintexpand,
    lfunc("expintexpand-assign", args => {
      let var_ = arg(args, 0)
      let val = arg(args, 1)
      if member(val, possible_values) is Nil {
        mseterr(
          var_,
          val,
          reason=Str(
            format_to_string("must be one of: ~{~A~^, ~}", [
              mapcar(x => stripdollar(x), possible_values),
            ]),
          ),
        )
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
  // (defmvar $expintrep nil ... :setting-predicate ...)
  putprop(
    q_d_expintrep,
    lfunc("expintrep-assign", args => {
      let var_ = arg(args, 0)
      let val = arg(args, 1)
      let ok = val is Nil || member(val, symval(q_ear_expintflag)).truthy()
      let reason = format_to_string(
        "~%  must be false or one of~{~<~%    ~1,80:; ~A~>~^,~}",
        [
          mapcar(
            v => stripdollar(d_verbify(v)),
            symval(q_ear_expintflag),
          ),
        ],
      )
      if !ok {
        mseterr(var_, val, reason=Str(reason))
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore

  // Part 1: Exponential Integral E
  putprop(q_p_expintegral_e, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(
    q_p_expintegral_e,
    q_conjugate_expintegral_e,
    q_conjugate_function,
  )
  |> ignore
  expintegral__defgrad(
    q_p_expintegral_e,
    [q_d_n, q_d_z],
    [
      // The derivative wrt the parameter n is expressed in terms of the
      // Regularized Hypergeometric function 2F2 (see functions.wolfram.com)
      maxima_lit(
        "gamma(1-n)*z^(n-1)*(log(z)-psi[0](1-n))-hypergeometric_regularized([1-n,1-n],[2-n,2-n],-z)*gamma(1-n)^2",
      ),
      // The derivative wrt the argument of the function
      maxima_lit("-expintegral_e(n-1,z)"),
    ],
  )
  putprop(
    q_p_expintegral_e,
    lread("((n z) nil ((mtimes) -1 ((%expintegral_e) ((mplus) 1 n) z)))"),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_e,
    q_simplim_pctexpintegral_e,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 2: Exponential Integral E1
  putprop(q_p_expintegral_e1, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(
    q_p_expintegral_e1,
    q_conjugate_expintegral_e1,
    q_conjugate_function,
  )
  |> ignore
  expintegral__defgrad(q_p_expintegral_e1, [q_d_x], [
    maxima_lit(" -(%e^-x/x)"),
  ])
  putprop(
    q_p_expintegral_e1,
    lread("((z) ((mtimes) -1 ((%expintegral_e) 2 z)))"),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_e1,
    q_simplim_pctexpintegral_e1,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 3: Exponential Integral Ei
  putprop(q_p_expintegral_ei, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(q_p_expintegral_ei, t, q_commutes_with_conjugate) |> ignore
  expintegral__defgrad(q_p_expintegral_ei, [q_d_x], [maxima_lit(" %e^x/x")])
  putprop(
    q_p_expintegral_ei,
    lread(
      "((x) ((mplus) ((mtimes) -1 ((mexpt) $%e x)) ((mtimes) x ((%expintegral_ei) x))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_ei,
    q_simplim_pctexpintegral_ei,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 4: Logarithmic integral li
  putprop(q_p_expintegral_li, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(
    q_p_expintegral_li,
    q_conjugate_expintegral_li,
    q_conjugate_function,
  )
  |> ignore
  expintegral__defgrad(q_p_expintegral_li, [q_d_x], [maxima_lit(" 1/log(x)")])
  putprop(
    q_p_expintegral_li,
    lread(
      "((x) ((mplus) ((mtimes) x ((%expintegral_li) x)) ((mtimes) -1 ((%expintegral_ei) ((mtimes) 2 ((%log) x))))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_li,
    q_simplim_pctexpintegral_li,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 5: Exponential Integral Si
  putprop(q_p_expintegral_si, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(q_p_expintegral_si, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_expintegral_si, q_odd_function_reflect, q_reflection_rule)
  |> ignore
  expintegral__defgrad(q_p_expintegral_si, [q_d_x], [maxima_lit(" sin(x)/x")])
  putprop(
    q_p_expintegral_si,
    lread("((x) ((mplus) ((%cos) x) ((mtimes) x ((%expintegral_si) x))))"),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_si,
    q_simplim_pctexpintegral_si,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 6: Exponential Integral Shi
  putprop(q_p_expintegral_shi, expintegral__bags(), q_distribute_u_over)
  |> ignore
  // (The Lisp source puts these two properties on %expintegral_si again.)
  putprop(q_p_expintegral_si, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_expintegral_si, q_odd_function_reflect, q_reflection_rule)
  |> ignore
  expintegral__defgrad(q_p_expintegral_shi, [q_d_x], [
    maxima_lit(" sinh(x)/x"),
  ])
  putprop(
    q_p_expintegral_shi,
    lread(
      "((x) ((mplus) ((mtimes) -1 ((%cosh) x)) ((mtimes) x ((%expintegral_shi) x))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_shi,
    q_simplim_pctexpintegral_shi,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 7: Exponential Integral Ci
  putprop(q_p_expintegral_ci, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(
    q_p_expintegral_ci,
    q_conjugate_expintegral_ci,
    q_conjugate_function,
  )
  |> ignore
  expintegral__defgrad(q_p_expintegral_ci, [q_d_x], [maxima_lit(" cos(x)/x")])
  putprop(
    q_p_expintegral_ci,
    lread(
      "((x) ((mplus) ((mtimes) x ((%expintegral_ci) x)) ((mtimes) -1 ((%sin) x))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_ci,
    q_simplim_pctexpintegral_ci,
    q_simplim_pctfunction,
  )
  |> ignore

  // Part 8: Exponential Integral Chi
  putprop(q_p_expintegral_chi, expintegral__bags(), q_distribute_u_over)
  |> ignore
  putprop(
    q_p_expintegral_chi,
    q_conjugate_expintegral_chi,
    q_conjugate_function,
  )
  |> ignore
  expintegral__defgrad(q_p_expintegral_chi, [q_d_x], [
    maxima_lit(" cosh(x)/x"),
  ])
  putprop(
    q_p_expintegral_chi,
    lread(
      "((x) ((mplus) ((mtimes) x ((%expintegral_chi) x)) ((mtimes) -1 ((%sinh) x))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_expintegral_chi,
    q_simplim_pctexpintegral_chi,
    q_simplim_pctfunction,
  )
  |> ignore
}
