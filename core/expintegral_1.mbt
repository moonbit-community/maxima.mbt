// Port of src/expintegral.lisp, part 1: the Exponential Integral E[n](z)
// (simplifier, limits and the numerical evaluation in float, complex float
// and bigfloat precision).
//
// Copyright (C) 2008 Dieter Kaiser (GPL)

///|
/// `(complex ($float ($realpart x)) ($float ($imagpart x)))`
fn expintegral__cfloat(x : Value) -> Value raise {
  complex(d_float(d_realpart(x)), i=d_float(d_imagpart(x)))
}

///|
/// `(add ($bfloat ($realpart x)) (mul '$%i ($bfloat ($imagpart x))))`
fn expintegral__cbfloat(x : Value) -> Value raise {
  add2(d_bfloat(d_realpart(x)), mul2(q_d__pcti, d_bfloat(d_imagpart(x))))
}

///|
/// `(add ($realpart r) (mul '$%i ($imagpart r)))`
fn expintegral__rect(r : Value) -> Value raise {
  add2(d_realpart(r), mul2(q_d__pcti, d_imagpart(r)))
}

///|
/// `(add (mul '$%i ($imagpart r)) ($realpart r))`
fn expintegral__rect2(r : Value) -> Value raise {
  add2(mul2(q_d__pcti, d_imagpart(r)), d_realpart(r))
}

///|
/// `(alike1 x '((mtimes) -1 $minf))` and friends.
fn expintegral__alike(x : Value, factors : Array[Value]) -> Bool raise {
  alike1(x, mk(q_mtimes, factors)).truthy()
}

///|
/// Exponential Integral E has mirror symmetry, but not on the real
/// negative axis.
fn conjugate_expintegral_e(args : Value) -> Value raise {
  let n = first(args)
  let z = second(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    take(list1(q_p_expintegral_e), [
      take(list1(q_d_conjugate), [n]),
      take(list1(q_d_conjugate), [z]),
    ])
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_expintegral_e), [n, z]))
  }
}

///|
/// The exponential integrals with a branch cut along the negative real
/// axis take different values on the two sides of it, so a limit onto the
/// cut depends on the direction from which it is approached. VALUE is what
/// the simplifier of the function returns on the cut itself, and ARG is
/// the argument of the function. For expintegral_ei, and for
/// expintegral_li between 0 and 1, that value is the principal value, the
/// mean of the two one-sided limits, and PRINCIPAL-VALUE-P is true. For the
/// others it is the limit from the upper half plane, whose mirror image is
/// the limit from the lower one. A path that runs along the cut itself
/// meets no jump. Returns NIL when the direction cannot be determined.
fn expintegral_cut_limit(
  value : Value,
  arg : Value,
  var_ : Value,
  val : Value,
  principal_value_p : Value,
) -> Value raise {
  let im = d_imagpart(arg)
  if zerop1(im).truthy() {
    value
  } else {
    let direction = behavior(im, var_, val)
    if eql(direction, Fix(1L)) {
      if principal_value_p.truthy() {
        add2(value, mul2(q_d__pcti, q_d__pctpi))
      } else {
        value
      }
    } else if eql(direction, Fix(-1L)) {
      if principal_value_p.truthy() {
        sub(value, mul2(q_d__pcti, q_d__pctpi))
      } else {
        ftake(q_d_conjugate, [value])
      }
    } else {
      Nil
    }
  }
}

///|
fn simplim_pctexpintegral_e(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the arguments.
  let a = limit(cadr(expr), var_, val, q_think)
  let z = limit(caddr(expr), var_, val, q_think)
  if onep1(a).truthy() &&
    (eq(z, q_d_zeroa) || eq(z, q_d_zerob) || zerop1(z).truthy()) {
    // Special case order a=1
    q_d_inf
  } else if memq(
      d_sign(add2(d_realpart(a), Fix(-1L))),
      list([q_d_neg, q_d_nz, q_d_zero]),
    ).truthy() {
    // realpart of order < 1
    if eq(z, q_d_zeroa) {
      // from above, always inf
      q_d_inf
    } else if eq(z, q_d_zerob) {
      // this can be further improved to give a directed infinity
      q_d_infinity
    } else if zerop1(z).truthy() {
      // no direction, return infinity
      q_d_infinity
    } else {
      ftake(q_p_expintegral_e, [a, z])
    }
  } else {
    // All other cases are handled by the simplifier of the function.
    ftake(q_p_expintegral_e, [a, z])
  }
}

///|
/// `(dosum summand index lo hi t)` with a fresh summation index.
fn expintegral__sum(
  summand : (Value) -> Value raise,
  lo : Value,
  hi : Value,
) -> Value raise {
  let index = gensumindex()
  dosum(summand(index), index, lo, hi, t)
}

///|
/// Exponential Integral E is a simplifying function
/// (def-simplifier expintegral_e (order arg)).
fn simp__pctexpintegral_e(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=Fix(2L),
      pretty_name=list3(
        list1(q_p_expintegral_e),
        expintegral__q_d_order,
        expintegral__q_d_arg,
      ),
    )
    |> ignore
  }
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_expintegral_e), list2(order, arg)),
    form,
  )
  // Check for special values
  if eq(arg, q_d_inf) || expintegral__alike(arg, [Fix(-1L), q_d_minf]) {
    // arg is inf or -minf, return zero
    return Fix(0L)
  }
  if zerop1(arg).truthy() {
    let sgn = d_sign(add2(d_realpart(order), Fix(-1L)))
    return if eq(sgn, q_d_pos) {
      // we handle the special case E[v](0) = 1/(v-1), for realpart(v)>1
      inv(add2(order, Fix(-1L)))
    } else if memq(sgn, list([q_d_neg, q_d_nz, q_d_zero])).truthy() {
      simp_domain_error(
        list([
          Str("expintegral_e: expintegral_e(~:M,~:M) is undefined."),
          order,
          arg,
        ]),
      )
    } else {
      give_up()
    }
  }
  if (symbolp(order) && member(order, symval(q_ear_infinities)).truthy()) ||
    (symbolp(arg) && member(arg, symval(q_ear_infinities)).truthy()) {
    // order or arg is one of the infinities, we return a noun form,
    // but we have already handled the special value inf for arg.
    return give_up()
  }
  if numberp(order) && integerp(order) {
    // The parameter of the Exponential integral is an integer. For this
    // case we can do further simplifications or numerical evaluation.
    if num_eq(order, Fix(0L)) {
      // Special case E[0](z) = %e^(-z)/z, z<>0
      // The case z=0 is already handled.
      return div(power(q_d__pcte, mul2(Fix(-1L), arg)), arg)
    }
    if num_eq(order, Fix(-1L)) {
      // Special case E[-1](0) = ((z+1)*%e^(-z))/z^2, z<>0
      // The case z=0 is already handled.
      return div(
        mul2(power(q_d__pcte, mul2(Fix(-1L), arg)), add2(arg, Fix(1L))),
        mul2(arg, arg),
      )
    }
    if num_lt(order, Fix(-1L)) {
      // We expand in a series, z<>0
      return muln_([
        factorial(num_neg(order)),
        power(arg, num_add(order, Fix(-1L))),
        power(q_d__pcte, mul2(Fix(-1L), arg)),
        expintegral__sum(
          index => div(
            power(arg, index),
            take(list1(q_mfactorial), [index]),
          ),
          Fix(0L),
          num_neg(order),
        ),
      ])
    }
    if num_gt(order, Fix(0L)) &&
      complex_float_numerical_eval_p(list1(arg)).truthy() {
      // Numerical evaluation for double float real or complex arg
      // order is an integer > 0 and arg <> 0 for order < 2
      let carg = expintegral__cfloat(arg)
      return complexify(expintegral_e(order, carg))
    }
    if num_gt(order, Fix(0L)) &&
      complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
      // Numerical evaluation for Bigfloat real or complex arg.
      return with_special(q_d_ratprint, Nil, () => {
        let carg = expintegral__cbfloat(arg)
        let result = bfloat_expintegral_e(order, carg)
        expintegral__rect(result)
      })
    }
    if symval(q_d_expintexpand).truthy() && num_gt(order, Fix(0L)) {
      // We only expand in terms of the Exponential Integral Ei
      // if the expand flag is set.
      return sub(
        muln_([
          Fix(-1L),
          power(mul2(Fix(-1L), arg), num_sub(order, Fix(1L))),
          inv(factorial(num_sub(order, Fix(1L)))),
          addn_([
            take(list1(q_p_expintegral_ei), [mul2(Fix(-1L), arg)]),
            mul2(
              inv(Fix(2L)),
              sub(
                take(list1(q_p_log), [mul2(Fix(-1L), inv(arg))]),
                take(list1(q_p_log), [mul2(Fix(-1L), arg)]),
              ),
            ),
            take(list1(q_p_log), [arg]),
          ]),
        ]),
        mul2(
          power(q_d__pcte, mul2(Fix(-1L), arg)),
          expintegral__sum(
            index => div(
              power(arg, add2(index, Fix(-1L))),
              take(list1(q_d_pochhammer), [num_sub(Fix(1L), order), index]),
            ),
            Fix(1L),
            num_sub(order, Fix(1L)),
          ),
        ),
      )
    }
    if eq(symval(q_d_expintrep), q_p_gamma_incomplete) {
      // We transform to the Incomplete Gamma function.
      return mul2(
        power(arg, num_sub(order, Fix(1L))),
        take(list1(q_p_gamma_incomplete), [num_sub(Fix(1L), order), arg]),
      )
    }
    return give_up()
  }
  if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    let z = integer_representation_p(order)
    if z.truthy() && plusp(z) {
      // We have a pure real positive order and the realpart is a float
      // representation of an integer value.
      // We call the routine for an integer order.
      let carg = expintegral__cfloat(arg)
      return complexify(expintegral_e(z, carg))
    } else {
      // The general case, order and arg are complex or real.
      let corder = expintegral__cfloat(order)
      let carg = expintegral__cfloat(arg)
      return complexify(frac_expintegral_e(corder, carg))
    }
  }
  if complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    let z = integer_representation_p(order)
    if z.truthy() && plusp(z) {
      // We have a real positive order and the realpart is a Float or
      // Bigfloat representation of an integer value.
      // We call the routine for an integer order.
      return with_special(q_d_ratprint, Nil, () => {
        let carg = expintegral__cbfloat(arg)
        let result = bfloat_expintegral_e(z, carg)
        expintegral__rect(result)
      })
    } else {
      // the general case, order and arg are bigfloat or complex bigfloat
      return with_special(q_d_ratprint, Nil, () => {
        let corder = expintegral__cbfloat(order)
        let carg = expintegral__cbfloat(arg)
        let result = frac_bfloat_expintegral_e(corder, carg)
        expintegral__rect(result)
      })
    }
  }
  if symval(q_d_expintexpand).truthy() {
    let ratorder = max_numeric_ratio_p(order, Fix(2L))
    if ratorder.truthy() {
      // We have a half integral order and $expintexpand is not NIL.
      // We expand in a series in terms of the Erfc or Erf function.
      let half = mk_simp(q_rat, [Fix(1L), Fix(2L)])
      let func = if eq(symval(q_d_expintexpand), q_p_erf) {
        sub(Fix(1L), ftake(q_p_erf, [power(arg, half)]))
      } else {
        ftake(q_p_erfc, [power(arg, half)])
      }
      let r_half = make_ratio(1N, 2N)
      let r_mhalf = make_ratio(-1N, 2N)
      if num_eq(ratorder, r_half) {
        return muln_([
          power(q_d__pctpi, half),
          power(arg, mk_simp(q_rat, [Fix(-1L), Fix(2L)])),
          func,
        ])
      } else if num_eq(ratorder, r_mhalf) {
        return add2(
          muln_([
            power(q_d__pctpi, half),
            inv(mul2(Fix(2L), power(arg, mk_simp(q_rat, [Fix(3L), Fix(2L)])))),
            func,
          ]),
          div(power(q_d__pcte, mul2(Fix(-1L), arg)), arg),
        )
      } else {
        let n = num_sub(ratorder, r_half)
        return mul2(
          power(arg, sub(n, half)),
          addn_([
            mul2(func, take(list1(q_p_gamma), [sub(half, n)])),
            mul2(
              power(q_d__pcte, mul2(Fix(-1L), arg)),
              expintegral__sum(
                index => div(
                  power(arg, add2(index, half)),
                  take(list1(q_d_pochhammer), [
                    sub(half, n),
                    addn_([index, n, Fix(1L)]),
                  ]),
                ),
                Fix(0L),
                mul2(Fix(-1L), add2(n, Fix(1L))),
              ),
            ),
            muln_([
              Fix(-1L),
              power(q_d__pcte, mul2(Fix(-1L), arg)),
              expintegral__sum(
                index => div(
                  power(arg, add2(index, half)),
                  take(list1(q_d_pochhammer), [
                    sub(half, n),
                    addn_([index, n, Fix(1L)]),
                  ]),
                ),
                num_neg(n),
                Fix(-1L),
              ),
            ]),
          ]),
        )
      }
    }
  }
  if eq(symval(q_d_expintrep), q_p_gamma_incomplete) {
    // We transform to the Incomplete Gamma function.
    return mul2(
      power(arg, sub(order, Fix(1L))),
      take(list1(q_p_gamma_incomplete), [sub(Fix(1L), order), arg]),
    )
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.34.26.0002.01:
    //
    //   expintegral_e(v,z) = z^(v-1)*gamma(1-v)
    //     - hypergeometric([1-v],[2-v], -z)
    //
    // But hypergeometric([1-v],[2-v],-z) gets simplified to
    // hypergeometric([1],[2-v],z)*exp(-z)
    return sub(
      mul2(
        power(arg, sub(order, Fix(1L))),
        ftake(q_p_gamma, [sub(Fix(1L), order)]),
      ),
      div(
        ftake(q_p_hypergeometric, [
          make_mlist(list1(sub(Fix(1L), order))),
          make_mlist(list1(sub(Fix(2L), order))),
          neg(arg),
        ]),
        sub(Fix(1L), order),
      ),
    )
  }
  give_up()
}

// ---------------------------------------------------------------------------
// Numerical evaluation of the Exponential Integral En(z)
//
// expintegral-e             - n positive integer, z real or complex
// frac-expintegral-e        - n,z real or complex; n not a positive integer
// bfloat-expintegral-e      - n positive integer,
//                             z Bigfloat or Complex Bigfloat
// frac-bfloat-expintegral-e - n Bigfloat, z Bigfloat or Complex Bigfloat
//
// The flonum versions return a CL complex number. The Bigfloat versions a
// Maxima Complex Bigfloat number.
//
// The evaluation uses an expansion in continued fractions for arguments
// with realpart(z) > 0 and abs(z)> 1.0 (A&S 5.1.22), evaluated by the
// modified Lentz's method for the more rapidly converging even form:
//
//                       1   n   1  n+1  2
//   En(z) = e^(-z) * ( --- --- --- --- --- ... )
//                      z+  1+  z+  1+  z+
//
// For the parameter n a positive integer we expand in a power series
// (A&S 5.1.12):
//                                           inf
//            (-z)^(n-1)                     \     (-z)^m
//   En(z) =  --------- * (-log(z)+psi(n)) *  >  ---------- ; n an integer
//               (n-1)!                      /   (m-n+1)*m!
//                                           m=0 (m <> n-1)
//
// For a parameter n not an integer we expand in the series
// (functions.wolfram.com):
//                                    inf
//                                    \    (-1)^m * z^m
//   Ev(z) = gamma(1-v) * z^(v-1) *    >   -------------  ; n not an integer
//                                    /     (m-v+1)*m!
//                                    m=0
//
// The evaluation stops if an accuracy better than *expint-eps* is
// achieved. If the expansion does not converge within *expint-maxit* steps
// a Maxima Error is thrown. The algorithm is based on techniques described
// in Numerical Recipes, 2nd Ed.

///|
fn expintegral__debug() -> Bool {
  symval(q_ear_debug_expintegral).truthy()
}

///|
fn expintegral__set_max(s : Value, i : Int) -> Unit raise {
  set(s, num_max(symval(s), int(i))) |> ignore
}

///|
fn expintegral_e(n : Value, z : Value) -> Value raise {
  let bindings = bind_all([
    (q_ear_expint_eps, symval(q_ear_expint_eps)),
    (q_ear_expint_maxit, symval(q_ear_expint_maxit)),
  ])
  defer unbind_all(bindings)
  // Add (complex) 0 to get rid of any signed zeroes, and make z
  // be a complex number.
  let z = num_add(Cplx(Flo(0.0), Flo(0.0)), z)
  if expintegral__debug() {
    format(t, "~&EXPINTEGRAL-E called with:~%", []) |> ignore
    format(t, "~&   : n = ~A~%", [n]) |> ignore
    format(t, "~&   : z = ~A~%", [z]) |> ignore
  }
  let eps = symval(q_ear_expint_eps)
  let maxit = symval(q_ear_expint_maxit)
  if (
      num_gt(num_abs(z), Flo(2.0)) &&
      num_lt(num_abs(phase(z)), num_mul(Flo(@math.PI), Flo(0.9)))
    ) ||
    // (abs z)>2.0 is necessary since there is a point
    // -1.700598-0.612828*%i which 1<(abs z)<2, phase z < 0.9pi and
    // still c-f expansion does not converge.
    (num_ge(realpart(z), Fix(0L)) && num_gt(num_abs(z), Flo(1.0))) {
    // We expand in continued fractions.
    if expintegral__debug() {
      format(t, "~&We expand in continued fractions.~%", []) |> ignore
    }
    let mut b = num_add(z, n)
    let mut c = num_div(Flo(1.0), num_mul(eps, eps))
    let mut d = num_div(Flo(1.0), b)
    let n1 = num_sub(n, Fix(1L))
    let mut h = d
    let mut e : Value = Flo(0.0)
    let mut i = 1
    let mut a = num_mul(Fix(-1L), n)
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: continued fractions failed.", [])
      }
      b = num_add(b, Flo(2.0))
      d = num_div(Flo(1.0), num_add(num_mul(a, d), b))
      c = num_add(b, num_div(a, c))
      e = num_mul(c, d)
      h = num_mul(h, e)
      if num_lt(num_abs(num_sub(e, Flo(1.0))), eps) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_maxit, i)
        }
        return num_mul(h, lexp(num_neg(z)))
      }
      i = i + 1
      a = num_mul(num_neg(int(i)), num_add(n1, int(i)))
    }
    Nil
  } else {
    // We expand in a power series.
    if expintegral__debug() {
      format(t, "~&We expand in a power series.~%", []) |> ignore
    }
    let n1 = num_sub(n, Fix(1L))
    let euler = mget(q_d__pctgamma, q_d_numer)
    let mut r = if num_eq(n1, Fix(0L)) {
      num_sub(num_neg(euler), llog(z))
    } else {
      num_div(Flo(1.0), n1)
    }
    let mut f : Value = Flo(1.0)
    let mut e : Value = Flo(0.0)
    let mut i = 1
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: series failed.", [])
      }
      f = num_mul(num_mul(Fix(-1L), f), num_div(z, int(i)))
      if num_eq(int(i), n1) {
        let mut psi = num_neg(euler)
        let mut ii : Value = Fix(0L)
        while num_lt(ii, n1) {
          psi = num_add(psi, num_div(Flo(1.0), num_add(ii, Fix(1L))))
          ii = num_add(ii, Fix(1L))
        }
        e = num_mul(f, num_sub(psi, llog(z)))
      } else {
        e = num_div(num_neg(f), num_sub(int(i), n1))
      }
      r = num_add(r, e)
      if num_lt(num_abs(e), num_mul(num_abs(r), eps)) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_maxit, i)
        }
        return r
      }
      i = i + 1
    }
    Nil
  }
}

///|
/// Numerical evaluation for a real or complex parameter.
fn frac_expintegral_e(n : Value, z : Value) -> Value raise {
  let bindings = bind_all([
    (q_ear_expint_eps, symval(q_ear_expint_eps)),
    (q_ear_expint_maxit, symval(q_ear_expint_maxit)),
  ])
  defer unbind_all(bindings)
  if expintegral__debug() {
    format(t, "~&FRAC-EXPINTEGRAL-E called with:~%", []) |> ignore
    format(t, "~&   : n = ~A~%", [n]) |> ignore
    format(t, "~&   : z = ~A~%", [z]) |> ignore
  }
  let eps = symval(q_ear_expint_eps)
  let maxit = symval(q_ear_expint_maxit)
  if num_gt(realpart(z), Fix(0L)) && num_gt(num_abs(z), Flo(1.0)) {
    // We expand in continued fractions.
    if expintegral__debug() {
      format(t, "~&We expand in continued fractions.~%", []) |> ignore
    }
    let mut b = num_add(z, n)
    let mut c = num_div(Flo(1.0), num_mul(eps, eps))
    let mut d = if zerop(b) { c } else { num_div(Flo(1.0), b) }
    let n1 = num_sub(n, Fix(1L))
    let mut h = d
    let mut e : Value = Flo(0.0)
    let mut i = 1
    let mut a = num_mul(Fix(-1L), n)
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: continued fractions failed.", [])
      }
      b = num_add(b, Flo(2.0))
      d = num_div(Flo(1.0), num_add(num_mul(a, d), b))
      c = num_add(b, num_div(a, c))
      e = num_mul(c, d)
      h = num_mul(h, e)
      if num_lt(num_abs(num_sub(e, Flo(1.0))), eps) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_fracmaxit, i)
        }
        return num_mul(h, lexp(num_neg(z)))
      }
      i = i + 1
      a = num_mul(num_neg(int(i)), num_add(n1, int(i)))
    }
    Nil
  } else if num_eq(imagpart(n), Fix(0L)) &&
    num_gt(realpart(n), Fix(0L)) &&
    num_eq(num_truncate(realpart(n)).1, Fix(0L)) {
    // We have a positive integer n or an float representation of an
    // integer. We call expintegral-e which does this calculation.
    if expintegral__debug() {
      format(t, "~&We call expintegral-e.~%", []) |> ignore
    }
    expintegral_e(truncate1(realpart(n)), z)
  } else {
    // At this point the parameter n is a real (not an float
    // representation of an integer) or complex. We expand in a power
    // series.
    if expintegral__debug() {
      format(t, "~&We expand in a power series.~%", []) |> ignore
    }
    let n1 = num_sub(n, Fix(1L))
    // It would be possible to call the numerical implementation
    // gamm-lanczos directly. But then the code would depend on the
    // details of the implementation.
    let gm = {
      let tmp = take(list1(q_p_gamma), [complexify(num_sub(Fix(1L), n))])
      complex(d_realpart(tmp), i=d_imagpart(tmp))
    }
    let mut r = num_sub(
      num_mul(expt(z, n1), gm),
      num_div(Flo(1.0), num_sub(Fix(1L), n)),
    )
    let mut f : Value = Flo(1.0)
    let mut e : Value = Flo(0.0)
    let mut i = 1
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: series failed.", [])
      }
      f = num_mul(num_mul(Fix(-1L), f), num_div(z, Flo(i.to_double())))
      e = num_div(num_neg(f), num_sub(Flo(i.to_double()), n1))
      r = num_add(r, e)
      if num_lt(num_abs(e), num_mul(num_abs(r), eps)) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_fracmaxit, i)
        }
        return r
      }
      i = i + 1
    }
    Nil
  }
}

// We have not changed the above algorithm, but generalized it to handle
// complex and real Bigfloat numbers. The accuracy of the result is
// determined by *expint-eps*, chosen to correspond to the value of
// $fpprec. We don't give any extra digits to fpprec, so we loose 1 to 2
// digits of precision.

///|
/// `(eq ($sign x) '$neg)`
fn expintegral__negp(x : Value) -> Bool raise {
  eq(d_sign(x), q_d_neg)
}

///|
fn bfloat_expintegral_e(n : Value, z : Value) -> Value raise {
  let bindings = bind_all([
    (
      q_ear_expint_eps,
      power(d_bfloat(Flo(10.0)), num_neg(symval(q_d_fpprec))),
    ),
    // arbitrarily chosen, we need a better choice
    (q_ear_expint_maxit, Fix(5000L)),
  ])
  defer unbind_all(bindings)
  let one = symval(q_ear_bigfloatone)
  let bigfloattwo = add2(one, one)
  let bigfloat_pcte = d_bfloat(q_d__pcte)
  let bigfloat_pctgamma = d_bfloat(q_d__pctgamma)
  let flz = expintegral__cfloat(z)
  if expintegral__debug() {
    format(t, "~&BFLOAT-EXPINTEGRAL-E called with:~%", []) |> ignore
    format(t, "~&   : n = ~A~%", [n]) |> ignore
    format(t, "~&   : z = ~A~%", [flz]) |> ignore
  }
  let eps = symval(q_ear_expint_eps)
  let maxit = symval(q_ear_expint_maxit)
  if (
      num_gt(num_abs(flz), Fix(2L)) &&
      num_lt(num_abs(phase(flz)), num_mul(Flo(@math.PI), Flo(0.9)))
    ) ||
    // The same condition as you see in expintegral-e()
    (num_ge(realpart(flz), Fix(0L)) && num_gt(num_abs(flz), Flo(1.0))) {
    // We expand in continued fractions.
    if expintegral__debug() {
      format(t, "~&We expand in continued fractions.~%", []) |> ignore
    }
    let mut b = add2(z, n)
    let mut c = div(one, mul2(eps, eps))
    let mut d = cdiv(one, b)
    let n1 = num_sub(n, Fix(1L))
    let mut h = d
    let mut e : Value = Flo(0.0)
    let mut i = 1
    let mut a = num_mul(Fix(-1L), n)
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: continued fractions failed.", [])
      }
      b = add2(b, bigfloattwo)
      d = cdiv(one, add2(mul2(a, d), b))
      c = add2(b, cdiv(a, c))
      e = cmul(c, d)
      h = cmul(h, e)
      if expintegral__negp(sub(cabs(sub(e, one)), eps)) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_bfloatmaxit, i)
        }
        return cmul(h, cpower(bigfloat_pcte, mul2(Fix(-1L), z)))
      }
      i = i + 1
      a = num_mul(num_neg(int(i)), num_add(n1, int(i)))
    }
    Nil
  } else {
    // We expand in a power series.
    if expintegral__debug() {
      format(t, "~&We expand in a power series.~%", []) |> ignore
    }
    let n1 = num_sub(n, Fix(1L))
    let meuler = mul2(Fix(-1L), bigfloat_pctgamma)
    let mut r = if num_eq(n1, Fix(0L)) {
      sub(meuler, ftake(q_p_log, [z]))
    } else {
      div(one, n1)
    }
    let mut f = one
    let mut e = symval(q_ear_bigfloatzero)
    let mut i = 1
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: series failed.", [])
      }
      f = mul2(Fix(-1L), cmul(f, cdiv(z, int(i))))
      if num_eq(int(i), n1) {
        let mut psi = meuler
        let mut ii : Value = Fix(0L)
        while num_lt(ii, n1) {
          psi = add2(psi, cdiv(one, num_add(ii, Fix(1L))))
          ii = num_add(ii, Fix(1L))
        }
        e = cmul(f, sub(psi, ftake(q_p_log, [z])))
      } else {
        e = cdiv(mul2(Fix(-1L), f), num_sub(int(i), n1))
      }
      r = add2(r, e)
      if expintegral__negp(sub(cabs(e), cmul(cabs(r), eps))) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_bfloatmaxit, i)
        }
        return r
      }
      i = i + 1
    }
    Nil
  }
}

///|
/// Numerical Bigfloat evaluation for a real (Bigfloat) parameter. The
/// algorithm would work for a Complex Bigfloat parameter too, but we need
/// the values of Gamma for Complex Bigfloats.
fn frac_bfloat_expintegral_e(n : Value, z : Value) -> Value raise {
  let bindings = bind_all([
    (
      q_ear_expint_eps,
      power(d_bfloat(Flo(10.0)), num_neg(symval(q_d_fpprec))),
    ),
    // arbitrarily chosen, we need a better choice
    (q_ear_expint_maxit, Fix(5000L)),
  ])
  defer unbind_all(bindings)
  let one = symval(q_ear_bigfloatone)
  let bigfloattwo = add2(one, one)
  let bigfloat_pcte = d_bfloat(q_d__pcte)
  if expintegral__debug() {
    format(t, "~&FRAC-BFLOAT-EXPINTEGRAL-E called with:~%", []) |> ignore
    format(t, "~&   : n = ~A~%", [n]) |> ignore
    format(t, "~&   : z = ~A~%", [z]) |> ignore
  }
  let eps = symval(q_ear_expint_eps)
  let maxit = symval(q_ear_expint_maxit)
  if (
      eq(d_sign(d_realpart(z)), q_d_pos) || eq(d_sign(d_realpart(z)), q_d_zero)
    ) &&
    eq(d_sign(sub(cabs(z), one)), q_d_pos) {
    // We expand in continued fractions.
    if expintegral__debug() {
      format(t, "We expand in continued fractions.~%", []) |> ignore
    }
    let mut b = add2(z, n)
    let mut c = div(one, mul2(eps, eps))
    let mut d = if zerop1(b).truthy() { c } else { cdiv(one, b) }
    let n1 = sub(n, Fix(1L))
    let mut h = d
    let mut e : Value = Flo(0.0)
    let mut i = 1
    let mut a = mul2(Fix(-1L), n)
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: continued fractions failed.", [])
      }
      b = add2(b, bigfloattwo)
      d = cdiv(one, add2(mul2(a, d), b))
      c = add2(b, cdiv(a, c))
      e = cmul(c, d)
      h = cmul(h, e)
      if expintegral__negp(sub(cabs(sub(e, one)), eps)) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_fracbfloatmaxit, i)
        }
        return cmul(h, cpower(bigfloat_pcte, mul2(Fix(-1L), z)))
      }
      i = i + 1
      a = cmul(num_neg(int(i)), add2(n1, int(i)))
    }
    Nil
  } else if (
      numberp(n) &&
      num_eq(d_imagpart(n), Fix(0L)) &&
      num_gt(d_realpart(n), Fix(0L)) &&
      num_eq(num_truncate(d_realpart(n)).1, Fix(0L))
    ) ||
    (
      d_bfloatp(n).truthy() &&
      eq(d_sign(n), q_d_pos) &&
      equal(
        sub(mul2(Fix(2L), d_fix(n)), mul2(Fix(2L), n)),
        symval(q_ear_bigfloatzero),
      )
    ) {
    // We have a Float or Bigfloat representation of positive integer.
    // We call bfloat-expintegral-e.
    if expintegral__debug() {
      format(t, "frac-Bigfloat with integer ~A~%", [n]) |> ignore
    }
    bfloat_expintegral_e(d_fix(d_realpart(n)), z)
  } else {
    // At this point the parameter n is a real (not a float representation
    // of an integer) or complex. We expand in a power series.
    if expintegral__debug() {
      format(t, "We expand in a power series.~%", []) |> ignore
    }
    let n1 = sub(n, one)
    let n2 = sub(one, n)
    let gm = take(list1(q_p_gamma), [n2])
    let mut r = sub(cmul(cpower(z, n1), gm), cdiv(one, n2))
    let mut f = one
    let mut e = symval(q_ear_bigfloatzero)
    let mut i = 1
    while true {
      if num_gt(int(i), maxit) {
        return merr("expintegral_e: series failed.", [])
      }
      f = cmul(mul2(Fix(-1L), one), cmul(f, cdiv(z, int(i))))
      e = cdiv(mul2(Fix(-1L), f), sub(int(i), n1))
      r = add2(r, e)
      if expintegral__negp(sub(cabs(e), cmul(cabs(r), eps))) {
        if expintegral__debug() {
          expintegral__set_max(q_ear_debug_expint_fracbfloatmaxit, i)
        }
        return r
      }
      i = i + 1
    }
    Nil
  }
}

///|
/// computes first pw terms of asymptotic expansion of expintegral_ei(z)
/// DLMF 8.20.2, using Ei(x) = E_1(-x)
fn ei_asymptotic_expansion(pw : Value, z : Value) -> Value raise {
  let terms = Collector::new()
  let mut k : Value = Fix(0L)
  while num_le(k, pw) {
    terms.add(
      mul2_star(
        mk(q_mfactorial, [k]),
        power_star(z, mul2_star(Fix(-1L), k)),
      ),
    )
    k = num_add(k, Fix(1L))
  }
  muln_star([
    power_star(q_d__pcte, z),
    power_star(z, Fix(-1L)),
    addn(terms.result(), Nil),
  ])
}

///|
/// computes first pw terms of powerseries expansion of expintegral_ei(z)
/// DLMF 6.6.1 for limits as z -> 0
fn ei_powerseries(pw : Value, z : Value) -> Value raise {
  let terms = Collector::new()
  let mut k : Value = Fix(1L)
  while num_le(k, pw) {
    terms.add(
      div_star(power_star(z, k), mul2_star(k, mk(q_mfactorial, [k]))),
    )
    k = num_add(k, Fix(1L))
  }
  addn_star([
    q_d__pctgamma,
    take(list1(q_p_log), [z]),
    addn(terms.result(), Nil),
  ])
}

///|
let expintegral__q_d_order : Value = sym("$order")

///|
let expintegral__q_d_arg : Value = sym("$arg")
