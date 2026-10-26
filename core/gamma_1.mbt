// Port of src/gamma.lisp, part 1: double factorial, the incomplete gamma
// function family (gamma_h_incomplete, gamma_incomplete_lower,
// gamma_incomplete_generalized, gamma_incomplete_regularized) and their
// numerical evaluation.  init_gamma (for the whole of gamma.lisp) is here.

///|
let gamma1__q_debug_cf_eval : Value = sym("bigfloat::*debug-cf-eval*")

///|
let gamma1__q_max_cf_iterations : Value = sym("bigfloat::*max-cf-iterations*")

///|
fn gamma1__rat_half() -> Value {
  mk_simp(q_rat, [Fix(1L), Fix(2L)])
}

///|
fn gamma1__sign_in(sgn : Value, syms : Array[Value]) -> Bool {
  for s in syms {
    if eq(sgn, s) {
      return true
    }
  }
  false
}

///|
/// `(simplify (list '(op) args...))`
fn gamma1__simp(op : Value, args : Array[Value]) -> Value raise {
  simplify(mk(op, args))
}

///|
fn gamma1__debug() -> Bool {
  symval(q_ear_debug_gamma).truthy()
}

// ---------------------------------------------------------------------------
// The parser changes connecting the operator !! to double_factorial(z).

///|
fn gamma1__bang_bang_led(op : Value, left : Value) -> Value raise {
  ignore(op)
  list3(q_d_expr, mheader(q_d_op_bang_bang), convert(left, q_d_expr))
}

// ---------------------------------------------------------------------------
// Double factorial

///|
fn simp__pctdouble_factorial(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_double_factorial, [q_d_z]),
    )
    |> ignore
  }
  let z = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_double_factorial), list1(z)), form)
  if fixnump(z) &&
    num_gt(z, Fix(-1L)) &&
    (minusp(symval(q_d_factlim)) || num_lt(z, symval(q_d_factlim))) {
    // Positive Integer less then $factlim or $factlim is -1. Call gfact.
    gfact(z, num_floor(num_div(z, Fix(2L))).0, Fix(2L))
  } else if mnump(z).truthy() &&
    eq(d_sign(z), q_d_neg) &&
    zerop1(
      sub(
        simplify(mk(q_p_truncate, [div(z, Fix(2L))])),
        div(z, Fix(2L)),
      ),
    ).truthy() {
    // Even negative integer or real representation. Not defined.
    simp_domain_error(
      list([
        Str("double_factorial: double_factorial(~:M) is undefined."),
        z,
      ]),
    )
  } else if integerp(z) && minusp(z) {
    // odd negative integer. Evaluate.
    if num_eq(z, Fix(-1L)) {
      Fix(1L)
    } else if num_eq(z, Fix(-3L)) {
      Fix(-1L)
    } else {
      // Apply identity: n!! = (- 1)^((n - 1)/2) n / (- n)!! for negative
      // odd integer n.
      let parity = num_mod(num_div(num_sub(z, Fix(1L)), Fix(2L)), Fix(2L))
      mul2(
        if num_eq(parity, Fix(0L)) {
          Fix(1L)
        } else {
          Fix(-1L)
        },
        div(z, ftake(q_p_double_factorial, [num_neg(z)])),
      )
    }
  } else if complex_float_numerical_eval_p(list1(z)).truthy() {
    // Odd negative integer, float or complex float.
    complexify(
      double_factorial(
        complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z))),
      ),
    )
  } else if !ratnump(z).truthy() &&
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    // bigfloat or complex bigfloat.
    bfloat_double_factorial(
      add2(d_bfloat(d_realpart(z)), mul2(q_d__pcti, d_bfloat(d_imagpart(z)))),
    )
  } else if eq(z, q_d_inf) {
    // double_factorial(inf) -> inf
    q_d_inf
  } else if symval(q_d_factorial_expand).truthy() &&
    mplusp(z).truthy() &&
    integerp(cadr(z)) {
    let mut k = cadr(z)
    let n = simplify(cons(list1(q_mplus), cddr(z)))
    if num_eq(k, Fix(-1L)) {
      // Special case double_factorial(n-1)
      // Not sure if this simplification is useful.
      div(
        simplify(mk(q_mfactorial, [n])),
        simplify(mk(q_p_double_factorial, [n])),
      )
    } else if num_eq(k, num_mul(Fix(2L), truncate1(num_div(k, Fix(2L))))) {
      // Special case double_factorial(2*k+n), k integer
      k = num_div(k, Fix(2L))
      // we get more simple expression when factoring
      d_factor(
        muln_([
          power(Fix(2L), k),
          simplify(mk(q_d_pochhammer, [add2(div(n, Fix(2L)), Fix(1L)), k])),
          simplify(mk(q_p_double_factorial, [n])),
        ]),
      )
    } else {
      give_up()
    }
  } else {
    give_up()
  }
}

///|
/// Double factorial for a complex float argument. The result is a CL
/// complex.
///
///   z!! = T[2](z) 2^(z/2) gamma(1 + z/2)
///
/// with T[2](z) = sqrt(2/%pi)^((1-cos(%pi z))/2).
fn double_factorial(z : Value) -> Value raise {
  let pival : Value = Flo(@math.PI)
  num_mul(
    num_mul(
      expt(
        num_div(Fix(2L), pival),
        num_div(num_sub(Fix(1L), lcos(num_mul(pival, z))), Fix(4L)),
      ),
      expt(Flo(2.0), num_div(z, Fix(2L))),
    ),
    gamma_lanczos(num_add(Fix(1L), num_div(z, Fix(2L)))),
  )
}

///|
/// Double factorial for a bigfloat or complex bigfloat argument
fn bfloat_double_factorial(z : Value) -> Value raise {
  let pival = d_bfloat(q_d__pctpi)
  let bigfloat1 = d_bfloat(symval(q_ear_bigfloatone))
  let bigfloat2 = add2(bigfloat1, bigfloat1)
  let bigfloat4 = add2(bigfloat2, bigfloat2)
  with_special(q_d_ratprint, Nil, () => cmul(
    cpower(
      cdiv(bigfloat2, pival),
      cdiv(sub(bigfloat1, simplify(mk(q_p_cos, [cmul(pival, z)]))), bigfloat4),
    ),
    cmul(
      cpower(bigfloat2, cdiv(z, bigfloat2)),
      simplify(mk(q_p_gamma, [add2(bigfloat1, cdiv(z, bigfloat2))])),
    ),
  ))
}

// ---------------------------------------------------------------------------
// The Incomplete Gamma function
//
// A&S 6.5.3:
//
//   gamma_h_incomplete(a, z) = integrate(t^(a-1)*%e^-t, t, z, inf)

///|
/// Incomplete Gamma function has not mirror symmetry for z on the negative
/// real axis. We support a conjugate-function which test this case.
fn conjugate_gamma_incomplete(args : Value) -> Value raise {
  let a = first(args)
  let z = second(args)
  if off_negative_real_axisp(z).truthy() {
    // Definitely not on the negative real axis for z. Mirror symmetry.
    simplify(
      mk(q_p_gamma_incomplete, [
        simplify(mk(q_d_conjugate, [a])),
        simplify(mk(q_d_conjugate, [z])),
      ]),
    )
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(
      list2(q_d_conjugate, q_simp),
      simplify(mk(q_p_gamma_incomplete, [a, z])),
    )
  }
}

///|
/// The derivative of gamma_h_incomplete wrt a.  The Lisp lambda returns a
/// second value of T (the result is built from the actual arguments and
/// is final); only the primary value survives the port's funcall.
fn gamma1__gamma_incomplete_grad_a(a : Value, z : Value) -> Value raise {
  let s = d_sign(a)
  if eq(s, q_d_pos) || eq(s, q_d_pz) {
    // The derivative wrt a in terms of hypergeometric_regularized 2F2
    // function and the Generalized Incomplete Gamma function
    // (functions.wolfram.com), only for a>0.
    let g = ftake(q_p_gamma, [a])
    addn_([
      mul2(
        sub(ftake(q_p_gamma_incomplete, [a, z]), g),
        ftake(q_p_log, [z]),
      ),
      muln_([
        power(g, Fix(2L)),
        ftake(q_d_hypergeometric_regularized, [
          list([list1(q_mlist), a, a]),
          list([list1(q_mlist), add2(a, Fix(1L)), add2(a, Fix(1L))]),
          neg(z),
        ]),
        power(z, a),
      ]),
      mul2(
        ftake(q_mqapply, [
          list2(list2(q_d_psi, q_array), Fix(0L)),
          a,
        ]),
        g,
      ),
    ])
  } else {
    // No derivative. Maxima generates a noun form.
    Nil
  }
}

///|
fn simplim_pctgamma_incomplete(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Set *preserve-direction* to true and find the limit of each argument.
  let b = bind(q_ear_preserve_direction, t)
  defer unbind(b)
  let mut a = limit(cadr(expr), var_, val, q_think)
  let mut z = limit(caddr(expr), var_, val, q_think)
  if eql(a, q_d_und) || eql(z, q_d_und) {
    // when either a or z is und, return und
    q_d_und
  } else if eq(z, q_d_infinity) || eq(z, q_d_inf) || eq(z, q_d_minf) {
    // z in {minf, inf, infinity}, use http://dlmf.nist.gov/8.11#i
    // Revert a & z to the arguments of gamma_h_incomplete.
    a = cadr(expr)
    z = caddr(expr)
    // Use gamma_h_incomplete(a,z) = z^(a-1)/exp(z) + ... for fixed a and
    // |z| --> inf.  When a isn't fixed, give up.
    if freeof(var_, a).truthy() {
      limit(
        div(
          ftake(q_mexpt, [z, sub(a, Fix(1L))]),
          ftake(q_mexpt, [q_d__pcte, z]),
        ),
        var_,
        val,
        q_think,
      )
    } else {
      throw_tag(q_limit, t)
    }
  } else if eql(a, Fix(0L)) &&
    !eq(z, q_d_ind) &&
    !eq(a, q_d_ind) &&
    eq(t, mgrp(Fix(0L), z)) {
    let im = behavior(cdr(risplit(caddr(expr))), var_, val)
    if eql(im, Fix(-1L)) {
      sub(
        mul2(q_d__pcti, q_d__pctpi),
        ftake(q_p_expintegral_ei, [mul2(Fix(-1L), z)]),
      )
    } else if eql(im, Fix(1L)) {
      sub(
        mul3(Fix(-1L), q_d__pcti, q_d__pctpi),
        ftake(q_p_expintegral_ei, [mul2(Fix(-1L), z)]),
      )
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if freeof(var_, a).truthy() &&
    (eql(z, Fix(0L)) || eq(z, q_d_zeroa) || eq(z, q_d_zerob)) {
    // z in {zerob, 0, zeroa}.
    // Two cases: (i) a <= 0 & integer (ii) a not a negative integer.
    // Revert a & z to the arguments of gamma_h_incomplete.
    a = cadr(expr)
    z = caddr(expr)
    if d_featurep(a, q_d_integer).truthy() && eq(t, mgrp(Fix(0L), a)) {
      // gamma_h_incomplete(a,z) = z^a/(-a) + ... for a negative integer a
      limit(
        div(ftake(q_mexpt, [z, a]), mul2(Fix(-1L), a)),
        var_,
        val,
        q_think,
      )
    } else if d_featurep(a, q_d_integer).truthy() && eq(t, mgqp(Fix(0L), a)) {
      // gamma_h_incomplete(0,z) = -log(z) + ...
      a = sub(Fix(0L), a)
      limit(
        div(
          mul3(
            Fix(-1L),
            ftake(q_mexpt, [Fix(-1L), a]),
            ftake(q_p_log, [z]),
          ),
          ftake(q_mfactorial, [a]),
        ),
        var_,
        val,
        q_think,
      )
    } else {
      limit(
        sub(ftake(q_p_gamma, [a]), div(ftake(q_mexpt, [z, a]), a)),
        var_,
        val,
        q_think,
      )
    }
  } else if !eq(z, q_d_ind) && eq(t, mgrp(Fix(0L), z)) {
    // z is on the branch cut. We need to know if the imaginary part of
    // (caddr exp) approaches zero from above or below. The incomplete
    // gamma function is continuous from above its branch cut. The check
    // for $ind is needed to avoid calling sign on $ind.
    let im = behavior(cdr(risplit(caddr(expr))), var_, val)
    if eql(im, Fix(1L)) {
      // use direct substitution
      ftake(q_p_gamma_incomplete, [a, z])
    } else if eql(im, Fix(-1L)) {
      if d_featurep(a, q_d_integer).truthy() && eq(t, mgrp(Fix(0L), a)) {
        // For a negative integer A the factor exp(-2*%i*%pi*a) below is 1
        // and gamma(A) is a pole. The limit of that formula as A
        // approaches the integer is the jump 2*%i*%pi*(-1)^a/gamma(1-a).
        add2(
          ftake(q_p_gamma_incomplete, [a, z]),
          div(
            muln_([
              Fix(2L),
              q_d__pcti,
              q_d__pctpi,
              ftake(q_mexpt, [Fix(-1L), a]),
            ]),
            ftake(q_p_gamma, [sub(Fix(1L), a)]),
          ),
        )
      } else {
        sub(
          ftake(q_p_gamma, [a]),
          mul2(
            ftake(q_mexpt, [
              q_d__pcte,
              muln_([Fix(-2L), q_d__pcti, q_d__pctpi, a]),
            ]),
            sub(ftake(q_p_gamma, [a]), ftake(q_p_gamma_incomplete, [a, z])),
          ),
        )
      }
    } else if eql(im, Fix(0L)) {
      throw_tag(q_limit, Nil)
    } else {
      Nil
    }
  } else if eq(a, q_d_ind) || eq(z, q_d_ind) {
    // Revert a & z to the arguments of gamma_h_incomplete. When z is off the
    // negative real axis or a is not a negative integer, return ind.
    a = cadr(expr)
    z = caddr(expr)
    if off_negative_real_axisp(z).truthy() ||
      !(d_featurep(a, q_d_integer).truthy() && eq(t, mgqp(Fix(0L), a))) {
      q_d_ind
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if eq(a, q_d_und) || eq(z, q_d_und) {
    q_d_und
  } else if a is Nil ||
    z is Nil ||
    extended_real_p(a).truthy() ||
    extended_real_p(z).truthy() {
    throw_tag(q_limit, Nil)
  } else {
    // All other cases are handled by the simplifier of the function.
    ftake(q_p_gamma_incomplete, [a, z])
  }
}

// ---------------------------------------------------------------------------
// The Lower Incomplete gamma function (A&S 6.5.2):
//
//   gamma_incomplete_lower(a, z) = integrate(t^(a-1)*%e^-t, t, 0, z)

///|
/// Handles some special cases for the order a and simplifies it to an
/// equivalent form, possibly involving erf and gamma_incomplete_lower to a
/// lower order.
fn simp__pctgamma_incomplete_lower(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=int(2),
      pretty_name=mk(q_p_gamma_incomplete_lower, [q_d_a, q_d_z]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let z = simpcheck(nth(2, form), p__pctsimpflag)
  let args = list2(a, z)
  if float_numerical_eval_p(args).truthy() ||
    complex_float_numerical_eval_p(args).truthy() ||
    bigfloat_numerical_eval_p(args).truthy() ||
    complex_bigfloat_numerical_eval_p(args).truthy() {
    ftake(q_p_gamma_incomplete_generalized, [a, Fix(0L), z])
  } else {
    let r = gamma_incomplete_lower_expand(a, z)
    if r.truthy() {
      r
    } else if symval(q_d_hypergeometric_representation).truthy() {
      // We make use of the fact that gamma_incomplete_lower(a,z) +
      // gamma_h_incomplete(a,z) = gamma(a).  Thus,
      // gamma_incomplete_lower(a,z) = gamma(a)-gamma_h_incomplete(a,z).
      // And we know the hypergeometric form for gamma_h_incomplete.
      sub(ftake(q_p_gamma, [a]), ftake(q_p_gamma_incomplete, [a, z]))
    } else {
      eqtest(cons(list1(q_p_gamma_incomplete_lower), list2(a, z)), form)
    }
  }
}

///|
/// Try to express gamma_incomplete_lower(a,z) in simpler terms for special
/// values of the order a.  If we can't, return NIL to say so.
fn gamma_incomplete_lower_expand(a : Value, z : Value) -> Value raise {
  let gamma_expand = symval(q_d_gamma_expand).truthy()
  if gamma_expand && integerp(a) && eql(a, Fix(1L)) {
    // gamma_incomplete_lower(0, x) = 1-exp(x)
    sub(Fix(1L), power(q_d__pcte, neg(z)))
  } else if gamma_expand && integerp(a) && plusp(a) {
    // gamma_incomplete_lower(a,z) can be simplified if a is a positive
    // integer.  Since gamma_incomplete_lower(a,z) = gamma(a) -
    // gamma_h_incomplete(a,z), use gamma_h_incomplete to get the result.
    sub(
      ftake_star(q_p_gamma, [a]),
      take(list1(q_p_gamma_incomplete), [a, z]),
    )
  } else if gamma_expand && alike1(a, symval(q_n1_sl_sl2)).truthy() {
    // A&S 6.5.12:
    //
    // gamma_incomplete_lower(1/2,x^2) = sqrt(%pi)*erf(x)
    //
    // gamma_incomplete_lower(1/2,z) = sqrt(%pi)*erf(sqrt(x))
    mul2(
      power(q_d__pctpi, gamma1__rat_half()),
      take(list1(q_p_erf), [power(z, gamma1__rat_half())]),
    )
  } else if gamma_expand && mplusp(a).truthy() && integerp(cadr(a)) {
    // gamma_incomplete_lower(a+n,z), where n is an integer
    let mut n = cadr(a)
    let a = simplify(cons(list1(q_mplus), cddr(a)))
    if num_gt(n, Fix(0L)) {
      // gamma_incomplete_lower(a+n,z). See DLMF 8.8.7:
      //
      //   gamma_incomplete_lower(a+n,z)
      //     = pochhammer(a,n)*gamma_incomplete_lower(a,z)
      //       -z^a*exp(-z)*sum(gamma(a+n)gamma(a+k+1)*z^k,k,0,n-1)
      sub(
        mul2(
          simplify(mk(q_d_pochhammer, [a, n])),
          simplify(mk(q_p_gamma_incomplete_lower, [a, z])),
        ),
        mul3(power(z, a), power(q_d__pcte, mul2(Fix(-1L), z)), {
          let gamma_a_plus_n = ftake_star(q_p_gamma, [add2(a, n)])
          let index = gensumindex()
          with_special(q_d_simpsum, t, () => simpsum1(
            mul2(
              div(
                gamma_a_plus_n,
                ftake_star(q_p_gamma, [addn_([a, index, Fix(1L)])]),
              ),
              power(z, index),
            ),
            index,
            Fix(0L),
            add2(n, Fix(-1L)),
          ))
        }),
      )
    } else if num_lt(n, Fix(0L)) {
      n = num_neg(n)
      // See DLMF 8.8.8.  For simplicity let g(a,z) =
      // gamma_incomplete_lower(a,z).
      //
      //   g(a-n,z) = gamma(a-n)/gamma(a)*g(a,z)
      //     + z^(a-1)*exp(-z)
      //       * sum(gamma(a-n)/gamma(a-k)*z^(-k),k,0,n-1)
      let gamma_a_n = ftake_star(q_p_gamma, [sub(a, n)])
      let index = gensumindex()
      with_special(q_d_simpsum, t, () => add2(
        mul2(
          div(gamma_a_n, mk(q_p_gamma, [a])),
          simplify(mk(q_p_gamma_incomplete_lower, [a, z])),
        ),
        mul3(
          power(z, sub(a, Fix(1L))),
          power(q_d__pcte, mul2(Fix(-1L), z)),
          simpsum1(
            mul2(
              div(gamma_a_n, ftake_star(q_p_gamma, [sub(a, index)])),
              power(z, mul2(Fix(-1L), index)),
            ),
            index,
            Fix(0L),
            add2(n, Fix(-1L)),
          ),
        ),
      ))
    } else {
      Nil
    }
  } else if gamma_expand &&
    consp(a) &&
    eq(q_rat, caar(a)) &&
    integerp(second(a)) &&
    integerp(third(a)) {
    // gamma_incomplete_lower of (numeric) rational order.  Expand it out
    // so that the resulting order is between 0 and 1.
    let (n, order) = num_floor(num_div(second(a), third(a)))
    // a = n + order where 0 <= order < 1.
    let rat_order = rat(numerator(order), denominator(order))
    if zerop(n) {
      // Nothing to do if the order is already between 0 and 1
      mk_simp(q_p_gamma_incomplete_lower, [a, z])
    } else {
      // Use gamma_h_incomplete(a+n,z) above. and then substitute a=order.
      // This works for n positive or negative.
      let ord = gensym()
      let g = simplify(mk(q_p_gamma_incomplete_lower, [add2(ord, n), z]))
      d_substitute(rat_order, ord, expr=g)
    }
  } else {
    // No expansion so return nil to indicate that
    Nil
  }
}

// ---------------------------------------------------------------------------
// Incomplete Gamma function is a simplifying function

///|
fn simp__pctgamma_incomplete(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=int(2),
      pretty_name=mk(q_p_gamma_incomplete, [q_d_a, q_d_z]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let z = simpcheck(nth(2, form), p__pctsimpflag)
  let b = bind(q_d_simpsum, t)
  defer unbind(b)
  gamma1__simp_gamma_incomplete(form, a, z)
}

///|
fn gamma1__simp_gamma_incomplete(
  form : Value,
  a0 : Value,
  z : Value,
) -> Value raise {
  let mut a = a0
  let give_up = () => eqtest(
    cons(list1(q_p_gamma_incomplete), list2(a0, z)),
    form,
  )
  let args = list2(a, z)
  // Check for specific values
  if zerop1(z).truthy() {
    // gamma_h_incomplete(v,0) is gamma(v) only if the realpart(v) > 0.  If
    // realpart(v) <= 0, gamma_h_incomplete is undefined.  For all other
    // cases, return the noun form.
    let sgn = d_sign(d_realpart(a))
    if gamma1__sign_in(sgn, [q_d_neg, q_d_zero]) {
      simp_domain_error(
        list([
          Str("gamma_h_incomplete: gamma_h_incomplete(~:M,~:M) is undefined."),
          a,
          z,
        ]),
      )
    } else if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      ftake(q_p_gamma, [a])
    } else {
      give_up()
    }
  } else if eq(z, q_d_inf) {
    Fix(0L)
  } else if eq(z, q_d_minf) && eql(a, Fix(0L)) {
    q_d_infinity
  } else if float_numerical_eval_p(args).truthy() {
    // Check for numerical evaluation in Float or Bigfloat precision
    if gamma1__debug() {
      format(t, "~&SIMP-GAMMA-INCOMPLETE in float-numerical-eval-p~%", [])
      |> ignore
    }
    // a and z are Maxima numbers, at least one has a float value
    let mut a = d_float(a)
    let z = d_float(z)
    if num_eq(a, Flo(0.0)) ||
      (num_eq(Fix(0L), num_sub(a, truncate1(a))) && num_lt(a, Flo(0.0))) {
      // a is zero or a negative float representing an integer.  For these
      // cases the numerical routines of gamma-incomplete do not work. Call
      // the numerical routine for the Exponential Integral E(n,z). The
      // routine is called with a positive integer!.
      a = truncate1(a)
      complexify(
        num_mul(expt(z, a), expintegral_e(num_sub(Fix(1L), a), z)),
      )
    } else {
      complexify(gamma_h_incomplete(a, z))
    }
  } else if complex_float_numerical_eval_p(args).truthy() {
    if gamma1__debug() {
      format(
        t,
        "~&SIMP-GAMMA-INCOMPLETE in complex-float-numerical-eval-p~%",
        [],
      )
      |> ignore
    }
    // a and z are Maxima numbers, at least one is a complex value and we
    // have at least one float part
    let mut ca = complex(d_float(d_realpart(a)), i=d_float(d_imagpart(a)))
    let cz = complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z)))
    if num_eq(imagpart(ca), Flo(0.0)) &&
      (
        num_eq(realpart(ca), Flo(0.0)) ||
        (
          num_eq(Fix(0L), num_sub(realpart(ca), truncate1(realpart(ca)))) &&
          num_lt(realpart(ca), Flo(0.0))
        )
      ) {
      // Call expintegral-e. See comment above.
      ca = truncate1(realpart(ca))
      complexify(
        num_mul(expt(cz, ca), expintegral_e(num_sub(Fix(1L), ca), cz)),
      )
    } else {
      complexify(gamma_h_incomplete(ca, cz))
    }
  } else if bigfloat_numerical_eval_p(args).truthy() {
    if gamma1__debug() {
      format(t, "~&SIMP-GAMMA-INCOMPLETE in bigfloat-numerical-eval-p~%", [])
      |> ignore
    }
    let mut a = d_bfloat(a)
    let z = d_bfloat(z)
    if eq(d_sign(a), q_d_zero) ||
      (
        eq(d_sign(sub(a, ftake(q_p_truncate, [a]))), q_d_zero) &&
        eq(d_sign(a), q_d_neg)
      ) {
      // Call bfloat-expintegral-e. See comment above.
      a = ftake(q_p_truncate, [a])
      d_rectform(
        mul2(power(z, a), bfloat_expintegral_e(num_sub(Fix(1L), a), z)),
      )
    } else {
      bfloat_gamma_incomplete(a, z)
    }
  } else if complex_bigfloat_numerical_eval_p(args).truthy() {
    if gamma1__debug() {
      format(
        t,
        "~&SIMP-GAMMA-INCOMPLETE in complex-bigfloat-numerical-eval-p~%",
        [],
      )
      |> ignore
    }
    let ca = add2(
      d_bfloat(d_realpart(a)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(a))),
    )
    let cz = add2(
      d_bfloat(d_realpart(z)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(z))),
    )
    if eq(d_sign(d_imagpart(ca)), q_d_zero) &&
      (
        eq(d_sign(d_realpart(ca)), q_d_zero) ||
        (
          eq(
            d_sign(
              sub(d_realpart(ca), ftake(q_p_truncate, [d_realpart(ca)])),
            ),
            q_d_zero,
          ) &&
          eq(d_sign(d_realpart(ca)), q_d_neg)
        )
      ) {
      // Call bfloat-expintegral-e. See comment above.
      if gamma1__debug() {
        format(
          t,
          "~& bigfloat-numerical-eval-p calls bfloat-expintegral-e~%",
          [],
        )
        |> ignore
      }
      a = ftake(q_p_truncate, [d_realpart(a)])
      d_rectform(
        mul2(power(cz, a), bfloat_expintegral_e(num_sub(Fix(1L), a), cz)),
      )
    } else {
      complex_bfloat_gamma_incomplete(ca, cz)
    }
  } else if symval(q_d_gamma_expand).truthy() && integerp(a) {
    // Check for transformations and argument simplification
    // Integer or a symbol declared to be an integer. Expand in a series.
    let sgn = d_sign(a)
    if eq(sgn, q_d_zero) {
      addn_([
        mul2(
          Fix(-1L),
          simplify(mk(q_p_expintegral_ei, [mul2(Fix(-1L), z)])),
        ),
        mul2(
          gamma1__rat_half(),
          sub(
            simplify(mk(q_p_log, [mul2(Fix(-1L), z)])),
            simplify(mk(q_p_log, [div(Fix(-1L), z)])),
          ),
        ),
        mul2(Fix(-1L), simplify(mk(q_p_log, [z]))),
      ])
    } else if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      mul3(simplify(mk(q_p_gamma, [a])), power(q_d__pcte, mul2(Fix(-1L), z)), {
        let index = gensumindex()
        simpsum1(
          div(
            power(z, index),
            // Simplify gamma, but do not expand to avoid division by zero.
            with_special(q_d_gamma_expand, Nil, () => simplify(
              mk(q_p_gamma, [add2(index, Fix(1L))]),
            )),
          ),
          index,
          Fix(0L),
          sub(a, Fix(1L)),
        )
      })
    } else if gamma1__sign_in(sgn, [q_d_neg, q_d_nz]) {
      sub(
        mul2(
          div(
            power(Fix(-1L), add2(mul2(Fix(-1L), a), Fix(-1L))),
            simplify(mk(q_p_gamma, [add2(mul2(Fix(-1L), a), Fix(1L))])),
          ),
          addn_([
            simplify(mk(q_p_expintegral_ei, [mul2(Fix(-1L), z)])),
            mul2(
              mk_simp(q_rat, [Fix(-1L), Fix(2L)]),
              sub(
                simplify(mk(q_p_log, [mul2(Fix(-1L), z)])),
                simplify(mk(q_p_log, [div(Fix(-1L), z)])),
              ),
            ),
            simplify(mk(q_p_log, [z])),
          ]),
        ),
        mul2(power(q_d__pcte, mul2(Fix(-1L), z)), {
          let index = gensumindex()
          simpsum1(
            div(
              power(z, addn_([index, a, Fix(-1L)])),
              simplify(mk(q_d_pochhammer, [a, index])),
            ),
            index,
            Fix(1L),
            mul2(Fix(-1L), a),
          )
        }),
      )
    } else {
      give_up()
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    max_numeric_ratio_p(a, Fix(2L)).truthy() {
    // We have a half integral order and $gamma_expand is not NIL.
    // We expand in a series with the Erfc function
    let mut ratorder = max_numeric_ratio_p(a, Fix(2L))
    ratorder = num_sub(ratorder, num_div(Fix(1L), Fix(2L)))
    if equal(ratorder, Fix(0L)) {
      mul2(
        power(q_d__pctpi, gamma1__rat_half()),
        simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())])),
      )
    } else if num_gt(ratorder, Fix(0L)) {
      sub(
        mul2(
          simplify(mk(q_p_gamma, [a])),
          simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())])),
        ),
        muln_([
          power(Fix(-1L), sub(ratorder, Fix(1L))),
          power(q_d__pcte, mul2(Fix(-1L), z)),
          power(z, gamma1__rat_half()),
          {
            let index = gensumindex()
            simpsum1(
              mul3(
                // we get more simple results when multiplying with -1
                Fix(-1L),
                simplify(
                  mk(q_d_pochhammer, [
                    sub(gamma1__rat_half(), ratorder),
                    sub(ratorder, add2(index, Fix(1L))),
                  ]),
                ),
                power(mul2(Fix(-1L), z), index),
              ),
              index,
              Fix(0L),
              sub(ratorder, Fix(1L)),
            )
          },
        ]),
      )
    } else if num_lt(ratorder, Fix(0L)) {
      ratorder = num_neg(ratorder)
      sub(
        div(
          mul3(
            power(Fix(-1L), ratorder),
            power(q_d__pctpi, gamma1__rat_half()),
            simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())])),
          ),
          simplify(mk(q_d_pochhammer, [gamma1__rat_half(), ratorder])),
        ),
        mul3(
          power(z, sub(gamma1__rat_half(), ratorder)),
          power(q_d__pcte, mul2(Fix(-1L), z)),
          {
            let index = gensumindex()
            simpsum1(
              div(
                power(z, index),
                simplify(
                  mk(q_d_pochhammer, [
                    sub(gamma1__rat_half(), ratorder),
                    add2(index, Fix(1L)),
                  ]),
                ),
              ),
              index,
              Fix(0L),
              sub(ratorder, Fix(1L)),
            )
          },
        ),
      )
    } else {
      Nil
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    mplusp(a).truthy() &&
    integerp(cadr(a)) {
    // Handle gamma_h_incomplete(a+n, z), where n is a numerical integer
    let mut n = cadr(a)
    let a = simplify(cons(list1(q_mplus), cddr(a)))
    if num_gt(n, Fix(0L)) {
      // See DLMF 8.8.9: https://dlmf.nist.gov/8.8.E9
      //
      //   gamma_h_incomplete(a+n,z) = pochhammer(a,n)*gamma_h_incomplete(a,z)
      //     + z^a*exp(-z)*sum(gamma(a+n)/gamma(a+k+1)*z^k,k,0,n-1)
      add2(
        mul2(
          simplify(mk(q_d_pochhammer, [a, n])),
          simplify(mk(q_p_gamma_incomplete, [a, z])),
        ),
        mul3(power(q_d__pcte, mul2(Fix(-1L), z)), power(z, a), {
          let gamma_a_plus_n = ftake_star(q_p_gamma, [add2(a, n)])
          let index = gensumindex()
          simpsum1(
            mul2(
              div(
                gamma_a_plus_n,
                ftake_star(q_p_gamma, [addn_([a, index, Fix(1L)])]),
              ),
              power(z, index),
            ),
            index,
            Fix(0L),
            add2(n, Fix(-1L)),
          )
        }),
      )
    } else if num_lt(n, Fix(0L)) {
      n = num_neg(n)
      // See http://functions.wolfram.com/06.06.17.0004.01
      //
      //   gamma_h_incomplete(a-n,z) =
      //     (-1)^n*gamma_h_incomplete(a,z)/pochhammer(1-a,n)
      //     -z^(a-n)*sum(z^k/pochhammer(a-n,k+1),k,0,n-1)
      sub(
        div(
          mul2(
            power(Fix(-1L), n),
            simplify(mk(q_p_gamma_incomplete, [a, z])),
          ),
          simplify(mk(q_d_pochhammer, [sub(Fix(1L), a), n])),
        ),
        mul3(power(q_d__pcte, mul2(Fix(-1L), z)), power(z, sub(a, n)), {
          let index = gensumindex()
          simpsum1(
            div(
              power(z, index),
              simplify(mk(q_d_pochhammer, [sub(a, n), add2(index, Fix(1L))])),
            ),
            index,
            Fix(0L),
            sub(n, Fix(1L)),
          )
        }),
      )
    } else {
      Nil
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    consp(a) &&
    eq(q_rat, caar(a)) &&
    integerp(second(a)) &&
    integerp(third(a)) {
    // gamma_h_incomplete of (numeric) rational order.  Expand it out so that
    // the resulting order is between 0 and 1.
    let (n, order) = num_floor(num_div(second(a), third(a)))
    // a = n + order where 0 <= order < 1.
    let rat_order = rat(numerator(order), denominator(order))
    if zerop(n) {
      // Nothing to do if the order is already between 0 and 1
      give_up()
    } else {
      // Use gamma_h_incomplete(a+n,z) above. and then substitute a=order.
      // This works for n positive or negative.
      let ord = gensym()
      let g = simplify(mk(q_p_gamma_incomplete, [add2(ord, n), z]))
      d_substitute(rat_order, ord, expr=g)
    }
  } else if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/06.06.26.0002.01
    //
    //  gamma_h_incomplete(a,z) = gamma(z) - z^a/a*%f[1,1]([a],[a+1},-z)
    //
    // However, hypergeomtric simplifies hypergeometric([a],[a+1],-z) to
    // hypergeometric([1],[a+1],z)*exp(-z).
    sub(
      ftake(q_p_gamma, [a]),
      mul3(
        power(z, a),
        div(Fix(1L), a),
        ftake(q_p_hypergeometric, [
          make_mlist(list1(a)),
          make_mlist(list1(add2(Fix(1L), a))),
          neg(z),
        ]),
      ),
    )
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// Numerical evaluation of the Incomplete Gamma function
//
//  gamma-incomplete (a,z)                - real and complex double float
//  bfloat-gamma-incomplete (a z)         - bigfloat
//  complex-bfloat-gamma-incomplete (a z) - complex bigfloat
//
//  Expansion in a power series for abs(x) < R, where R is
//  *gamma-radius* + real(a) if real(a) > 0 or *gamma-radius* otherwise
//  (A&S 6.5.29), else continued fractions (A&S 6.5.31).  Near the negative
//  real axis use gamma(a,z) = gamma(a) - gamma_lower(a,z), with the
//  continued fraction for gamma_incomplete_lower
//  (http://functions.wolfram.com/06.06.10.0009.01):
//
//   gamma_lower(a,z) = exp(-z) * z^a / cf(a,z)
//
//                -a*z   z    (a+1)*z   2*z  (a+2)*z
//  cf(a,z) = a + ----  ----  -------  ----  -------
//                a+1+  a+2-  a+3+     a+4-   a+5+

///|
/// The numerical evaluation for CL float or complex values a and x.  When
/// the flag regularized is T, the result is divided by gamma(a) and Maxima
/// returns the numerical result for gamma_incomplete_regularized.
fn gamma_h_incomplete(
  a : Value,
  x : Value,
  regularized? : Value = Nil,
) -> Value raise {
  let x = num_add(
    x,
    if complexp(x) {
      Cplx(Flo(0.0), Flo(0.0))
    } else if realp(x) {
      Flo(0.0)
    } else {
      Nil
    },
  )
  // Compute the factor needed to scale the series or continued fraction.
  // This is x^a*exp(-x) or x^a*exp(-x)/gamma(a) depending on whether we
  // want a non-regularized or regularized form.  We want to compute the
  // factor carefully to avoid unnecessary overflow if possible.
  let factor = if regularized.truthy() {
    let r = try_float_computation(
      lfunc("gamma-incomplete-factor", _ => if complexp(a) {
        num_div(num_mul(expt(x, a), lexp(num_neg(x))), gamma_lanczos(a))
      } else {
        // gammafloat is more accurate for real values of a.
        num_div(num_mul(expt(x, a), lexp(num_neg(x))), gammafloat(a))
      }),
    )
    if r.truthy() {
      r
    } else {
      // Easy way failed.  Use logs to compute the result.  This loses some
      // precision, especially for large values of a and/or x because we
      // use many bits to hold the exponent part.
      lexp(
        num_sub(
          num_sub(num_mul(a, llog(x)), x),
          log_gamma_lanczos(if complexp(a) { a } else { complex(a) }),
        ),
      )
    }
  } else {
    let r = try_float_computation(
      lfunc("gamma-incomplete-factor", _ => num_mul(
        expt(x, a),
        lexp(num_neg(x)),
      )),
    )
    if r.truthy() {
      r
    } else {
      // Easy way failed, so use the log form.
      lexp(num_sub(num_mul(a, llog(x)), x))
    }
  }
  let (result, lower_incomplete_tail_p) = p_gamma_h_incomplete(a, x)
  if lower_incomplete_tail_p.truthy() {
    // %gamma-incomplete compute the lower incomplete gamma function, so we
    // need to subtract that from gamma(a), more or less.
    if regularized.truthy() {
      num_sub(Fix(1L), num_mul(result, factor))
    } else if complexp(a) {
      num_sub(gamma_lanczos(a), num_mul(result, factor))
    } else {
      num_sub(gammafloat(a), num_mul(result, factor))
    }
  } else {
    // Continued fraction used.  Just multiply by the factor to get the
    // final result.
    num_mul(factor, result)
  }
}

///|
/// Compute the key part of the gamma incomplete function using either a
/// series expression or a continued fraction expression.  Two values are
/// returned: the value itself and a boolean, indicating what the computed
/// value is.  If the boolean non-NIL, then the computed value is the lower
/// incomplete gamma function.
fn p_gamma_h_incomplete(a : Value, x : Value) -> (Value, Value) raise {
  let gm_maxit = symval(q_ear_gamma_incomplete_maxit)
  let gm_eps = symval(q_ear_gamma_incomplete_eps)
  let gm_min = symval(q_ear_gamma_incomplete_min)
  if gamma1__debug() {
    format(t, "~&GAMMA-INCOMPLETE with ~A and ~A~%", [a, x]) |> ignore
  }
  // The series expansion is done for x within a circle of radius R, where
  // R = *gamma-radius*+(realpart(a)) for realpart(a) > 0 and R =
  // *gamma-radisu* for realpart(a) < 0.  Otherwise a continued fraction is
  // used.
  if num_gt(
      num_abs(x),
      num_add(
        symval(q_ear_gamma_radius),
        if num_gt(realpart(a), Flo(0.0)) {
          realpart(a)
        } else {
          Flo(0.0)
        },
      ),
    ) {
    if num_lt(realpart(x), Fix(0L)) &&
      num_lt(
        num_abs(imagpart(x)),
        num_mul(symval(q_ear_gamma_imag), num_abs(realpart(x))),
      ) {
      // For x near the negative real axis, use the relationship
      // gamma_h_incomplete(a,z) = gamma(a) - gamma_incomplete_lower(a,z),
      // where gamma_incomplete_lower(a,z) is the lower part of the
      // incomplete gamma function.  We can evaluate that using a continued
      // fraction from http://functions.wolfram.com/06.06.10.0009.01.
      //
      // Also note that this appears to be valid for all values of x (real
      // or complex), but we don't want to use this everywhere for
      // gamma_h_incomplete.  Consider what happens for large real x.
      // gamma_h_incomplete(a,x) is small, but gamma_h_incomplete(a,x) =
      // gamma(x) - cf will have large roundoff errors.
      if gamma1__debug() {
        format(
          t,
          "~&GAMMA-INCOMPLETE in continued fractions for lower integral~%",
          [],
        )
        |> ignore
      }
      let a = bf_to(a)
      let x = bf_to(x)
      let v = with_specials(
        [
          (gamma1__q_debug_cf_eval, symval(q_ear_debug_gamma)),
          (gamma1__q_max_cf_iterations, symval(q_ear_gamma_incomplete_maxit)),
        ],
        () => bf_inv(
          bf_lentz(
            lfunc("gamma-incomplete-cf-b", args => bf_add(arg(args, 0), a)),
            lfunc("gamma-incomplete-cf-a", args => {
              let n = arg(args, 0)
              if evenp(n) {
                bf_mul(ash(n, -1), x)
              } else {
                bf_neg(bf_mul(bf_add(a, ash(n, -1)), x))
              }
            }),
          ),
        ),
      )
      (v, t)
    } else {
      // Expansion in continued fractions for gamma_h_incomplete.
      if gamma1__debug() {
        format(t, "~&GAMMA-INCOMPLETE in continued fractions~%", []) |> ignore
      }
      let mut i = 1
      let mut an = num_sub(a, Flo(1.0))
      let mut b = num_add(num_add(Flo(3.0), x), num_neg(a))
      let mut c = num_div(Flo(1.0), gm_min)
      let mut d = {
        let b0 = num_sub(b, Flo(2.0))
        num_div(
          Flo(1.0),
          if num_lt(num_abs(b0), gm_min) {
            gm_min
          } else {
            b0
          },
        )
      }
      let mut h = d
      let mut del : Value = Flo(0.0)
      while true {
        if num_gt(int(i), gm_maxit) {
          merr(
            "gamma_h_incomplete: continued fractions failed for gamma_h_incomplete(~:M, ~:M).",
            [a, x],
          )
          |> ignore
        }
        d = num_add(num_mul(an, d), b)
        if num_lt(num_abs(d), gm_min) {
          d = gm_min
        }
        c = num_add(b, num_div(an, c))
        if num_lt(num_abs(c), gm_min) {
          c = gm_min
        }
        d = num_div(Flo(1.0), d)
        del = num_mul(d, c)
        h = num_mul(h, del)
        if num_lt(num_abs(num_sub(del, Flo(1.0))), gm_eps) {
          // Return nil to indicate we used the continued fraction.
          return (h, Nil)
        }
        i = i + 1
        an = num_mul(int(i), num_sub(a, int(i)))
        b = num_add(b, Flo(2.0))
      }
      (Nil, Nil)
    }
  } else {
    // Expansion in a series
    if gamma1__debug() {
      format(t, "~&GAMMA-INCOMPLETE in series~%", []) |> ignore
    }
    let mut i = 1
    let mut ap = a
    let mut del = num_div(Flo(1.0), a)
    let mut sum = del
    while true {
      if num_gt(int(i), gm_maxit) {
        merr(
          "gamma_h_incomplete: series expansion failed for gamma_h_incomplete(~:M, ~:M).",
          [a, x],
        )
        |> ignore
      }
      if num_lt(num_abs(del), num_mul(num_abs(sum), gm_eps)) {
        if gamma1__debug() {
          format(t, "~&Series converged.~%", []) |> ignore
        }
        // Return T to indicate we used the series and the series is for
        // the integral from 0 to x, not x to inf.
        return (sum, t)
      }
      i = i + 1
      ap = num_add(ap, Flo(1.0))
      del = num_mul(del, num_div(x, ap))
      sum = num_add(sum, del)
    }
    (Nil, Nil)
  }
}

///|
/// `(simplify (list '(mabs) x))`
fn gamma1__mabs(x : Value) -> Value raise {
  simplify(mk(q_mabs, [x]))
}

///|
/// The lower incomplete gamma continued fraction 1/cf(a,x) by LENTZ, for
/// bigfloat (or complex bigfloat) Maxima numbers a and x.
fn gamma1__bf_lower_cf(a0 : Value, x0 : Value) -> Value raise {
  let a = bf_to(a0)
  let x = bf_to(x0)
  maxima_to(
    bf_inv(
      bf_lentz(
        lfunc("gamma-incomplete-cf-b", args => bf_add(arg(args, 0), a)),
        lfunc("gamma-incomplete-cf-a", args => {
          let n = arg(args, 0)
          if evenp(n) {
            bf_mul(ash(n, -1), x)
          } else {
            bf_neg(bf_mul(bf_add(a, ash(n, -1)), x))
          }
        }),
      ),
    ),
  )
}

///|
/// This function is called for a and x real
fn bfloat_gamma_incomplete(a : Value, x : Value) -> Value raise {
  let gm_maxit = symval(q_ear_gamma_incomplete_maxit)
  let gm_eps = power(d_bfloat(Flo(10.0)), num_neg(symval(q_d_fpprec)))
  let gm_min = mul2(gm_eps, gm_eps)
  let b = bind(q_d_ratprint, Nil)
  defer unbind(b)
  // The series expansion is done for x within a circle of radius R, where
  // R = *gamma-radius*+(realpart(a)) for realpart(a) > 0 and R =
  // *gamma-radisu* for realpart(a) < 0.  Otherwise a continued fraction is
  // used.
  if eq(
      d_sign(
        sub(
          gamma1__mabs(x),
          add2(
            symval(q_ear_gamma_radius),
            if eq(d_sign(a), q_d_pos) {
              a
            } else {
              Flo(0.0)
            },
          ),
        ),
      ),
      q_d_pos,
    ) {
    if eq(d_sign(x), q_d_pos) {
      // Expansion in continued fractions of the Incomplete Gamma function
      let mut i = 1
      let mut an = sub(a, Flo(1.0))
      let mut b = addn_([Flo(3.0), x, mul2(Fix(-1L), a)])
      let mut c = div(Flo(1.0), gm_min)
      let mut d = {
        let b0 = sub(b, Flo(2.0))
        div(
          Flo(1.0),
          if eq(d_sign(sub(ftake(q_mabs, [b0]), gm_min)), q_d_neg) {
            gm_min
          } else {
            b0
          },
        )
      }
      let mut h = d
      let mut del : Value = Flo(0.0)
      while true {
        if num_gt(int(i), gm_maxit) {
          merr(
            "gamma_h_incomplete: continued fractions failed for gamma_h_incomplete(~:M, ~:M).",
            [a, x],
          )
          |> ignore
        }
        if gamma1__debug() {
          format(t, "~&in continued fractions:~%", []) |> ignore
          mformat(list([t, Str("~&   : i = ~M~%"), int(i)])) |> ignore
          mformat(list([t, Str("~&   : h = ~M~%"), h])) |> ignore
        }
        d = add2(mul2(an, d), b)
        if eq(d_sign(sub(gamma1__mabs(d), gm_min)), q_d_neg) {
          d = gm_min
        }
        c = add2(b, div(an, c))
        if eq(d_sign(sub(gamma1__mabs(c), gm_min)), q_d_neg) {
          c = gm_min
        }
        d = div(Flo(1.0), d)
        del = mul2(d, c)
        h = mul2(h, del)
        if eq(d_sign(sub(gamma1__mabs(sub(del, Flo(1.0))), gm_eps)), q_d_neg) {
          return mul3(h, power(x, a), power(d_bfloat(q_d__pcte), mul2(Fix(-1L), x)))
        }
        i = i + 1
        an = mul2(int(i), sub(a, int(i)))
        b = add2(b, Flo(2.0))
      }
      Nil
    } else {
      // Expand to multiply everything out.
      d_expand(
        // Expansion in continued fraction for the lower incomplete gamma.
        sub(
          simplify(mk(q_p_gamma, [a])),
          // NOTE: We want (power x a) instead of bigfloat:expt because this
          // preserves how maxima computes x^a when x is negative and a is
          // rational.  For, example (-8)^(1/2) is -2.  bigfloat:expt
          // returns the principal value.
          mul3(
            power(x, a),
            power(d_bfloat(q_d__pcte), mul2(Fix(-1L), x)),
            gamma1__bf_lower_cf(a, x),
          ),
        ),
      )
    }
  } else {
    // Series expansion of the Incomplete Gamma function
    let mut i = 1
    let mut ap = a
    let mut del = div(Flo(1.0), a)
    let mut sum = del
    while true {
      if num_gt(int(i), gm_maxit) {
        merr(
          "gamma_h_incomplete: series expansion failed for gamma_h_incomplete(~:M, ~:M).",
          [a, x],
        )
        |> ignore
      }
      if gamma1__debug() {
        format(t, "~&GAMMA-INCOMPLETE in series:~%", []) |> ignore
        mformat(list([t, Str("~&   : i    = ~M~%"), int(i)])) |> ignore
        mformat(list([t, Str("~&   : ap   = ~M~%"), ap])) |> ignore
        mformat(list([t, Str("~&   : x/ap = ~M~%"), div(x, ap)])) |> ignore
        mformat(list([t, Str("~&   : del  = ~M~%"), del])) |> ignore
        mformat(list([t, Str("~&   : sum  = ~M~%"), sum])) |> ignore
      }
      if eq(
          d_sign(sub(gamma1__mabs(del), mul2(gamma1__mabs(sum), gm_eps))),
          q_d_neg,
        ) {
        if gamma1__debug() {
          mformat(list([t, Str("~&Series converged to ~M.~%"), sum])) |> ignore
        }
        return sub(
          simplify(mk(q_p_gamma, [a])),
          d_rectform(
            mul3(sum, power(x, a), power(d_bfloat(q_d__pcte), mul2(Fix(-1L), x))),
          ),
        )
      }
      i = i + 1
      ap = add2(ap, Flo(1.0))
      del = mul2(del, div(x, ap))
      sum = add2(sum, del)
    }
    Nil
  }
}

///|
fn complex_bfloat_gamma_incomplete(a : Value, x : Value) -> Value raise {
  let gm_maxit = symval(q_ear_gamma_incomplete_maxit)
  let gm_eps = power(d_bfloat(Flo(10.0)), num_neg(symval(q_d_fpprec)))
  let gm_min = mul2(gm_eps, gm_eps)
  let b = bind(q_d_ratprint, Nil)
  defer unbind(b)
  if gamma1__debug() {
    format(t, "~&COMPLEX-BFLOAT-GAMMA-INCOMPLETE~%", []) |> ignore
    format(t, "   : a = ~A~%", [a]) |> ignore
    format(t, "   : x = ~A~%", [x]) |> ignore
  }
  // The series expansion is done for x within a circle of radius R, where
  // R = *gamma-radius*+(realpart(a)) for realpart(a) > 0 and R =
  // *gamma-radisu* for realpart(a) < 0.  Otherwise a continued fraction is
  // used.
  if eq(
      d_sign(
        sub(
          gamma1__mabs(x),
          add2(
            symval(q_ear_gamma_radius),
            if eq(d_sign(d_realpart(a)), q_d_pos) {
              d_realpart(a)
            } else {
              Flo(0.0)
            },
          ),
        ),
      ),
      q_d_pos,
    ) {
    if !(
        eq(d_sign(d_realpart(x)), q_d_neg) &&
        eq(
          d_sign(
            sub(gamma1__mabs(d_imagpart(x)), gamma1__mabs(d_realpart(x))),
          ),
          q_d_neg,
        )
      ) {
      // Expansion in continued fractions of the Incomplete Gamma function
      if gamma1__debug() {
        format(t, "~&in continued fractions:~%", []) |> ignore
      }
      let mut i = 1
      let mut an = sub(a, Flo(1.0))
      let mut b = addn_([Flo(3.0), x, mul2(Fix(-1L), a)])
      let mut c = cdiv(Flo(1.0), gm_min)
      let mut d = {
        let b0 = sub(b, Flo(2.0))
        cdiv(
          Flo(1.0),
          if eq(d_sign(sub(ftake(q_mabs, [b0]), gm_min)), q_d_neg) {
            gm_min
          } else {
            b0
          },
        )
      }
      let mut h = d
      let mut del : Value = Flo(0.0)
      while true {
        if num_gt(int(i), gm_maxit) {
          merr(
            "gamma_h_incomplete: continued fractions failed for gamma_h_incomplete(~:M, ~:M).",
            [a, x],
          )
          |> ignore
        }
        d = add2(cmul(an, d), b)
        if eq(d_sign(sub(gamma1__mabs(d), gm_min)), q_d_neg) {
          d = gm_min
        }
        c = add2(b, cdiv(an, c))
        if eq(d_sign(sub(gamma1__mabs(c), gm_min)), q_d_neg) {
          c = gm_min
        }
        d = cdiv(Flo(1.0), d)
        del = cmul(d, c)
        h = cmul(h, del)
        if eq(d_sign(sub(gamma1__mabs(sub(del, Flo(1.0))), gm_eps)), q_d_neg) {
          // force evaluation of expressions with sin or cos
          return d_bfloat(
            cmul(
              h,
              cmul(
                cpower(x, a),
                cpower(d_bfloat(q_d__pcte), d_bfloat(mul2(Fix(-1L), x))),
              ),
            ),
          )
        }
        i = i + 1
        an = mul2(int(i), sub(a, int(i)))
        b = add2(b, Flo(2.0))
      }
      Nil
    } else {
      // Expand to multiply everything out.
      d_expand(
        // Expansion in continued fraction for the lower incomplete gamma.
        sub(
          d_rectform(simplify(mk(q_p_gamma, [a]))),
          // NOTE: We want (power x a) instead of bigfloat:expt because this
          // preserves how maxima computes x^a when x is negative and a is
          // rational.
          mul3(
            d_rectform(power(x, a)),
            d_rectform(power(d_bfloat(q_d__pcte), mul2(Fix(-1L), x))),
            gamma1__bf_lower_cf(a, x),
          ),
        ),
      )
    }
  } else {
    // Series expansion of the Incomplete Gamma function
    if gamma1__debug() {
      format(t, "~&GAMMA-INCOMPLETE in series:~%", []) |> ignore
    }
    let mut i = 1
    let mut ap = a
    let mut del = cdiv(Flo(1.0), a)
    let mut sum = del
    while true {
      if num_gt(int(i), gm_maxit) {
        merr(
          "gamma_h_incomplete: series expansion failed for gamma_h_incomplete(~:M, ~:M).",
          [a, x],
        )
        |> ignore
      }
      if eq(
          d_sign(sub(gamma1__mabs(del), mul2(gamma1__mabs(sum), gm_eps))),
          q_d_neg,
        ) {
        if gamma1__debug() {
          format(t, "~&Series converged.~%", []) |> ignore
        }
        // force evaluation of expressions with sin or cos
        return d_bfloat(
          sub(
            simplify(mk(q_p_gamma, [a])),
            cmul(
              sum,
              cmul(cpower(x, a), cpower(d_bfloat(q_d__pcte), mul2(Fix(-1L), x))),
            ),
          ),
        )
      }
      i = i + 1
      ap = add2(ap, Flo(1.0))
      del = cmul(del, cdiv(x, ap))
      sum = add2(sum, del)
    }
    Nil
  }
}

// ---------------------------------------------------------------------------
// The Generalized Incomplete Gamma function
//
//   gamma_incomplete_generalized(a, z1, z2) =
//     integrate(t^(a-1)*%e^-t, t, z1, z2)

///|
/// Generalized Incomplete Gamma function has not mirror symmetry for z1 or
/// z2 on the negative real axis.  We support a conjugate-function which
/// test this case.
fn conjugate_gamma_incomplete_generalized(args : Value) -> Value raise {
  let a = first(args)
  let z1 = second(args)
  let z2 = third(args)
  if off_negative_real_axisp(z1).truthy() &&
    off_negative_real_axisp(z2).truthy() {
    // z1 and z2 definitely not on the negative real axis. Mirror symmetry.
    simplify(
      mk(q_p_gamma_incomplete_generalized, [
        simplify(mk(q_d_conjugate, [a])),
        simplify(mk(q_d_conjugate, [z1])),
        simplify(mk(q_d_conjugate, [z2])),
      ]),
    )
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(
      list2(q_d_conjugate, q_simp),
      simplify(mk(q_p_gamma_incomplete_generalized, [a, z1, z2])),
    )
  }
}

///|
/// Generalized Incomplete Gamma function is a simplifying function
fn simp__pctgamma_incomplete_generalized(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 3 {
    wna_err(
      form,
      required_arg_count=int(3),
      pretty_name=mk(q_p_gamma_incomplete_generalized, [q_d_a, q_d_z1, q_d_z2]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let z1 = simpcheck(nth(2, form), p__pctsimpflag)
  let z2 = simpcheck(nth(3, form), p__pctsimpflag)
  let b = bind(q_d_simpsum, t)
  defer unbind(b)
  let give_up = () => eqtest(
    cons(list1(q_p_gamma_incomplete_generalized), list3(a, z1, z2)),
    form,
  )
  let args = list3(a, z1, z2)
  // Check for specific values
  if zerop1(z2).truthy() {
    let sgn = d_sign(d_realpart(a))
    if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      sub(
        simplify(mk(q_p_gamma_incomplete, [a, z1])),
        simplify(mk(q_p_gamma, [a])),
      )
    } else {
      give_up()
    }
  } else if zerop1(z1).truthy() {
    let sgn = d_sign(d_realpart(a))
    if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      sub(
        simplify(mk(q_p_gamma, [a])),
        simplify(mk(q_p_gamma_incomplete, [a, z2])),
      )
    } else {
      give_up()
    }
  } else if zerop1(sub(z1, z2)).truthy() {
    Fix(0L)
  } else if eq(z2, q_d_inf) {
    simplify(mk(q_p_gamma_incomplete, [a, z1]))
  } else if eq(z1, q_d_inf) {
    mul2(Fix(-1L), simplify(mk(q_p_gamma_incomplete, [a, z2])))
  } else if float_numerical_eval_p(args).truthy() {
    // Check for numerical evaluation in Float or Bigfloat precision.  Use
    // the numerical routines of the Incomplete Gamma function
    complexify(
      num_sub(
        gamma_h_incomplete(d_float(a), d_float(z1)),
        gamma_h_incomplete(d_float(a), d_float(z2)),
      ),
    )
  } else if complex_float_numerical_eval_p(args).truthy() {
    let ca = complex(d_float(d_realpart(a)), i=d_float(d_imagpart(a)))
    let cz1 = complex(d_float(d_realpart(z1)), i=d_float(d_imagpart(z1)))
    let cz2 = complex(d_float(d_realpart(z2)), i=d_float(d_imagpart(z2)))
    complexify(num_sub(gamma_h_incomplete(ca, cz1), gamma_h_incomplete(ca, cz2)))
  } else if bigfloat_numerical_eval_p(args).truthy() {
    sub(
      bfloat_gamma_incomplete(d_bfloat(a), d_bfloat(z1)),
      bfloat_gamma_incomplete(d_bfloat(a), d_bfloat(z2)),
    )
  } else if complex_bigfloat_numerical_eval_p(args).truthy() {
    let ca = add2(
      d_bfloat(d_realpart(a)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(a))),
    )
    let cz1 = add2(
      d_bfloat(d_realpart(z1)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(z1))),
    )
    let cz2 = add2(
      d_bfloat(d_realpart(z2)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(z2))),
    )
    sub(
      complex_bfloat_gamma_incomplete(ca, cz1),
      complex_bfloat_gamma_incomplete(ca, cz2),
    )
  } else if symval(q_d_gamma_expand).truthy() &&
    mplusp(a).truthy() &&
    integerp(cadr(a)) {
    // Check for transformations and argument simplification
    // Expand gamma_incomplete_generalized(a+n,z1,z2) with n an integer
    let mut n = cadr(a)
    let a = simplify(cons(list1(q_mplus), cddr(a)))
    if num_gt(n, Fix(0L)) {
      mul2(
        simplify(mk(q_d_pochhammer, [a, n])),
        addn_([
          simplify(mk(q_p_gamma_incomplete_generalized, [a, z1, z2])),
          mul2(power(q_d__pcte, mul2(Fix(-1L), z1)), {
            let index = gensumindex()
            simpsum1(
              div(
                power(z1, addn_([a, index, Fix(-1L)])),
                simplify(mk(q_d_pochhammer, [a, index])),
              ),
              index,
              Fix(1L),
              n,
            )
          }),
          mul3(Fix(-1L), power(q_d__pcte, mul2(Fix(-1L), z2)), {
            let index = gensumindex()
            simpsum1(
              div(
                power(z2, addn_([a, index, Fix(-1L)])),
                simplify(mk(q_d_pochhammer, [a, index])),
              ),
              index,
              Fix(1L),
              n,
            )
          }),
        ]),
      )
    } else if num_lt(n, Fix(0L)) {
      n = num_neg(n)
      addn_([
        mul2(
          div(
            power(Fix(-1L), n),
            d_factor(simplify(mk(q_d_pochhammer, [sub(Fix(1L), a), n]))),
          ),
          simplify(mk(q_p_gamma_incomplete_generalized, [a, z1, z2])),
        ),
        mul3(Fix(-1L), power(q_d__pcte, mul2(Fix(-1L), z1)), {
          let index = gensumindex()
          simpsum1(
            div(
              power(z1, addn_([a, index, num_neg(n), Fix(-1L)])),
              simplify(mk(q_d_pochhammer, [sub(a, n), index])),
            ),
            index,
            Fix(1L),
            n,
          )
        }),
        mul2(power(q_d__pcte, mul2(Fix(-1L), z2)), {
          let index = gensumindex()
          simpsum1(
            div(
              power(z2, addn_([a, index, num_neg(n), Fix(-1L)])),
              simplify(mk(q_d_pochhammer, [sub(a, n), index])),
            ),
            index,
            Fix(1L),
            n,
          )
        }),
      ])
    } else {
      Nil
    }
  } else if symval(q_d_hypergeometric_representation).truthy() {
    // Use the fact that gamma_incomplete_generalized(a,z1,z2) =
    // gamma_h_incomplete(a,z1) - gamma_h_incomplete(a,z2).
    sub(
      ftake(q_p_gamma_incomplete, [a, z1]),
      ftake(q_p_gamma_incomplete, [a, z2]),
    )
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// The Regularized Incomplete Gamma function (A&S 6.5.1)
//
//   gamma_incomplete_regularized(a, z) = gamma_h_incomplete(a, z)/gamma(a)

///|
/// Regularized Incomplete Gamma function has not mirror symmetry for z on
/// the negative real axis.  We support a conjugate-function which test
/// this case.
fn conjugate_gamma_incomplete_regularized(args : Value) -> Value raise {
  let a = first(args)
  let z = second(args)
  if off_negative_real_axisp(z).truthy() {
    // z definitely not on the negative real axis. Mirror symmetry.
    simplify(
      mk(q_p_gamma_incomplete_regularized, [
        simplify(mk(q_d_conjugate, [a])),
        simplify(mk(q_d_conjugate, [z])),
      ]),
    )
  } else {
    // On the negative real axis or no information. Unsimplified.
    list2(
      list2(q_d_conjugate, q_simp),
      simplify(mk(q_p_gamma_incomplete_regularized, [a, z])),
    )
  }
}

///|
/// Regularized Incomplete Gamma function is a simplifying function
fn simp__pctgamma_incomplete_regularized(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=int(2),
      pretty_name=mk(q_p_gamma_incomplete_regularized, [q_d_a, q_d_z]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let z = simpcheck(nth(2, form), p__pctsimpflag)
  let b = bind(q_d_simpsum, t)
  defer unbind(b)
  let give_up = () => eqtest(
    cons(list1(q_p_gamma_incomplete_regularized), list2(a, z)),
    form,
  )
  let args = list2(a, z)
  // Check for specific values
  if zerop1(z).truthy() {
    let sgn = d_sign(d_realpart(a))
    if gamma1__sign_in(sgn, [q_d_neg, q_d_zero]) {
      simp_domain_error(
        list([
          Str(
            "gamma_incomplete_regularized: gamma_incomplete_regularized(~:M,~:M) is undefined.",
          ),
          a,
          z,
        ]),
      )
    } else if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      Fix(1L)
    } else {
      give_up()
    }
  } else if zerop1(a).truthy() ||
    (integer_representation_p(a).truthy() && eq(d_sign(a), q_d_neg)) {
    // 1/gamma(a) is zero for a zero or negative integer.
    Fix(0L)
  } else if eq(z, q_d_inf) {
    Fix(0L)
  } else if float_numerical_eval_p(args).truthy() {
    // Check for numerical evaluation in Float or Bigfloat precision
    // gamma_h_incomplete returns a regularized result
    complexify(gamma_h_incomplete(d_float(a), d_float(z), regularized=t))
  } else if complex_float_numerical_eval_p(args).truthy() {
    let ca = complex(d_float(d_realpart(a)), i=d_float(d_imagpart(a)))
    let cz = complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z)))
    // gamma_h_incomplete returns a regularized result
    complexify(gamma_h_incomplete(ca, cz, regularized=t))
  } else if bigfloat_numerical_eval_p(args).truthy() {
    div(
      bfloat_gamma_incomplete(d_bfloat(a), d_bfloat(z)),
      simplify(mk(q_p_gamma, [d_bfloat(a)])),
    )
  } else if complex_bigfloat_numerical_eval_p(args).truthy() {
    let ca = add2(
      d_bfloat(d_realpart(a)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(a))),
    )
    let cz = add2(
      d_bfloat(d_realpart(z)),
      mul2(q_d__pcti, d_bfloat(d_imagpart(z))),
    )
    d_rectform(
      div(complex_bfloat_gamma_incomplete(ca, cz), simplify(mk(q_p_gamma, [ca]))),
    )
  } else if symval(q_d_gamma_expand).truthy() && integerp(a) {
    // Check for transformations and argument simplification
    // An integer. Expand the expression.
    let sgn = d_sign(a)
    if gamma1__sign_in(sgn, [q_d_pos, q_d_pz]) {
      mul2(power(q_d__pcte, mul2(Fix(-1L), z)), {
        let index = gensumindex()
        simpsum1(
          div(
            power(z, index),
            with_special(q_d_gamma_expand, Nil, () => simplify(
              mk(q_p_gamma, [add2(index, Fix(1L))]),
            )),
          ),
          index,
          Fix(0L),
          sub(a, Fix(1L)),
        )
      })
    } else if gamma1__sign_in(sgn, [q_d_neg, q_d_nz]) {
      Fix(0L)
    } else {
      give_up()
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    max_numeric_ratio_p(a, Fix(2L)).truthy() {
    // We have a half integral order and $gamma_expand is not NIL.
    // We expand in a series with the Erfc function
    let mut ratorder = max_numeric_ratio_p(a, Fix(2L))
    ratorder = num_sub(ratorder, num_div(Fix(1L), Fix(2L)))
    if gamma1__debug() {
      format(t, "~&SIMP-GAMMA-INCOMPLETE-REGULARIZED in RATORDER~%", [])
      |> ignore
      format(t, "~&   : a        = ~A~%", [a]) |> ignore
      format(t, "~&   : ratorder = ~A~%", [ratorder]) |> ignore
    }
    if equal(ratorder, Fix(0L)) {
      simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())]))
    } else if num_gt(ratorder, Fix(0L)) {
      add2(
        simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())])),
        muln_([
          power(Fix(-1L), sub(ratorder, Fix(1L))),
          power(q_d__pcte, mul2(Fix(-1L), z)),
          power(z, gamma1__rat_half()),
          div(Fix(1L), simplify(mk(q_p_gamma, [a]))),
          {
            let index = gensumindex()
            simpsum1(
              mul2(
                power(mul2(Fix(-1L), z), index),
                simplify(
                  mk(q_d_pochhammer, [
                    sub(gamma1__rat_half(), ratorder),
                    sub(ratorder, add2(index, Fix(1L))),
                  ]),
                ),
              ),
              index,
              Fix(0L),
              sub(ratorder, Fix(1L)),
            )
          },
        ]),
      )
    } else if num_lt(ratorder, Fix(0L)) {
      ratorder = num_neg(ratorder)
      add2(
        simplify(mk(q_p_erfc, [power(z, gamma1__rat_half())])),
        muln_([
          Fix(-1L),
          power(q_d__pcte, mul2(Fix(-1L), z)),
          power(z, sub(gamma1__rat_half(), ratorder)),
          inv(simplify(mk(q_p_gamma, [sub(gamma1__rat_half(), ratorder)]))),
          {
            let index = gensumindex()
            simpsum1(
              div(
                power(z, index),
                simplify(
                  mk(q_d_pochhammer, [
                    sub(gamma1__rat_half(), ratorder),
                    add2(index, Fix(1L)),
                  ]),
                ),
              ),
              index,
              Fix(0L),
              sub(ratorder, Fix(1L)),
            )
          },
        ]),
      )
    } else {
      Nil
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    mplusp(a).truthy() &&
    integerp(cadr(a)) {
    if gamma1__debug() {
      format(t, "~&SIMP-GAMMA-INCOMPLETE-REGULARIZED in COND (mplusp)~%", [])
      |> ignore
    }
    let mut n = cadr(a)
    let a = simplify(cons(list1(q_mplus), cddr(a)))
    if num_gt(n, Fix(0L)) {
      add2(
        simplify(mk(q_p_gamma_incomplete_regularized, [a, z])),
        // We factor the second summand.  Some factors vanish and the
        // result is more readable.
        d_factor(
          muln_([
            power(q_d__pcte, mul2(Fix(-1L), z)),
            power(z, add2(a, Fix(-1L))),
            div(Fix(1L), simplify(mk(q_p_gamma, [a]))),
            {
              let index = gensumindex()
              simpsum1(
                div(power(z, index), simplify(mk(q_d_pochhammer, [a, index]))),
                index,
                Fix(1L),
                n,
              )
            },
          ]),
        ),
      )
    } else if num_lt(n, Fix(0L)) {
      n = num_neg(n)
      add2(
        simplify(mk(q_p_gamma_incomplete_regularized, [a, z])),
        // We factor the second summand.
        d_factor(
          muln_([
            Fix(-1L),
            power(q_d__pcte, mul2(Fix(-1L), z)),
            power(z, sub(a, add2(n, Fix(1L)))),
            div(Fix(1L), simplify(mk(q_p_gamma, [add2(a, num_neg(n))]))),
            {
              let index = gensumindex()
              simpsum1(
                div(
                  power(z, index),
                  simplify(mk(q_d_pochhammer, [add2(a, num_neg(n)), index])),
                ),
                index,
                Fix(1L),
                n,
              )
            },
          ]),
        ),
      )
    } else {
      Nil
    }
  } else if symval(q_d_gamma_expand).truthy() &&
    consp(a) &&
    eq(q_rat, caar(a)) &&
    integerp(second(a)) &&
    integerp(third(a)) {
    // gamma_incomplete_regularized of numeric rational order.  Expand it
    // out so that the resulting order is between 0 and 1.  Use
    // gamma_incomplete_regularized(a+n,z) to do the dirty work.
    let (n, order) = num_floor(num_div(second(a), third(a)))
    // a = n + order where 0 <= order < 1.
    let rat_order = rat(numerator(order), denominator(order))
    if zerop(n) {
      // Nothing to do if the order is already between 0 and 1
      give_up()
    } else {
      // Use gamma_incomplete_regularized(a+n,z) above. and then substitute
      // a=order.  This works for n positive or negative.
      let ord = gensym()
      let g = simplify(mk(q_p_gamma_incomplete_regularized, [add2(ord, n), z]))
      d_substitute(rat_order, ord, expr=g)
    }
  } else if symval(q_d_hypergeometric_representation).truthy() {
    // gamma_incomplete_regularized(a,z)
    //   = gamma_h_incomplete(a,z)/gamma(a)
    //   = (gamma(a) - gamma_incomplete_lower(a,z))/gamma(a)
    //   = 1 - gamma_incomplete_lower(a,z)/gamma(a)
    sub(
      Fix(1L),
      div(
        ftake(q_p_gamma_incomplete_lower, [a, z]),
        ftake(q_p_gamma, [a]),
      ),
    )
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// Top-level forms of gamma.lisp

///|
fn gamma1__defgrad(name : Value, grads : Array[Value]) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  putprop(name, list(grads), q_grad) |> ignore
}

///|
fn gamma1__bags() -> Value {
  list3(q_mlist, q_d_matrix, q_mequal)
}

///|
fn init_gamma() -> Unit raise {
  defmvar(
    q_d_erf_representation,
    val=Nil,
    list([
      kw("setting-list"),
      list([Nil, t, q_p_erf, q_p_erfc, q_p_erfi]),
    ]),
  )
  |> ignore
  defmvar(q_d_erf__pctiargs, val=Nil, Nil) |> ignore
  // The changes to the parser to connect the operator !! to
  // double_factorial(z)
  def_mheader(q_d_op_bang_bang, list1(q_p_double_factorial)) |> ignore
  putprop(
    q_d_op_bang_bang,
    lfunc("$!!-led", args => gamma1__bang_bang_led(arg(args, 0), arg(args, 1))),
    q_led,
  )
  |> ignore
  set_lbp_and_rbp(q_d_op_bang_bang, Fix(160L), Nil) |> ignore
  // Pretty-printer display double_factorial(n) as n!! .
  setf_get(
    q_p_double_factorial,
    q_dissym,
    list2(Char('!'), Char('!')),
  )
  |> ignore
  setf_get(
    q_d_double_factorial,
    q_dissym,
    list2(Char('!'), Char('!')),
  )
  |> ignore
  setf_get(q_p_double_factorial, q_dimension, q_dimension_postfix) |> ignore
  setf_get(q_d_double_factorial, q_dimension, q_dimension_postfix) |> ignore
  // Double factorial distributes over bags
  putprop(q_p_double_factorial, gamma1__bags(), q_distribute_over) |> ignore
  // Double factorial has mirror symmetry
  putprop(q_p_double_factorial, t, q_commutes_with_conjugate) |> ignore
  // Differentiation of Double factorial
  gamma1__defgrad(q_p_double_factorial, [
    list1(q_d_z),
    maxima_lit(
      "(double_factorial(z)*((%pi*log(2/%pi)*sin(%pi*z))/2+psi[0](z/2+1)+log(2)))/2",
    ),
  ])
  // *debug-gamma* is a literal defvar (gen_vars).
  // Incomplete Gamma distributes over bags
  putprop(q_p_gamma_incomplete, gamma1__bags(), q_distribute_over)
  |> ignore
  putprop(
    q_p_gamma_incomplete,
    q_conjugate_gamma_incomplete,
    q_conjugate_function,
  )
  |> ignore
  // Derivative of the Incomplete Gamma function
  gamma1__defgrad(q_p_gamma_incomplete, [
    list2(q_d_a, q_d_z),
    // wrt a
    lfunc("gamma_h_incomplete-grad-a", args => gamma1__gamma_incomplete_grad_a(
      arg(args, 0),
      arg(args, 1),
    )),
    // wrt z
    maxima_lit("-(%e^-z*z^(a-1))"),
  ])
  // Integral of the Incomplete Gamma function
  putprop(
    q_p_gamma_incomplete,
    lread(
      "((a z) nil ((mplus) ((mtimes) -1 ((%gamma_h_incomplete) ((mplus) 1 a) z)) ((mtimes) ((%gamma_h_incomplete) a z) z)))",
    ),
    q_integral,
  )
  |> ignore
  putprop(
    q_p_gamma_incomplete,
    q_simplim_pctgamma_incomplete,
    q_simplim_pctfunction,
  )
  |> ignore
  // Lower incomplete gamma
  putprop(q_p_gamma_incomplete_lower, gamma1__bags(), q_distribute_over)
  |> ignore
  gamma1__defgrad(q_p_gamma_incomplete_lower, [
    list2(q_d_a, q_d_z),
    // wrt a: involves functions that Maxima doesn't know.
    Nil,
    // wrt z
    maxima_lit("z^(a-1)*exp(-z)"),
  ])
  // Numerical evaluation parameters
  defvar_init(
    q_ear_gamma_incomplete_eps,
    num_mul(Fix(2L), symval(q_n_plusflonum_epsilon_plus)),
  )
  // Generalized Incomplete Gamma function
  putprop(
    q_p_gamma_incomplete_generalized,
    q_conjugate_gamma_incomplete_generalized,
    q_conjugate_function,
  )
  |> ignore
  putprop(
    q_p_gamma_incomplete_generalized,
    gamma1__bags(),
    q_distribute_over,
  )
  |> ignore
  gamma1__defgrad(q_p_gamma_incomplete_generalized, [
    list3(q_d_a, q_d_z1, q_d_z2),
    // The derivative wrt a in terms of hypergeometric_regularized 2F2
    // function and the Generalized Incomplete Gamma function
    // (functions.wolfram.com)
    maxima_lit(
      "gamma_incomplete_generalized(a,0,z2)*log(z2) -gamma(a)^2*hypergeometric_regularized([a,a],[a+1,a+1],-z2)*z2^a -gamma_incomplete_generalized(a,0,z1)*log(z1) +gamma(a)^2*hypergeometric_regularized([a,a],[a+1,a+1],-z1)*z1^a",
    ),
    // The derivative wrt z1
    maxima_lit("-(z1^(a-1)*%e^-z1)"),
    // The derivative wrt z2
    maxima_lit("z2^(a-1)*%e^-z2"),
  ])
  // Regularized Incomplete Gamma function
  putprop(
    q_p_gamma_incomplete_regularized,
    q_conjugate_gamma_incomplete_regularized,
    q_conjugate_function,
  )
  |> ignore
  putprop(
    q_p_gamma_incomplete_regularized,
    gamma1__bags(),
    q_distribute_over,
  )
  |> ignore
  gamma1__defgrad(q_p_gamma_incomplete_regularized, [
    list2(q_d_a, q_d_z),
    // The derivative wrt a in terms of hypergeometric_regularized 2F2
    // function and the Regularized Generalized Incomplete Gamma function
    // (functions.wolfram.com)
    maxima_lit(
      "'gamma_incomplete_generalized_regularized(a,z,0)*(log(z)-psi[0](a)) +gamma(a)*hypergeometric_regularized([a,a],[a+1,a+1],-z)*z^a",
    ),
    // The derivative wrt z
    maxima_lit("-((%e^-z*z^(a-1))/gamma(a))"),
  ])
  // The rest of gamma.lisp
  gamma2__init()
  gamma3__init()
}
