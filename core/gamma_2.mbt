// Port of src/gamma.lisp, part 2: log_gamma, erf, erf_generalized, erfc,
// erfi, inverse_erf, inverse_erfc and the Newton iterations used for the
// inverse error functions.  (Lines ~1796-2986 of gamma.lisp.)

// ---------------------------------------------------------------------------
// Logarithm of the Gamma function

///|
fn d_log_gamma(z : Value) -> Value raise {
  simplify(mk(q_p_log_gamma, [z]))
}

///|
/// integrate(log_gamma(x),x) = psi[-2](x)
fn log_gamma_integral(x : Value) -> Value raise {
  take(list1(q_mqapply), [take(list1(q_d_psi), [Fix(-2L)]), x])
}

///|
fn simp_log_gamma(expr : Value, z : Value, simpflag : Value) -> Value raise {
  ignore(z)
  oneargcheck(expr) |> ignore
  let z = simpcheck(cadr(expr), simpflag)
  if mnump(z).truthy() &&
    (
      zerop1(z).truthy() ||
      (
        eq(d_sign(z), q_d_neg) &&
        zerop1(sub(z, ftake(q_p_truncate, [z]))).truthy()
      )
    ) {
    // We have zero, a negative integer or a float or bigfloat representation.
    simp_domain_error(
      list([Str("log_gamma: log_gamma(~:M) is undefined."), z]),
    )
  } else if eq(z, q_d_inf) {
    q_d_inf
  } else if float_numerical_eval_p(list1(z)).truthy() {
    complexify(log_gamma_lanczos(complex(d_float(z), i=Fix(0L))))
  } else if complex_float_numerical_eval_p(list1(z)).truthy() {
    complexify(
      log_gamma_lanczos(
        complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z))),
      ),
    )
  } else if bigfloat_numerical_eval_p(list1(z)).truthy() {
    bfloat_log_gamma(d_bfloat(z))
  } else if complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    complex_bfloat_log_gamma(
      add2(d_bfloat(d_realpart(z)), mul2(q_d__pcti, d_bfloat(d_imagpart(z)))),
    )
  } else if integerp(z) {
    // Transform to Logarithm of Factorial for integer values
    simplify(mk(q_p_log, [simplify(mk(q_mfactorial, [num_sub(z, Fix(1L))]))]))
  } else {
    eqtest(mk(q_p_log_gamma, [z]), expr)
  }
}

///|
let gamma2__lanczos_c : Array[Double] = [
  0.99999999999999709182, 57.156235665862923517, -59.597960355475491248, 14.136097974741747174,
  -0.49191381609762019978, 0.33994649984811888699e-4, 0.46523628927048575665e-4, -0.98374475304879564677e-4,
  0.15808870322491248884e-3, -0.21026444172410488319e-3, 0.21743961811521264320e-3, -0.16431810653676389022e-3,
  0.84418223983852743293e-4, -0.26190838401581408670e-4, 0.36899182659531622704e-5,
]

///|
/// The Logarithm of the Gamma function for a CL (complex) float argument.
fn log_gamma_lanczos(z : Value) -> Value raise {
  let c = gamma2__lanczos_c
  let pi : Value = Flo(@math.PI)
  let i_one : Value = Cplx(Fix(0L), Fix(1L))
  if minusp(realpart(z)) {
    let z = num_neg(z)
    let fl = num_floor(realpart(z)).0
    let a = num_prod([
      num_neg(pi),
      i_one,
      num_abs(fl),
      num_sub(Fix(1L), num_abs(signum(imagpart(z)))),
    ])
    let b = llog(pi)
    let cc = num_neg(llog(num_neg(z)))
    let d = num_neg(llog(lsin(num_mul(pi, num_sub(z, num_floor(realpart(z)).0)))))
    let e = num_prod([pi, i_one, num_floor(realpart(z)).0, signum(imagpart(z))])
    num_sub(
      num_add(num_add(num_add(num_add(a, b), cc), d), e),
      log_gamma_lanczos(z),
    )
  } else {
    let z = num_sub(z, Fix(1L))
    // 1/2 and 607/128 are exactly representable, so adding the doubles is
    // the same as CL's rational contagion.
    let zh = num_add(z, Flo(0.5))
    let zgh = num_add(zh, Flo(4.7421875))
    let lnzp = num_mul(num_div(zh, Fix(2L)), llog(zgh))
    let mut ss : Value = Flo(0.0)
    let mut pp = c.length() - 1
    while pp >= 1 {
      ss = num_add(ss, num_div(Flo(c[pp]), num_add(z, int(pp))))
      pp = pp - 1
    }
    num_add(
      num_add(
        llog(lsqrt(Flo(2.0 * @math.PI))),
        llog(num_add(ss, Flo(c[0]))),
      ),
      num_add(num_neg(zgh), num_mul(Fix(2L), lnzp)),
    )
  }
}

///|
/// Common reflection term for bfloat-log-gamma and complex-bfloat-log-gamma.
/// `z` is already negated; `sinarg` builds pi*(z - floor(realpart(z))).
fn gamma2__log_gamma_reflect(
  z : Value,
  bigfloat_pct_pi : Value,
  sinarg : Value,
) -> Value raise {
  addn_([
    muln_([
      Fix(-1L),
      bigfloat_pct_pi,
      q_d__pcti,
      simplify(mk(q_mabs, [simplify(mk(q_d_floor, [d_realpart(z)]))])),
      sub(
        Fix(1L),
        simplify(mk(q_mabs, [simplify(mk(q_p_signum, [d_imagpart(z)]))])),
      ),
    ]),
    simplify(mk(q_p_log, [bigfloat_pct_pi])),
    mul2(Fix(-1L), simplify(mk(q_p_log, [mul2(Fix(-1L), z)]))),
    mul2(
      Fix(-1L),
      simplify(mk(q_p_log, [simplify(mk(q_p_sin, [sinarg]))])),
    ),
    muln_([
      bigfloat_pct_pi,
      q_d__pcti,
      simplify(mk(q_d_floor, [d_realpart(z)])),
      simplify(mk(q_p_signum, [d_imagpart(z)])),
    ]),
  ])
}

///|
fn bfloat_log_gamma(z : Value) -> Value raise {
  with_special(q_d_ratprint, Nil, () => {
    let bigfloat_pct_pi = d_bfloat(q_d__pctpi)
    if eq(d_sign(z), q_d_neg) {
      let z = mul2(Fix(-1L), z)
      sub(
        gamma2__log_gamma_reflect(
          z,
          bigfloat_pct_pi,
          mul2(
            bigfloat_pct_pi,
            sub(z, simplify(mk(q_d_floor, [d_realpart(z)]))),
          ),
        ),
        bfloat_log_gamma(z),
      )
    } else {
      let k = num_mul(
        Fix(2L),
        num_add(
          Fix(1L),
          d_entier(num_mul(Flo(0.41), symval(q_d_fpprec))),
        ),
      )
      let mut m = d_bfloat(symval(q_ear_bigfloatone))
      let z_plus_k = addn_([z, k, Fix(-1L)])
      let y = power(z_plus_k, Fix(2L))
      let mut x = d_bfloat(symval(q_ear_bigfloatzero))
      let n = to_int(num_div(k, Fix(2L)))
      for i in 0..<n {
        let ii = num_mul(Fix(2L), num_add(int(i), Fix(1L)))
        m = muln_([m, addn_([z, ii, Fix(-2L)]), addn_([z, ii, Fix(-1L)])])
        let kmii = num_add(k, num_neg(ii))
        x = div(
          add2(
            x,
            div(
              ftake(q_p_bern, [num_add(kmii, Fix(2L))]),
              num_mul(num_add(kmii, Fix(1L)), num_add(kmii, Fix(2L))),
            ),
          ),
          y,
        )
      }
      addn_([
        div(
          simplify(
            mk(q_p_log, [muln_([Fix(2L), bigfloat_pct_pi, z_plus_k])]),
          ),
          Fix(2L),
        ),
        mul2(
          z_plus_k,
          addn_([simplify(mk(q_p_log, [z_plus_k])), x, Fix(-1L)]),
        ),
        mul2(Fix(-1L), simplify(mk(q_p_log, [m]))),
      ])
    }
  })
}

///|
fn complex_bfloat_log_gamma(z : Value) -> Value raise {
  with_special(q_d_ratprint, Nil, () => {
    let bigfloat_pct_pi = d_bfloat(q_d__pctpi)
    if eq(d_sign(d_realpart(z)), q_d_neg) {
      let z = mul2(Fix(-1L), z)
      sub(
        gamma2__log_gamma_reflect(
          z,
          bigfloat_pct_pi,
          cmul(
            bigfloat_pct_pi,
            sub(z, simplify(mk(q_d_floor, [d_realpart(z)]))),
          ),
        ),
        complex_bfloat_log_gamma(z),
      )
    } else {
      let k = num_mul(
        Fix(2L),
        num_add(
          Fix(1L),
          d_entier(num_mul(Flo(0.41), symval(q_d_fpprec))),
        ),
      )
      let mut logm = d_bfloat(symval(q_ear_bigfloatzero))
      let z_plus_k = addn_([z, k, Fix(-1L)])
      let y = d_rectform(power(z_plus_k, Fix(2L)))
      let mut x = d_bfloat(symval(q_ear_bigfloatzero))
      let n = to_int(num_div(k, Fix(2L)))
      for i in 0..<n {
        let ii = num_mul(Fix(2L), num_add(int(i), Fix(1L)))
        logm = d_rectform(
          addn_([
            logm,
            ftake(q_p_log, [addn_([z, ii, Fix(-2L)])]),
            ftake(q_p_log, [addn_([z, ii, Fix(-1L)])]),
          ]),
        )
        let kmii = num_add(k, num_neg(ii))
        x = d_rectform(
          div(
            add2(
              x,
              div(
                ftake(q_p_bern, [num_add(kmii, Fix(2L))]),
                num_mul(num_add(kmii, Fix(1L)), num_add(kmii, Fix(2L))),
              ),
            ),
            y,
          ),
        )
      }
      d_rectform(
        addn_([
          div(
            simplify(
              mk(q_p_log, [muln_([Fix(2L), bigfloat_pct_pi, z_plus_k])]),
            ),
            Fix(2L),
          ),
          mul2(
            z_plus_k,
            addn_([simplify(mk(q_p_log, [z_plus_k])), x, Fix(-1L)]),
          ),
          neg(logm),
        ]),
      )
    }
  })
}

// ---------------------------------------------------------------------------
// The Error function Erf(z)

///|
fn erf_hypergeometric(z : Value) -> Value raise {
  // See A&S 7.1.21 or http://functions.wolfram.com/06.25.26.0001.01
  muln_([
    Fix(2L),
    z,
    power(q_d__pctpi, mk_simp(q_rat, [Fix(-1L), Fix(2L)])),
    ftake(q_p_hypergeometric, [
      make_mlist(list1(symval(q_n1_sl_sl2))),
      make_mlist(list1(symval(q_n3_sl_sl2))),
      mul2(Fix(-1L), power(z, Fix(2L))),
    ]),
  ])
}

///|
/// The common one-argument def-simplifier prologue.
fn gamma2__simp_arg1(
  form : Value,
  noun : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  if length(cdr(form)) != 1 {
    wna_err(form, required_arg_count=int(1), pretty_name=mk(noun, [q_d_z]))
    |> ignore
  }
  simpcheck(nth(1, form), p__pctsimpflag)
}

///|
/// Is the inner function's argument real with lo < x < hi?
fn gamma2__real_between(arg : Value, lo : Value, hi : Value) -> Bool raise {
  let tr = trisplit(arg)
  let rpart = car(tr)
  let ipart = cdr(tr)
  eq(meqp(Fix(0L), ipart), t) &&
  eq(mgrp(rpart, lo), t) &&
  eq(mgrp(hi, rpart), t)
}

///|
fn simp__pcterf(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = gamma2__simp_arg1(form, q_p_erf, p__pctsimpflag)
  let give_up = () => eqtest(mk(q_p_erf, [z]), form)
  if zerop1(z).truthy() {
    return z
  }
  if eq(z, q_d_inf) {
    return Fix(1L)
  }
  if eq(z, q_d_minf) {
    return Fix(-1L)
  }
  // erf(inverse_erf(x)) = x for -1 < x < 1
  if listp(z) &&
    is_op(z, q_p_inverse_erf) &&
    gamma2__real_between(cadr(z), Fix(-1L), Fix(1L)) {
    return cadr(z)
  }
  // Check for numerical evaluation
  if float_numerical_eval_p(list1(z)).truthy() {
    return bf_bf_erf(d_float(z))
  }
  if complex_float_numerical_eval_p(list1(z)).truthy() {
    return complexify(
      bf_bf_erf(complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z)))),
    )
  }
  if bigfloat_numerical_eval_p(list1(z)).truthy() {
    return maxima_to(bf_bf_erf(bf_to(d_bfloat(z))))
  }
  if complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    return maxima_to(
      bf_bf_erf(
        bf_to(
          add2(d_bfloat(d_realpart(z)), mul2(q_d__pcti, d_bfloat(d_imagpart(z)))),
        ),
      ),
    )
  }
  // Argument simplification
  let tz = taylorize(mop(form), second(form))
  if tz.truthy() {
    return tz
  }
  if symval(q_d_erf__pctiargs).truthy() &&
    !symval(q_d_erf_representation).truthy() &&
    multiplep(z, q_d__pcti).truthy() {
    return mul2(q_d__pcti, simplify(mk(q_p_erfi, [coeff(z, q_d__pcti, Fix(1L))])))
  }
  let rz = apply_reflection_simp(mop(form), z, b=symval(q_d_trigsign))
  if rz.truthy() {
    return rz
  }
  // Representation through more general functions
  if symval(q_d_hypergeometric_representation).truthy() {
    return erf_hypergeometric(z)
  }
  // Transformation to Erfc or Erfi
  let rep = symval(q_d_erf_representation)
  if rep.truthy() && !eq(rep, q_d_erf) {
    if eq(rep, q_p_erfc) {
      return sub(Fix(1L), take(list1(q_p_erfc), [z]))
    } else if eq(rep, q_p_erfi) {
      return muln_([
        Fix(-1L),
        q_d__pcti,
        take(list1(q_p_erfi), [mul2(q_d__pcti, z)]),
      ])
    } else {
      return give_up()
    }
  }
  give_up()
}

///|
fn erf(z : Value) -> Value raise {
  // We use the slatec routine for float values.
  Flo(@slatec.derf(to_double(lfloat(z))))
}

///|
/// erf(z) = sqrt(z^2)/z*(1 - gamma_incomplete(1/2,z^2)/sqrt(%pi)) for a CL
/// complex z.
fn complex_erf(z : Value) -> Value raise {
  let sgn : Value = if num_lt(realpart(z), Flo(0.0)) ||
    (num_eq(realpart(z), Flo(0.0)) && num_lt(imagpart(z), Flo(0.0))) {
    Fix(-1L)
  } else {
    Fix(1L)
  }
  let result = num_mul(
    sgn,
    num_sub(
      Flo(1.0),
      num_mul(
        num_inv(Flo(@math.PI.sqrt())),
        gamma_incomplete(Flo(0.5), num_mul(z, z)),
      ),
    ),
  )
  if num_eq(imagpart(z), Flo(0.0)) {
    // Pure real argument, the result is real
    complex(realpart(result), i=Flo(0.0))
  } else if num_eq(realpart(z), Flo(0.0)) {
    // Pure imaginary argument, the result is pure imaginary
    complex(Flo(0.0), i=imagpart(result))
  } else {
    result
  }
}

///|
fn bfloat_erf(z : Value) -> Value raise {
  // Warning!  This has round-off problems when abs(z) is very small.
  // The argument is real, the result is real too
  d_realpart(
    mul2(
      simplify(mk(q_p_signum, [z])),
      sub(
        Fix(1L),
        mul2(
          div(Fix(1L), power(d_bfloat(q_d__pctpi), symval(q_ear_bfhalf))),
          bfloat_gamma_incomplete(
            symval(q_ear_bfhalf),
            d_bfloat(power(z, Fix(2L))),
          ),
        ),
      ),
    ),
  )
}

///|
fn complex_bfloat_erf(z : Value) -> Value raise {
  // Warning!  This has round-off problems when abs(z) is very small.
  with_special(q_d_ratprint, Nil, () => {
    let result = cmul(
      cdiv(cpower(cpower(z, Fix(2L)), symval(q_ear_bfhalf)), z),
      sub(
        Fix(1L),
        cmul(
          div(Fix(1L), power(d_bfloat(q_d__pctpi), symval(q_ear_bfhalf))),
          complex_bfloat_gamma_incomplete(
            symval(q_ear_bfhalf),
            d_bfloat(cpower(z, Fix(2L))),
          ),
        ),
      ),
    )
    if zerop1(d_imagpart(z)).truthy() {
      // Pure real argument, the result is real
      d_realpart(result)
    } else if zerop1(d_realpart(z)).truthy() {
      // Pure imaginary argument, the result is pure imaginary
      mul2(q_d__pcti, d_imagpart(result))
    } else {
      result
    }
  })
}

///|
/// Erf(z) for all z.  Z must be a CL real or complex number or a BIGFLOAT or
/// COMPLEX-BIGFLOAT object.  The result will be of the same type as Z.
fn bf_bf_erf(z : Value) -> Value raise {
  if realp(z) {
    // Use Slatec derf, which should be faster than the series.
    erf(z)
  } else if bf_le(bf_abs(z), Flo(0.476936)) {
    // Use the series A&S 7.1.5 for small x:
    //
    // erf(z) = 2*z/sqrt(%pi) * sum((-1)^n*z^(2*n)/n!/(2*n+1), n, 0, inf)
    //
    // The threshold is approximately erf(x) = 0.5.
    let z2 = bf_mul(z, z)
    bf_div(
      bf_mul(
        bf_mul(Fix(2L), z),
        bf_sum_power_series(
          z2,
          lfunc("bf-erf-term", args => {
            let k = args[0]
            let k2 = bf_add(k, k)
            bf_neg(
              bf_op_sl(bf_sub(k2, Fix(1L)), list2(k, bf_add(k2, Fix(1L)))),
            )
          }),
        ),
      ),
      bf_sqrt(bf_p_pi(z)),
    )
  } else if realp(z) {
    erf(z)
  } else if complexp(z) {
    complex_erf(z)
  } else if bf_is_bigfloat(z) {
    bf_bigfloat(d_bfloat(d_expand(bfloat_erf(maxima_to(z)))))
  } else if bf_is_complex_bigfloat(z) {
    bf_bigfloat(d_bfloat(d_expand(complex_bfloat_erf(maxima_to(z)))))
  } else {
    raise LispError::SimpleError("BF-ERF: fell through ETYPECASE")
  }
}

///|
fn bf_bf_erfc(z : Value) -> Value raise {
  // erfc(z) = 1/sqrt(pi)*gamma_incomplete_tail(1/2,z^2)       realpart(z) > 0
  //         = 2 - 1/sqrt(pi)*gamma_incomplete(1/2,z^2)        realpart(z) < 0
  let gamma_inc = (z : Value) => if numberp(z) {
    gamma_incomplete(Flo(0.5), z)
  } else if bf_is_bigfloat(z) {
    bf_to(
      d_bfloat(
        bfloat_gamma_incomplete(d_bfloat(symval(q_n1_sl_sl2)), maxima_to(z)),
      ),
    )
  } else if bf_is_complex_bigfloat(z) {
    bf_to(
      d_bfloat(
        complex_bfloat_gamma_incomplete(
          d_bfloat(symval(q_n1_sl_sl2)),
          maxima_to(z),
        ),
      ),
    )
  } else {
    raise LispError::SimpleError("BF-ERFC: fell through ETYPECASE")
  }
  let pos = if bf_zerop(bf_realpart(z)) {
    !bf_minusp(bf_imagpart(z))
  } else {
    bf_gt(bf_realpart(z), Fix(0L))
  }
  if pos {
    bf_div(gamma_inc(bf_mul(z, z)), bf_sqrt(bf_p_pi(z)))
  } else {
    bf_sub(Fix(2L), bf_div(gamma_inc(bf_mul(z, z)), bf_sqrt(bf_p_pi(z))))
  }
}

// ---------------------------------------------------------------------------
// The Generalized Error function Erf(z1,z2)

///|
fn gamma2__is_inf(z : Value) -> Bool raise {
  eq(z, q_d_inf) ||
  alike1(z, mk(q_mtimes, [Fix(-1L), q_d_minf])).truthy()
}

///|
fn gamma2__is_minf(z : Value) -> Bool raise {
  eq(z, q_d_minf) ||
  alike1(z, mk(q_mtimes, [Fix(-1L), q_d_inf])).truthy()
}

///|
fn simplim_pcterf_generalized(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the arguments.
  let z1 = limit(cadr(expr), var_, val, q_think)
  let z2 = limit(caddr(expr), var_, val, q_think)
  let is_zab = (z : Value) => eq(z, q_d_zeroa) || eq(z, q_d_zerob)
  if gamma2__is_inf(z2) {
    sub(Fix(1L), take(list1(q_p_erf), [z1]))
  } else if gamma2__is_minf(z2) {
    sub(mul2(Fix(-1L), take(list1(q_p_erf), [z1])), Fix(1L))
  } else if gamma2__is_inf(z1) {
    sub(take(list1(q_p_erf), [z2]), Fix(1L))
  } else if gamma2__is_minf(z1) {
    add2(take(list1(q_p_erf), [z2]), Fix(1L))
  } else if !eq(z1, z2) && (is_zab(z1) || is_zab(z2)) {
    // erf_generalized(z1, z2) is erf(z2) - erf(z1), and erf maps an
    // infinitesimal to an infinitesimal of the same sign, so negating one
    // exchanges zeroa and zerob.
    add2(
      if is_zab(z2) {
        z2
      } else {
        take(list1(q_p_erf), [z2])
      },
      if eq(z1, q_d_zeroa) {
        q_d_zerob
      } else if eq(z1, q_d_zerob) {
        q_d_zeroa
      } else {
        mul2(Fix(-1L), take(list1(q_p_erf), [z1]))
      },
    )
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(mk(q_p_erf_generalized, [z1, z2]))
  }
}

///|
fn simp__pcterf_generalized(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=int(2),
      pretty_name=mk(q_p_erf_generalized, [q_d_z1, q_d_z2]),
    )
    |> ignore
  }
  let z1 = simpcheck(nth(1, form), p__pctsimpflag)
  let z2 = simpcheck(nth(2, form), p__pctsimpflag)
  let erf1 = (x : Value) => take(list1(q_p_erf), [x])
  if zerop1(z1).truthy() && zerop1(z2).truthy() {
    Fix(0L)
  } else if zerop1(z1).truthy() {
    erf1(z2)
  } else if zerop1(z2).truthy() {
    mul2(Fix(-1L), erf1(z1))
  } else if gamma2__is_inf(z2) {
    sub(Fix(1L), erf1(z1))
  } else if gamma2__is_minf(z2) {
    sub(mul2(Fix(-1L), erf1(z1)), Fix(1L))
  } else if gamma2__is_inf(z1) {
    sub(erf1(z2), Fix(1L))
  } else if gamma2__is_minf(z1) {
    add2(erf1(z2), Fix(1L))
  } else if float_numerical_eval_p(list2(z1, z2)).truthy() {
    // Check for numerical evaluation. Use erf(z1,z2) = erf(z2)-erf(z1)
    num_sub(bf_bf_erf(d_float(z2)), bf_bf_erf(d_float(z1)))
  } else if complex_float_numerical_eval_p(list2(z1, z2)).truthy() {
    complexify(
      num_sub(
        bf_bf_erf(complex(d_float(d_realpart(z2)), i=d_float(d_imagpart(z2)))),
        bf_bf_erf(complex(d_float(d_realpart(z1)), i=d_float(d_imagpart(z1)))),
      ),
    )
  } else if bigfloat_numerical_eval_p(list2(z1, z2)).truthy() {
    maxima_to(
      bf_sub(
        bf_bf_erf(bf_to(d_bfloat(z2))),
        bf_bf_erf(bf_to(d_bfloat(z1))),
      ),
    )
  } else if complex_bigfloat_numerical_eval_p(list2(z1, z2)).truthy() {
    let cbf = (z : Value) => bf_to(
      add2(d_bfloat(d_realpart(z)), mul2(q_d__pcti, d_bfloat(d_imagpart(z)))),
    )
    maxima_to(bf_sub(bf_bf_erf(cbf(z2)), bf_bf_erf(cbf(z1))))
  } else if symval(q_d_trigsign).truthy() &&
    great(mul2(Fix(-1L), z1), z1).truthy() &&
    great(mul2(Fix(-1L), z2), z2).truthy() {
    // Argument simplification
    mul2(
      Fix(-1L),
      simplify(
        mk(q_p_erf_generalized, [mul2(Fix(-1L), z1), mul2(Fix(-1L), z2)]),
      ),
    )
  } else if symval(q_d_hypergeometric_representation).truthy() {
    sub(erf_hypergeometric(z2), erf_hypergeometric(z1))
  } else if symval(q_d_erf_representation).truthy() {
    sub(simplify(mk(q_p_erf, [z2])), simplify(mk(q_p_erf, [z1])))
  } else {
    eqtest(cons(list1(q_p_erf_generalized), list2(z1, z2)), form)
  }
}

// ---------------------------------------------------------------------------
// The Complementary Error function Erfc(z)

///|
fn simplim_pcterfc(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    Fix(0L)
  } else if eq(z, q_d_minf) {
    Fix(2L)
  } else if eq(z, q_d_infinity) {
    // parallel to code in simplim%erf-%tanh
    let tr = trisplit(cadr(expr))
    let rpart = car(tr)
    let ipart = cdr(tr)
    let rlim = limit(rpart, var_, val, q_think)
    let mut ans = limit(
      m_star(list2(rpart, m_hatt(ipart, Fix(-1L)))),
      var_,
      val,
      q_think,
    )
    ans = d_asksign(m_plus(list2(mk(q_mabs, [ans]), Fix(-1L))))
    if eq(ans, q_d_pos) || eq(ans, q_d_zero) {
      if eq(rlim, q_d_inf) {
        Fix(0L)
      } else if eq(rlim, q_d_minf) {
        Fix(2L)
      } else {
        q_d_und
      }
    } else {
      q_d_und
    }
  } else if eq(z, q_d_ind) {
    q_d_ind
  } else if eq(z, q_d_zeroa) {
    // erfc decreases through erfc(0) = 1.
    add2(Fix(1L), q_d_zerob)
  } else if eq(z, q_d_zerob) {
    add2(Fix(1L), q_d_zeroa)
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(mk(q_p_erfc, [z]))
  }
}

///|
fn simp__pcterfc(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = gamma2__simp_arg1(form, q_p_erfc, p__pctsimpflag)
  let give_up = () => eqtest(mk(q_p_erfc, [z]), form)
  if zerop1(z).truthy() {
    return Fix(1L)
  }
  if eq(z, q_d_inf) {
    return Fix(0L)
  }
  if eq(z, q_d_minf) {
    return Fix(2L)
  }
  // erfc(inverse_erfc(x)) = x for 0 < x < 2
  if listp(z) &&
    is_op(z, q_p_inverse_erfc) &&
    gamma2__real_between(cadr(z), Fix(0L), Fix(2L)) {
    return cadr(z)
  }
  // Check for numerical evaluation.
  if numerical_eval_p(list1(z)).truthy() {
    return maxima_to(bf_bf_erfc(bf_to(z)))
  }
  // Argument simplification
  let tz = taylorize(mop(form), second(form))
  if tz.truthy() {
    return tz
  }
  if symval(q_d_trigsign).truthy() && great(mul2(Fix(-1L), z), z).truthy() {
    return sub(Fix(2L), simplify(mk(q_p_erfc, [mul2(Fix(-1L), z)])))
  }
  // Representation through more general functions
  if symval(q_d_hypergeometric_representation).truthy() {
    return sub(Fix(1L), erf_hypergeometric(z))
  }
  // Transformation to Erf or Erfi
  let rep = symval(q_d_erf_representation)
  if rep.truthy() && !eq(rep, q_d_erfc) {
    if eq(rep, q_p_erf) {
      return sub(Fix(1L), take(list1(q_p_erf), [z]))
    } else if eq(rep, q_p_erfi) {
      return add2(
        Fix(1L),
        mul2(q_d__pcti, take(list1(q_p_erfi), [mul2(q_d__pcti, z)])),
      )
    } else {
      return give_up()
    }
  }
  give_up()
}

// ---------------------------------------------------------------------------
// The Imaginary Error function Erfi(z)

///|
fn simplim_pcterfi(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    q_d_inf
  } else if eq(z, q_d_minf) {
    q_d_minf
  } else if eq(z, q_d_und) {
    q_d_und
  } else if eq(z, q_d_ind) {
    q_d_ind
  } else if eq(z, q_d_zerob) || eq(z, q_d_zeroa) {
    z
  } else if eq(z, q_d_infinity) {
    q_d_und
  } else {
    // All other cases are handled by the simplifier of the function.
    ftake(q_p_erfi, [z])
  }
}

///|
fn bf_bf_erfi(z : Value) -> Value raise {
  let erfi = (z : Value) => {
    // Use the relationship erfi(z) = -%i*erf(%i*z)
    let iz = bf_complex(bf_neg(bf_imagpart(z)), b=bf_realpart(z)) // %i*z
    let result = bf_bf_erf(iz)
    bf_complex(bf_imagpart(result), b=bf_neg(bf_realpart(result)))
  }
  // Take care to return real results when the argument is real.
  if bf_realp(z) {
    if bf_minusp(z) {
      bf_neg(bf_bf_erfi(bf_neg(z)))
    } else {
      bf_realpart(erfi(z))
    }
  } else {
    erfi(z)
  }
}

///|
fn simp__pcterfi(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = gamma2__simp_arg1(form, q_p_erfi, p__pctsimpflag)
  let give_up = () => eqtest(mk(q_p_erfi, [z]), form)
  if zerop1(z).truthy() {
    return z
  }
  if eq(z, q_d_inf) {
    return q_d_inf
  }
  if eq(z, q_d_minf) {
    return q_d_minf
  }
  // Check for numerical evaluation. Use erfi(z) = -%i*erf(%i*z).
  if numerical_eval_p(list1(z)).truthy() {
    return maxima_to(bf_bf_erfi(bf_to(z)))
  }
  // Argument simplification
  let tz = taylorize(mop(form), second(form))
  if tz.truthy() {
    return tz
  }
  if symval(q_d_erf__pctiargs).truthy() && multiplep(z, q_d__pcti).truthy() {
    return mul2(q_d__pcti, simplify(mk(q_p_erf, [coeff(z, q_d__pcti, Fix(1L))])))
  }
  let rz = apply_reflection_simp(mop(form), z, b=symval(q_d_trigsign))
  if rz.truthy() {
    return rz
  }
  // Representation through more general functions
  if symval(q_d_hypergeometric_representation).truthy() {
    return muln_([Fix(-1L), q_d__pcti, erf_hypergeometric(mul2(q_d__pcti, z))])
  }
  // Transformation to Erf or Erfc
  let rep = symval(q_d_erf_representation)
  if rep.truthy() && !eq(rep, q_d_erfi) {
    if eq(rep, q_p_erf) {
      return muln_([
        Fix(-1L),
        q_d__pcti,
        take(list1(q_p_erf), [mul2(q_d__pcti, z)]),
      ])
    } else if eq(rep, q_p_erfc) {
      return sub(
        mul2(q_d__pcti, take(list1(q_p_erfc), [mul2(q_d__pcti, z)])),
        q_d__pcti,
      )
    } else {
      return give_up()
    }
  }
  give_up()
}

// ---------------------------------------------------------------------------
// The Inverse Error function

///|
fn simplim_pctinverse_erf(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if onep1(z).truthy() {
    q_d_inf
  } else if onep1(mul2(Fix(-1L), z)).truthy() {
    q_d_minf
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(mk(q_p_inverse_erf, [z]))
  }
}

///|
fn simp__pctinverse_erf(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = gamma2__simp_arg1(form, q_p_inverse_erf, p__pctsimpflag)
  if onep1(z).truthy() || onep1(mul2(Fix(-1L), z)).truthy() {
    simp_domain_error(
      list([Str("inverse_erf: inverse_erf(~:M) is undefined."), z]),
    )
  } else if zerop1(z).truthy() {
    z
  } else if listp(z) &&
    is_op(z, q_p_erf) &&
    eq(meqp(Fix(0L), d_imagpart(cadr(z))), t) {
    // inverse_erf(erf(x)) = x for real x
    cadr(z)
  } else if numerical_eval_p(list1(z)).truthy() {
    maxima_to(bf_bf_inverse_erf(bf_to(z)))
  } else {
    let tz = taylorize(mop(form), cadr(form))
    if tz.truthy() {
      tz
    } else {
      eqtest(mk(q_p_inverse_erf, [z]), form)
    }
  }
}

// ---------------------------------------------------------------------------
// The Inverse Complementary Error function

///|
fn simplim_pctinverse_erfc(
  expr : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  // Look for the limit of the argument.
  let z = limit(cadr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    q_d_inf
  } else if zerop1(add2(z, Fix(-2L))).truthy() {
    q_d_minf
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(mk(q_p_inverse_erfc, [z]))
  }
}

///|
fn simp__pctinverse_erfc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = gamma2__simp_arg1(form, q_p_inverse_erfc, p__pctsimpflag)
  if zerop1(z).truthy() || zerop1(add2(z, Fix(-2L))).truthy() {
    simp_domain_error(
      list([Str("inverse_erfc: inverse_erfc(~:M) is undefined."), z]),
    )
  } else if onep1(z).truthy() {
    Fix(0L)
  } else if listp(z) &&
    is_op(z, q_p_erfc) &&
    eq(meqp(Fix(0L), d_imagpart(cadr(z))), t) {
    // inverse_erfc(erfc(x)) = x for real x
    cadr(z)
  } else if numerical_eval_p(list1(z)).truthy() {
    maxima_to(bf_bf_inverse_erfc(bf_to(z)))
  } else {
    let tz = taylorize(mop(form), cadr(form))
    if tz.truthy() {
      tz
    } else {
      eqtest(mk(q_p_inverse_erfc, [z]), form)
    }
  }
}

// ---------------------------------------------------------------------------
// Newton algorithm to calculate numerical values of the Inverse Error
// functions in float or bigfloat precision.  The algorithm is a modified
// version of the routine in newton1.mac.

///|
fn float_newton(expr : Value, var_ : Value, x0 : Value, eps : Value) -> Value raise {
  let s = sdiff(expr, var_)
  let mut xn = x0
  let mut count = 0L
  while !num_gt(Fix(count), symval(q_ear_newton_maxcount)) {
    let sn = d_float(maxima_substitute(xn, var_, expr))
    if num_lt(num_abs(sn), eps) {
      return xn
    }
    if symval(q_ear_debug_newton).truthy() {
      format(t, "~&xn = ~A~%", [xn]) |> ignore
    }
    xn = d_float(sub(xn, div(sn, maxima_substitute(xn, var_, s))))
    count = count + 1L
  }
  merr("float-newton: Newton does not converge for ~:M", [expr])
}

///|
fn bfloat_newton(expr : Value, var_ : Value, x0 : Value, eps : Value) -> Value raise {
  let s = sdiff(expr, var_)
  let mut xn = x0
  let mut count = 0L
  while !num_gt(Fix(count), symval(q_ear_newton_maxcount)) {
    let sn = d_bfloat(maxima_substitute(xn, var_, expr))
    if eq(d_sign(sub(simplify(mk(q_mabs, [sn])), eps)), q_d_neg) {
      return xn
    }
    if symval(q_ear_debug_newton).truthy() {
      format(t, "~&xn = ~A~%", [xn]) |> ignore
    }
    xn = d_bfloat(sub(xn, div(sn, maxima_substitute(xn, var_, s))))
    count = count + 1L
  }
  merr("bfloat-newton: Newton does not converge for ~:M", [expr])
}

///|
/// Compute inverse_erf(z) for z a real or complex number, including bigfloat
/// objects.  The value is computing using a Newton iteration to solve
/// erf(x) = z.
fn bf_bf_inverse_erf(z : Value) -> Value raise {
  if bf_zerop(z) {
    return z
  }
  if bf_eq(z, Fix(1L)) || bf_eq(z, Fix(-1L)) {
    return merr("bf-inverse-erf: inverse_erf(~M) is undefined", [z])
  }
  if bf_minusp(bf_realpart(z)) {
    // inverse_erf is odd because erf is.
    return bf_neg(bf_bf_inverse_erf(bf_neg(z)))
  }
  let approx = (z : Value) => {
    // Find an approximate solution for x = inverse_erf(z).
    let result = if bf_le(bf_abs(z), Fix(1L)) {
      // For small z, inverse_erf(z) = z*sqrt(%pi)/2 + O(z^3).
      bf_mul(bf_mul(z, bf_sqrt(bf_p_pi(z))), num_div(Fix(1L), Fix(2L)))
    } else {
      // For |z| > 1 and realpart(z) >= 0, use the fixed-point iteration
      //   x = sqrt(-log(x*sqrt(%pi)*(1-z))
      let sp = bf_sqrt(bf_p_pi(z))
      let mut a = bf_sqrt(bf_neg(bf_log(bf_mul(sp, bf_sub(Fix(1L), z)))))
      a = bf_sqrt(
        bf_neg(bf_log(bf_mul(bf_mul(a, sp), bf_sub(Fix(1L), z)))),
      )
      a = bf_sqrt(
        bf_neg(bf_log(bf_mul(bf_mul(a, sp), bf_sub(Fix(1L), z)))),
      )
      a
    }
    if symval(q_ear_debug_newton).truthy() {
      format(t, "approx = ~S~%", [result]) |> ignore
    }
    result
  }
  let two_sqrt_pi = bf_div(Fix(2L), bf_sqrt(bf_p_pi(z)))
  let eps = if bf_le(bf_abs(z), Fix(1L)) {
    if realp(z) {
      bf_mul(
        symval(q_ear_newton_epsilon_factor_float),
        symval(q_n_plusflonum_epsilon_plus),
      )
    } else {
      bf_mul(symval(q_ear_newton_epsilon_factor), bf_epsilon(z))
    }
  } else {
    bf_mul(symval(q_ear_newton_epsilon_factor), bf_epsilon(z))
  }
  if symval(q_ear_debug_newton).truthy() {
    format(t, "eps = ~S~%", [eps]) |> ignore
  }
  // Derivative of erf(x)
  let diff = lfunc("bf-inverse-erf-diff", args => {
    let x = args[0]
    bf_mul(two_sqrt_pi, bf_exp(bf_neg(bf_mul(x, x))))
  })
  bf_bf_newton(
    lfunc("bf-erf", args => bf_bf_erf(args[0])),
    diff,
    z,
    approx(z),
    eps,
  )
}

///|
fn bf_bf_inverse_erfc(z : Value) -> Value raise {
  if bf_zerop(z) {
    return merr("bf-inverse-erfc: inverse_erfc(~M) is undefined", [z])
  }
  if bf_eq(z, Fix(1L)) {
    return bf_float(Fix(0L), z)
  }
  let approx = (z : Value) => {
    // inverse_erfc(z) = inverse_erf(1-z), so that's a good starting point.
    let one_minus_z = if bf_complexp(z) {
      // FLOAT takes only a real number.
      bf_sub(Fix(1L), z)
    } else {
      bf_float(bf_sub(Fix(1L), z), Flo(0.0))
    }
    let result = if bf_eq(Fix(1L), one_minus_z) {
      let e5 = bf_mul(Fix(5L), symval(q_n_plusflonum_epsilon_plus))
      if bf_minusp(bf_realpart(z)) {
        bf_bf_inverse_erf(bf_add(Fix(1L), e5))
      } else {
        bf_bf_inverse_erf(bf_sub(Fix(1L), e5))
      }
    } else {
      bf_bf_inverse_erf(one_minus_z)
    }
    if symval(q_ear_debug_newton).truthy() {
      format(t, "approx = ~S~%", [result]) |> ignore
    }
    result
  }
  let m_two_sqrt_pi = bf_div(Fix(-2L), bf_sqrt(bf_p_pi(z)))
  let eps = bf_mul(symval(q_ear_newton_epsilon_factor), bf_epsilon(z))
  if symval(q_ear_debug_newton).truthy() {
    format(t, "eps = ~S~%", [eps]) |> ignore
  }
  // Derivative of erfc(x)
  let diff = lfunc("bf-inverse-erfc-diff", args => {
    let x = args[0]
    bf_mul(m_two_sqrt_pi, bf_exp(bf_neg(bf_mul(x, x))))
  })
  bf_bf_newton(
    lfunc("bf-erfc", args => bf_bf_erfc(args[0])),
    diff,
    z,
    approx(z),
    eps,
  )
}

///|
/// Newton iteration for solving f(x) = z, given f and the derivative of f.
fn bf_bf_newton(
  f : Value,
  df : Value,
  z : Value,
  start : Value,
  eps : Value,
) -> Value raise {
  let maxcount = symval(q_ear_newton_maxcount)
  let mut x = start
  let mut delta = bf_div(bf_sub(funcall(f, [start]), z), funcall(df, [start]))
  let mut count = 0L
  while !(
      bf_lt(bf_abs(delta), bf_mul(bf_abs(x), eps)) ||
      num_gt(Fix(count), maxcount)
    ) {
    if symval(q_ear_debug_newton).truthy() {
      format(t, "x = ~S, abs(delta) = ~S relerr = ~S~%", [
        x,
        bf_abs(delta),
        bf_div(bf_abs(delta), bf_abs(x)),
      ])
      |> ignore
    }
    x = bf_sub(x, delta)
    delta = bf_div(bf_sub(funcall(f, [x]), z), funcall(df, [x]))
    count = count + 1L
  }
  if num_gt(Fix(count), maxcount) {
    merr(
      "bf-newton: failed to converge after ~M iterations: delta = ~S,  x = ~S eps = ~S",
      [Fix(count), delta, x, eps],
    )
  } else {
    x
  }
}

// ---------------------------------------------------------------------------
// Top-level forms of this section

///|
fn gamma2__bags() -> Value {
  list([q_mlist, q_d_matrix, q_mequal])
}

///|
fn gamma2__defgrad(name : Value, args : Value, grads : Array[Value]) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  putprop(name, cons(args, list(grads)), q_grad) |> ignore
}

///|
fn gamma2__init() -> Unit raise {
  // log_gamma
  putprop(q_d_log_gamma, q_p_log_gamma, q_alias) |> ignore
  putprop(q_d_log_gamma, q_p_log_gamma, q_verb) |> ignore
  putprop(q_p_log_gamma, q_d_log_gamma, q_reversealias) |> ignore
  putprop(q_p_log_gamma, q_d_log_gamma, q_noun) |> ignore
  putprop(q_p_log_gamma, q_simp_log_gamma, q_operators) |> ignore
  putprop(q_p_log_gamma, gamma2__bags(), q_distribute_u_over) |> ignore
  gamma2__defgrad(q_p_log_gamma, list1(q_d_z), [maxima_lit("psi[0](z)")])
  putprop(q_p_log_gamma, list2(list1(q_x), q_log_gamma_integral), q_integral)
  |> ignore

  // erf
  putprop(q_p_erf, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_erf, q_odd_function_reflect, q_reflection_rule) |> ignore
  putprop(q_p_erf, gamma2__bags(), q_distribute_u_over) |> ignore
  gamma2__defgrad(q_p_erf, list1(q_d_z), [
    maxima_lit("(2*%e^-z^2)/sqrt(%pi)"),
  ])
  putprop(
    q_p_erf,
    lread(
      "((z) ((mplus) ((mtimes) ((mexpt) $%pi ((rat) -1 2)) ((mexpt) $%e ((mtimes) -1 ((mexpt) z 2)))) ((mtimes) z ((%erf) z))))",
    ),
    q_integral,
  )
  |> ignore

  // erf_generalized
  putprop(q_p_erf_generalized, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_erf_generalized, gamma2__bags(), q_distribute_u_over) |> ignore
  // Generalized Erf is antisymmetric Erf(z1,z2) = - Erf(z2,z1)
  with_specials([(q_d_context, q_d_global), (q_context, q_d_global)], () => {
    meval(mk(q_d_declare, [q_p_erf_generalized, q_d_antisymmetric])) |> ignore
    // Let's remove built-in symbols from list for user-defined properties.
    set(q_d_props, remove(q_p_erf_generalized, symval(q_d_props))) |> ignore
  })
  gamma2__defgrad(q_p_erf_generalized, list2(q_d_z1, q_d_z2), [
    maxima_lit("-((2*%e^-z1^2)/sqrt(%pi))"),
    maxima_lit("(2*%e^-z2^2)/sqrt(%pi)"),
  ])
  putprop(
    q_p_erf_generalized,
    q_simplim_pcterf_generalized,
    q_simplim_pctfunction,
  )
  |> ignore

  // erfc
  putprop(q_p_erfc, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_erfc, gamma2__bags(), q_distribute_u_over) |> ignore
  gamma2__defgrad(q_p_erfc, list1(q_d_z), [
    maxima_lit("-((2*%e^-z^2)/sqrt(%pi))"),
  ])
  putprop(
    q_p_erfc,
    lread(
      "((z) ((mplus) ((mtimes) -1 ((mexpt) $%pi ((rat) -1 2)) ((mexpt) $%e ((mtimes) -1 ((mexpt) z 2)))) ((mtimes) z ((%erfc) z))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_erfc, q_simplim_pcterfc, q_simplim_pctfunction) |> ignore

  // erfi
  putprop(q_p_erfi, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_erfi, q_odd_function_reflect, q_reflection_rule) |> ignore
  putprop(q_p_erfi, gamma2__bags(), q_distribute_u_over) |> ignore
  gamma2__defgrad(q_p_erfi, list1(q_d_z), [
    maxima_lit("(2*%e^z^2)/sqrt(%pi)"),
  ])
  putprop(
    q_p_erfi,
    lread(
      "((z) ((mplus) ((mtimes) -1 ((mexpt) $%pi ((rat) -1 2)) ((mexpt) $%e ((mexpt) z 2))) ((mtimes) z ((%erfi) z))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_erfi, q_simplim_pcterfi, q_simplim_pctfunction) |> ignore

  // inverse_erf
  putprop(q_p_inverse_erf, gamma2__bags(), q_distribute_u_over) |> ignore
  putprop(q_p_inverse_erf, q_p_erf, q_d_inverse) |> ignore
  putprop(q_p_erf, q_p_inverse_erf, q_d_inverse) |> ignore
  gamma2__defgrad(q_p_inverse_erf, list1(q_d_z), [
    maxima_lit("(%e^inverse_erf(z)^2*sqrt(%pi))/2"),
  ])
  putprop(
    q_p_inverse_erf,
    lread(
      "((z) ((mtimes) -1 ((mexpt) $%pi ((rat) -1 2)) ((mexpt) $%e ((mtimes) -1 ((mexpt) ((%inverse_erf) z) 2)))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_inverse_erf, q_simplim_pctinverse_erf, q_simplim_pctfunction)
  |> ignore

  // inverse_erfc
  putprop(q_p_inverse_erfc, gamma2__bags(), q_distribute_u_over) |> ignore
  putprop(q_p_inverse_erfc, q_p_erfc, q_d_inverse) |> ignore
  putprop(q_p_erfc, q_p_inverse_erfc, q_d_inverse) |> ignore
  gamma2__defgrad(q_p_inverse_erfc, list1(q_d_z), [
    maxima_lit("-((%e^inverse_erfc(z)^2*sqrt(%pi))/2)"),
  ])
  putprop(
    q_p_inverse_erfc,
    lread(
      "((z) ((mtimes) ((mexpt) $%pi ((rat) -1 2)) ((mexpt) $%e ((mtimes) -1 ((mexpt) ((%inverse_erfc) z) 2)))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_inverse_erfc, q_simplim_pctinverse_erfc, q_simplim_pctfunction)
  |> ignore
}
