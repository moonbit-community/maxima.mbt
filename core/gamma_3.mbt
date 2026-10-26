// Port of src/gamma.lisp, part 3: the Fresnel integrals S(z) and C(z), and
// the incomplete Beta functions (beta_incomplete,
// beta_incomplete_generalized, beta_incomplete_regularized).

///|
/// `(gettext ...)` message used by the beta_incomplete simplifier.
let gamma3__beta_inc_undefined : String = "beta_incomplete: beta_incomplete(~:M,~:M,~:M) is undefined."

///|
let gamma3__beta_inc_gen_undefined : String = "beta_incomplete_generalized: beta_incomplete_generalized(~:M,~:M,~:M,~:M) is undefined."

///|
let gamma3__beta_inc_reg_undefined : String = "beta_incomplete_regularized: beta_incomplete_regularized(~:M,~:M,~:M) is undefined."

///|
/// '((rat simp) n d)
fn gamma3__rat(n : Int, d : Int) -> Value {
  mk_simp(q_rat, [int(n), int(d)])
}

///|
/// (simplify (list '($pochhammer) a n))
fn gamma3__pochhammer(a : Value, n : Value) -> Value raise {
  simplify(list3(list1(q_d_pochhammer), a, n))
}

///|
/// (simplify (list '(mfactorial) n))
fn gamma3__factorial(n : Value) -> Value raise {
  simplify(list2(list1(q_mfactorial), n))
}

///|
/// CL complex number with rational parts, e.g. (complex 1/2 -1/2).
fn gamma3__cl_complex(rn : Int, rd : Int, in_ : Int, id : Int) -> Value raise {
  bf_complex(num_div(int(rn), int(rd)), b=num_div(int(in_), int(id)))
}

// ---------------------------------------------------------------------------
// Fresnel Integral S(z)

///|
/// Limits of the Fresnel Integral S
fn simplim_pctfresnel_s(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let arg = limit(cadr(exp_), var_, val, q_think)
  if eq(arg, q_d_inf) {
    gamma3__rat(1, 2)
  } else if eq(arg, q_d_minf) {
    gamma3__rat(-1, 2)
  } else {
    mk(q_p_fresnel_s, [arg])
  }
}

///|
/// (in-package :bigfloat) BF-FRESNEL: returns fresnel_s(z) and fresnel_c(z).
fn bf_bf_fresnel(z : Value) -> (Value, Value) raise {
  let eps = bf_epsilon(z)
  let maxit = symval(q_ear_fresnel_maxit)
  let xmin : Value = Flo(1.5)
  let bf_pi = bf_p_pi(z)
  // For very small x, we have
  //  fresnel_s(x) = %pi/6*z^3
  //  fresnel_c(x) = x
  let mut s = bf_mul(bf_mul(bf_mul(bf_div(bf_pi, int(6)), z), z), z)
  let mut c = z
  if bf_gt(bf_abs(z), eps) {
    if bf_lt(bf_abs(z), xmin) {
      if symval(q_ear_debug_gamma).truthy() {
        format(t, "~& in FRESNEL series expansion.~%", []) |> ignore
      }
      let mut sums : Value = int(0)
      let mut sumc = z
      let mut sum : Value = int(0)
      let mut sign : Value = int(1)
      let fact = bf_mul(bf_div(bf_pi, int(2)), bf_mul(z, z))
      let mut term = z
      let mut odd = true
      let mut tst : Value = int(0)
      let mut n : Value = int(3)
      let mut k : Value = int(1)
      while true {
        if bf_gt(k, maxit) {
          merr(
            "fresnel: series expansion failed for (COMPLEX-BFLOAT-FRESNEL ~:M).",
            [z],
          )
          |> ignore
        }
        term = bf_mul(term, bf_div(fact, k))
        sum = bf_add(sum, bf_div(bf_mul(sign, term), n))
        tst = bf_mul(bf_abs(sum), eps)
        if odd {
          sign = bf_neg(sign)
          sums = sum
          sum = sumc
        } else {
          sumc = sum
          sum = sums
        }
        if bf_lt(bf_abs(term), tst) {
          break
        }
        odd = !odd
        n = bf_add(n, int(2))
        k = bf_add(k, int(1))
      }
      s = sums
      c = sumc
    } else {
      let sqrt_pi = bf_sqrt(bf_pi)
      let z_plus = bf_mul(gamma3__cl_complex(1, 2, 1, 2), bf_mul(sqrt_pi, z))
      let z_minus = bf_mul(gamma3__cl_complex(1, 2, -1, 2), bf_mul(sqrt_pi, z))
      let erf_plus = bf_bf_erf(z_plus)
      let erf_minus = bf_bf_erf(z_minus)
      s = bf_mul(
        gamma3__cl_complex(1, 4, 1, 4),
        bf_add(erf_plus, bf_mul(bf_complex(int(0), b=int(-1)), erf_minus)),
      )
      c = bf_mul(
        gamma3__cl_complex(1, 4, -1, 4),
        bf_add(erf_plus, bf_mul(bf_complex(int(0), b=int(1)), erf_minus)),
      )
    }
  }
  (s, c)
}

///|
fn bf_bf_fresnel_s(z : Value) -> Value raise {
  if bf_complexp(z) && bf_zerop(bf_realpart(z)) {
    // A pure imaginary argument. Use fresnel_s(%i*x)=-%i*fresnel_s(x).
    bf_complex(int(0), b=bf_neg(bf_bf_fresnel_s(bf_imagpart(z))))
  } else {
    let fs = bf_bf_fresnel(z).0
    if bf_realp(z) {
      bf_realpart(fs)
    } else {
      fs
    }
  }
}

///|
fn bf_bf_fresnel_c(z : Value) -> Value raise {
  if bf_complexp(z) && bf_zerop(bf_realpart(z)) {
    // A pure imaginary argument. Use fresnel_c(%i*x)=%i*fresnel_c(x).
    bf_complex(int(0), b=bf_bf_fresnel_c(bf_imagpart(z)))
  } else {
    let fc = bf_bf_fresnel(z).1
    if bf_realp(z) {
      bf_realpart(fc)
    } else {
      fc
    }
  }
}

///|
/// fresnel_s is a simplifying function
fn simp__pctfresnel_s(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_fresnel_s, [q_d_z]),
    )
    |> ignore
  }
  let z = simpcheck(nth(1, form), p__pctsimpflag)
  // Check for specific values
  if zerop1(z).truthy() {
    return z
  }
  if eq(z, q_d_inf) {
    return gamma3__rat(1, 2)
  }
  if eq(z, q_d_minf) {
    return gamma3__rat(-1, 2)
  }
  // Check for numerical evaluation
  if numerical_eval_p(list1(z)).truthy() {
    return maxima_to(bf_bf_fresnel_s(bf_to(z)))
  }
  // Check for argument simplification
  let tz = taylorize(mop(form), second(form))
  if tz.truthy() {
    return tz
  }
  if symval(q_d__pctiargs).truthy() && multiplep(z, q_d__pcti).truthy() {
    return mul(
      list([
        int(-1),
        q_d__pcti,
        simplify(list2(list1(q_p_fresnel_s), coeff(z, q_d__pcti, int(1)))),
      ]),
    )
  }
  let rs = apply_reflection_simp(mop(form), z, b=symval(q_d_trigsign))
  if rs.truthy() {
    return rs
  }
  // Representation through equivalent functions
  if symval(q_d_erf_representation).truthy() {
    return mul2(
      div(add2(int(1), q_d__pcti), int(4)),
      add2(
        simplify(
          list2(
            list1(q_p_erf),
            mul(
              list([
                div(add2(int(1), q_d__pcti), int(2)),
                power(q_d__pctpi, gamma3__rat(1, 2)),
                z,
              ]),
            ),
          ),
        ),
        mul(
          list([
            int(-1),
            q_d__pcti,
            simplify(
              list2(
                list1(q_p_erf),
                mul(
                  list([
                    div(sub(int(1), q_d__pcti), int(2)),
                    power(q_d__pctpi, gamma3__rat(1, 2)),
                    z,
                  ]),
                ),
              ),
            ),
          ]),
        ),
      ),
    )
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    return mul2(
      div(mul2(q_d__pctpi, power(z, int(3))), int(6)),
      ftake(q_p_hypergeometric, [
        list2(list1(q_mlist), div(int(3), int(4))),
        list3(list1(q_mlist), div(int(3), int(2)), div(int(7), int(4))),
        mul2(
          int(-1),
          div(mul2(power(q_d__pctpi, int(2)), power(z, int(4))), int(16)),
        ),
      ]),
    )
  }
  eqtest(cons(list1(q_p_fresnel_s), list1(z)), form)
}

// ---------------------------------------------------------------------------
// Fresnel Integral C(z)

///|
/// Limits of the Fresnel Integral C
fn simplim_pctfresnel_c(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let arg = limit(cadr(exp_), var_, val, q_think)
  if eq(arg, q_d_inf) {
    gamma3__rat(1, 2)
  } else if eq(arg, q_d_minf) {
    gamma3__rat(-1, 2)
  } else {
    mk(q_p_fresnel_c, [arg])
  }
}

///|
/// fresnel_c is a simplifying function
fn simp__pctfresnel_c(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_fresnel_c, [q_d_z]),
    )
    |> ignore
  }
  let z = simpcheck(nth(1, form), p__pctsimpflag)
  // Check for specific values
  if zerop1(z).truthy() {
    return z
  }
  if eq(z, q_d_inf) {
    return gamma3__rat(1, 2)
  }
  if eq(z, q_d_minf) {
    return gamma3__rat(-1, 2)
  }
  // Check for numerical evaluation
  if numerical_eval_p(list1(z)).truthy() {
    return maxima_to(bf_bf_fresnel_c(bf_to(z)))
  }
  // Check for argument simplification
  let tz = taylorize(mop(form), second(form))
  if tz.truthy() {
    return tz
  }
  if symval(q_d__pctiargs).truthy() && multiplep(z, q_d__pcti).truthy() {
    return mul2(
      q_d__pcti,
      simplify(list2(list1(q_p_fresnel_c), coeff(z, q_d__pcti, int(1)))),
    )
  }
  let rs = apply_reflection_simp(mop(form), z, b=symval(q_d_trigsign))
  if rs.truthy() {
    return rs
  }
  // Representation through equivalent functions
  if symval(q_d_erf_representation).truthy() {
    return mul2(
      div(sub(int(1), q_d__pcti), int(4)),
      add2(
        simplify(
          list2(
            list1(q_p_erf),
            mul(
              list([
                div(add2(int(1), q_d__pcti), int(2)),
                power(q_d__pctpi, gamma3__rat(1, 2)),
                z,
              ]),
            ),
          ),
        ),
        mul2(
          q_d__pcti,
          simplify(
            list2(
              list1(q_p_erf),
              mul(
                list([
                  div(sub(int(1), q_d__pcti), int(2)),
                  power(q_d__pctpi, gamma3__rat(1, 2)),
                  z,
                ]),
              ),
            ),
          ),
        ),
      ),
    )
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    return mul2(
      z,
      ftake(q_p_hypergeometric, [
        list2(list1(q_mlist), div(int(1), int(4))),
        list3(list1(q_mlist), div(int(1), int(2)), div(int(5), int(4))),
        mul2(
          int(-1),
          div(mul2(power(q_d__pctpi, int(2)), power(z, int(4))), int(16)),
        ),
      ]),
    )
  }
  eqtest(cons(list1(q_p_fresnel_c), list1(z)), form)
}

// ---------------------------------------------------------------------------
// Incomplete Beta function

///|
fn simp__pctbeta_incomplete(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 3 {
    wna_err(
      form,
      required_arg_count=int(3),
      pretty_name=mk(q_p_beta_incomplete, [q_d_a, q_d_b, q_d_z]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let b = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_beta_incomplete), list3(a, b, z)), form)
  with_special(q_d_simpsum, t, () => {
    if symval(q_ear_debug_gamma).truthy() {
      format(t, "~&SIMP-BETA-INCOMPLETE:~%", []) |> ignore
      format(t, "~&   : a = ~A~%", [a]) |> ignore
      format(t, "~&   : b = ~A~%", [b]) |> ignore
      format(t, "~&   : z = ~A~%", [z]) |> ignore
    }
    // Check for specific values
    if zerop1(z).truthy() {
      let sgn = d_sign(d_realpart(a))
      return if eq(sgn, q_d_neg) || eq(sgn, q_d_zero) {
        simp_domain_error(list([Str(gamma3__beta_inc_undefined), a, b, z]))
      } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        z
      } else {
        give_up()
      }
    }
    if onep1(z).truthy() && eq(d_sign(d_realpart(b)), q_d_pos) {
      // z=1 and realpart(b)>0. Simplify to a Beta function.
      // If we have to evaluate numerically preserve the type.
      return if complex_float_numerical_eval_p(list3(a, b, z)).truthy() {
        ftake_star(q_p_beta, [d_float(a), d_float(b)])
      } else if complex_bigfloat_numerical_eval_p(list3(a, b, z)).truthy() {
        ftake_star(q_p_beta, [d_bfloat(a), d_bfloat(b)])
      } else {
        ftake_star(q_p_beta, [a, b])
      }
    }
    if zerop1(a).truthy() ||
      (
        integer_representation_p(a).truthy() &&
        eq(d_sign(a), q_d_neg) &&
        (
          (mnump(b).truthy() && !integer_representation_p(b).truthy()) ||
          eq(d_sign(add2(a, b)), q_d_pos)
        )
      ) {
      // The argument a is zero or a is negative and the argument b is
      // not in a valid range. Beta incomplete is undefined.
      // It would be more correct to return Complex infinity.
      return simp_domain_error(list([Str(gamma3__beta_inc_undefined), a, b, z]))
    }

    // Check for numerical evaluation in Float or Bigfloat precision
    if complex_float_numerical_eval_p(list3(a, b, z)).truthy() {
      return if !(
          integer_representation_p(a).truthy() && num_lt(a, Flo(0.0))
        ) {
        with_special(
          q_ear_beta_incomplete_eps,
          bf_epsilon(d_float(Flo(1.0))),
          () => beta_incomplete(d_float(a), d_float(b), d_float(z)),
        )
      } else {
        // Negative integer a and b is in a valid range. Expand.
        d_rectform(
          beta_incomplete_expand_negative_integer(
            num_truncate(a).0,
            d_float(b),
            d_float(z),
          ),
        )
      }
    }
    if complex_bigfloat_numerical_eval_p(list3(a, b, z)).truthy() {
      return if !(
          integer_representation_p(a).truthy() && eq(d_sign(a), q_d_neg)
        ) {
        with_special(
          q_ear_beta_incomplete_eps,
          bf_epsilon(bf_bigfloat(Flo(1.0))),
          () => beta_incomplete(d_bfloat(a), d_bfloat(b), d_bfloat(z)),
        )
      } else {
        // Negative integer a and b is in a valid range. Expand.
        d_rectform(
          beta_incomplete_expand_negative_integer(
            ftake(q_p_truncate, [a]),
            d_bfloat(b),
            d_bfloat(z),
          ),
        )
      }
    }

    // Argument simplifications and transformations
    if integerp(b) && plusp(b) && (!integerp(a) || plusp(a)) {
      // Expand for b a positive integer and a not a negative integer.
      let index = gensumindex()
      return mul(
        list([
          ftake_star(q_p_beta, [a, b]),
          power(z, a),
          simpsum1(
            div(
              mul2(gamma3__pochhammer(a, index), power(sub(int(1), z), index)),
              gamma3__factorial(index),
            ),
            index,
            int(0),
            sub(b, int(1)),
          ),
        ]),
      )
    }
    if integerp(a) && plusp(a) {
      // Expand for a a positive integer.
      return mul2(
        ftake_star(q_p_beta, [a, b]),
        sub(
          int(1),
          mul2(power(sub(int(1), z), b), {
            let index = gensumindex()
            simpsum1(
              div(
                mul2(gamma3__pochhammer(b, index), power(z, index)),
                gamma3__factorial(index),
              ),
              index,
              int(0),
              sub(a, int(1)),
            )
          }),
        ),
      )
    }
    if integerp(a) &&
      minusp(a) &&
      integerp(b) &&
      plusp(b) &&
      num_le(b, num_neg(a)) {
      // Expand for a a negative integer and b an integer with b <= -a.
      let index = gensumindex()
      return mul2(
        power(z, a),
        simpsum1(
          div(
            mul2(gamma3__pochhammer(sub(int(1), b), index), power(z, index)),
            mul2(add2(index, a), gamma3__factorial(index)),
          ),
          index,
          int(0),
          sub(b, int(1)),
        ),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      plusp(cadr(a)) {
      let n = cadr(a)
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return sub(
        mul2(
          div(gamma3__pochhammer(a, n), gamma3__pochhammer(add2(a, b), n)),
          ftake(q_p_beta_incomplete, [a, b, z]),
        ),
        mul2(power(add(list([a, b, n, int(-1)])), int(-1)), {
          let index = gensumindex()
          simpsum1(
            mul2(
              div(
                gamma3__pochhammer(
                  add(list([int(1), mul2(int(-1), a), mul2(int(-1), n)])),
                  index,
                ),
                gamma3__pochhammer(
                  add(
                    list([
                      int(2),
                      mul2(int(-1), a),
                      mul2(int(-1), b),
                      mul2(int(-1), n),
                    ]),
                  ),
                  index,
                ),
              ),
              mul2(
                power(sub(int(1), z), b),
                power(z, add(list([a, n, mul2(int(-1), index), int(-1)]))),
              ),
            ),
            index,
            int(0),
            sub(n, int(1)),
          )
        }),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      minusp(cadr(a)) {
      let n = num_neg(cadr(a))
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return sub(
        mul2(
          div(
            gamma3__pochhammer(
              add(list([int(1), mul2(int(-1), a), mul2(int(-1), b)])),
              n,
            ),
            gamma3__pochhammer(sub(int(1), a), n),
          ),
          ftake(q_p_beta_incomplete, [a, b, z]),
        ),
        mul2(
          div(
            gamma3__pochhammer(
              add(list([int(2), mul2(int(-1), a), mul2(int(-1), b)])),
              sub(n, int(1)),
            ),
            gamma3__pochhammer(sub(int(1), a), n),
          ),
          {
            let index = gensumindex()
            simpsum1(
              mul2(
                div(
                  gamma3__pochhammer(sub(int(1), a), index),
                  gamma3__pochhammer(
                    add(list([int(2), mul2(int(-1), a), mul2(int(-1), b)])),
                    index,
                  ),
                ),
                mul2(
                  power(sub(int(1), z), b),
                  power(z, add(list([a, mul2(int(-1), index), int(-1)]))),
                ),
              ),
              index,
              int(0),
              sub(n, int(1)),
            )
          },
        ),
      )
    }
    if symval(q_d_hypergeometric_representation).truthy() {
      // There are several cases to consider.
      //
      // For -a not an integer see
      // http://functions.wolfram.com/06.19.26.0005.01
      //
      //   beta_incomplete(a,b,z) = z^a/a*%f[2,1]([a,1-b],[a+1],z)
      //
      // For -b not an integer see
      // http://functions.wolfram.com/06.19.26.0007.01
      //
      //   beta_incomplete(a,b,z) = beta(a,b) -
      //     (1-z)^b*z^a/b*%f[2,1]([1,a+b],[b+1],1-z)
      //
      // For a+b not a positive integer see
      // http://functions.wolfram.com/06.19.26.0008.01
      //
      //   beta_incomplete(a,b,z) =
      //     z^a*(-z)^(b-1)/(a+b-1)*%f[2,1]([1-b,-a-b+1],[-a-b+2],1/z)
      //       + z^a*beta(1-a-b,a)*(-z)^(-a)
      //
      // We need to handle more cases here
      return mul2(
        div(power(z, a), a),
        ftake(q_p_hypergeometric, [
          make_mlist(list2(a, sub(int(1), b))),
          make_mlist(list1(add2(int(1), a))),
          z,
        ]),
      )
    }
    give_up()
  })
}

///|
fn beta_incomplete_expand_negative_integer(
  a : Value,
  b : Value,
  z : Value,
) -> Value raise {
  mul2(
    power(z, a),
    {
      let index = gensumindex()
      with_special(q_d_simpsum, t, () => simpsum1(
        div(
          mul2(gamma3__pochhammer(sub(int(1), b), index), power(z, index)),
          mul2(add2(index, a), gamma3__factorial(index)),
        ),
        index,
        int(0),
        sub(b, int(1)),
      ))
    },
  )
}

///|
fn beta_incomplete(a : Value, b : Value, z : Value) -> Value raise {
  if eq(
      d_sign(
        sub(
          mul2(d_realpart(z), d_realpart(add(list([a, b, int(2)])))),
          d_realpart(add2(a, int(1))),
        ),
      ),
      q_d_pos,
    ) {
    d_rectform(
      sub(
        ftake_star(q_p_beta, [a, b]),
        maxima_to(numeric_beta_incomplete(b, a, sub(Flo(1.0), z))),
      ),
    )
  } else {
    maxima_to(numeric_beta_incomplete(a, b, z))
  }
}

///|
fn numeric_beta_incomplete(a : Value, b : Value, z : Value) -> Value raise {
  if symval(q_ear_debug_gamma).truthy() {
    format(t, "~&NUMERIC-BETA-INCOMPLETE enters continued fractions~%", [])
    |> ignore
  }
  let a = bf_to(a)
  let b = bf_to(b)
  let z = bf_to(z)
  let beta_maxit = symval(q_ear_beta_incomplete_maxit)
  let beta_eps = symval(q_ear_beta_incomplete_eps)
  let beta_min = bf_mul(beta_eps, beta_eps)
  let ab = bf_add(a, b)
  let ap = bf_add(a, Flo(1.0))
  let am = bf_sub(a, Flo(1.0))
  let mut c : Value = Flo(1.0)
  let mut d = bf_sub(Flo(1.0), bf_div(bf_mul(z, ab), ap))
  d = if bf_lt(bf_abs(d), beta_min) { beta_min } else { d }
  d = bf_div(Flo(1.0), d)
  let mut h = d
  let mut aa : Value = Flo(0.0)
  let mut de : Value = Flo(0.0)
  let mut m2 = int(0)
  let mut m = int(1)
  while true {
    if num_gt(m, beta_maxit) {
      merr(
        "beta_incomplete: continued fractions failed for beta_incomplete(~:M, ~:M, ~:M).",
        [a, b, z],
      )
      |> ignore
    }
    m2 = num_add(m, m)
    aa = bf_div(
      bf_mul(bf_mul(m, z), bf_sub(b, m)),
      bf_mul(bf_add(am, m2), bf_add(a, m2)),
    )
    d = bf_add(Flo(1.0), bf_mul(aa, d))
    if bf_lt(bf_abs(d), beta_min) {
      d = beta_min
    }
    c = bf_add(Flo(1.0), bf_div(aa, c))
    if bf_lt(bf_abs(c), beta_min) {
      c = beta_min
    }
    d = bf_div(Flo(1.0), d)
    h = bf_mul(bf_mul(h, d), c)
    aa = bf_div(
      bf_mul(bf_mul(bf_mul(int(-1), bf_add(a, m)), bf_add(ab, m)), z),
      bf_mul(bf_add(a, m2), bf_add(ap, m2)),
    )
    d = bf_add(Flo(1.0), bf_mul(aa, d))
    if bf_lt(bf_abs(d), beta_min) {
      d = beta_min
    }
    c = bf_add(Flo(1.0), bf_div(aa, c))
    if bf_lt(bf_abs(c), beta_min) {
      c = beta_min
    }
    d = bf_div(Flo(1.0), d)
    de = bf_mul(d, c)
    h = bf_mul(h, de)
    if bf_lt(bf_abs(bf_sub(de, Flo(1.0))), beta_eps) {
      if symval(q_ear_debug_gamma).truthy() {
        format(t, "~&Continued fractions finished.~%", []) |> ignore
        format(t, "~&  z = ~A~%", [z]) |> ignore
        format(t, "~&  a = ~A~%", [a]) |> ignore
        format(t, "~&  b = ~A~%", [b]) |> ignore
        format(t, "~&  h = ~A~%", [h]) |> ignore
      }
      let result = bf_div(
        bf_mul(bf_mul(h, bf_expt(z, a)), bf_expt(bf_sub(Flo(1.0), z), b)),
        a,
      )
      if symval(q_ear_debug_gamma).truthy() {
        format(t, "~& result = ~A~%", [result]) |> ignore
      }
      return result
    }
    m = num_add(m, int(1))
  }
  Nil
}

// ---------------------------------------------------------------------------
// Generalized Incomplete Beta function

///|
fn conjugate_beta_incomplete_generalized(args : Value) -> Value raise {
  let a = first(args)
  let b = second(args)
  let z1 = third(args)
  let z2 = fourth(args)
  if off_negative_real_axisp(z1).truthy() &&
    !(
      zerop1(d_imagpart(z1)).truthy() &&
      eq(d_sign(sub(d_realpart(z1), int(1))), q_d_pos)
    ) &&
    off_negative_real_axisp(z2).truthy() &&
    !(
      zerop1(d_imagpart(z2)).truthy() &&
      eq(d_sign(sub(d_realpart(z2), int(1))), q_d_pos)
    ) {
    simplify(
      list([
        list1(q_p_beta_incomplete_generalized),
        simplify(list2(list1(q_d_conjugate), a)),
        simplify(list2(list1(q_d_conjugate), b)),
        simplify(list2(list1(q_d_conjugate), z1)),
        simplify(list2(list1(q_d_conjugate), z2)),
      ]),
    )
  } else {
    list2(
      list2(q_d_conjugate, q_simp),
      simplify(list([list1(q_p_beta_incomplete_generalized), a, b, z1, z2])),
    )
  }
}

///|
fn simp__pctbeta_incomplete_generalized(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 4 {
    wna_err(
      form,
      required_arg_count=int(4),
      pretty_name=mk(q_p_beta_incomplete_generalized, [
        q_d_a, q_d_b, q_d_z1, q_d_z2,
      ]),
    )
    |> ignore
  }
  let a = simpcheck(nth(1, form), p__pctsimpflag)
  let b = simpcheck(nth(2, form), p__pctsimpflag)
  let z1 = simpcheck(nth(3, form), p__pctsimpflag)
  let z2 = simpcheck(nth(4, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_beta_incomplete_generalized), list4(a, b, z1, z2)),
    form,
  )
  with_special(q_d_simpsum, t, () => {
    // Check for specific values
    if zerop1(z2).truthy() {
      let sgn = d_sign(d_realpart(a))
      return if eq(sgn, q_d_neg) {
        simp_domain_error(
          list([Str(gamma3__beta_inc_gen_undefined), a, b, z1, z2]),
        )
      } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        mul2(int(-1), ftake(q_p_beta_incomplete, [a, b, z1]))
      } else {
        give_up()
      }
    }
    if zerop1(z1).truthy() {
      let sgn = d_sign(d_realpart(a))
      return if eq(sgn, q_d_neg) {
        simp_domain_error(
          list([Str(gamma3__beta_inc_gen_undefined), a, b, z1, z2]),
        )
      } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        ftake(q_p_beta_incomplete, [a, b, z2])
      } else {
        give_up()
      }
    }
    if onep1(z2).truthy() &&
      (!mnump(a).truthy() || !mnump(b).truthy() || !mnump(z1).truthy()) {
      let sgn = d_sign(d_realpart(b))
      return if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        sub(
          ftake_star(q_p_beta, [a, b]),
          ftake(q_p_beta_incomplete, [a, b, z1]),
        )
      } else {
        give_up()
      }
    }
    if onep1(z1).truthy() &&
      (!mnump(a).truthy() || !mnump(b).truthy() || !mnump(z2).truthy()) {
      let sgn = d_sign(d_realpart(b))
      return if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        sub(
          ftake(q_p_beta_incomplete, [a, b, z2]),
          ftake_star(q_p_beta, [a, b]),
        )
      } else {
        give_up()
      }
    }

    // Check for numerical evaluation in Float or Bigfloat precision
    if complex_float_numerical_eval_p(list4(a, b, z1, z2)).truthy() {
      return with_special(
        q_ear_beta_incomplete_eps,
        bf_epsilon(d_float(Flo(1.0))),
        () => sub(
          beta_incomplete(d_float(a), d_float(b), d_float(z2)),
          beta_incomplete(d_float(a), d_float(b), d_float(z1)),
        ),
      )
    }
    if complex_bigfloat_numerical_eval_p(list4(a, b, z1, z2)).truthy() {
      return with_special(
        q_ear_beta_incomplete_eps,
        bf_epsilon(bf_bigfloat(Flo(1.0))),
        () => sub(
          beta_incomplete(d_bfloat(a), d_bfloat(b), d_bfloat(z2)),
          beta_incomplete(d_bfloat(a), d_bfloat(b), d_bfloat(z1)),
        ),
      )
    }

    // Check for argument simplifications and transformations
    if integerp(a) && plusp(a) {
      return mul2(
        ftake_star(q_p_beta, [a, b]),
        sub(
          mul2(power(sub(int(1), z1), b), {
            let index = gensumindex()
            simpsum1(
              div(
                mul2(gamma3__pochhammer(b, index), power(z1, index)),
                gamma3__factorial(index),
              ),
              index,
              int(0),
              sub(a, int(1)),
            )
          }),
          mul2(power(sub(int(1), z2), b), {
            let index = gensumindex()
            simpsum1(
              div(
                mul2(gamma3__pochhammer(b, index), power(z2, index)),
                gamma3__factorial(index),
              ),
              index,
              int(0),
              sub(a, int(1)),
            )
          }),
        ),
      )
    }
    if integerp(b) && plusp(b) {
      return mul2(
        ftake_star(q_p_beta, [a, b]),
        sub(
          mul2(power(z2, a), {
            let index = gensumindex()
            simpsum1(
              div(
                mul2(
                  gamma3__pochhammer(a, index),
                  power(sub(int(1), z2), index),
                ),
                gamma3__factorial(index),
              ),
              index,
              int(0),
              sub(b, int(1)),
            )
          }),
          mul2(power(z1, a), {
            let index = gensumindex()
            simpsum1(
              div(
                mul2(
                  gamma3__pochhammer(a, index),
                  power(sub(int(1), z1), index),
                ),
                gamma3__factorial(index),
              ),
              index,
              int(0),
              sub(b, int(1)),
            )
          }),
        ),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      plusp(cadr(a)) {
      let n = cadr(a)
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return add2(
        mul2(
          div(gamma3__pochhammer(a, n), gamma3__pochhammer(add2(a, b), n)),
          take(list1(q_p_beta_incomplete_generalized), [a, b, z1, z2]),
        ),
        mul2(power(add(list([a, b, n, int(-1)])), int(-1)), {
          let index = gensumindex()
          simpsum1(
            mul2(
              div(
                gamma3__pochhammer(
                  add(list([int(1), mul2(int(-1), a), mul2(int(-1), n)])),
                  index,
                ),
                gamma3__pochhammer(
                  add(
                    list([
                      int(2),
                      mul2(int(-1), a),
                      mul2(int(-1), b),
                      mul2(int(-1), n),
                    ]),
                  ),
                  index,
                ),
              ),
              sub(
                mul2(
                  power(sub(int(1), z1), b),
                  power(z1, add(list([a, n, mul2(int(-1), index), int(-1)]))),
                ),
                mul2(
                  power(sub(int(1), z2), b),
                  power(z2, add(list([a, n, mul2(int(-1), index), int(-1)]))),
                ),
              ),
            ),
            index,
            int(0),
            sub(n, int(1)),
          )
        }),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      minusp(cadr(a)) {
      let n = num_neg(cadr(a))
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return sub(
        mul2(
          div(
            gamma3__pochhammer(
              add(list([int(1), mul2(int(-1), a), mul2(int(-1), b)])),
              n,
            ),
            gamma3__pochhammer(sub(int(1), a), n),
          ),
          take(list1(q_p_beta_incomplete_generalized), [a, b, z1, z2]),
        ),
        mul2(
          div(
            gamma3__pochhammer(
              add(list([int(2), mul2(int(-1), a), mul2(int(-1), b)])),
              sub(n, int(1)),
            ),
            gamma3__pochhammer(sub(int(1), a), n),
          ),
          {
            let index = gensumindex()
            simpsum1(
              mul2(
                div(
                  gamma3__pochhammer(sub(int(1), a), index),
                  gamma3__pochhammer(
                    add(list([int(2), mul2(int(-1), a), mul2(int(-1), b)])),
                    index,
                  ),
                ),
                sub(
                  mul2(
                    power(sub(int(1), z2), b),
                    power(z2, add(list([a, mul2(int(-1), index), int(-1)]))),
                  ),
                  mul2(
                    power(sub(int(1), z1), b),
                    power(z1, add(list([a, mul2(int(-1), index), int(-1)]))),
                  ),
                ),
              ),
              index,
              int(0),
              sub(n, int(1)),
            )
          },
        ),
      )
    }
    give_up()
  })
}

// ---------------------------------------------------------------------------
// Regularized Incomplete Beta function

///|
/// `(if ($bfloatp x) (minusp (cadr x)) (minusp x))`
fn gamma3__bf_or_num_minusp(x : Value) -> Bool raise {
  if d_bfloatp(x).truthy() {
    minusp(cadr(x))
  } else {
    minusp(x)
  }
}

///|
fn simp__pctbeta_incomplete_regularized(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 3 {
    wna_err(
      form,
      required_arg_count=int(3),
      pretty_name=mk(q_p_beta_incomplete_regularized, [q_d_a, q_d_b, q_d_z]),
    )
    |> ignore
  }
  let mut a = simpcheck(nth(1, form), p__pctsimpflag)
  let mut b = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  let a0 = a
  let b0 = b
  let give_up = () => eqtest(
    cons(list1(q_p_beta_incomplete_regularized), list3(a0, b0, z)),
    form,
  )
  with_special(q_d_simpsum, t, () => {
    // Check for specific values
    if zerop1(z).truthy() {
      let sgn = d_sign(d_realpart(a))
      return if eq(sgn, q_d_neg) {
        simp_domain_error(list([Str(gamma3__beta_inc_reg_undefined), a, b, z]))
      } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        int(0)
      } else {
        give_up()
      }
    }
    if onep1(z).truthy() &&
      (!mnump(a).truthy() || !mnump(b).truthy() || !mnump(z).truthy()) {
      let sgn = d_sign(d_realpart(b))
      return if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
        int(1)
      } else {
        give_up()
      }
    }
    if integer_representation_p(b).truthy() && gamma3__bf_or_num_minusp(b) {
      // Problem: for b a negative integer the Regularized Incomplete
      // Beta function is defined to be zero. BUT: When we calculate
      // e.g. beta_incomplete(1.0,-2.0,1/2)/beta(1.0,-2.0) we get the
      // result -3.0, because beta_incomplete and beta are defined for
      // for this case. How do we get a consistent behaviour?
      return int(0)
    }
    if integer_representation_p(a).truthy() && gamma3__bf_or_num_minusp(a) {
      // TODO: The following line does not work for bigfloats.
      return if integer_representation_p(b).truthy() && num_le(b, num_neg(a)) {
        div(
          ftake(q_p_beta_incomplete, [a, b, z]),
          ftake_star(q_p_beta, [a, b]),
        )
      } else {
        int(1)
      }
    }

    // Check for numerical evaluation in Float or Bigfloat precision
    if complex_float_numerical_eval_p(list3(a, b, z)).truthy() {
      return with_special(
        q_ear_beta_incomplete_eps,
        bf_epsilon(d_float(Flo(1.0))),
        () => {
          a = d_float(a)
          b = d_float(b)
          let beta = ftake_star(q_p_beta, [a, b])
          let mut ibeta : Value = Nil
          let underflow = num_lt(d_abs(beta), Flo(1.0e-307)) || {
            ibeta = beta_incomplete(a, b, d_float(z))
            num_lt(d_abs(ibeta), Flo(1.0e-307))
          }
          if underflow {
            // In case of underflow (see bug #2999) or precision loss use bigfloats
            // and emporarily give some extra precision but avoid fpprec dependency.
            // Is this workaround correct for complex values?
            with_special(q_fpprec, int(70), () => d_float(
              take(list1(q_p_beta_incomplete_regularized), [
                d_bfloat(a),
                d_bfloat(b),
                z,
              ]),
            ))
          } else {
            d_rectform(div(ibeta, beta))
          }
        },
      )
    }
    if complex_bigfloat_numerical_eval_p(list3(a, b, z)).truthy() {
      return with_special(
        q_ear_beta_incomplete_eps,
        bf_epsilon(bf_bigfloat(Flo(1.0))),
        () => {
          a = d_bfloat(a)
          b = d_bfloat(b)
          d_rectform(
            div(
              beta_incomplete(a, b, d_bfloat(z)),
              ftake_star(q_p_beta, [a, b]),
            ),
          )
        },
      )
    }

    // Check for argument simplifications and transformations
    if integerp(b) && plusp(b) {
      return div(
        ftake(q_p_beta_incomplete, [a, b, z]),
        ftake_star(q_p_beta, [a, b]),
      )
    }
    if integerp(a) && plusp(a) {
      return div(
        ftake(q_p_beta_incomplete, [a, b, z]),
        ftake_star(q_p_beta, [a, b]),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      plusp(cadr(a)) {
      let n = cadr(a)
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return sub(
        take(list1(q_p_beta_incomplete_regularized), [a, b, z]),
        mul(
          list([
            power(add(list([a, b, n, int(-1)])), int(-1)),
            power(ftake_star(q_p_beta, [add2(a, n), b]), int(-1)),
            {
              let index = gensumindex()
              simpsum1(
                mul(
                  list([
                    div(
                      gamma3__pochhammer(
                        add(
                          list([int(1), mul2(int(-1), a), mul2(int(-1), n)]),
                        ),
                        index,
                      ),
                      gamma3__pochhammer(
                        add(
                          list([
                            int(2),
                            mul2(int(-1), a),
                            mul2(int(-1), b),
                            mul2(int(-1), n),
                          ]),
                        ),
                        index,
                      ),
                    ),
                    power(sub(int(1), z), b),
                    power(z, add(list([a, n, mul2(int(-1), index), int(-1)]))),
                  ]),
                ),
                index,
                int(0),
                sub(n, int(1)),
              )
            },
          ]),
        ),
      )
    }
    if symval(q_d_beta_expand).truthy() &&
      mplusp(a).truthy() &&
      integerp(cadr(a)) &&
      minusp(cadr(a)) {
      let n = num_neg(cadr(a))
      let a = simplify(cons(list1(q_mplus), cddr(a)))
      return add2(
        take(list1(q_p_beta_incomplete_regularized), [a, b, z]),
        mul(
          list([
            power(add(list([a, b, int(-1)])), int(-1)),
            power(ftake_star(q_p_beta, [a, b]), int(-1)),
            {
              let index = gensumindex()
              simpsum1(
                mul(
                  list([
                    div(
                      gamma3__pochhammer(sub(int(1), a), index),
                      gamma3__pochhammer(
                        add(list([int(2), mul2(int(-1), a), mul2(int(-1), b)])),
                        index,
                      ),
                    ),
                    power(sub(int(1), z), b),
                    power(z, add(list([a, mul2(int(-1), index), int(-1)]))),
                  ]),
                ),
                index,
                int(0),
                sub(n, int(1)),
              )
            },
          ]),
        ),
      )
    }
    give_up()
  })
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn gamma3__defgrad(name : Value, args : Array[Value], grads : Array[Value]) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  setf_get(name, q_grad, cons(list(args), list(grads))) |> ignore
}

///|
/// Top-level forms of the Fresnel / incomplete Beta section of gamma.lisp,
/// in source order. Called from init_gamma().
fn gamma3__init() -> Unit raise {
  let bags = list3(q_mlist, q_d_matrix, q_mequal)

  // fresnel_s
  putprop(q_p_fresnel_s, bags, q_distribute_u_over) |> ignore
  putprop(q_p_fresnel_s, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_fresnel_s, q_odd_function_reflect, q_reflection_rule) |> ignore
  gamma3__defgrad(q_p_fresnel_s, [q_d_z], [maxima_lit("sin((%pi*z^2)/2)")])
  putprop(
    q_p_fresnel_s,
    lread(
      "((z) ((mplus) ((mtimes) z ((%fresnel_s) z)) ((mtimes) ((mexpt) $%pi -1) ((%cos) ((mtimes) ((rat) 1 2) $%pi ((mexpt) z 2))))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_fresnel_s, q_simplim_pctfresnel_s, q_simplim_pctfunction)
  |> ignore
  // *fresnel-maxit* and *fresnel-min* are literal defvars.
  defvar_init(
    q_ear_fresnel_eps,
    num_mul(int(2), symval(q_n_plusflonum_epsilon_plus)),
  )

  // fresnel_c
  putprop(q_p_fresnel_c, bags, q_distribute_u_over) |> ignore
  putprop(q_p_fresnel_c, t, q_commutes_with_conjugate) |> ignore
  putprop(q_p_fresnel_c, q_odd_function_reflect, q_reflection_rule) |> ignore
  gamma3__defgrad(q_p_fresnel_c, [q_d_z], [maxima_lit("cos((%pi*z^2)/2)")])
  putprop(
    q_p_fresnel_c,
    lread(
      "((z) ((mplus) ((mtimes) z ((%fresnel_c) z)) ((mtimes) -1 ((mexpt) $%pi -1) ((%sin) ((mtimes) ((rat) 1 2) $%pi ((mexpt) z 2))))))",
    ),
    q_integral,
  )
  |> ignore
  putprop(q_p_fresnel_c, q_simplim_pctfresnel_c, q_simplim_pctfunction)
  |> ignore

  // Beta is symmetric beta(a,b) = beta(b,a)
  with_specials([(q_d_context, q_d_global), (q_context, q_d_global)], () => {
    meval(list3(list1(q_d_declare), q_p_beta, q_d_symmetric)) |> ignore
    // Let's remove built-in symbols from list for user-defined properties.
    set(q_d_props, remove(q_p_beta, symval(q_d_props)))
  })
  |> ignore

  // beta_incomplete
  // *beta-incomplete-maxit* and *beta-incomplete-eps* are literal defvars.
  putprop(q_p_beta_incomplete, bags, q_distribute_u_over) |> ignore
  gamma3__defgrad(q_p_beta_incomplete, [q_d_a, q_d_b, q_d_z], [
    // Derivative wrt a
    maxima_lit(
      "beta_incomplete(a,b,z)*log(z)-gamma(a)^2*hypergeometric_regularized([a,a,1-b],[a+1,a+1],z)*z^a",
    ),
    // Derivative wrt b
    maxima_lit(
      "gamma(b)^2*hypergeometric_regularized([b,b,1-a],[b+1,b+1],1-z)*(1-z)^b-beta_incomplete(b,a,1-z)*log(1-z)+beta(a,b)*(psi[0](b)-psi[0](b+a))",
    ),
    // The derivative wrt z
    maxima_lit("(1-z)^(b-1)*z^(a-1)"),
  ])
  putprop(
    q_p_beta_incomplete,
    lread(
      "((a b z) nil nil ((mplus) ((mtimes) -1 ((%beta_incomplete) ((mplus) 1 a) b z)) ((mtimes) ((%beta_incomplete) a b z) z)))",
    ),
    q_integral,
  )
  |> ignore

  // beta_incomplete_generalized
  putprop(q_p_beta_incomplete_generalized, bags, q_distribute_u_over) |> ignore
  putprop(
    q_p_beta_incomplete_generalized,
    q_conjugate_beta_incomplete_generalized,
    q_conjugate_function,
  )
  |> ignore
  gamma3__defgrad(
    q_p_beta_incomplete_generalized,
    [q_d_a, q_d_b, q_d_z1, q_d_z2],
    [
      // Derivative wrt a
      maxima_lit(
        "beta_incomplete(a,b,z2)*log(z2)+gamma(a)^2*(hypergeometric_regularized([a,a,1-b],[a+1,a+1],z1)*z1^a-hypergeometric_regularized([a,a,1-b],[a+1,a+1],z2)*z2^a)-beta_incomplete(a,b,z1)*log(z1)",
      ),
      // Derivative wrt b
      maxima_lit(
        "-(gamma(b)^2*(hypergeometric_regularized([b,b,1-a],[b+1,b+1],1-z1)*(1-z1)^b-hypergeometric_regularized([b,b,1-a],[b+1,b+1],1-z2)*(1-z2)^b))-beta_incomplete(b,a,1-z2)*log(1-z2)+beta_incomplete(b,a,1-z1)*log(1-z1)",
      ),
      // The derivative wrt z1
      maxima_lit("-((1-z1)^(b-1)*z1^(a-1))"),
      // The derivative wrt z2
      maxima_lit("(1-z2)^(b-1)*z2^(a-1)"),
    ],
  )
  putprop(
    q_p_beta_incomplete_generalized,
    lread(
      "((a b z1 z2) nil nil ((mplus) ((%beta_incomplete) ((mplus) 1 a) b z1) ((mtimes) ((%beta_incomplete_generalized) a b z1 z2) z1)) ((mplus) ((mtimes) -1 ((%beta_incomplete) ((mplus) 1 a) b z2)) ((mtimes) ((%beta_incomplete_generalized) a b z1 z2) z2)))",
    ),
    q_integral,
  )
  |> ignore

  // beta_incomplete_regularized
  putprop(q_p_beta_incomplete_regularized, bags, q_distribute_u_over) |> ignore
  gamma3__defgrad(q_p_beta_incomplete_regularized, [q_d_a, q_d_b, q_d_z], [
    // Derivative wrt a
    maxima_lit(
      "beta_incomplete_regularized(a,b,z)*(log(z)+psi[0](b+a)-psi[0](a))-(gamma(a)*hypergeometric_regularized([a,a,1-b],[a+1,a+1],z)*gamma(b+a)*z^a)/gamma(b)",
    ),
    // Derivative wrt b
    maxima_lit(
      "(gamma(b)*gamma(b+a)*hypergeometric_regularized([b,b,1-a],[b+1,b+1],1-z)*(1-z)^b)/gamma(a)+beta_incomplete_regularized(b,a,1-z)*(-log(1-z)-psi[0](b+a)+psi[0](b))",
    ),
    // The derivative wrt z
    maxima_lit("((1-z)^(b-1)*z^(a-1))/beta(a,b)"),
  ])
  putprop(
    q_p_beta_incomplete_regularized,
    lread(
      "((a b z) nil nil ((mplus) ((mtimes) -1 a ((%beta_incomplete_regularized) ((mplus) 1 a) b z) ((mexpt) ((mplus) a b) -1)) ((mtimes) ((%beta_incomplete_regularized) a b z) z)))",
    ),
    q_integral,
  )
  |> ignore
}
