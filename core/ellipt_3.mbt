// Port of src/ellipt.lisp, part 3: elliptic integrals (float routines in
// the maxima package and their simplifiers) and Carlson's integrals.

///|
/// `(coerce x '(complex flonum))`
fn ellipt__to_cflonum(x : Value) -> Value raise {
  make_complex(lfloat(realpart(x)), lfloat(imagpart(x)))
}

// Elliptic integrals

///|
/// Compute Carlson's incomplete or complete elliptic integral of the first
/// kind:
///
///                   INF
///                  /
///                  [                     1
///  RF(x, y, z) =   I    ----------------------------------- dt
///                  ]    SQRT(x + t) SQRT(y + t) SQRT(z + t)
///                  /
///                   0
///
///  x, y, and z may be complex.
fn crf(x : Value, y : Value, z : Value) -> Value raise {
  let errtol = expt(Flo(4.0 * double_float_epsilon), ellipt__q(1, 6))
  let c1 : Value = Flo(1.0 / 24.0)
  let c2 : Value = Flo(3.0 / 44.0)
  let c3 : Value = Flo(1.0 / 14.0)
  let mut x = ellipt__to_cflonum(x)
  let mut y = ellipt__to_cflonum(y)
  let mut z = ellipt__to_cflonum(z)
  while true {
    let mu = num_div(num_add(num_add(x, y), z), int(3))
    let x_dev = num_sub(int(2), num_div(num_add(mu, x), mu))
    let y_dev = num_sub(int(2), num_div(num_add(mu, y), mu))
    let z_dev = num_sub(int(2), num_div(num_add(mu, z), mu))
    if num_lt(
        num_max(num_max(num_abs(x_dev), num_abs(y_dev)), num_abs(z_dev)),
        errtol,
      ) {
      let e2 = num_sub(num_mul(x_dev, y_dev), num_mul(z_dev, z_dev))
      let e3 = num_mul(num_mul(x_dev, y_dev), z_dev)
      return num_div(
        num_add(
          num_add(
            int(1),
            num_mul(
              e2,
              num_sub(num_sub(num_mul(c1, e2), ellipt__q(1, 10)), num_mul(c2, e3)),
            ),
          ),
          num_mul(c3, e3),
        ),
        lsqrt(mu),
      )
    }
    let x_root = lsqrt(x)
    let y_root = lsqrt(y)
    let z_root = lsqrt(z)
    let lam = num_add(
      num_mul(x_root, num_add(y_root, z_root)),
      num_mul(y_root, z_root),
    )
    x = num_mul(num_add(x, lam), ellipt__q(1, 4))
    y = num_mul(num_add(y, lam), ellipt__q(1, 4))
    z = num_mul(num_add(z, lam), ellipt__q(1, 4))
  }
  Nil
}

// Elliptic integral of the first kind (Legendre's form):
//
//      phi
//     /
//     [             1
//     I    ------------------- ds
//     ]                  2
//     /    SQRT(1 - m SIN (s))
//     0

///|
fn elliptic_f(phi_arg : Value, m_arg : Value) -> Value raise {
  fn base(phi_arg : Value, m_arg : Value) -> Value raise {
    if realp(m_arg) && realp(phi_arg) {
      let phi = float(phi_arg)
      let m = float(m_arg)
      if num_gt(m, int(1)) {
        // A&S 17.4.15
        //
        // F(phi|m) = 1/sqrt(m)*F(theta|1/m)
        //
        // with sin(theta) = sqrt(m)*sin(phi)
        num_div(
          elliptic_f(lasin(num_mul(lsqrt(m), lsin(phi))), num_inv(m)),
          lsqrt(m),
        )
      } else if num_lt(m, int(0)) {
        // A&S 17.4.17
        let m = num_neg(m)
        let m_1 = num_add(int(1), m)
        let root = lsqrt(m_1)
        let m_m_1 = num_div(m, m_1)
        num_sub(
          num_div(elliptic_f(Flo(@math.PI / 2.0), m_m_1), root),
          num_div(elliptic_f(num_sub(Flo(@math.PI / 2.0), phi), m_m_1), root),
        )
      } else if num_eq(m, int(0)) {
        // A&S 17.4.19
        phi
      } else if num_eq(m, int(1)) {
        // A&S 17.4.21
        //
        // F(phi,1) = log(sec(phi)+tan(phi))
        //          = log(tan(pi/4+pi/2))
        llog(ltan(num_add(num_div(phi, int(2)), Flo(@math.PI / 4.0))))
      } else if minusp(phi) {
        num_neg(elliptic_f(num_neg(phi), m))
      } else if num_gt(phi, Flo(@math.PI)) {
        // A&S 17.4.3
        let (s, phi_rem) = num_truncate(phi, b=Flo(@math.PI))
        num_add(
          num_mul(num_mul(int(2), s), elliptic_k(m)),
          elliptic_f(phi_rem, m),
        )
      } else if num_le(phi, Flo(@math.PI / 2.0)) {
        let sin_phi = lsin(phi)
        let cos_phi = lcos(phi)
        let k = lsqrt(m)
        num_mul(
          sin_phi,
          bf_bf_rf(
            num_mul(cos_phi, cos_phi),
            num_mul(
              num_sub(int(1), num_mul(k, sin_phi)),
              num_add(int(1), num_mul(k, sin_phi)),
            ),
            Flo(1.0),
          ),
        )
      } else if num_lt(phi, Flo(@math.PI)) {
        num_add(
          num_mul(int(2), elliptic_k(m)),
          elliptic_f(num_sub(phi, Flo(@math.PI)), m),
        )
      } else {
        raise LispError::SimpleError(
          format_to_string(
            "Shouldn't happen! Unhandled case in elliptic-f: ~S ~S~%",
            [phi_arg, m_arg],
          ),
        )
      }
    } else {
      let phi = ellipt__to_cflonum(phi_arg)
      let m = ellipt__to_cflonum(m_arg)
      let sin_phi = lsin(phi)
      let cos_phi = lcos(phi)
      let k = lsqrt(m)
      num_mul(
        sin_phi,
        crf(
          num_mul(cos_phi, cos_phi),
          num_mul(
            num_sub(int(1), num_mul(k, sin_phi)),
            num_add(int(1), num_mul(k, sin_phi)),
          ),
          Flo(1.0),
        ),
      )
    }
  }

  // Elliptic F is quasi-periodic wrt to z:
  //
  // F(z|m) = F(z - pi*round(Re(z)/pi)|m) + 2*round(Re(z)/pi)*K(m)
  let period = num_round(realpart(phi_arg), b=Flo(@math.PI)).0
  num_add(
    base(num_sub(phi_arg, num_mul(Flo(@math.PI), period)), m_arg),
    if zerop(period) {
      int(0)
    } else {
      num_mul(num_mul(int(2), period), bf_to(elliptic_k(m_arg)))
    },
  )
}

///|
/// Complete elliptic integral of the first kind
fn elliptic_k(m : Value) -> Value raise {
  if realp(m) {
    if num_lt(m, int(0)) {
      // A&S 17.4.17
      let m = num_neg(m)
      let m_1 = num_add(int(1), m)
      let root = lsqrt(m_1)
      let m_m_1 = num_div(m, m_1)
      num_sub(
        num_div(elliptic_k(m_m_1), root),
        num_div(elliptic_f(Flo(0.0), m_m_1), root),
      )
    } else if num_eq(m, int(0)) {
      // A&S 17.4.19
      Flo(@math.PI / 2.0)
    } else if num_eq(m, int(1)) {
      merr("elliptic_kc: elliptic_kc(1) is undefined.", [])
    } else {
      bf_bf_rf(Flo(0.0), num_sub(int(1), m), Flo(1.0))
    }
  } else {
    bf_bf_rf(Flo(0.0), num_sub(int(1), m), Flo(1.0))
  }
}

// Elliptic integral of the second kind (Legendre's form):
//
//      phi
//     /
//     [                  2
//     I    SQRT(1 - m SIN (s)) ds
//     ]
//     /
//      0

///|
fn elliptic_e(phi : Value, m : Value) -> Value raise {
  fn base(phi : Value, m : Value) -> Value raise {
    if num_eq(m, int(0)) {
      // A&S 17.4.23
      phi
    } else if num_eq(m, int(1)) {
      // A&S 17.4.25
      lsin(phi)
    } else {
      let sin_phi = lsin(phi)
      let cos_phi = lcos(phi)
      let k = lsqrt(m)
      let y = num_mul(
        num_sub(int(1), num_mul(k, sin_phi)),
        num_add(int(1), num_mul(k, sin_phi)),
      )
      num_sub(
        num_mul(sin_phi, bf_bf_rf(num_mul(cos_phi, cos_phi), y, Flo(1.0))),
        num_mul(
          num_mul(num_div(m, int(3)), expt(sin_phi, int(3))),
          bf_bf_rd(num_mul(cos_phi, cos_phi), y, Flo(1.0)),
        ),
      )
    }
  }

  // Elliptic E is quasi-periodic wrt to phi:
  //
  // E(z|m) = E(z - %pi*round(Re(z)/%pi)|m) + 2*round(Re(z)/%pi)*E(m)
  let period = num_round(realpart(phi), b=Flo(@math.PI)).0
  num_add(
    base(num_sub(phi, num_mul(Flo(@math.PI), period)), m),
    num_mul(num_mul(int(2), period), elliptic_ec(m)),
  )
}

///|
/// Complete version
fn elliptic_ec(m : Value) -> Value raise {
  if num_eq(m, int(0)) {
    // A&S 17.4.23
    Flo(@math.PI / 2.0)
  } else if num_eq(m, int(1)) {
    // A&S 17.4.25
    Flo(1.0)
  } else {
    let y = num_sub(int(1), m)
    num_sub(
      bf_bf_rf(Flo(0.0), y, Flo(1.0)),
      num_mul(num_div(m, int(3)), bf_bf_rd(Flo(0.0), y, Flo(1.0))),
    )
  }
}

// Define the elliptic integrals for maxima
//
// We use the definitions given in A&S 17.2.6 and 17.2.8.  In particular:
//
//                 phi
//                /
//                [             1
// F(phi|m)  =    I    ------------------- ds
//                ]                  2
//                /    SQRT(1 - m SIN (s))
//                 0
//
// and
//
//              phi
//             /
//             [                  2
// E(phi|m) =  I    SQRT(1 - m SIN (s)) ds
//             ]
//             /
//              0
//
// That is, we do not use the modular angle, alpha, as the second arg; the
// parameter m = sin(alpha)^2 is used.

///|
fn simp__pctelliptic_f(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_f, [q_d_phi, q_d_m])
  let phi = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if float_numerical_eval_p(list2(phi, m)).truthy() {
    // Numerically evaluate it
    return maxima_to(elliptic_f(d_float(phi), d_float(m)))
  }
  let args = complex_float_numerical_eval_p(list2(phi, m))
  if args.truthy() {
    let phi = first(args)
    let m = second(args)
    return maxima_to(elliptic_f(bf_to(d_float(phi)), bf_to(d_float(m))))
  }
  if bigfloat_numerical_eval_p(list2(phi, m)).truthy() {
    return maxima_to(
      bf_bf_elliptic_f(bf_to(d_bfloat(phi)), bf_to(d_bfloat(m))),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list2(phi, m))
  if args.truthy() {
    let phi = first(args)
    let m = second(args)
    return maxima_to(
      bf_bf_elliptic_f(bf_to(d_bfloat(phi)), bf_to(d_bfloat(m))),
    )
  }
  if zerop1(phi).truthy() {
    int(0)
  } else if zerop1(m).truthy() {
    // A&S 17.4.19
    phi
  } else if onep1(m).truthy() {
    // A&S 17.4.21.  Let's pick the log tan form.  But this isn't right if
    // we know that abs(phi) > %pi/2, where elliptic_f is undefined (or
    // infinity).
    if !eq(q_d_pos, csign(sub(d_abs(phi), div(q_d__pctpi, int(2))))) {
      ftake(q_p_log, [
        ftake(q_p_tan, [
          add2(
            mul2(q_d__pctpi, div(int(1), int(4))),
            mul2(ellipt__mq(1, 2), phi),
          ),
        ]),
      ])
    } else {
      merr("elliptic_f: elliptic_f(~:M, ~:M) is undefined.", [phi, m])
    }
  } else if alike1(phi, div(q_d__pctpi, int(2))).truthy() {
    // Complete elliptic integral
    ftake(q_p_elliptic_kc, [m])
  } else {
    // Nothing to do
    ellipt__give_up(q_p_elliptic_f, [phi, m], form)
  }
}

///|
fn simp__pctelliptic_e(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_e, [q_d_phi, q_d_m])
  let phi = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if float_numerical_eval_p(list2(phi, m)).truthy() {
    // Numerically evaluate it
    return complexify(elliptic_e(d_float(phi), d_float(m)))
  }
  if complex_float_numerical_eval_p(list2(phi, m)).truthy() {
    return complexify(
      bf_bf_elliptic_e(
        complex(d_float(d_realpart(phi)), i=d_float(d_imagpart(phi))),
        complex(d_float(d_realpart(m)), i=d_float(d_imagpart(m))),
      ),
    )
  }
  if bigfloat_numerical_eval_p(list2(phi, m)).truthy() {
    return maxima_to(
      bf_bf_elliptic_e(bf_to(d_bfloat(phi)), bf_to(d_bfloat(m))),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list2(phi, m))
  if args.truthy() {
    let phi = first(args)
    let m = second(args)
    return maxima_to(
      bf_bf_elliptic_e(bf_to(d_bfloat(phi)), bf_to(d_bfloat(m))),
    )
  }
  if zerop1(phi).truthy() {
    return int(0)
  }
  if zerop1(m).truthy() {
    // A&S 17.4.23
    return phi
  }
  if onep1(m).truthy() {
    // A&S 17.4.25, but handle periodicity:
    // elliptic_e(x,m) = elliptic_e(x-%pi*round(x/%pi), m)
    //                    + 2*round(x/%pi)*elliptic_ec(m)
    //
    // Or
    //
    // elliptic_e(x,1) = sin(x-%pi*round(x/%pi)) + 2*round(x/%pi)*elliptic_ec(m)
    let mult_pi = ftake(q_p_round, [div(phi, q_d__pctpi)])
    return add2(
      ftake(q_p_sin, [sub(phi, mul2(q_d__pctpi, mult_pi))]),
      mul2(int(2), mul2(mult_pi, ftake(q_p_elliptic_ec, [m]))),
    )
  }
  if alike1(phi, div(q_d__pctpi, int(2))).truthy() {
    // Complete elliptic integral
    return ftake(q_p_elliptic_ec, [m])
  }
  let numeric_period = () => {
    let r = ftake(q_p_round, [div(phi, q_d__pctpi)])
    d_numberp(r).truthy() && !zerop1(r).truthy()
  }
  if d_numberp(phi).truthy() && numeric_period() {
    // Handle the case where phi is a number where we can apply the
    // periodicity property without blowing up the expression.
    return add2(
      ftake(q_p_elliptic_e, [
        add2(
          phi,
          mul2(
            mul2(int(-1), q_d__pctpi),
            ftake(q_p_round, [div(phi, q_d__pctpi)]),
          ),
        ),
        m,
      ]),
      mul2(
        int(2),
        mul2(
          ftake(q_p_round, [div(phi, q_d__pctpi)]),
          ftake(q_p_elliptic_ec, [m]),
        ),
      ),
    )
  }
  // Nothing to do
  ellipt__give_up(q_p_elliptic_e, [phi, m], form)
}

// Complete elliptic integrals
//
// elliptic_kc(m) = elliptic_f(%pi/2, m)
//
// elliptic_ec(m) = elliptic_e(%pi/2, m)

// We support a simplim%function. The function is looked up in simplimit
// and handles specific values of the function.

///|
fn simplim_pctelliptic_kc(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let m = limit(cadr(expr), var_, val, q_think)
  if onep1(m).truthy() {
    // For an argument 1 return $infinity.
    q_d_infinity
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list2(list1(q_p_elliptic_kc), m))
  }
}

///|
fn simp__pctelliptic_kc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_kc, [q_d_m])
  let m = simpcheck(nth(1, form), p__pctsimpflag)
  if onep1(m).truthy() {
    // elliptic_kc(1) is complex infinity. Maxima can not handle infinities
    // correctly, throw a Maxima error.
    return merr("elliptic_kc: elliptic_kc(~:M) is undefined.", [m])
  }
  if float_numerical_eval_p(list1(m)).truthy() {
    // Numerically evaluate it
    return maxima_to(elliptic_k(d_float(m)))
  }
  if complex_float_numerical_eval_p(list1(m)).truthy() {
    return complexify(
      bf_bf_elliptic_k(
        complex(d_float(d_realpart(m)), i=d_float(d_imagpart(m))),
      ),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list1(m))
  if args.truthy() {
    let m = first(args)
    return maxima_to(bf_bf_elliptic_k(bf_to(d_bfloat(m))))
  }
  if zerop1(m).truthy() {
    mul2(ellipt__mq(1, 2), q_d__pctpi)
  } else if alike1(m, ellipt__mq(1, 2)).truthy() {
    // http://functions.wolfram.com/EllipticIntegrals/EllipticK/03/01/
    //
    // elliptic_kc(1/2) = 8*%pi^(3/2)/gamma(-1/4)^2
    div(
      mul2(int(8), power(q_d__pctpi, div(int(3), int(2)))),
      power(gm(div(int(-1), int(4))), int(2)),
    )
  } else if eql(int(-1), m) {
    // elliptic_kc(-1) = gamma(1/4)^2/(4*sqrt(2*%pi))
    div(
      power(gm(div(int(1), int(4))), int(2)),
      mul2(int(4), power(mul2(int(2), q_d__pctpi), ellipt__mq(1, 2))),
    )
  } else if alike1(
      m,
      add2(int(17), mul2(int(-12), power(int(2), ellipt__mq(1, 2)))),
    ).truthy() {
    // elliptic_kc(17-12*sqrt(2)) = 2*(2+sqrt(2))*%pi^(3/2)/gamma(-1/4)^2
    div(
      mul2(
        int(2),
        mul2(
          add2(int(2), power(int(2), ellipt__mq(1, 2))),
          power(q_d__pctpi, div(int(3), int(2))),
        ),
      ),
      power(gm(div(int(-1), int(4))), int(2)),
    )
  } else if alike1(
      m,
      div(add2(int(2), power(int(3), ellipt__mq(1, 2))), int(4)),
    ).truthy() ||
    alike1(
      m,
      add2(div(power(int(3), ellipt__mq(1, 2)), int(4)), ellipt__mq(1, 2)),
    ).truthy() {
    // elliptic_kc((sqrt(3)+2)/4) = sqrt(%pi)*gamma(1/3)/gamma(5/6).
    //
    // First evaluate this integral, where y = sqrt(1+t^3).
    //
    //   integrate(1/y,t,-1,inf) = integrate(1/y,t,-1,0) + integrate(1/y,t,0,inf).
    //
    // The second integral, maxima gives beta(1/6,1/3)/3.
    //
    // For the first, we can use the change of variable x=-u^(1/3) to get
    //
    //   integrate(1/sqrt(1-u)/u^(2/3),u,0,1)
    //
    // which is a beta integral that maxima can evaluate to
    // beta(1/3,1/2)/3.  Then we see the value of the initial integral is
    //
    //    beta(1/6,1/3)/3 + beta(1/3,1/2)/3
    //
    // (Thanks to Guilherme Namen for this derivation on the mailing list,
    // 2023-03-09.)
    //
    // We can simplify this expression by converting to gamma functions:
    //
    //   beta(1/6,1/3)/3 + beta(1/3,1/2)/3 =
    //     (gamma(1/3)*(gamma(1/6)*gamma(5/6)+%pi))/(3*sqrt(%pi)*gamma(5/6));
    //
    // Using the reflection formula gamma(1-z)*gamma(z) = %pi/sin(%pi*z),
    // we can write gamma(1/6)*gamma(5/6) = %pi/sin(%pi*1/6) = 2*%pi.
    // Finally, we have
    //
    //   sqrt(%pi)*gamma(1/3)/gamma(5/6);
    //
    // All that remains is to show that integrate(1/y,t) can be written as
    // an inverse_jacobi_cn function with modulus (sqrt(3)+2)/4.
    //
    // First apply the substitution
    //
    //    s = (t+sqrt(3)+1)/(t-sqrt(3)+1).  We then have the integral
    //
    //   C*integrate(1/sqrt(s^2-1)/sqrt(s^2+4*sqrt(3)+7),s)
    //
    // where C is some constant.  From A&S 14.4.49, we can see this
    // integral is the inverse_jacobi_nc function with modulus of
    // (4*sqrt(3)+7)/(4*sqrt(3)+7+1) = (sqrt(3)+2)/4.
    div(
      mul2(
        power(q_d__pctpi, ellipt__mq(1, 2)),
        ftake(q_p_gamma, [div(int(1), int(3))]),
      ),
      ftake(q_p_gamma, [div(int(5), int(6))]),
    )
  } else if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/08.02.26.0001.01
    //
    //   elliptic_kc(z) = %pi/2*%f[2,1]([1/2,1/2],[1], z)
    mul2(
      div(q_d__pctpi, int(2)),
      ftake(q_p_hypergeometric, [
        make_mlist(list2(ellipt__mq(1, 2), ellipt__mq(1, 2))),
        make_mlist(list1(int(1))),
        m,
      ]),
    )
  } else {
    // Nothing to do
    ellipt__give_up(q_p_elliptic_kc, [m], form)
  }
}

///|
fn simp__pctelliptic_ec(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_ec, [q_d_m])
  let m = simpcheck(nth(1, form), p__pctsimpflag)
  if float_numerical_eval_p(list1(m)).truthy() {
    // Numerically evaluate it
    return complexify(elliptic_ec(d_float(m)))
  }
  let args = complex_float_numerical_eval_p(list1(m))
  if args.truthy() {
    let m = first(args)
    return complexify(bf_bf_elliptic_ec(bf_to(d_float(m))))
  }
  let args = complex_bigfloat_numerical_eval_p(list1(m))
  if args.truthy() {
    let m = first(args)
    return maxima_to(bf_bf_elliptic_ec(bf_to(d_bfloat(m))))
  }
  // Some special cases we know about.
  if zerop1(m).truthy() {
    div(q_d__pctpi, int(2))
  } else if onep1(m).truthy() {
    int(1)
  } else if alike1(m, ellipt__mq(1, 2)).truthy() {
    // elliptic_ec(1/2). Use the identity
    //
    //   elliptic_ec(z)*elliptic_kc(1-z) - elliptic_kc(z)*elliptic_kc(1-z)
    //     + elliptic_ec(1-z)*elliptic_kc(z) = %pi/2;
    //
    // Let z = 1/2 to get
    //
    //   %pi^(3/2)*'elliptic_ec(1/2)/gamma(3/4)^2-%pi^3/(4*gamma(3/4)^4) = %pi/2
    //
    // since we know that elliptic_kc(1/2) = %pi^(3/2)/(2*gamma(3/4)^2).
    // Hence
    //
    //   elliptic_ec(1/2)
    //      = (2*%pi*gamma(3/4)^4+%pi^3)/(4*%pi^(3/2)*gamma(3/4)^2)
    //      = gamma(3/4)^2/(2*sqrt(%pi))+%pi^(3/2)/(4*gamma(3/4)^2)
    add2(
      div(
        power(ftake(q_p_gamma, [div(int(3), int(4))]), int(2)),
        mul2(int(2), power(q_d__pctpi, ellipt__mq(1, 2))),
      ),
      div(
        power(q_d__pctpi, div(int(3), int(2))),
        mul2(int(4), power(ftake(q_p_gamma, [div(int(3), int(4))]), int(2))),
      ),
    )
  } else if zerop1(add2(int(1), m)).truthy() {
    // elliptic_ec(-1). Use the identity
    // http://functions.wolfram.com/08.01.17.0002.01
    //
    //   elliptic_ec(z) = sqrt(1 - z)*elliptic_ec(z/(z-1))
    //
    // Let z = -1 to get
    //
    //   elliptic_ec(-1) = sqrt(2)*elliptic_ec(1/2)
    //
    // Should we expand out elliptic_ec(1/2) using the above result?
    mul2(
      power(int(2), ellipt__mq(1, 2)),
      ftake(q_p_elliptic_ec, [ellipt__mq(1, 2)]),
    )
  } else if symval(q_d_hypergeometric_representation).truthy() {
    // See http://functions.wolfram.com/08.01.26.0001.01
    //
    //   elliptic_ec(z) = %pi/2*%f[2,1]([-1/2,1/2],[1], z)
    mul2(
      div(q_d__pctpi, int(2)),
      ftake(q_p_hypergeometric, [
        make_mlist(list2(ellipt__mq(-1, 2), ellipt__mq(1, 2))),
        make_mlist(list1(int(1))),
        m,
      ]),
    )
  } else {
    // Nothing to do
    ellipt__give_up(q_p_elliptic_ec, [m], form)
  }
}

// Elliptic integral of the third kind:
//
// (A&S 17.2.14)
//
//                 phi
//                /
//                [                     1
// PI(n;phi|m) =  I    ----------------------------------- ds
//                ]                  2               2
//                /    SQRT(1 - m SIN (s)) (1 - n SIN (s))
//                 0
//
// As with E and F, we do not use the modular angle alpha but the parameter
// m = sin(alpha)^2.

///|
fn simp__pctelliptic_pi(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_pi, [q_d_n, q_d_phi, q_d_m])
  let n = simpcheck(nth(1, form), p__pctsimpflag)
  let phi = simpcheck(nth(2, form), p__pctsimpflag)
  let m = simpcheck(nth(3, form), p__pctsimpflag)
  if float_numerical_eval_p(list3(n, phi, m)).truthy() {
    // Numerically evaluate it
    return elliptic_pi(d_float(n), d_float(phi), d_float(m))
  }
  let args = complex_float_numerical_eval_p(list3(n, phi, m))
  if args.truthy() {
    let n = first(args)
    let phi = second(args)
    let m = third(args)
    return elliptic_pi(
      bf_to(d_float(n)),
      bf_to(d_float(phi)),
      bf_to(d_float(m)),
    )
  }
  if bigfloat_numerical_eval_p(list3(n, phi, m)).truthy() {
    return maxima_to(bf_bf_elliptic_pi(bf_to(n), bf_to(phi), bf_to(m)))
  }
  let args = complex_bigfloat_numerical_eval_p(list3(n, phi, m))
  if args.truthy() {
    let n = first(args)
    let phi = second(args)
    let m = third(args)
    return maxima_to(bf_bf_elliptic_pi(bf_to(n), bf_to(phi), bf_to(m)))
  }
  if zerop1(n).truthy() {
    ftake(q_p_elliptic_f, [phi, m])
  } else if zerop1(m).truthy() {
    // 3 cases depending on n < 1, n > 1, or n = 1.
    let s = asksign(add2(int(-1), n))
    if eq(s, q_d_positive) {
      div(
        ftake(q_p_atanh, [
          mul2(
            power(add2(n, int(-1)), ellipt__mq(1, 2)),
            ftake(q_p_tan, [phi]),
          ),
        ]),
        power(add2(n, int(-1)), ellipt__mq(1, 2)),
      )
    } else if eq(s, q_d_negative) {
      div(
        ftake(q_p_atan, [
          mul2(power(sub(int(1), n), ellipt__mq(1, 2)), ftake(q_p_tan, [phi])),
        ]),
        power(sub(int(1), n), ellipt__mq(1, 2)),
      )
    } else if eq(s, q_d_zero) {
      ftake(q_p_tan, [phi])
    } else {
      Nil
    }
  } else {
    // Nothing to do
    ellipt__give_up(q_p_elliptic_pi, [n, phi, m], form)
  }
}

///|
/// Complete elliptic-pi.  That is phi = %pi/2.  Then
/// elliptic_pi(n,m)
///   = Rf(0, 1-m,1) + Rj(0,1-m,1-n)*n/3;
fn elliptic_pi_complete(n : Value, m : Value) -> Value raise {
  bf_add(
    bf_bf_rf(int(0), num_sub(int(1), m), int(1)),
    bf_muln([
      ellipt__q(1, 3),
      n,
      bf_bf_rj(int(0), num_sub(int(1), m), int(1), num_sub(int(1), n)),
    ]),
  )
}

// To compute elliptic_pi for all z, we use the property
// (http://functions.wolfram.com/08.06.16.0002.01)
//
// elliptic_pi(n, z + %pi*k, m)
//   = 2*k*elliptic_pi(n, %pi/2, m) + elliptic_pi(n, z, m)
//
// So we are left with computing the integral for 0 <= z < %pi.  Using
// Carlson's formulation produces the wrong values for %pi/2 < z < %pi.
// How to do that?
//
// Let
//
//   I(a,b) = integrate(1/(1-n*sin(x)^2)/sqrt(1 - m*sin(x)^2), x, a, b)
//
// That is, I(a,b) is the integral for the elliptic_pi function but with a
// lower limit of a and an upper limit of b.
//
// Then, we want to compute I(0, z), with %pi <= z < %pi.  Let w = z +
// %pi/2, 0 <= w < %pi/2.  Then
//
//   I(0, w+%pi/2) = I(0, %pi/2) + I(%pi/2, w+%pi/2)
//
// To evaluate I(%pi/2, w+%pi/2), use a change of variables:
//
//   changevar('integrate(1/(1-n*sin(x)^2)/sqrt(1 - m*sin(x)^2), x, %pi/2, w + %pi/2),
//      x-%pi+u,u,x)
//
//     = integrate(-1/(sqrt(1-m*sin(u)^2)*(1-n*sin(u)^2)),u,%pi/2-w,%pi/2)
//     = I(%pi/2-w,%pi/2)
//     = I(0,%pi/2) - I(0,%pi/2-w)
//
// Thus,
//
//   I(0,%pi/2+w) = 2*I(0,%pi/2) - I(0,%pi/2-w)
//
// This allows us to compute the general result with 0 <= z < %pi
//
//   I(0, k*%pi + z) = 2*k*I(0,%pi/2) + I(0,z);
//
// If 0 <= z < %pi/2, then the we are done.  If %pi/2 <= z < %pi, let z =
// w+%pi/2. Then
//
//   I(0,z) = 2*I(0,%pi/2) - I(0,%pi/2-w)
//
// Or, since w = z-%pi/2:
//
//   I(0,z) = 2*I(0,%pi/2) - I(0,%pi-z)

///|
fn elliptic_pi(n : Value, phi : Value, m : Value) -> Value raise {
  // elliptic_pi(n, -phi, m) = -elliptic_pi(n, phi, m).  That is, it is an
  // odd function of phi.
  if minusp(realpart(phi)) {
    return num_neg(elliptic_pi(n, num_neg(phi), m))
  }
  // Note: Carlson's DRJ has n defined as the negative of the n given in
  // A&S.
  fn base(n : Value, phi : Value, m : Value) -> Value raise {
    // elliptic_pi(n,phi,m) =
    //   sin(phi)*Rf(cos(phi)^2, 1-m*sin(phi)^2, 1)
    //   - (-n / 3) * sin(phi)^3
    //     * Rj(cos(phi)^2, 1-m*sin(phi)^2, 1, 1-n*sin(phi)^2)
    let nn = num_neg(n)
    let sin_phi = lsin(phi)
    let cos_phi = lcos(phi)
    let k = lsqrt(m)
    let k2sin = num_mul(
      num_sub(int(1), num_mul(k, sin_phi)),
      num_add(int(1), num_mul(k, sin_phi)),
    )
    num_sub(
      num_mul(sin_phi, bf_bf_rf(num_mul(cos_phi, cos_phi), k2sin, Flo(1.0))),
      num_mul(
        num_mul(num_div(nn, int(3)), expt(sin_phi, int(3))),
        bf_bf_rj(
          num_mul(cos_phi, cos_phi),
          k2sin,
          Flo(1.0),
          num_sub(int(1), num_mul(n, num_mul(sin_phi, sin_phi))),
        ),
      ),
    )
  }

  // FIXME: Reducing the arg by pi has significant round-off.  Consider
  // doing something better.
  let cycles = num_round(realpart(phi), b=Flo(@math.PI)).0
  let rem = num_sub(phi, num_mul(cycles, Flo(@math.PI)))
  let complete = elliptic_pi_complete(n, m)
  maxima_to(
    num_add(num_mul(num_mul(int(2), cycles), complete), base(n, rem, m)),
  )
}

// Define Carlson's elliptic integrals.

///|
fn simp__pctcarlson_rc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_carlson_rc, [q_d_x, q_d_y])
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  let y = simpcheck(nth(2, form), p__pctsimpflag)
  fn floatify(z : Value) -> Value raise {
    // If z is a complex rational, convert to a complex double-float.
    // Otherwise, leave it as is.  If we don't do this, %i is handled as
    // #c(0 1), which makes bf-rc use single-float arithmetic instead of
    // the desired double-float.
    if complexp(z) && rationalp(realpart(z)) {
      complex(float(realpart(z)), i=float(imagpart(z)))
    } else {
      z
    }
  }

  fn calc(x : Value, y : Value) -> Value raise {
    maxima_to(bf_bf_rc(floatify(bf_to(x)), floatify(bf_to(y))))
  }

  // See comments from bf-rc
  if float_numerical_eval_p(list2(x, y)).truthy() {
    return calc(d_float(x), d_float(y))
  }
  if bigfloat_numerical_eval_p(list2(x, y)).truthy() {
    return calc(d_bfloat(x), d_bfloat(y))
  }
  let args = complex_float_numerical_eval_p(list2(x, y))
  if args.truthy() {
    return calc(d_float(first(args)), d_float(second(args)))
  }
  let args = complex_bigfloat_numerical_eval_p(list2(x, y))
  if args.truthy() {
    return calc(d_bfloat(first(args)), d_bfloat(second(args)))
  }
  if zerop1(x).truthy() && onep1(y).truthy() {
    // rc(0, 1) = %pi/2
    div(q_d__pctpi, int(2))
  } else if zerop1(x).truthy() && alike1(y, div(int(1), int(4))).truthy() {
    // rc(0,1/4) = %pi
    q_d__pctpi
  } else if eql(x, int(2)) && onep1(y).truthy() {
    // rc(2,1) = 1/2*integrate(1/sqrt(t+2)/(t+1), t, 0, inf)
    //   = (log(sqrt(2)+1)-log(sqrt(2)-1))/2
    // ratsimp(logcontract(%)),algebraic:
    //   = -log(3-2^(3/2))/2
    //   = -log(sqrt(3-2^(3/2)))
    //   = -log(sqrt(2)-1)
    //   = log(1/(sqrt(2)-1))
    // ratsimp(%),algebraic;
    //   = log(sqrt(2)+1)
    ftake(q_p_log, [add2(int(1), power(int(2), ellipt__mq(1, 2)))])
  } else if eq(x, q_d__pcti) && alike1(y, add2(int(1), q_d__pcti)).truthy() {
    // rc(%i, %i+1) = 1/2*integrate(1/sqrt(t+%i)/(t+%i+1), t, 0, inf)
    //   = %pi/2-atan((-1)^(1/4))
    // ratsimp(logcontract(ratsimp(rectform(%o42)))),algebraic;
    //   = (%i*log(3-2^(3/2))+%pi)/4
    //   = (%i*log(3-2^(3/2)))/4+%pi/4
    //   = %i*log(sqrt(3-2^(3/2)))/2+%pi/4
    // sqrtdenest(%);
    //   = %pi/4 + %i*log(sqrt(2)-1)/2
    add2(
      div(q_d__pctpi, int(4)),
      muln_([
        q_d__pcti,
        ellipt__mq(1, 2),
        ftake(q_p_log, [sub(power(int(2), ellipt__mq(1, 2)), int(1))]),
      ]),
    )
  } else if zerop1(x).truthy() && eq(y, q_d__pcti) {
    // rc(0,%i) = 1/2*integrate(1/(sqrt(t)*(t+%i)), t, 0, inf)
    //   = -((sqrt(2)*%i-sqrt(2))*%pi)/4
    //   = ((1-%i)*%pi)/2^(3/2)
    div(
      mul2(sub(int(1), q_d__pcti), q_d__pctpi),
      power(int(2), ellipt__mq(3, 2)),
    )
  } else if alike1(x, y).truthy() && eq(d_sign(d_realpart(x)), q_d_pos) {
    // carlson_rc(x,x) = 1/2*integrate(1/sqrt(t+x)/(t+x), t, 0, inf)
    //    = 1/sqrt(x)
    power(x, ellipt__mq(-1, 2))
  } else if alike1(x, power(div(add2(int(1), y), int(2)), int(2))).truthy() &&
    eq(d_sign(d_realpart(y)), q_d_pos) {
    // Rc(((1+x)/2)^2,x) = log(x)/(x-1) for x > 0.
    //
    // This is done by looking at Rc(x,y) and seeing if ((1+y)/2)^2 is the
    // same as x.
    div(ftake(q_p_log, [y]), sub(y, int(1)))
  } else {
    ellipt__give_up(q_p_carlson_rc, [x, y], form)
  }
}

///|
fn simp__pctcarlson_rd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_carlson_rd, [q_d_x, q_d_y, q_d_z])
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  let y = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  fn calc(x : Value, y : Value, z : Value) -> Value raise {
    maxima_to(bf_bf_rd(bf_to(x), bf_to(y), bf_to(z)))
  }

  // See https://dlmf.nist.gov/19.20.E18
  if eql(x, int(1)) && eql(x, y) && eql(y, z) {
    // Rd(1,1,1) = 1
    return int(1)
  }
  if alike1(x, y).truthy() && alike1(y, z).truthy() {
    // Rd(x,x,x) = x^(-3/2)
    return power(x, div(int(-3), int(2)))
  }
  if zerop1(x).truthy() && alike1(y, z).truthy() {
    // Rd(0,y,y) = 3/4*%pi*y^(-3/2)
    return muln_([
      div(int(3), int(4)),
      q_d__pctpi,
      power(y, div(int(-3), int(2))),
    ])
  }
  if alike1(y, z).truthy() {
    // Rd(x,y,y) = 3/(2*(y-x))*(Rc(x, y) - sqrt(x)/y)
    return mul2(
      div(int(3), mul2(int(2), sub(y, x))),
      sub(
        ftake(q_p_carlson_rc, [x, y]),
        div(power(x, ellipt__mq(1, 2)), y),
      ),
    )
  }
  if alike1(x, y).truthy() {
    // Rd(x,x,z) = 3/(z-x)*(Rc(z,x) - 1/sqrt(z))
    return mul2(
      div(int(3), sub(z, x)),
      sub(
        ftake(q_p_carlson_rc, [z, x]),
        div(int(1), power(z, ellipt__mq(1, 2))),
      ),
    )
  }
  if eql(z, int(1)) &&
    ((eql(x, int(0)) && eql(y, int(2))) || (eql(x, int(2)) && eql(y, int(0)))) {
    // Rd(0,2,1) = 3*(gamma(3/4)^2)/sqrt(2*%pi)
    // See https://dlmf.nist.gov/19.20.E22.
    //
    // But that's the same as 3*sqrt(%pi)*gamma(3/4)/gamma(1/4).  We can
    // see this by taking the ratio to get gamma(1/4)*gamma(3/4)/sqrt(2)*%pi.
    // But gamma(1/4)*gamma(3/4) = beta(1/4,3/4) = sqrt(2)*%pi.  Hence, the
    // ratio is 1.
    //
    // Note also that Rd(x,y,z) = Rd(y,x,z)
    return muln_([
      int(3),
      power(q_d__pctpi, ellipt__mq(1, 2)),
      div(
        ftake(q_p_gamma, [div(int(3), int(4))]),
        ftake(q_p_gamma, [div(int(1), int(4))]),
      ),
    ])
  }
  if (eql(x, int(0)) || eql(y, int(0))) && eql(z, int(1)) {
    // 1/3*m*Rd(0,1-m,1) = K(m) - E(m).
    // See https://dlmf.nist.gov/19.25.E1
    //
    // Thus, Rd(0,y,1) = 3/(1-y)*(K(1-y) - E(1-y))
    //
    // Note that Rd(x,y,z) = Rd(y,x,z).
    let m = sub(int(1), y)
    return mul2(
      div(int(3), m),
      sub(ftake(q_p_elliptic_kc, [m]), ftake(q_p_elliptic_ec, [m])),
    )
  }
  if (eql(x, int(0)) && eql(y, int(1))) || (eql(x, int(1)) && eql(y, int(0))) {
    // 1/3*m*(1-m)*Rd(0,1,1-m) = E(m) - (1-m)*K(m)
    // See https://dlmf.nist.gov/19.25.E1
    //
    // Thus
    //  Rd(0,1,z) = 3/(z*(1-z))*(E(1-z) - z*K(1-z))
    // Recall that Rd(x,y,z) = Rd(y,x,z).
    return mul2(
      div(int(3), mul2(z, sub(int(1), z))),
      sub(
        ftake(q_p_elliptic_ec, [sub(int(1), z)]),
        mul2(z, ftake(q_p_elliptic_kc, [sub(int(1), z)])),
      ),
    )
  }
  if float_numerical_eval_p(list3(x, y, z)).truthy() {
    return calc(d_float(x), d_float(y), d_float(z))
  }
  if bigfloat_numerical_eval_p(list3(x, y, z)).truthy() {
    return calc(d_bfloat(x), d_bfloat(y), d_bfloat(z))
  }
  let args = complex_float_numerical_eval_p(list3(x, y, z))
  if args.truthy() {
    return calc(
      d_float(first(args)),
      d_float(second(args)),
      d_float(third(args)),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list3(x, y, z))
  if args.truthy() {
    return calc(
      d_bfloat(first(args)),
      d_bfloat(second(args)),
      d_bfloat(third(args)),
    )
  }
  ellipt__give_up(q_p_carlson_rd, [x, y, z], form)
}

///|
/// `(some pred (list (list x y z) (list x z y) (list y x z) (list y z x)
/// (list z x y) (list z y x)))` where PRED returns a Lisp value.
fn ellipt__some_perm(
  x : Value,
  y : Value,
  z : Value,
  pred : (Value, Value, Value) -> Value raise,
) -> Value raise {
  let perms = [
    (x, y, z),
    (x, z, y),
    (y, x, z),
    (y, z, x),
    (z, x, y),
    (z, y, x),
  ]
  for p in perms {
    let v = pred(p.0, p.1, p.2)
    if v.truthy() {
      return v
    }
  }
  Nil
}

///|
fn simp__pctcarlson_rf(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_carlson_rf, [q_d_x, q_d_y, q_d_z])
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  let y = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  fn calc(x : Value, y : Value, z : Value) -> Value raise {
    maxima_to(bf_bf_rf(bf_to(x), bf_to(y), bf_to(z)))
  }

  let i_minus_i_0 = (x : Value, y : Value, z : Value) => lbool(
    eq(x, q_d__pcti) &&
    alike1(y, mul2(int(-1), q_d__pcti)).truthy() &&
    eql(z, int(0)),
  )
  // See https://dlmf.nist.gov/19.20.i
  if alike1(x, y).truthy() && alike1(y, z).truthy() {
    // Rf(x,x,x) = x^(-1/2)
    return power(x, ellipt__mq(-1, 2))
  }
  if zerop1(x).truthy() && alike1(y, z).truthy() {
    // Rf(0,y,y) = 1/2*%pi*y^(-1/2)
    return muln_([
      ellipt__mq(1, 2),
      q_d__pctpi,
      power(y, ellipt__mq(-1, 2)),
    ])
  }
  if alike1(y, z).truthy() {
    return ftake(q_p_carlson_rc, [x, y])
  }
  if ellipt__some_perm(x, y, z, (x, y, z) => lbool(
      zerop1(x).truthy() && eql(y, int(1)) && eql(z, int(2)),
    )).truthy() {
    // Rf(0,1,2) = (gamma(1/4))^2/(4*sqrt(2*%pi))
    //
    // And Rf is symmetric in all the args, so check every permutation
    // too.  This could probably be simplified without consing all the
    // lists, but I'm lazy.
    return div(
      power(ftake(q_p_gamma, [div(int(1), int(4))]), int(2)),
      mul2(int(4), power(mul2(int(2), q_d__pctpi), ellipt__mq(1, 2))),
    )
  }
  if ellipt__some_perm(x, y, z, i_minus_i_0).truthy() {
    // rf(%i, -%i, 0)
    //   = 1/2*integrate(1/sqrt(t^2+1)/sqrt(t),t,0,inf)
    //   = beta(1/4,1/4)/4;
    // makegamma(%)
    //   = gamma(1/4)^2/(4*sqrt(%pi))
    //
    // Rf is symmetric, so check all the permutations too.
    return div(
      power(ftake(q_p_gamma, [div(int(1), int(4))]), int(2)),
      mul2(int(4), power(q_d__pctpi, ellipt__mq(1, 2))),
    )
  }
  let args = ellipt__some_perm(x, y, z, (x, y, z) => if zerop1(x).truthy() &&
    eql(z, int(1)) {
    // Check that x = 0 and z = 1, and return y.
    y
  } else {
    Nil
  })
  if args.truthy() {
    // Rf(0,1-m,1) = elliptic_kc(m).
    // See https://dlmf.nist.gov/19.25.E1
    return ftake(q_p_elliptic_kc, [sub(int(1), args)])
  }
  if ellipt__some_perm(x, y, z, i_minus_i_0).truthy() {
    // rf(%i, -%i, 0)
    //   = 1/2*integrate(1/sqrt(t^2+1)/sqrt(t),t,0,inf)
    //   = beta(1/4,1/4)/4;
    // makegamma(%)
    //   = gamma(1/4)^2/(4*sqrt(%pi))
    //
    // Rf is symmetric, so check all the permutations too.
    return div(
      power(ftake(q_p_gamma, [div(int(1), int(4))]), int(2)),
      mul2(int(4), power(q_d__pctpi, ellipt__mq(1, 2))),
    )
  }
  if float_numerical_eval_p(list3(x, y, z)).truthy() {
    return calc(d_float(x), d_float(y), d_float(z))
  }
  if bigfloat_numerical_eval_p(list3(x, y, z)).truthy() {
    return calc(d_bfloat(x), d_bfloat(y), d_bfloat(z))
  }
  let args = complex_float_numerical_eval_p(list3(x, y, z))
  if args.truthy() {
    return calc(
      d_float(first(args)),
      d_float(second(args)),
      d_float(third(args)),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list3(x, y, z))
  if args.truthy() {
    return calc(
      d_bfloat(first(args)),
      d_bfloat(second(args)),
      d_bfloat(third(args)),
    )
  }
  ellipt__give_up(q_p_carlson_rf, [x, y, z], form)
}

///|
fn simp__pctcarlson_rj(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_carlson_rj, [q_d_x, q_d_y, q_d_z, q_d_p])
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  let y = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  let p = simpcheck(nth(4, form), p__pctsimpflag)
  fn calc(x : Value, y : Value, z : Value, p : Value) -> Value raise {
    maxima_to(bf_bf_rj(bf_to(x), bf_to(y), bf_to(z), bf_to(p)))
  }

  // See https://dlmf.nist.gov/19.20.iii
  if alike1(x, y).truthy() && alike1(y, z).truthy() && alike1(z, p).truthy() {
    // Rj(x,x,x,x) = x^(-3/2)
    return power(x, div(int(-3), int(2)))
  }
  if alike1(z, p).truthy() {
    // Rj(x,y,z,z) = Rd(x,y,z)
    return ftake(q_p_carlson_rd, [x, y, z])
  }
  if zerop1(x).truthy() && alike1(y, z).truthy() {
    // Rj(0,y,y,p) = 3*%pi/(2*(y*sqrt(p)+p*sqrt(y)))
    return div(
      mul2(int(3), q_d__pctpi),
      mul2(
        int(2),
        add2(
          mul2(y, power(p, ellipt__mq(1, 2))),
          mul2(p, power(y, ellipt__mq(1, 2))),
        ),
      ),
    )
  }
  if alike1(y, z).truthy() {
    // Rj(x,y,y,p) = 3/(p-y)*(Rc(x,y) - Rc(x,p))
    return mul2(
      div(int(3), sub(p, y)),
      sub(ftake(q_p_carlson_rc, [x, y]), ftake(q_p_carlson_rc, [x, p])),
    )
  }
  if alike1(y, z).truthy() && alike1(y, p).truthy() {
    // Rj(x,y,y,y) = Rd(x,y,y)
    return ftake(q_p_carlson_rd, [x, y, y])
  }
  if float_numerical_eval_p(list([x, y, z, p])).truthy() {
    return calc(d_float(x), d_float(y), d_float(z), d_float(p))
  }
  if bigfloat_numerical_eval_p(list([x, y, z, p])).truthy() {
    return calc(d_bfloat(x), d_bfloat(y), d_bfloat(z), d_bfloat(p))
  }
  let args = complex_float_numerical_eval_p(list([x, y, z, p]))
  if args.truthy() {
    return calc(
      d_float(first(args)),
      d_float(second(args)),
      d_float(third(args)),
      d_float(fourth(args)),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list([x, y, z, p]))
  if args.truthy() {
    return calc(
      d_bfloat(first(args)),
      d_bfloat(second(args)),
      d_bfloat(third(args)),
      d_bfloat(fourth(args)),
    )
  }
  ellipt__give_up(q_p_carlson_rj, [x, y, z, p], form)
}
