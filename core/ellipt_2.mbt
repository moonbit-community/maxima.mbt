// Port of src/ellipt.lisp, part 2: helpers shared by the simplifiers,
// kc-arg, and the simplifiers for jacobi_sn, jacobi_cn, jacobi_dn and
// their inverses.

///|
/// The Maxima rational ((rat simp) n d).
fn ellipt__mq(n : Int, d : Int) -> Value {
  mk_simp(q_rat, [int(n), int(d)])
}

///|
/// The operators of the inverse Jacobian elliptic functions.
let ellipt__inverse_ops : Value = list([
  q_p_inverse_jacobi_sn, q_p_inverse_jacobi_ns, q_p_inverse_jacobi_cn, q_p_inverse_jacobi_nc,
  q_p_inverse_jacobi_dn, q_p_inverse_jacobi_nd, q_p_inverse_jacobi_sc, q_p_inverse_jacobi_cs,
  q_p_inverse_jacobi_sd, q_p_inverse_jacobi_ds, q_p_inverse_jacobi_cd, q_p_inverse_jacobi_dc,
])

///|
/// The argument-count check done by DEF-SIMPLIFIER.  NAMES are the
/// dollarified lambda-list variables used in the error message.
fn ellipt__check_nargs(
  form : Value,
  op : Value,
  names : Array[Value],
) -> Unit raise {
  if length(cdr(form)) != names.length() {
    wna_err(
      form,
      required_arg_count=int(names.length()),
      pretty_name=mk(op, names),
    )
    |> ignore
  }
}

///|
/// The local GIVE-UP of DEF-SIMPLIFIER.
fn ellipt__give_up(op : Value, args : Array[Value], form : Value) -> Value raise {
  eqtest(cons(list1(op), list(args)), form)
}

///|
/// The four numerical-evaluation clauses of the Jacobian elliptic function
/// simplifiers (float, complex float, bigfloat, complex bigfloat, in this
/// order).  F receives the BIGFLOAT:TO conversions of ($float u) and
/// ($float m), or of ($bfloat u) and ($bfloat m); its result is converted
/// back with TO.  None if no clause applies.
fn ellipt__numeval_um(
  u : Value,
  m : Value,
  f : (Value, Value) -> Value raise,
) -> Value? raise {
  if float_numerical_eval_p(list2(u, m)).truthy() {
    let uu = bf_to(d_float(u))
    let mm = bf_to(d_float(m))
    return Some(maxima_to(f(uu, mm)))
  }
  let args = complex_float_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(d_float(first(args)))
    let mm = bf_to(d_float(second(args)))
    return Some(maxima_to(f(uu, mm)))
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    let uu = bf_to(d_bfloat(u))
    let mm = bf_to(d_bfloat(m))
    return Some(maxima_to(f(uu, mm)))
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(d_bfloat(first(args)))
    let mm = bf_to(d_bfloat(second(args)))
    return Some(maxima_to(f(uu, mm)))
  }
  None
}

///|
/// The test `(and $triginverses (listp u) (member (caar u) '(...)) (alike1
/// (third u) m))` used by the Jacobian elliptic function simplifiers.
fn ellipt__inverse_arg_p(u : Value, m : Value) -> Bool raise {
  symval(q_d_triginverses).truthy() &&
  listp(u) &&
  memq(caar(u), ellipt__inverse_ops).truthy() &&
  alike1(third(u), m).truthy()
}

///|
/// The test `(and (eq $triginverses '$all) (listp u) (eq (caar u) op)
/// (alike1 (third u) m))` used by the inverse function simplifiers.
fn ellipt__all_inverse_p(u : Value, m : Value, op : Value) -> Bool raise {
  eq(symval(q_d_triginverses), q_d_all) &&
  listp(u) &&
  eq(caar(u), op) &&
  alike1(third(u), m).truthy()
}

// Possible forms of a complex number:
//
// 2.3
// $%i
// ((mplus simp) 2.3 ((mtimes simp) 2.3 $%i))
// ((mplus simp) 2.3 $%i))
// ((mtimes simp) 2.3 $%i)

///|
fn kc_arg(exp_ : Value, m : Value) -> Value raise {
  // Replace elliptic_kc(m) in the expression with sym.  Check to see if
  // the resulting expression is linear in sym and the constant term is
  // zero.  If so, return the coefficient of sym, i.e, the coefficient of
  // elliptic_kc(m).
  let sym_ = gensym()
  let arg_ = maxima_substitute(sym_, mk(q_p_elliptic_kc, [m]), exp_)
  if !equalp(arg_, exp_) &&
    linearp(arg_, sym_).truthy() &&
    zerop1(coefficient(arg_, sym_, int(0))).truthy() {
    coefficient(arg_, sym_, int(1))
  } else {
    Nil
  }
}

///|
fn kc_arg2(exp_ : Value, m : Value) -> Value raise {
  // Replace elliptic_kc(m) in the expression with sym.  Check to see if
  // the resulting expression is linear in sym and the constant term is
  // zero.  If so, return the coefficient of sym, i.e, the coefficient of
  // elliptic_kc(m), and the constant term.  Otherwise, return NIL.
  let sym_ = gensym()
  let arg_ = maxima_substitute(sym_, mk(q_p_elliptic_kc, [m]), exp_)
  if !equalp(arg_, exp_) && linearp(arg_, sym_).truthy() {
    list2(coefficient(arg_, sym_, int(1)), coefficient(arg_, sym_, int(0)))
  } else {
    Nil
  }
}

///|
/// `(mod lin n)` for an integer LIN, as a MoonBit Int.
fn ellipt__mod(lin : Value, n : Int) -> Int raise {
  to_int(num_mod(lin, int(n)))
}

///|
/// The ECASE error for an impossible remainder.
fn ellipt__ecase_error(v : Int) -> Value raise {
  raise LispError::SimpleError("ECASE: fell through with value \{v}")
}

// Tell maxima how to simplify the functions

///|
fn simp__pctjacobi_sn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_sn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_sn, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_sn(uu, mm)) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    // A&S 16.5.1
    return int(0)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.1
    return ftake(q_p_sin, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.1
    return ftake(q_p_tanh, [u])
  }
  if symval(q_d_trigsign).truthy() && mminusp_star(u).truthy() {
    return neg(ftake_star(q_p_jacobi_sn, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    let inv_arg = second(u)
    let op = caar(u)
    return if eq(op, q_p_inverse_jacobi_sn) {
      // jacobi_sn(inverse_jacobi_sn(u,m), m) = u
      inv_arg
    } else if eq(op, q_p_inverse_jacobi_ns) {
      // inverse_jacobi_ns(u,m) = inverse_jacobi_sn(1/u,m)
      div(int(1), inv_arg)
    } else if eq(op, q_p_inverse_jacobi_cn) {
      // sn(x)^2 + cn(x)^2 = 1 so sn(x) = sqrt(1-cn(x)^2)
      power(sub(int(1), mul2(inv_arg, inv_arg)), ellipt__mq(1, 2))
    } else if eq(op, q_p_inverse_jacobi_nc) {
      // inverse_jacobi_nc(u) = inverse_jacobi_cn(1/u)
      ftake(q_p_jacobi_sn, [
        ftake(q_p_inverse_jacobi_cn, [div(int(1), inv_arg), m]),
        m,
      ])
    } else if eq(op, q_p_inverse_jacobi_dn) {
      // dn(x)^2 + m*sn(x)^2 = 1 so
      // sn(x) = 1/sqrt(m)*sqrt(1-dn(x)^2)
      mul2(
        div(int(1), power(m, ellipt__mq(1, 2))),
        power(sub(int(1), mul2(inv_arg, inv_arg)), ellipt__mq(1, 2)),
      )
    } else if eq(op, q_p_inverse_jacobi_nd) {
      // inverse_jacobi_nd(u) = inverse_jacobi_dn(1/u)
      ftake(q_p_jacobi_sn, [
        ftake(q_p_inverse_jacobi_dn, [div(int(1), inv_arg), m]),
        m,
      ])
    } else if eq(op, q_p_inverse_jacobi_sc) {
      // See below for inverse_jacobi_sc.
      div(
        inv_arg,
        power(add2(int(1), mul2(inv_arg, inv_arg)), ellipt__mq(1, 2)),
      )
    } else if eq(op, q_p_inverse_jacobi_cs) {
      // inverse_jacobi_cs(u) = inverse_jacobi_sc(1/u)
      ftake(q_p_jacobi_sn, [
        ftake(q_p_inverse_jacobi_sc, [div(int(1), inv_arg), m]),
        m,
      ])
    } else if eq(op, q_p_inverse_jacobi_sd) {
      // See below for inverse_jacobi_sd
      div(
        inv_arg,
        power(
          add2(int(1), mul2(m, mul2(inv_arg, inv_arg))),
          ellipt__mq(1, 2),
        ),
      )
    } else if eq(op, q_p_inverse_jacobi_ds) {
      // inverse_jacobi_ds(u) = inverse_jacobi_sd(1/u)
      ftake(q_p_jacobi_sn, [
        ftake(q_p_inverse_jacobi_sd, [div(int(1), inv_arg), m]),
        m,
      ])
    } else if eq(op, q_p_inverse_jacobi_cd) {
      // See below
      div(
        power(sub(int(1), mul2(inv_arg, inv_arg)), ellipt__mq(1, 2)),
        power(
          sub(int(1), mul2(m, mul2(inv_arg, inv_arg))),
          ellipt__mq(1, 2),
        ),
      )
    } else {
      // %inverse_jacobi_dc
      ftake(q_p_jacobi_sn, [
        ftake(q_p_inverse_jacobi_cd, [div(int(1), inv_arg), m]),
        m,
      ])
    }
  }
  // A&S 16.20.1 (Jacobi's Imaginary transformation)
  if symval(q_d__pctiargs).truthy() && multiplep(u, q_d__pcti).truthy() {
    return mul2(
      q_d__pcti,
      ftake_star(q_p_jacobi_sc, [
        coeff(u, q_d__pcti, int(1)),
        add2(int(1), neg(m)),
      ]),
    )
  }
  let coef = kc_arg2(u, m)
  if coef.truthy() {
    // sn(m*K+u)
    //
    // A&S 16.8.1
    let lin = first(coef)
    let const_ = second(coef)
    if integerp(lin) {
      return match ellipt__mod(lin, 4) {
        0 =>
          // sn(4*m*K + u) = sn(u), sn(0) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            ftake(q_p_jacobi_sn, [const_, m])
          }
        1 =>
          // sn(4*m*K + K + u) = sn(K+u) = cd(u)
          // sn(K) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_cd, [const_, m])
          }
        2 =>
          // sn(4*m*K+2*K + u) = sn(2*K+u) = -sn(u)
          // sn(2*K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            neg(ftake(q_p_jacobi_sn, [const_, m]))
          }
        3 =>
          // sn(4*m*K+3*K+u) = sn(2*K + K + u) = -sn(K+u) = -cd(u)
          // sn(3*K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_cd, [const_, m]))
          }
        v => ellipt__ecase_error(v)
      }
    } else if alike1(lin, ellipt__mq(1, 2)).truthy() &&
      zerop1(const_).truthy() {
      // A&S 16.5.2
      //
      // sn(1/2*K) = 1/sqrt(1+sqrt(1-m))
      return div(
        int(1),
        power(
          add2(int(1), power(sub(int(1), m), ellipt__mq(1, 2))),
          ellipt__mq(1, 2),
        ),
      )
    } else if alike1(lin, ellipt__mq(3, 2)).truthy() &&
      zerop1(const_).truthy() {
      // A&S 16.5.2
      //
      // sn(1/2*K + K) = cd(1/2*K,m)
      return ftake(q_p_jacobi_cd, [
        mul2(ellipt__mq(1, 2), ftake(q_p_elliptic_kc, [m])),
        m,
      ])
    } else {
      return give_up()
    }
  }
  // Nothing to do
  give_up()
}

///|
fn simp__pctjacobi_cn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_cn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_cn, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_cn(uu, mm)) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    // A&S 16.5.1
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.2
    return ftake(q_p_cos, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.2
    return ftake(q_p_sech, [u])
  }
  if symval(q_d_trigsign).truthy() && mminusp_star(u).truthy() {
    return ftake_star(q_p_jacobi_cn, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_cn) {
      second(u)
    } else {
      // I'm lazy.  Use cn(x) = sqrt(1-sn(x)^2).  Hope this is right.
      power(
        sub(int(1), power(ftake(q_p_jacobi_sn, [u, third(u)]), int(2))),
        ellipt__mq(1, 2),
      )
    }
  }
  // A&S 16.20.2 (Jacobi's Imaginary transformation)
  if symval(q_d__pctiargs).truthy() && multiplep(u, q_d__pcti).truthy() {
    return ftake_star(q_p_jacobi_nc, [
      coeff(u, q_d__pcti, int(1)),
      add2(int(1), neg(m)),
    ])
  }
  let coef = kc_arg2(u, m)
  if coef.truthy() {
    // cn(m*K+u)
    //
    // A&S 16.8.2
    let lin = first(coef)
    let const_ = second(coef)
    if integerp(lin) {
      return match ellipt__mod(lin, 4) {
        0 =>
          // cn(4*m*K + u) = cn(u),
          // cn(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_cn, [const_, m])
          }
        1 =>
          // cn(4*m*K + K + u) = cn(K+u) = -sqrt(m1)*sd(u)
          // cn(K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            neg(
              mul2(
                power(sub(int(1), m), ellipt__mq(1, 2)),
                ftake(q_p_jacobi_sd, [const_, m]),
              ),
            )
          }
        2 =>
          // cn(4*m*K + 2*K + u) = cn(2*K+u) = -cn(u)
          // cn(2*K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_cn, [const_, m]))
          }
        3 =>
          // cn(4*m*K + 3*K + u) = cn(2*K + K + u) =
          // -cn(K+u) = sqrt(m1)*sd(u)
          //
          // cn(3*K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            mul2(
              power(sub(int(1), m), ellipt__mq(1, 2)),
              ftake(q_p_jacobi_sd, [const_, m]),
            )
          }
        v => ellipt__ecase_error(v)
      }
    } else if alike1(lin, ellipt__mq(1, 2)).truthy() &&
      zerop1(const_).truthy() {
      // A&S 16.5.2
      // cn(1/2*K) = (1-m)^(1/4)/sqrt(1+sqrt(1-m))
      return mul2(
        power(sub(int(1), m), div(int(1), int(4))),
        power(
          add2(int(1), power(sub(int(1), m), ellipt__mq(1, 2))),
          ellipt__mq(1, 2),
        ),
      )
    } else {
      return give_up()
    }
  }
  give_up()
}

///|
fn simp__pctjacobi_dn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_dn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_dn, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_dn(uu, mm)) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    // A&S 16.5.1
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.3
    return int(1)
  }
  if onep1(m).truthy() {
    // A&S 16.6.3
    return ftake(q_p_sech, [u])
  }
  if symval(q_d_trigsign).truthy() && mminusp_star(u).truthy() {
    return ftake_star(q_p_jacobi_dn, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_dn) {
      // jacobi_dn(inverse_jacobi_dn(u,m), m) = u
      second(u)
    } else {
      // Express in terms of sn:
      // dn(x) = sqrt(1-m*sn(x)^2)
      power(
        sub(int(1), mul2(m, power(ftake(q_p_jacobi_sn, [u, m]), int(2)))),
        ellipt__mq(1, 2),
      )
    }
  }
  if zerop1(d_ratsimp(sub(u, power(sub(int(1), m), ellipt__mq(1, 2))), Nil)).truthy() {
    // A&S 16.5.3
    // dn(sqrt(1-m),m) = K(m)
    return ftake(q_p_elliptic_kc, [m])
  }
  // A&S 16.20.2 (Jacobi's Imaginary transformation)
  if symval(q_d__pctiargs).truthy() && multiplep(u, q_d__pcti).truthy() {
    return ftake_star(q_p_jacobi_dc, [
      coeff(u, q_d__pcti, int(1)),
      add2(int(1), neg(m)),
    ])
  }
  let coef = kc_arg2(u, m)
  if coef.truthy() {
    // A&S 16.8.3
    //
    // dn(m*K+u) has period 2K
    let lin = first(coef)
    let const_ = second(coef)
    if integerp(lin) {
      return match ellipt__mod(lin, 2) {
        0 =>
          // dn(2*m*K + u) = dn(u)
          // dn(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            // dn(4*m*K+2*K + u) = dn(2*K+u) = dn(u)
            ftake(q_p_jacobi_dn, [const_, m])
          }
        1 =>
          // dn(2*m*K + K + u) = dn(K + u) = sqrt(1-m)*nd(u)
          // dn(K) = sqrt(1-m)
          if zerop1(const_).truthy() {
            power(sub(int(1), m), ellipt__mq(1, 2))
          } else {
            mul2(
              power(sub(int(1), m), ellipt__mq(1, 2)),
              ftake(q_p_jacobi_nd, [const_, m]),
            )
          }
        v => ellipt__ecase_error(v)
      }
    } else if alike1(lin, ellipt__mq(1, 2)).truthy() &&
      zerop1(const_).truthy() {
      // A&S 16.5.2
      // dn(1/2*K) = (1-m)^(1/4)
      return power(sub(int(1), m), div(int(1), int(4)))
    } else {
      return give_up()
    }
  }
  give_up()
}

// Should we simplify the inverse elliptic functions into the appropriate
// incomplete elliptic integral?  I think we should leave it, but perhaps
// allow some way to do that transformation if desired.

///|
fn simp__pctinverse_jacobi_sn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_sn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  // To numerically evaluate inverse_jacobi_sn (asn), use
  //
  // asn(x,m) = F(asin(x),m)
  //
  // But F(phi,m) = sin(phi)*rf(cos(phi)^2, 1-m*sin(phi)^2,1).  Thus
  //
  // asn(x,m) = F(asin(x),m)
  //          = x*rf(1-x^2,1-m*x^2,1)
  //
  // I (rtoy) am not 100% about the first identity above for all complex
  // values of x and m, but tests seem to indicate that it produces the
  // correct value as verified by verifying
  // jacobi_sn(inverse_jacobi_sn(x,m),m) = x.
  if float_numerical_eval_p(list2(u, m)).truthy() {
    let uu = bf_to(d_float(u))
    let mm = bf_to(d_float(m))
    return complexify(
      num_mul(
        uu,
        bf_bf_rf(
          bf_to(num_sub(int(1), num_mul(uu, uu))),
          bf_to(num_sub(int(1), num_mul(num_mul(mm, uu), uu))),
          int(1),
        ),
      ),
    )
  }
  let args = complex_float_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(d_float(first(args)))
    let mm = bf_to(d_float(second(args)))
    return complexify(
      num_mul(
        uu,
        bf_bf_rf(
          num_sub(int(1), num_mul(uu, uu)),
          num_sub(int(1), num_mul(num_mul(mm, uu), uu)),
          int(1),
        ),
      ),
    )
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    let uu = bf_to(u)
    let mm = bf_to(m)
    return maxima_to(
      bf_mul(
        uu,
        bf_bf_rf(
          bf_sub(int(1), bf_mul(uu, uu)),
          bf_sub(int(1), bf_mul(bf_mul(mm, uu), uu)),
          int(1),
        ),
      ),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(first(args))
    let mm = bf_to(second(args))
    return maxima_to(
      bf_mul(
        uu,
        bf_bf_rf(
          bf_sub(int(1), bf_mul(uu, uu)),
          bf_sub(int(1), bf_mul(bf_mul(mm, uu), uu)),
          int(1),
        ),
      ),
    )
  }
  if zerop1(u).truthy() {
    // asn(0,m) = 0
    int(0)
  } else if onep1(u).truthy() {
    // asn(1,m) = elliptic_kc(m)
    ftake(q_p_elliptic_kc, [m])
  } else if numberp(u) && onep1(num_neg(u)).truthy() {
    // asn(-1,m) = -elliptic_kc(m)
    mul2(int(-1), ftake(q_p_elliptic_kc, [m]))
  } else if zerop1(m).truthy() {
    // asn(x,0) = F(asin(x),0) = asin(x)
    ftake(q_p_asin, [u])
  } else if onep1(m).truthy() {
    // asn(x,1) = F(asin(x),1) = log(tan(pi/4+asin(x)/2))
    ftake(q_p_elliptic_f, [ftake(q_p_asin, [u]), int(1)])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_sn) {
    // inverse_jacobi_sn(sn(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_sn, [u, m], form)
  }
}

///|
fn simp__pctinverse_jacobi_cn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_cn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if float_numerical_eval_p(list2(u, m)).truthy() {
    // Numerically evaluate acn
    //
    // acn(x,m) = F(acos(x),m)
    return maxima_to(elliptic_f(lacos(d_float(u)), d_float(m)))
  }
  let args = complex_float_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let u = first(args)
    let m = second(args)
    return maxima_to(
      elliptic_f(lacos(bf_to(d_float(u))), bf_to(d_float(m))),
    )
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    return maxima_to(bf_bf_elliptic_f(bf_acos(bf_to(u)), bf_to(m)))
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let u = first(args)
    let m = second(args)
    return maxima_to(bf_bf_elliptic_f(bf_acos(bf_to(u)), bf_to(m)))
  }
  if zerop1(m).truthy() {
    // asn(x,0) = F(acos(x),0) = acos(x)
    ftake(q_p_elliptic_f, [ftake(q_p_acos, [u]), int(0)])
  } else if onep1(m).truthy() {
    // asn(x,1) = F(asin(x),1) = log(tan(pi/2+asin(x)/2))
    ftake(q_p_elliptic_f, [ftake(q_p_acos, [u]), int(1)])
  } else if zerop1(u).truthy() {
    ftake(q_p_elliptic_kc, [m])
  } else if onep1(u).truthy() {
    int(0)
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_cn) {
    // inverse_jacobi_cn(cn(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_cn, [u, m], form)
  }
}

///|
fn simp__pctinverse_jacobi_dn(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_dn, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if float_numerical_eval_p(list2(u, m)).truthy() {
    return maxima_to(
      bf_bf_inverse_jacobi_dn(bf_to(float(u)), bf_to(float(m))),
    )
  }
  let args = complex_float_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(d_float(first(args)))
    let mm = bf_to(d_float(second(args)))
    return maxima_to(bf_bf_inverse_jacobi_dn(uu, mm))
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    let uu = bf_to(u)
    let mm = bf_to(m)
    return maxima_to(bf_bf_inverse_jacobi_dn(uu, mm))
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let uu = bf_to(first(args))
    let mm = bf_to(second(args))
    return maxima_to(bf_bf_inverse_jacobi_dn(uu, mm))
  }
  if onep1(m).truthy() {
    // x = dn(u,1) = sech(u).  so u = asech(x)
    ftake(q_p_asech, [u])
  } else if onep1(u).truthy() {
    // jacobi_dn(0,m) = 1
    int(0)
  } else if zerop1(d_ratsimp(sub(u, power(sub(int(1), m), ellipt__mq(1, 2))), Nil)).truthy() {
    // jacobi_dn(K(m),m) = sqrt(1-m) so
    // inverse_jacobi_dn(sqrt(1-m),m) = K(m)
    ftake(q_p_elliptic_kc, [m])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_dn) {
    // inverse_jacobi_dn(dn(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_dn, [u, m], form)
  }
}
