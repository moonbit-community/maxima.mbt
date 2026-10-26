// Port of src/ellipt.lisp, part 4: the other Jacobian elliptic functions
// and their inverses, make_elliptic_f/e, elliptic_eu, risplit for sn, cn,
// dn, jacobi_am, and the top-level properties (init_ellipt).

///|
/// The `(setq coef (kc-arg2 u m))` clause of the Jacobian elliptic function
/// simplifiers.  None when kc-arg2 returns NIL.  Otherwise, for an integer
/// coefficient LIN of elliptic_kc(m), INT_CASE gets (mod lin n) and the
/// constant term; for LIN = 1/2 with zero constant term, HALF_CASE (if
/// any) gives the value; else GIVE_UP.
fn ellipt__kc_clause(
  u : Value,
  m : Value,
  n : Int,
  int_case : (Int, Value) -> Value raise,
  half_case : (() -> Value raise)?,
  give_up : () -> Value raise,
) -> Value? raise {
  let coef = kc_arg2(u, m)
  if !coef.truthy() {
    return None
  }
  let lin = first(coef)
  let const_ = second(coef)
  if integerp(lin) {
    return Some(int_case(ellipt__mod(lin, n), const_))
  }
  match half_case {
    Some(h) =>
      if alike1(lin, ellipt__mq(1, 2)).truthy() && zerop1(const_).truthy() {
        return Some(h())
      }
    None => ()
  }
  Some(give_up())
}

///|
/// sqrt(1-m)
fn ellipt__root_m1(m : Value) -> Value raise {
  power(sub(int(1), m), ellipt__mq(1, 2))
}

///|
/// 1/2*elliptic_kc(m)
fn ellipt__half_kc(m : Value) -> Value raise {
  mul2(ellipt__mq(1, 2), ftake(q_p_elliptic_kc, [m]))
}

///|
/// The coefficient of %i in u and 1-m, for Jacobi's imaginary
/// transformation.
fn ellipt__imag_args(u : Value, m : Value) -> Array[Value] raise {
  [coeff(u, q_d__pcti, int(1)), add2(int(1), neg(m))]
}

///|
fn ellipt__iargs_p(u : Value) -> Bool raise {
  symval(q_d__pctiargs).truthy() && multiplep(u, q_d__pcti).truthy()
}

///|
fn ellipt__trigsign_p(u : Value) -> Bool raise {
  symval(q_d_trigsign).truthy() && mminusp_star(u).truthy()
}

// Other Jacobian elliptic functions

///|
/// jacobi_ns(u,m) = 1/jacobi_sn(u,m)
fn simp__pctjacobi_ns(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_ns, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_ns, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_inv(bf_sn(uu, mm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(m).truthy() {
    // A&S 16.6.10
    return ftake(q_p_csc, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.10
    return ftake(q_p_coth, [u])
  }
  if zerop1(u).truthy() {
    return dbz_err1(q_jacobi_ns)
  }
  if ellipt__trigsign_p(u) {
    // ns is odd
    return neg(ftake_star(q_p_jacobi_ns, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_ns) {
      second(u)
    } else {
      // Express in terms of sn:
      // ns(x) = 1/sn(x)
      div(int(1), ftake(q_p_jacobi_sn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // ns(i*u) = 1/sn(i*u) = -i/sc(u,m1) = -i*cs(u,m1)
    return neg(
      mul2(q_d__pcti, ftake_star(q_p_jacobi_cs, ellipt__imag_args(u, m))),
    )
  }
  // A&S 16.8.10
  //
  // ns(m*K+u) = 1/sn(m*K+u)
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // ns(4*m*K+u) = ns(u)
          // ns(0) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_ns)
          } else {
            ftake(q_p_jacobi_ns, [const_, m])
          }
        1 =>
          // ns(4*m*K + K + u) = ns(K+u) = dc(u)
          // ns(K) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_dc, [const_, m])
          }
        2 =>
          // ns(4*m*K+2*K + u) = ns(2*K+u) = -ns(u)
          // ns(2*K) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_ns)
          } else {
            neg(ftake(q_p_jacobi_ns, [const_, m]))
          }
        3 =>
          // ns(4*m*K+3*K+u) = ns(2*K + K + u) = -ns(K+u) = -dc(u)
          // ns(3*K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_dc, [const_, m]))
          }
        v => ellipt__ecase_error(v)
      },
      Some(() => div(int(1), ftake(q_p_jacobi_sn, [u, m]))),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_nc(u,m) = 1/jacobi_cn(u,m)
fn simp__pctjacobi_nc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_nc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_nc, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_inv(bf_cn(uu, mm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.8
    return ftake(q_p_sec, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.8
    return ftake(q_p_cosh, [u])
  }
  if ellipt__trigsign_p(u) {
    // nc is even
    return ftake_star(q_p_jacobi_nc, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_nc) {
      second(u)
    } else {
      // Express in terms of cn:
      // nc(x) = 1/cn(x)
      div(int(1), ftake(q_p_jacobi_cn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // nc(i*u) = 1/cn(i*u) = 1/nc(u,1-m) = cn(u,1-m)
    return ftake_star(q_p_jacobi_cn, ellipt__imag_args(u, m))
  }
  // A&S 16.8.8
  //
  // nc(u) = 1/cn(u)
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // nc(4*m*K+u) = nc(u)
          // nc(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_nc, [const_, m])
          }
        1 =>
          // nc(4*m*K+K+u) = nc(K+u) = -ds(u)/sqrt(1-m)
          // nc(K) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_nc)
          } else {
            neg(div(ftake(q_p_jacobi_ds, [const_, m]), ellipt__root_m1(m)))
          }
        2 =>
          // nc(4*m*K+2*K+u) = nc(2*K+u) = -nc(u)
          // nc(2*K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_nc, [const_, m]))
          }
        3 =>
          // nc(4*m*K+3*K+u) = nc(3*K+u) = nc(2*K+K+u) =
          // -nc(K+u) = ds(u)/sqrt(1-m)
          //
          // nc(3*K) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_nc)
          } else {
            div(ftake(q_p_jacobi_ds, [const_, m]), ellipt__root_m1(m))
          }
        v => ellipt__ecase_error(v)
      },
      Some(() => div(int(1), ftake(q_p_jacobi_cn, [u, m]))),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_nd(u,m) = 1/jacobi_dn(u,m)
fn simp__pctjacobi_nd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_nd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_nd, [u, m], form)
  match ellipt__numeval_um(u, m, (uu, mm) => bf_inv(bf_dn(uu, mm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.6
    return int(1)
  }
  if onep1(m).truthy() {
    // A&S 16.6.6
    return ftake(q_p_cosh, [u])
  }
  if ellipt__trigsign_p(u) {
    // nd is even
    return ftake_star(q_p_jacobi_nd, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_nd) {
      second(u)
    } else {
      // Express in terms of dn:
      // nd(x) = 1/dn(x)
      div(int(1), ftake(q_p_jacobi_dn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // nd(i*u) = 1/dn(i*u) = 1/dc(u,1-m) = cd(u,1-m)
    return ftake_star(q_p_jacobi_cd, ellipt__imag_args(u, m))
  }
  // A&S 16.8.6
  match
    ellipt__kc_clause(
      u,
      m,
      2,
      (r, const_) => match r {
        // nd has period 2K
        0 =>
          // nd(2*m*K+u) = nd(u)
          // nd(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_nd, [const_, m])
          }
        1 =>
          // nd(2*m*K+K+u) = nd(K+u) = dn(u)/sqrt(1-m)
          // nd(K) = 1/sqrt(1-m)
          if zerop1(const_).truthy() {
            power(sub(int(1), m), ellipt__mq(-1, 2))
          } else {
            div(ftake(q_p_jacobi_nd, [const_, m]), ellipt__root_m1(m))
          }
        v => ellipt__ecase_error(v)
      },
      None,
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_sc(u,m) = jacobi_sn/jacobi_cn
fn simp__pctjacobi_sc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_sc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_sc, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_sn(fu, fm), bf_cn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(0)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.9
    return ftake(q_p_tan, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.9
    return ftake(q_p_sinh, [u])
  }
  if ellipt__trigsign_p(u) {
    // sc is odd
    return neg(ftake_star(q_p_jacobi_sc, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_sc) {
      second(u)
    } else {
      // Express in terms of sn and cn
      // sc(x) = sn(x)/cn(x)
      div(ftake(q_p_jacobi_sn, [u, m]), ftake(q_p_jacobi_cn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // sc(i*u) = sn(i*u)/cn(i*u) = i*sc(u,m1)/nc(u,m1) = i*sn(u,m1)
    return mul2(q_d__pcti, ftake_star(q_p_jacobi_sn, ellipt__imag_args(u, m)))
  }
  // A&S 16.8.9
  // sc(2*m*K+u) = sc(u)
  match
    ellipt__kc_clause(
      u,
      m,
      2,
      (r, const_) => match r {
        0 =>
          // sc(2*m*K+ u) = sc(u)
          // sc(0) = 0
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_sc, [const_, m])
          }
        1 =>
          // sc(2*m*K + K + u) = sc(K+u)= - cs(u)/sqrt(1-m)
          // sc(K) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_sc)
          } else {
            mul2(
              int(-1),
              div(
                ftake_star(q_p_jacobi_cs, [const_, m]),
                ellipt__root_m1(m),
              ),
            )
          }
        v => ellipt__ecase_error(v)
      },
      // From A&S 16.3.3 and 16.5.2:
      // sc(1/2*K) = 1/(1-m)^(1/4)
      Some(() => power(sub(int(1), m), div(int(-1), int(4)))),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_sd(u,m) = jacobi_sn/jacobi_dn
fn simp__pctjacobi_sd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_sd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_sd, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_sn(fu, fm), bf_dn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(0)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.5
    return ftake(q_p_sin, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.5
    return ftake(q_p_sinh, [u])
  }
  if ellipt__trigsign_p(u) {
    // sd is odd
    return neg(ftake_star(q_p_jacobi_sd, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_sd) {
      second(u)
    } else {
      // Express in terms of sn and dn
      div(ftake(q_p_jacobi_sn, [u, m]), ftake(q_p_jacobi_dn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // sd(i*u) = sn(i*u)/dn(i*u) = i*sc(u,m1)/dc(u,m1) = i*sd(u,m1)
    return mul2(q_d__pcti, ftake_star(q_p_jacobi_sd, ellipt__imag_args(u, m)))
  }
  // A&S 16.8.5
  // sd(4*m*K+u) = sd(u)
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // sd(4*m*K+u) = sd(u)
          // sd(0) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            ftake(q_p_jacobi_sd, [const_, m])
          }
        1 =>
          // sd(4*m*K+K+u) = sd(K+u) = cn(u)/sqrt(1-m)
          // sd(K) = 1/sqrt(m1)
          if zerop1(const_).truthy() {
            ellipt__root_m1(m)
          } else {
            div(ftake(q_p_jacobi_cn, [const_, m]), ellipt__root_m1(m))
          }
        2 =>
          // sd(4*m*K+2*K+u) = sd(2*K+u) = -sd(u)
          // sd(2*K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            neg(ftake(q_p_jacobi_sd, [const_, m]))
          }
        3 =>
          // sd(4*m*K+3*K+u) = sd(3*K+u) = sd(2*K+K+u) =
          // -sd(K+u) = -cn(u)/sqrt(1-m)
          // sd(3*K) = -1/sqrt(m1)
          if zerop1(const_).truthy() {
            neg(power(sub(int(1), m), ellipt__mq(-1, 2)))
          } else {
            neg(div(ftake(q_p_jacobi_cn, [const_, m]), ellipt__root_m1(m)))
          }
        v => ellipt__ecase_error(v)
      },
      // jacobi_sn/jacobi_dn
      Some(() => div(
        ftake(q_p_jacobi_sn, [ellipt__half_kc(m), m]),
        ftake(q_p_jacobi_dn, [ellipt__half_kc(m), m]),
      )),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_cs(u,m) = jacobi_cn/jacobi_sn
fn simp__pctjacobi_cs(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_cs, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_cs, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_cn(fu, fm), bf_sn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(m).truthy() {
    // A&S 16.6.12
    return ftake(q_p_cot, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.12
    return ftake(q_p_csch, [u])
  }
  if zerop1(u).truthy() {
    return dbz_err1(q_jacobi_cs)
  }
  if ellipt__trigsign_p(u) {
    // cs is odd
    return neg(ftake_star(q_p_jacobi_cs, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_cs) {
      second(u)
    } else {
      // Express in terms of cn an sn
      div(ftake(q_p_jacobi_cn, [u, m]), ftake(q_p_jacobi_sn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // cs(i*u) = cn(i*u)/sn(i*u) = -i*nc(u,m1)/sc(u,m1) = -i*ns(u,m1)
    return neg(
      mul2(q_d__pcti, ftake_star(q_p_jacobi_ns, ellipt__imag_args(u, m))),
    )
  }
  // A&S 16.8.12
  //
  // cs(2*m*K + u) = cs(u)
  match
    ellipt__kc_clause(
      u,
      m,
      2,
      (r, const_) => match r {
        0 =>
          // cs(2*m*K + u) = cs(u)
          // cs(0) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_cs)
          } else {
            ftake(q_p_jacobi_cs, [const_, m])
          }
        1 =>
          // cs(K+u) = -sqrt(1-m)*sc(u)
          // cs(K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            neg(mul2(ellipt__root_m1(m), ftake(q_p_jacobi_sc, [const_, m])))
          }
        v => ellipt__ecase_error(v)
      },
      // 1/jacobi_sc
      Some(() => div(int(1), ftake(q_p_jacobi_sc, [ellipt__half_kc(m), m]))),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_cd(u,m) = jacobi_cn/jacobi_dn
fn simp__pctjacobi_cd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_cd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_cd, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_cn(fu, fm), bf_dn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.4
    return ftake(q_p_cos, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.4
    return int(1)
  }
  if ellipt__trigsign_p(u) {
    // cd is even
    return ftake_star(q_p_jacobi_cd, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_cd) {
      second(u)
    } else {
      // Express in terms of cn and dn
      div(ftake(q_p_jacobi_cn, [u, m]), ftake(q_p_jacobi_dn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // cd(i*u) = cn(i*u)/dn(i*u) = nc(u,m1)/dc(u,m1) = nd(u,m1)
    return ftake_star(q_p_jacobi_nd, ellipt__imag_args(u, m))
  }
  // A&S 16.8.4
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // cd(4*m*K + u) = cd(u)
          // cd(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_cd, [const_, m])
          }
        1 =>
          // cd(4*m*K + K + u) = cd(K+u) = -sn(u)
          // cd(K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            neg(ftake(q_p_jacobi_sn, [const_, m]))
          }
        2 =>
          // cd(4*m*K + 2*K + u) = cd(2*K+u) = -cd(u)
          // cd(2*K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_cd, [const_, m]))
          }
        3 =>
          // cd(4*m*K + 3*K + u) = cd(2*K + K + u) =
          // -cd(K+u) = sn(u)
          // cd(3*K) = 0
          if zerop1(const_).truthy() {
            int(0)
          } else {
            ftake(q_p_jacobi_sn, [const_, m])
          }
        v => ellipt__ecase_error(v)
      },
      // jacobi_cn/jacobi_dn
      Some(() => div(
        ftake(q_p_jacobi_cn, [ellipt__half_kc(m), m]),
        ftake(q_p_jacobi_dn, [ellipt__half_kc(m), m]),
      )),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_ds(u,m) = jacobi_dn/jacobi_sn
fn simp__pctjacobi_ds(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_ds, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_ds, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_dn(fu, fm), bf_sn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(m).truthy() {
    // A&S 16.6.11
    return ftake(q_p_csc, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.11
    return ftake(q_p_csch, [u])
  }
  if zerop1(u).truthy() {
    return dbz_err1(q_jacobi_ds)
  }
  if ellipt__trigsign_p(u) {
    return neg(ftake_star(q_p_jacobi_ds, [neg(u), m]))
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_ds) {
      second(u)
    } else {
      // Express in terms of dn and sn
      div(ftake(q_p_jacobi_dn, [u, m]), ftake(q_p_jacobi_sn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // ds(i*u) = dn(i*u)/sn(i*u) = -i*dc(u,m1)/sc(u,m1) = -i*ds(u,m1)
    return neg(
      mul2(q_d__pcti, ftake_star(q_p_jacobi_ds, ellipt__imag_args(u, m))),
    )
  }
  // A&S 16.8.11
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // ds(4*m*K + u) = ds(u)
          // ds(0) = infinity
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_ds)
          } else {
            ftake(q_p_jacobi_ds, [const_, m])
          }
        1 =>
          // ds(4*m*K + K + u) = ds(K+u) = sqrt(1-m)*nc(u)
          // ds(K) = sqrt(1-m)
          if zerop1(const_).truthy() {
            ellipt__root_m1(m)
          } else {
            mul2(ellipt__root_m1(m), ftake(q_p_jacobi_nc, [const_, m]))
          }
        2 =>
          // ds(4*m*K + 2*K + u) = ds(2*K+u) = -ds(u)
          // ds(0) = pole
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_ds)
          } else {
            neg(ftake(q_p_jacobi_ds, [const_, m]))
          }
        3 =>
          // ds(4*m*K + 3*K + u) = ds(2*K + K + u) =
          // -ds(K+u) = -sqrt(1-m)*nc(u)
          // ds(3*K) = -sqrt(1-m)
          if zerop1(const_).truthy() {
            neg(ellipt__root_m1(m))
          } else {
            neg(mul2(ellipt__root_m1(m), ftake(q_p_jacobi_nc, [u, m])))
          }
        v => ellipt__ecase_error(v)
      },
      // jacobi_dn/jacobi_sn
      Some(() => div(
        ftake(q_p_jacobi_dn, [ellipt__half_kc(m), m]),
        ftake(q_p_jacobi_sn, [ellipt__half_kc(m), m]),
      )),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

///|
/// jacobi_dc(u,m) = jacobi_dn/jacobi_cn
fn simp__pctjacobi_dc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_dc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => ellipt__give_up(q_p_jacobi_dc, [u, m], form)
  match
    ellipt__numeval_um(u, m, (fu, fm) => bf_div(bf_dn(fu, fm), bf_cn(fu, fm))) {
    Some(v) => return v
    None => ()
  }
  if zerop1(u).truthy() {
    return int(1)
  }
  if zerop1(m).truthy() {
    // A&S 16.6.7
    return ftake(q_p_sec, [u])
  }
  if onep1(m).truthy() {
    // A&S 16.6.7
    return int(1)
  }
  if ellipt__trigsign_p(u) {
    return ftake_star(q_p_jacobi_dc, [neg(u), m])
  }
  if ellipt__inverse_arg_p(u, m) {
    return if eq(caar(u), q_p_inverse_jacobi_dc) {
      second(u)
    } else {
      // Express in terms of dn and cn
      div(ftake(q_p_jacobi_dn, [u, m]), ftake(q_p_jacobi_cn, [u, m]))
    }
  }
  // A&S 16.20 (Jacobi's Imaginary transformation)
  if ellipt__iargs_p(u) {
    // dc(i*u) = dn(i*u)/cn(i*u) = dc(u,m1)/nc(u,m1) = dn(u,m1)
    return ftake_star(q_p_jacobi_dn, ellipt__imag_args(u, m))
  }
  // See A&S 16.8.7
  match
    ellipt__kc_clause(
      u,
      m,
      4,
      (r, const_) => match r {
        0 =>
          // dc(4*m*K + u) = dc(u)
          // dc(0) = 1
          if zerop1(const_).truthy() {
            int(1)
          } else {
            ftake(q_p_jacobi_dc, [const_, m])
          }
        1 =>
          // dc(4*m*K + K + u) = dc(K+u) = -ns(u)
          // dc(K) = pole
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_dc)
          } else {
            neg(ftake(q_p_jacobi_ns, [const_, m]))
          }
        2 =>
          // dc(4*m*K + 2*K + u) = dc(2*K+u) = -dc(u)
          // dc(2K) = -1
          if zerop1(const_).truthy() {
            int(-1)
          } else {
            neg(ftake(q_p_jacobi_dc, [const_, m]))
          }
        3 =>
          // dc(4*m*K + 3*K + u) = dc(2*K + K + u) =
          // -dc(K+u) = ns(u)
          // dc(3*K) = ns(0) = inf
          if zerop1(const_).truthy() {
            dbz_err1(q_jacobi_dc)
          } else {
            ftake(q_p_jacobi_dc, [const_, m])
          }
        v => ellipt__ecase_error(v)
      },
      // jacobi_dn/jacobi_cn
      Some(() => div(
        ftake(q_p_jacobi_dn, [ellipt__half_kc(m), m]),
        ftake(q_p_jacobi_cn, [ellipt__half_kc(m), m]),
      )),
      give_up,
    ) {
    Some(v) => return v
    None => ()
  }
  // Nothing to do
  give_up()
}

// Other inverse Jacobian functions

///|
/// `(or (float-numerical-eval-p u m) (complex-float-numerical-eval-p u m)
/// (bigfloat-numerical-eval-p u m) (complex-bigfloat-numerical-eval-p u m))`
fn ellipt__any_numerical_p(u : Value, m : Value) -> Bool raise {
  float_numerical_eval_p(list2(u, m)).truthy() ||
  complex_float_numerical_eval_p(list2(u, m)).truthy() ||
  bigfloat_numerical_eval_p(list2(u, m)).truthy() ||
  complex_bigfloat_numerical_eval_p(list2(u, m)).truthy()
}

///|
/// inverse_jacobi_ns(x)
///
/// Let u = inverse_jacobi_ns(x).  Then jacobi_ns(u) = x or 1/jacobi_sn(u) =
/// x or
///
/// jacobi_sn(u) = 1/x
///
/// so u = inverse_jacobi_sn(1/x)
fn simp__pctinverse_jacobi_ns(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_ns, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if float_numerical_eval_p(list2(u, m)).truthy() {
    // Numerically evaluate asn
    //
    // ans(x,m) = asn(1/x,m) = F(asin(1/x),m)
    return maxima_to(elliptic_f(lasin(num_inv(d_float(u))), d_float(m)))
  }
  if complex_float_numerical_eval_p(list2(u, m)).truthy() {
    let fu = d_float(u)
    let cu = complex(d_realpart(fu), i=d_imagpart(fu))
    let fm = d_float(m)
    return maxima_to(
      elliptic_f(
        lasin(num_inv(cu)),
        complex(d_realpart(fm), i=d_imagpart(fm)),
      ),
    )
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    return maxima_to(
      bf_bf_elliptic_f(
        bf_asin(bf_inv(bf_to(d_bfloat(u)))),
        bf_to(d_bfloat(m)),
      ),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let u = first(args)
    let m = second(args)
    return maxima_to(
      bf_bf_elliptic_f(
        bf_asin(bf_inv(bf_to(d_bfloat(u)))),
        bf_to(d_bfloat(m)),
      ),
    )
  }
  if zerop1(m).truthy() {
    // ans(x,0) = F(asin(1/x),0) = asin(1/x)
    ftake(q_p_elliptic_f, [ftake(q_p_asin, [div(int(1), u)]), int(0)])
  } else if onep1(m).truthy() {
    // ans(x,1) = F(asin(1/x),1) = log(tan(pi/2+asin(1/x)/2))
    ftake(q_p_elliptic_f, [ftake(q_p_asin, [div(int(1), u)]), int(1)])
  } else if onep1(u).truthy() {
    ftake(q_p_elliptic_kc, [m])
  } else if alike1(u, int(-1)).truthy() {
    neg(ftake(q_p_elliptic_kc, [m]))
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_ns) {
    // inverse_jacobi_ns(ns(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_ns, [u, m], form)
  }
}

///|
/// inverse_jacobi_nc(x)
///
/// Let u = inverse_jacobi_nc(x).  Then jacobi_nc(u) = x or 1/jacobi_cn(u) =
/// x or
///
/// jacobi_cn(u) = 1/x
///
/// so u = inverse_jacobi_cn(1/x)
fn simp__pctinverse_jacobi_nc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_nc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_cn, [d_rectform(div(int(1), u)), m])
  } else if onep1(u).truthy() {
    int(0)
  } else if alike1(u, int(-1)).truthy() {
    mul2(int(2), ftake(q_p_elliptic_kc, [m]))
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_nc) {
    // inverse_jacobi_nc(nc(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_nc, [u, m], form)
  }
}

///|
/// inverse_jacobi_nd(x)
///
/// Let u = inverse_jacobi_nd(x).  Then jacobi_nd(u) = x or 1/jacobi_dn(u) =
/// x or
///
/// jacobi_dn(u) = 1/x
///
/// so u = inverse_jacobi_dn(1/x)
fn simp__pctinverse_jacobi_nd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_nd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_dn, [d_rectform(div(int(1), u)), m])
  } else if onep1(u).truthy() {
    int(0)
  } else if onep1(d_ratsimp(mul2(ellipt__root_m1(m), u), Nil)).truthy() {
    // jacobi_nd(1/sqrt(1-m),m) = K(m).  This follows from
    // jacobi_dn(sqrt(1-m),m) = K(m).
    ftake(q_p_elliptic_kc, [m])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_nd) {
    // inverse_jacobi_nd(nd(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_nd, [u, m], form)
  }
}

///|
/// inverse_jacobi_sc(x)
///
/// Let u = inverse_jacobi_sc(x).  Then jacobi_sc(u) = x or
/// x = jacobi_sn(u)/jacobi_cn(u)
///
/// x^2 = sn^2/cn^2
///     = sn^2/(1-sn^2)
///
/// so
///
/// sn^2 = x^2/(1+x^2)
///
/// sn(u) = x/sqrt(1+x^2)
///
/// u = inverse_sn(x/sqrt(1+x^2))
fn simp__pctinverse_jacobi_sc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_sc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_sn, [
      d_rectform(
        div(u, power(add2(int(1), mul2(u, u)), ellipt__mq(1, 2))),
      ),
      m,
    ])
  } else if zerop1(u).truthy() {
    // jacobi_sc(0,m) = 0
    int(0)
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_sc) {
    // inverse_jacobi_sc(sc(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_sc, [u, m], form)
  }
}

///|
/// inverse_jacobi_sd(x)
///
/// Let u = inverse_jacobi_sd(x).  Then jacobi_sd(u) = x or
/// x = jacobi_sn(u)/jacobi_dn(u)
///
/// x^2 = sn^2/dn^2
///     = sn^2/(1-m*sn^2)
///
/// so
///
/// sn^2 = x^2/(1+m*x^2)
///
/// sn(u) = x/sqrt(1+m*x^2)
///
/// u = inverse_sn(x/sqrt(1+m*x^2))
fn simp__pctinverse_jacobi_sd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_sd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_sn, [
      d_rectform(
        div(
          u,
          power(add2(int(1), mul2(m, mul2(u, u))), ellipt__mq(1, 2)),
        ),
      ),
      m,
    ])
  } else if zerop1(u).truthy() {
    int(0)
  } else if eql(
      int(0),
      d_ratsimp(sub(u, div(int(1), ellipt__root_m1(m))), Nil),
    ) {
    // inverse_jacobi_sd(1/sqrt(1-m), m) = elliptic_kc(m)
    //
    // We can see this from inverse_jacobi_sd(x,m) =
    // inverse_jacobi_sn(x/sqrt(1+m*x^2), m).  So
    // inverse_jacobi_sd(1/sqrt(1-m),m) = inverse_jacobi_sn(1,m)
    ftake(q_p_elliptic_kc, [m])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_sd) {
    // inverse_jacobi_sd(sd(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_sd, [u, m], form)
  }
}

///|
/// inverse_jacobi_cs(x)
///
/// Let u = inverse_jacobi_cs(x).  Then jacobi_cs(u) = x or
/// 1/x = 1/jacobi_cs(u) = jacobi_sc(u)
///
/// u = inverse_sc(1/x)
fn simp__pctinverse_jacobi_cs(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_cs, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_sc, [d_rectform(div(int(1), u)), m])
  } else if zerop1(u).truthy() {
    ftake(q_p_elliptic_kc, [m])
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_cs, [u, m], form)
  }
}

///|
/// inverse_jacobi_cd(x)
///
/// Let u = inverse_jacobi_cd(x).  Then jacobi_cd(u) = x or
/// x = jacobi_cn(u)/jacobi_dn(u)
///
/// x^2 = cn^2/dn^2
///     = (1-sn^2)/(1-m*sn^2)
///
/// or
///
/// sn^2 = (1-x^2)/(1-m*x^2)
///
/// sn(u) = sqrt(1-x^2)/sqrt(1-m*x^2)
///
/// u = inverse_sn(sqrt(1-x^2)/sqrt(1-m*x^2))
fn simp__pctinverse_jacobi_cd(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_cd, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if complex_float_numerical_eval_p(list2(u, m)).truthy() ||
    complex_bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    with_special(q_d_numer, t, () => ftake(q_p_inverse_jacobi_sn, [
      d_rectform(
        div(
          power(mul2(sub(int(1), u), add2(int(1), u)), ellipt__mq(1, 2)),
          power(sub(int(1), mul2(m, mul2(u, u))), ellipt__mq(1, 2)),
        ),
      ),
      m,
    ]))
  } else if onep1(u).truthy() {
    int(0)
  } else if zerop1(u).truthy() {
    ftake(q_p_elliptic_kc, [m])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_cd) {
    // inverse_jacobi_cd(cd(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_cd, [u, m], form)
  }
}

///|
/// inverse_jacobi_ds(x)
///
/// Let u = inverse_jacobi_ds(x).  Then jacobi_ds(u) = x or
/// 1/x = 1/jacobi_ds(u) = jacobi_sd(u)
///
/// u = inverse_sd(1/x)
fn simp__pctinverse_jacobi_ds(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_ds, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if ellipt__any_numerical_p(u, m) {
    ftake(q_p_inverse_jacobi_sd, [d_rectform(div(int(1), u)), m])
  } else if ellipt__trigsign_p(u) {
    neg(ftake_star(q_p_inverse_jacobi_ds, [neg(u), m]))
  } else if eql(int(0), d_ratsimp(sub(u, ellipt__root_m1(m)), Nil)) {
    // inverse_jacobi_ds(sqrt(1-m),m) = elliptic_kc(m)
    //
    // Since inverse_jacobi_ds(sqrt(1-m), m) =
    // inverse_jacobi_sd(1/sqrt(1-m),m).  And we know from above that this
    // is elliptic_kc(m)
    ftake(q_p_elliptic_kc, [m])
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_ds) {
    // inverse_jacobi_ds(ds(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_ds, [u, m], form)
  }
}

///|
/// inverse_jacobi_dc(x)
///
/// Let u = inverse_jacobi_dc(x).  Then jacobi_dc(u) = x or
/// 1/x = 1/jacobi_dc(u) = jacobi_cd(u)
///
/// u = inverse_cd(1/x)
fn simp__pctinverse_jacobi_dc(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_inverse_jacobi_dc, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if complex_float_numerical_eval_p(list2(u, m)).truthy() ||
    complex_bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    ftake(q_p_inverse_jacobi_cd, [d_rectform(div(int(1), u)), m])
  } else if onep1(u).truthy() {
    int(0)
  } else if ellipt__all_inverse_p(u, m, q_p_jacobi_dc) {
    // inverse_jacobi_dc(dc(u)) = u
    second(u)
  } else {
    // Nothing to do
    ellipt__give_up(q_p_inverse_jacobi_dc, [u, m], form)
  }
}

///|
/// Convert an inverse Jacobian function into the equivalent elliptic
/// integral F.
///
/// See A&S 17.4.41-17.4.52.
fn make_elliptic_f(e : Value) -> Value raise {
  if atom(e) {
    return e
  }
  let fn_ = caar(e)
  if !memq(
      fn_,
      list([
        q_p_inverse_jacobi_sc, q_p_inverse_jacobi_cs, q_p_inverse_jacobi_nd, q_p_inverse_jacobi_dn,
        q_p_inverse_jacobi_sn, q_p_inverse_jacobi_cd, q_p_inverse_jacobi_dc, q_p_inverse_jacobi_ns,
        q_p_inverse_jacobi_nc, q_p_inverse_jacobi_ds, q_p_inverse_jacobi_sd, q_p_inverse_jacobi_cn,
      ]),
    ).truthy() {
    return recur_apply(q_make_elliptic_f, e)
  }
  // We have some inverse Jacobi function.  Convert it to the F form.
  if length(cdr(e)) != 2 {
    raise LispError::SimpleError(
      "MAKE-ELLIPTIC-F: wrong number of arguments in destructuring-bind",
    )
  }
  let u = cadr(e)
  let m = caddr(e)
  if eq(fn_, q_p_inverse_jacobi_sc) {
    // A&S 17.4.41
    ftake(q_p_elliptic_f, [ftake(q_p_atan, [u]), m])
  } else if eq(fn_, q_p_inverse_jacobi_cs) {
    // A&S 17.4.42
    ftake(q_p_elliptic_f, [ftake(q_p_atan, [div(int(1), u)]), m])
  } else if eq(fn_, q_p_inverse_jacobi_nd) {
    // A&S 17.4.43
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [
        muln_([
          power(m, ellipt__mq(-1, 2)),
          div(int(1), u),
          power(add2(int(-1), mul2(u, u)), ellipt__mq(1, 2)),
        ]),
      ]),
      m,
    ])
  } else if eq(fn_, q_p_inverse_jacobi_dn) {
    // A&S 17.4.44
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [
        mul2(
          power(m, ellipt__mq(-1, 2)),
          power(sub(int(1), power(u, int(2))), ellipt__mq(1, 2)),
        ),
      ]),
      m,
    ])
  } else if eq(fn_, q_p_inverse_jacobi_sn) {
    // A&S 17.4.45
    ftake(q_p_elliptic_f, [ftake(q_p_asin, [u]), m])
  } else if eq(fn_, q_p_inverse_jacobi_cd) {
    // A&S 17.4.46
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [
        power(
          mul2(sub(int(1), mul2(u, u)), sub(int(1), muln_([m, u, u]))),
          ellipt__mq(1, 2),
        ),
      ]),
      m,
    ])
  } else if eq(fn_, q_p_inverse_jacobi_dc) {
    // A&S 17.4.47
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [
        power(
          mul2(sub(mul2(u, u), int(1)), sub(mul2(u, u), m)),
          ellipt__mq(1, 2),
        ),
      ]),
      m,
    ])
  } else if eq(fn_, q_p_inverse_jacobi_ns) {
    // A&S 17.4.48
    ftake(q_p_elliptic_f, [ftake(q_p_asin, [div(int(1), u)]), m])
  } else if eq(fn_, q_p_inverse_jacobi_nc) {
    // A&S 17.4.49
    ftake(q_p_elliptic_f, [ftake(q_p_acos, [div(int(1), u)]), m])
  } else if eq(fn_, q_p_inverse_jacobi_ds) {
    // A&S 17.4.50
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [power(add2(m, mul2(u, u)), ellipt__mq(1, 2))]),
      m,
    ])
  } else if eq(fn_, q_p_inverse_jacobi_sd) {
    // A&S 17.4.51
    ftake(q_p_elliptic_f, [
      ftake(q_p_asin, [
        div(u, power(add2(int(1), muln_([m, u, u])), ellipt__mq(1, 2))),
      ]),
      m,
    ])
  } else {
    // %inverse_jacobi_cn
    // A&S 17.4.52
    ftake(q_p_elliptic_f, [ftake(q_p_acos, [u]), m])
  }
}

///|
fn d_make_elliptic_f(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    simplify(make_elliptic_f(e))
  }
}

///|
fn make_elliptic_e(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_d_elliptic_eu) {
    if length(cdr(e)) != 2 {
      raise LispError::SimpleError(
        "MAKE-ELLIPTIC-E: wrong number of arguments in destructuring-bind",
      )
    }
    let u = cadr(e)
    let m = caddr(e)
    ftake(q_p_elliptic_e, [
      ftake(q_p_asin, [ftake(q_p_jacobi_sn, [u, m])]),
      m,
    ])
  } else {
    recur_apply(q_make_elliptic_e, e)
  }
}

///|
fn d_make_elliptic_e(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    simplify(make_elliptic_e(e))
  }
}

///|
/// Eu(u,m) = integrate(jacobi_dn(v,m)^2,v,0,u)
///         = integrate(sqrt((1-m*t^2)/(1-t^2)),t,0,jacobi_sn(u,m))
///
/// Eu(u,m) = E(am(u),m)
///
/// where E(u,m) is elliptic-e above.
///
/// Checks.
/// Lawden gives the following relationships
///
/// E(u+v) = E(u) + E(v) - m*sn(u)*sn(v)*sn(u+v)
/// E(u,0) = u, E(u,1) = tanh u
///
/// E(i*u,k) = i*sc(u,k')*dn(u,k') - i*E(u,k') + i*u
///
/// E(2*i*K') = 2*i*(K'-E')
///
/// E(u + 2*i*K') = E(u) + 2*i*(K' - E')
///
/// E(u+K) = E(u) + E - k^2*sn(u)*cd(u)
fn elliptic_eu(u : Value, m : Value) -> Value raise {
  if realp(u) {
    // E(u + 2*n*K) = E(u) + 2*n*E
    let ell_k = maxima_to(elliptic_k(m))
    let ell_e = elliptic_ec(m)
    let (n, u_rem) = num_floor(u, b=num_mul(int(2), ell_k))
    // 0 <= u-rem < 2*K
    num_add(
      num_mul(num_mul(int(2), n), ell_e),
      if num_ge(u_rem, ell_k) {
        // 0 <= u-rem < K so
        // E(u + K) = E(u) + E - m*sn(u)*cd(u)
        let u_k = num_sub(u, ell_k)
        num_sub(
          num_add(elliptic_e(lasin(bf_sn(u_k, m)), m), ell_e),
          num_div(
            num_mul(num_mul(m, bf_sn(u_k, m)), bf_cn(u_k, m)),
            bf_dn(u_k, m),
          ),
        )
      } else {
        elliptic_e(lasin(bf_sn(u, m)), m)
      },
    )
  } else if complexp(u) {
    // From Lawden:
    //
    // E(u+i*v, m) = E(u,m) -i*E(v,m') + i*v + i*sc(v,m')*dn(v,m')
    //                -i*m*sn(u,m)*sc(v,m')*sn(u+i*v,m)
    let u_r = realpart(u)
    let u_i = imagpart(u)
    let m1 = num_sub(int(1), m)
    num_add(
      elliptic_eu(u_r, m),
      num_mul(
        Cplx(int(0), int(1)),
        num_sub(
          num_add(
            u_i,
            num_div(num_mul(bf_sn(u_i, m1), bf_dn(u_i, m1)), bf_cn(u_i, m1)),
          ),
          num_add(
            elliptic_eu(u_i, m1),
            num_div(
              num_mul(
                num_mul(num_mul(m, bf_sn(u_r, m)), bf_sn(u_i, m1)),
                bf_sn(u, m),
              ),
              bf_cn(u_i, m1),
            ),
          ),
        ),
      ),
    )
  } else {
    Nil
  }
}

///|
fn simp__pctelliptic_eu(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_elliptic_eu, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  // as it stands, ELLIPTIC-EU can't handle bigfloats or complex bigfloats,
  // so handle only floats and complex floats here.
  if float_numerical_eval_p(list2(u, m)).truthy() {
    elliptic_eu(d_float(u), d_float(m))
  } else if complex_float_numerical_eval_p(list2(u, m)).truthy() {
    let u_r = d_realpart(u)
    let u_i = d_imagpart(u)
    let m = d_float(m)
    complexify(elliptic_eu(complex(u_r, i=u_i), m))
  } else {
    ellipt__give_up(q_p_elliptic_eu, [u, m], form)
  }
}

///|
/// Real and imaginary part for Jacobi elliptic functions.
fn risplit_sn_cn_dn(expr : Value) -> Value raise {
  let arg_ = second(expr)
  let param = third(expr)
  // We only split on the argument, not the order
  let ri = risplit(arg_)
  let arg_r = car(ri)
  let arg_i = cdr(ri)
  if eq0(arg_i) {
    // Pure real
    return cons(take(first(expr), [arg_r, param]), int(0))
  }
  let s = ftake(q_p_jacobi_sn, [arg_r, param])
  let c = ftake(q_p_jacobi_cn, [arg_r, param])
  let d = ftake(q_p_jacobi_dn, [arg_r, param])
  let s1 = ftake(q_p_jacobi_sn, [arg_i, sub(int(1), param)])
  let c1 = ftake(q_p_jacobi_cn, [arg_i, sub(int(1), param)])
  let d1 = ftake(q_p_jacobi_dn, [arg_i, sub(int(1), param)])
  let den = add2(mul2(c1, c1), mul2(param, mul2(mul2(s, s), mul2(s1, s1))))
  // Let s = jacobi_sn(x,m)
  //     c = jacobi_cn(x,m)
  //     d = jacobi_dn(x,m)
  //     s1 = jacobi_sn(y,1-m)
  //     c1 = jacobi_cn(y,1-m)
  //     d1 = jacobi_dn(y,1-m)
  let op = caar(expr)
  if eq(op, q_p_jacobi_sn) {
    // A&S 16.21.1
    // jacobi_sn(x+%i*y,m) =
    //
    //  s*d1 + %i*c*d*s1*c1
    //  -------------------
    //    c1^2+m*s^2*s1^2
    cons(div(mul2(s, d1), den), div(mul2(c, mul2(d, mul2(s1, c1))), den))
  } else if eq(op, q_p_jacobi_cn) {
    // A&S 16.21.2
    //
    // cn(x+%i_y, m) =
    //
    //  c*c1 - %i*s*d*s1*d1
    //  -------------------
    //    c1^2+m*s^2*s1^2
    cons(
      div(mul2(c, c1), den),
      div(mul2(int(-1), mul2(s, mul2(d, mul2(s1, d1)))), den),
    )
  } else if eq(op, q_p_jacobi_dn) {
    // A&S 16.21.3
    //
    // dn(x+%i_y, m) =
    //
    //  d*c1*d1 - %i*m*s*c*s1
    //  ---------------------
    //    c1^2+m*s^2*s1^2
    cons(
      div(mul2(d, mul2(c1, d1)), den),
      div(mul2(int(-1), mul2(param, mul2(s, mul2(c, s1)))), den),
    )
  } else {
    Nil
  }
}

// Jacobi amplitude function.

///|
fn simp__pctjacobi_am(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  ellipt__check_nargs(form, q_p_jacobi_am, [q_d_u, q_d_m])
  let u = simpcheck(nth(1, form), p__pctsimpflag)
  let m = simpcheck(nth(2, form), p__pctsimpflag)
  if zerop1(u).truthy() {
    // am(0,m) = 0
    return int(0)
  }
  if zerop1(m).truthy() {
    // See https://dlmf.nist.gov/22.16.E4
    //
    // am(u,0) = u
    return u
  }
  if eql(m, int(1)) {
    // See https://dlmf.nist.gov/22.16.E5.  This is equivalent to the
    // Gudermannian function.
    //
    // am(u,1) = 2*atan(exp(u))-%pi/2
    return sub(
      mul2(int(2), ftake(q_p_atan, [ftake(q_p_exp, [u])])),
      div(q_d__pctpi, int(2)),
    )
  }
  if float_numerical_eval_p(list2(u, m)).truthy() {
    return maxima_to(
      bf_bf_jacobi_am(d_float(u), d_float(m), Flo(double_float_epsilon)),
    )
  }
  let args = complex_float_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let u = first(args)
    let m = second(args)
    return maxima_to(
      bf_bf_jacobi_am(
        bf_to(d_float(u)),
        bf_to(d_float(m)),
        Flo(double_float_epsilon),
      ),
    )
  }
  if bigfloat_numerical_eval_p(list2(u, m)).truthy() {
    return maxima_to(
      bf_bf_jacobi_am(
        bf_to(d_bfloat(u)),
        bf_to(d_bfloat(m)),
        expt(int(2), num_neg(symval(q_fpprec))),
      ),
    )
  }
  let args = complex_bigfloat_numerical_eval_p(list2(u, m))
  if args.truthy() {
    let u = first(args)
    let m = second(args)
    return maxima_to(
      bf_bf_jacobi_am(
        bf_to(d_bfloat(u)),
        bf_to(d_bfloat(m)),
        expt(int(2), num_neg(symval(q_fpprec))),
      ),
    )
  }
  // Nothing to do
  ellipt__give_up(q_p_jacobi_am, [u, m], form)
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
/// `(defgrad name args derivs...)`
fn ellipt__defgrad(name : Value, args : Value, derivs : Array[Value]) -> Unit {
  if !memq(name, symval(q_ear_defgrad_syms)).truthy() {
    push_special(name, q_ear_defgrad_syms) |> ignore
  }
  putprop(name, cons(args, list(derivs)), q_grad) |> ignore
}

///|
fn init_ellipt() -> Unit raise {
  let um = list2(q_d_u, q_d_m)
  let xm = list2(q_d_x, q_d_m)
  // Tell maxima what the derivatives are.
  //
  // Lawden says the derivative wrt to k but that's not what we want.
  //
  // Here's the derivation we used, based on how Lawden gets his results.
  //
  // Let
  //
  // diff(sn(u,m),m) = s
  // diff(cn(u,m),m) = p
  // diff(dn(u,m),m) = q
  //
  // From the derivatives of sn, cn, dn wrt to u, we have
  //
  // diff(sn(u,m),u) = cn(u)*dn(u)
  // diff(cn(u,m),u) = -cn(u)*dn(u)
  // diff(dn(u,m),u) = -m*sn(u)*cn(u)
  //
  // Differentiate these wrt to m:
  //
  // diff(s,u) = p*dn + cn*q
  // diff(p,u) = -p*dn - q*dn
  // diff(q,u) = -sn*cn - m*s*cn - m*sn*q
  //
  // Also recall that
  //
  // sn(u)^2 + cn(u)^2 = 1
  // dn(u)^2 + m*sn(u)^2 = 1
  //
  // Differentiate these wrt to m:
  //
  // sn*s + cn*p = 0
  // 2*dn*q + sn^2 + 2*m*sn*s = 0
  //
  // Thus,
  //
  // p = -s*sn/cn
  // q = -m*s*sn/dn - sn^2/dn/2
  //
  // So
  // diff(s,u) = -s*sn*dn/cn - m*s*sn*cn/dn - sn^2*cn/dn/2
  //
  // or
  //
  // diff(s,u) + s*(sn*dn/cn + m*sn*cn/dn) = -1/2*sn^2*cn/dn
  //
  // diff(s,u) + s*sn/cn/dn*(dn^2 + m*cn^2) = -1/2*sn^2*cn/dn
  //
  // Multiply through by the integrating factor 1/cn/dn:
  //
  // diff(s/cn/dn, u) = -1/2*sn^2/dn^2 = -1/2*sd^2.
  //
  // Integrate this to get
  //
  // s/cn/dn = C + -1/2*int sd^2
  //
  // It can be shown that C is zero.
  //
  // We know that (by differentiating this expression)
  //
  // int dn^2 = (1-m)*u+m*sn*cd + m*(1-m)*int sd^2
  //
  // or
  //
  // int sd^2 = 1/m/(1-m)*int dn^2 - u/m - sn*cd/(1-m)
  //
  // Thus, we get
  //
  // s/cn/dn = u/(2*m) + sn*cd/(2*(1-m)) - 1/2/m/(1-m)*int dn^2
  //
  // or
  //
  // s = 1/(2*m)*u*cn*dn + 1/(2*(1-m))*sn*cn^2 - 1/2/(m*(1-m))*cn*dn*E(u)
  //
  // where E(u) = int dn^2 = elliptic_e(am(u)) = elliptic_e(asin(sn(u)))
  //
  // This is our desired result:
  //
  // s = 1/(2*m)*cn*dn*[u - elliptic_e(asin(sn(u)),m)/(1-m)] + sn*cn^2/2/(1-m)
  //
  //
  // Since diff(cn(u,m),m) = p = -s*sn/cn, we have
  //
  // p = -1/(2*m)*sn*dn[u - elliptic_e(asin(sn(u)),m)/(1-m)] - sn^2*cn/2/(1-m)
  //
  // diff(dn(u,m),m) = q = -m*s*sn/dn - sn^2/dn/2
  //
  // q = -1/2*sn*cn*[u-elliptic_e(asin(sn),m)/(1-m)] - m*sn^2*cn^2/dn/2/(1-m)
  //
  //      - sn^2/dn/2
  //
  //   = -1/2*sn*cn*[u-elliptic_e(asin(sn),m)/(1-m)] + dn*sn^2/2/(m-1)
  ellipt__defgrad(q_p_jacobi_sn, um, [
    maxima_lit("jacobi_cn(u,m)*jacobi_dn(u,m)"),
    maxima_lit(
      "(jacobi_cn(u,m)*jacobi_dn(u,m)*(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n  /(2*m)\n  +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m))",
    ),
  ])
  ellipt__defgrad(q_p_jacobi_cn, um, [
    maxima_lit(" -(jacobi_dn(u,m)*jacobi_sn(u,m))"),
    maxima_lit(
      " -((jacobi_dn(u,m)*jacobi_sn(u,m)*(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /(2*m))\n -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))",
    ),
  ])
  ellipt__defgrad(q_p_jacobi_dn, um, [
    maxima_lit(" -(m*jacobi_cn(u,m)*jacobi_sn(u,m))"),
    maxima_lit(
      " -((jacobi_cn(u,m)*jacobi_sn(u,m)*(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /2)\n -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))",
    ),
  ])
  // The inverse elliptic functions.
  //
  // F(phi|m) = asn(sin(phi),m)
  //
  // so asn(u,m) = F(asin(u)|m)
  ellipt__defgrad(q_p_inverse_jacobi_sn, xm, [
    maxima_lit(" 1/(sqrt(1-x^2)*sqrt(1-m*x^2))"),
    maxima_lit(
      " ((elliptic_e(asin(x),m)-(1-m)*elliptic_f(asin(x),m))/m\n -(x*sqrt(1-x^2))/sqrt(1-m*x^2))\n/(1-m)",
    ),
  ])
  // Let u = inverse_jacobi_cn(x).  Then jacobi_cn(u) = x or
  // sqrt(1-jacobi_sn(u)^2) = x.  Or
  //
  // jacobi_sn(u) = sqrt(1-x^2)
  //
  // So u = inverse_jacobi_sn(sqrt(1-x^2),m) = inverse_jacob_cn(x,m)
  ellipt__defgrad(q_p_inverse_jacobi_cn, xm, [
    // Whittaker and Watson, 22.121
    // inverse_jacobi_cn(u,m) = integrate(1/sqrt(1-t^2)/sqrt(1-m+m*t^2), t, u, 1)
    // -> -1/sqrt(1-x^2)/sqrt(1-m+m*x^2)
    maxima_lit("-(1/(sqrt(1-x^2)*sqrt(m*x^2-m+1)))"),
    maxima_lit(
      "((elliptic_e(asin(sqrt(1-x^2)),m)-(1-m)*elliptic_f(asin(sqrt(1-x^2)),m))/m\n -(sqrt(1-x^2)*abs(x))/sqrt(1-m*(1-x^2)))\n /(1-m)",
    ),
  ])
  // Let u = inverse_jacobi_dn(x).  Then
  //
  // jacobi_dn(u) = x or
  //
  // x^2 = jacobi_dn(u)^2 = 1 - m*jacobi_sn(u)^2
  //
  // so jacobi_sn(u) = sqrt(1-x^2)/sqrt(m)
  //
  // or u = inverse_jacobi_sn(sqrt(1-x^2)/sqrt(m))
  ellipt__defgrad(q_p_inverse_jacobi_dn, xm, [
    // Whittaker and Watson, 22.121
    // inverse_jacobi_dn(u,m) = integrate(1/sqrt(1-t^2)/sqrt(t^2-(1-m)), t, u, 1)
    // -> -1/sqrt(1-x^2)/sqrt(x^2+m-1)
    maxima_lit("1/(sqrt(1-x^2)*sqrt(x^2+m-1))"),
    maxima_lit(
      " ((elliptic_e(asin(sqrt(1-x^2)/sqrt(m)),m)\n -(1-m)*elliptic_f(asin(sqrt(1-x^2)/sqrt(m)),m))\n /m\n -(sqrt(1-(1-x^2)/m)*sqrt(1-x^2))/(sqrt(m)*abs(x)))\n /(1-m)\n -sqrt(1-x^2)/(2*m^(3/2)*sqrt(1-(1-x^2)/m)*abs(x)) ",
    ),
  ])
  // The derivative of F(phi|m) wrt to phi is easy.  The derivative wrt to
  // m is harder:
  //
  //   d
  // 2 -- (elliptic_F(PHI, m)) =
  //   dm
  //
  //  elliptic_E(PHI, m) - (1 - m) elliptic_F(PHI, m)     COS(PHI) SIN(PHI)
  //  ---------------------------------------------- - ---------------------
  //                     m                                         2
  //                                                   SQRT(1 - m SIN (PHI))
  //   ----------------------------------------------------------------------
  //                                    1 - m
  ellipt__defgrad(q_p_elliptic_f, list2(q_d_phi, q_d_m), [
    // diff wrt phi
    // 1/sqrt(1-m*sin(phi)^2)
    maxima_lit("1/sqrt(1-m*sin(phi)^2)"),
    // diff wrt m
    maxima_lit(
      "((elliptic_e(phi,m)-(1-m)*elliptic_f(phi,m))/m\n -(cos(phi)*sin(phi))/sqrt(1-m*sin(phi)^2))\n /(2*(1-m))",
    ),
  ])
  // The derivative of E(phi|m) wrt to m is much simpler to derive than
  // F(phi|m):
  //
  //   d                         elliptic_E(PHI, m) - elliptic_F(PHI, m)
  //   -- (elliptic_E(PHI, m)) = ---------------------------------------
  //   dm                                         2 m
  ellipt__defgrad(q_p_elliptic_e, list2(q_d_phi, q_d_m), [
    // sqrt(1-m*sin(phi)^2)
    maxima_lit("sqrt(1-m*sin(phi)^2)"),
    // diff wrt m
    maxima_lit("(elliptic_e(phi,m)-elliptic_f(phi,m))/(2*m)"),
  ])
  setf_get(q_p_elliptic_kc, q_simplim_pctfunction, q_simplim_pctelliptic_kc)
  |> ignore
  ellipt__defgrad(q_p_elliptic_kc, list1(q_d_m), [
    // diff wrt m
    maxima_lit("(elliptic_ec(m)-(1-m)*elliptic_kc(m))/(2*(1-m)*m)"),
  ])
  ellipt__defgrad(q_p_elliptic_ec, list1(q_d_m), [
    maxima_lit("(elliptic_ec(m)-elliptic_kc(m))/(2*m)"),
  ])
  // Deriviatives from functions.wolfram.com
  // http://functions.wolfram.com/EllipticIntegrals/EllipticPi3/20/
  ellipt__defgrad(q_p_elliptic_pi, list3(q_d_n, q_d_z, q_d_m), [
    // Derivative wrt first argument
    maxima_lit(
      "(-((n*sqrt(1-m*sin(z)^2)*sin(2*z))/(2*(1-n*sin(z)^2)))\n +((m-n)*elliptic_f(z,m))/n+elliptic_e(z,m)+((n^2-m)*elliptic_pi(n,z,m))/n)\n /(2*(m-n)*(n-1))",
    ),
    // Derivative wrt second argument
    maxima_lit("1/(sqrt(1-m*sin(z)^2)*(1-n*sin(z)^2))"),
    // Derivative wrt third argument
    maxima_lit(
      "(-((m*sin(2*z))/(2*(m-1)*sqrt(1-m*sin(z)^2)))\n +elliptic_e(z,m)/(m-1)+elliptic_pi(n,z,m))\n /(2*(n-m))",
    ),
  ])
  // Other Jacobian elliptic functions

  // jacobi_ns(u,m) = 1/jacobi_sn(u,m)
  ellipt__defgrad(q_p_jacobi_ns, um, [
    // diff wrt u
    maxima_lit(" -((jacobi_cn(u,m)*jacobi_dn(u,m))/jacobi_sn(u,m)^2)"),
    // diff wrt m
    maxima_lit(
      " -(((jacobi_cn(u,m)*jacobi_dn(u,m)\n                  *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /(2*m)\n +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m)))\n /jacobi_sn(u,m)^2)",
    ),
  ])
  // jacobi_nc(u,m) = 1/jacobi_cn(u,m)
  ellipt__defgrad(q_p_jacobi_nc, um, [
    // wrt u
    maxima_lit("(jacobi_dn(u,m)*jacobi_sn(u,m))/jacobi_cn(u,m)^2"),
    // wrt m
    maxima_lit(
      "-((-((jacobi_dn(u,m)*jacobi_sn(u,m)\n                    *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /(2*m))\n -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n /jacobi_cn(u,m)^2)",
    ),
  ])
  // jacobi_nd(u,m) = 1/jacobi_dn(u,m)
  ellipt__defgrad(q_p_jacobi_nd, um, [
    // wrt u
    maxima_lit(" (m*jacobi_cn(u,m)*jacobi_sn(u,m))/jacobi_dn(u,m)^2"),
    // wrt m
    maxima_lit(
      " -((-((jacobi_cn(u,m)*jacobi_sn(u,m)\n                     *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n           /2)\n          -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n        /jacobi_dn(u,m)^2)",
    ),
  ])
  // jacobi_sc(u,m) = jacobi_sn/jacobi_cn
  ellipt__defgrad(q_p_jacobi_sc, um, [
    // wrt u
    maxima_lit(" jacobi_dn(u,m)/jacobi_cn(u,m)^2"),
    // wrt m
    maxima_lit(
      " ((jacobi_cn(u,m)*jacobi_dn(u,m)*(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n       /(2*m)\n       +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m)))\n  /jacobi_cn(u,m)\n  -(jacobi_sn(u,m)*(-((jacobi_dn(u,m)*jacobi_sn(u,m)\n                                *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                              /(1-m)))\n                      /(2*m))\n                     -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))))\n  /jacobi_cn(u,m)^2",
    ),
  ])
  // jacobi_sd(u,m) = jacobi_sn/jacobi_dn
  ellipt__defgrad(q_p_jacobi_sd, um, [
    // wrt u
    maxima_lit(" jacobi_cn(u,m)/jacobi_dn(u,m)^2"),
    // wrt m
    maxima_lit(
      " ((jacobi_cn(u,m)*jacobi_dn(u,m)*(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n       /(2*m)\n       +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m)))\n  /jacobi_dn(u,m)\n -(jacobi_sn(u,m)*(-((jacobi_cn(u,m)*jacobi_sn(u,m)\n                               *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                             /(1-m)))\n                     /2)\n                    -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))))\n  /jacobi_dn(u,m)^2",
    ),
  ])
  // jacobi_cs(u,m) = jacobi_cn/jacobi_sn
  ellipt__defgrad(q_p_jacobi_cs, um, [
    // wrt u
    maxima_lit(" -(jacobi_dn(u,m)/jacobi_sn(u,m)^2)"),
    // wrt m
    maxima_lit(
      " (-((jacobi_dn(u,m)*jacobi_sn(u,m)\n                   *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n         /(2*m))\n        -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n  /jacobi_sn(u,m)\n  -(jacobi_cn(u,m)*((jacobi_cn(u,m)*jacobi_dn(u,m)\n                              *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                            /(1-m)))\n                    /(2*m)\n                    +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m))))\n  /jacobi_sn(u,m)^2",
    ),
  ])
  // jacobi_cd(u,m) = jacobi_cn/jacobi_dn
  ellipt__defgrad(q_p_jacobi_cd, um, [
    // wrt u
    maxima_lit(" ((m-1)*jacobi_sn(u,m))/jacobi_dn(u,m)^2"),
    // wrt m
    maxima_lit(
      " (-((jacobi_dn(u,m)*jacobi_sn(u,m)\n                  *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /(2*m))\n -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n /jacobi_dn(u,m)\n -(jacobi_cn(u,m)*(-((jacobi_cn(u,m)*jacobi_sn(u,m)\n                                    *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                        /(1-m)))\n                  /2)\n                  -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))))\n  /jacobi_dn(u,m)^2",
    ),
  ])
  // jacobi_ds(u,m) = jacobi_dn/jacobi_sn
  ellipt__defgrad(q_p_jacobi_ds, um, [
    // wrt u
    maxima_lit(" -(jacobi_cn(u,m)/jacobi_sn(u,m)^2)"),
    // wrt m
    maxima_lit(
      " (-((jacobi_cn(u,m)*jacobi_sn(u,m)\n                  *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /2)\n -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n /jacobi_sn(u,m)\n -(jacobi_dn(u,m)*((jacobi_cn(u,m)*jacobi_dn(u,m)\n                                  *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                      /(1-m)))\n                  /(2*m)\n                  +(jacobi_cn(u,m)^2*jacobi_sn(u,m))/(2*(1-m))))\n  /jacobi_sn(u,m)^2",
    ),
  ])
  // jacobi_dc(u,m) = jacobi_dn/jacobi_cn
  ellipt__defgrad(q_p_jacobi_dc, um, [
    // wrt u
    maxima_lit(" ((1-m)*jacobi_sn(u,m))/jacobi_cn(u,m)^2"),
    // wrt m
    maxima_lit(
      " (-((jacobi_cn(u,m)*jacobi_sn(u,m)\n                  *(u-elliptic_e(asin(jacobi_sn(u,m)),m)/(1-m)))\n /2)\n -(jacobi_dn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m)))\n /jacobi_cn(u,m)\n -(jacobi_dn(u,m)*(-((jacobi_dn(u,m)*jacobi_sn(u,m)\n                                    *(u-elliptic_e(asin(jacobi_sn(u,m)),m)\n                                        /(1-m)))\n                  /(2*m))\n                  -(jacobi_cn(u,m)*jacobi_sn(u,m)^2)/(2*(1-m))))\n  /jacobi_cn(u,m)^2",
    ),
  ])
  // The second defgrad of %jacobi_dc replaces the first one.
  let dc_grad = lread(
    "((u m) ((mtimes) ((mplus) 1 ((mtimes) -1 m)) ((mexpt) ((%jacobi_cn) u m) -2) ((%jacobi_sn) u m)) ((mplus) ((mtimes) ((mexpt) ((%jacobi_cn) u m) -1) ((mplus) ((mtimes) ((rat) -1 2) ((mexpt) ((mplus) 1 ((mtimes) -1 m)) -1) ((%jacobi_dn) u m) ((mexpt) ((%jacobi_sn) u m) 2)) ((mtimes) ((rat) -1 2) ((%jacobi_cn) u m) ((%jacobi_sn) u m) ((mplus) u ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 m)) -1) ((%elliptic_e) ((%asin) ((%jacobi_sn) u m)) m)))))) ((mtimes) -1 ((mexpt) ((%jacobi_cn) u m) -2) ((%jacobi_dn) u m) ((mplus) ((mtimes) ((rat) -1 2) ((mexpt) ((mplus) 1 ((mtimes) -1 m)) -1) ((%jacobi_cn) u m) ((mexpt) ((%jacobi_sn) u m) 2)) ((mtimes) ((rat) -1 2) ((mexpt) m -1) ((%jacobi_dn) u m) ((%jacobi_sn) u m) ((mplus) u ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 m)) -1) ((%elliptic_e) ((%asin) ((%jacobi_sn) u m)) m))))))))",
  )
  ellipt__defgrad(q_p_jacobi_dc, car(dc_grad), list_to_array(cdr(dc_grad)))
  // Other inverse Jacobian functions

  // inverse_jacobi_ns(x)
  ellipt__defgrad(q_p_inverse_jacobi_ns, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_ns(u,m) = integrate(1/sqrt(t^2-1)/sqrt(t^2-m), t, u, inf)
    // -> -1/sqrt(x^2-1)/sqrt(x^2-m)
    maxima_lit(" -(1/(sqrt(x^2-1)*sqrt(x^2-m)))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_nc(x)
  ellipt__defgrad(q_p_inverse_jacobi_nc, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_nc(u,m) = integrate(1/sqrt(t^2-1)/sqrt((1-m)*t^2+m), t, 1, u)
    // -> 1/sqrt(x^2-1)/sqrt((1-m)*x^2+m)
    maxima_lit(" 1/(sqrt(x^2-1)*sqrt(m-(m-1)*x^2))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_nd(x)
  ellipt__defgrad(q_p_inverse_jacobi_nd, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_nd(u,m) = integrate(1/sqrt(t^2-1)/sqrt(1-(1-m)*t^2), t, 1, u)
    // -> 1/sqrt(u^2-1)/sqrt(1-(1-m)*t^2)
    maxima_lit(" 1/(sqrt(x^2-1)*sqrt((m-1)*x^2+1))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_sc(x)
  ellipt__defgrad(q_p_inverse_jacobi_sc, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_sc(u,m) = integrate(1/sqrt(1+t^2)/sqrt(1+(1-m)*t^2), t, 0, u)
    // -> 1/sqrt(1+x^2)/sqrt(1+(1-m)*x^2)
    maxima_lit(" 1/(sqrt(x^2+1)*sqrt(1-(m-1)*x^2))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_sd(x)
  ellipt__defgrad(q_p_inverse_jacobi_sd, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_sd(u,m) = integrate(1/sqrt(1-(1-m)*t^2)/sqrt(1+m*t^2), t, 0, u)
    // -> 1/sqrt(1-(1-m)*x^2)/sqrt(1+m*x^2)
    maxima_lit(" 1/(sqrt((m-1)*x^2+1)*sqrt(m*x^2+1))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_cs(x)
  ellipt__defgrad(q_p_inverse_jacobi_cs, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_cs(u,m) = integrate(1/sqrt(t^2+1)/sqrt(t^2+(1-m)), t, u, inf)
    // -> -1/sqrt(x^2+1)/sqrt(x^2+(1-m))
    maxima_lit(" -(1/(sqrt(x^2+1)*sqrt(x^2-m+1)))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_cd(x)
  ellipt__defgrad(q_p_inverse_jacobi_cd, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_cd(u,m) = integrate(1/sqrt(1-t^2)/sqrt(1-m*t^2), t, u, 1)
    // -> -1/sqrt(1-x^2)/sqrt(1-m*x^2)
    maxima_lit(" -(1/(sqrt(1-x^2)*sqrt(1-m*x^2)))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_ds(x)
  ellipt__defgrad(q_p_inverse_jacobi_ds, xm, [
    // wrt x
    // Whittaker and Watson, example in 22.122
    // inverse_jacobi_ds(u,m) = integrate(1/sqrt(t^2-(1-m))/sqrt(t^2+m), t, u, inf)
    // -> -1/sqrt(x^2-(1-m))/sqrt(x^2+m)
    maxima_lit(" -(1/(sqrt(x^2+m-1)*sqrt(x^2+m)))"),
    // wrt m
    Nil,
  ])
  // inverse_jacobi_dc(x)
  ellipt__defgrad(q_p_inverse_jacobi_dc, xm, [
    // wrt x
    // Note: Whittaker and Watson, example in 22.122 says
    // inverse_jacobi_dc(u,m) = integrate(1/sqrt(t^2-1)/sqrt(t^2-m), t, u,
    // 1) but that seems wrong.  A&S 17.4.47 says
    // integrate(1/sqrt(t^2-1)/sqrt(t^2-m), t, a, u) =
    // inverse_jacobi_cd(x,m).  Lawden 3.2.8 says the same.
    // functions.wolfram.com says the derivative is
    // 1/sqrt(t^2-1)/sqrt(t^2-m).
    maxima_lit(" 1/(sqrt(x^2-1)*sqrt(x^2-m))"),
    // wrt m
    Nil,
  ])
  ellipt__defgrad(q_p_elliptic_eu, um, [
    // wrt u
    maxima_lit(" jacobi_dn(u,m)^2 "),
    // wrt m
    Nil,
  ])
  // Integrals.  At present with respect to first argument only.

  // A&S 16.24.1: integrate(jacobi_sn(u,m),u)
  //              = log(jacobi_dn(u,m)-sqrt(m)*jacobi_cn(u,m))/sqrt(m)
  putprop(
    q_p_jacobi_sn,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) m ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((mtimes simp) -1 ((mexpt simp) m ((rat simp) 1 2)) ((%jacobi_cn simp) u m)) ((%jacobi_dn simp) u m)))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.2: integrate(jacobi_cn(u,m),u) = acos(jacobi_dn(u,m))/sqrt(m)
  putprop(
    q_p_jacobi_cn,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) m ((rat simp) -1 2)) ((%acos simp) ((%jacobi_dn simp) u m))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.3: integrate(jacobi_dn(u,m),u) = asin(jacobi_sn(u,m))
  putprop(
    q_p_jacobi_dn,
    lread("((u m) ((%asin simp) ((%jacobi_sn simp) u m)) nil)"),
    q_integral,
  )
  |> ignore
  // A&S 16.24.4: integrate(jacobi_cd(u,m),u)
  //              = log(jacobi_nd(u,m)+sqrt(m)*jacobi_sd(u,m))/sqrt(m)
  putprop(
    q_p_jacobi_cd,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) m ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((%jacobi_nd simp) u m) ((mtimes simp) ((mexpt simp) m ((rat simp) 1 2)) ((%jacobi_sd simp) u m))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // integrate(jacobi_sd(u,m),u)
  //
  // A&S 16.24.5 gives
  //   asin(-sqrt(m)*jacobi_cd(u,m))/sqrt(m*m_1), where m + m_1 = 1
  //  but this does not pass some simple tests.
  //
  // functions.wolfram.com 09.35.21.001.01 gives
  //  -asin(sqrt(m)*jacobi_cd(u,m))*sqrt(1-m*jacobi_cd(u,m)^2)*jacobi_dn(u,m)/((1-m)*sqrt(m))
  // and this does pass.
  putprop(
    q_p_jacobi_sd,
    lread(
      "((u m) ((mtimes simp) -1 ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) -1) ((mexpt simp) m ((rat simp) -1 2)) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m ((mexpt simp) ((%jacobi_cd simp) u m) 2))) ((rat simp) 1 2)) ((%jacobi_dn simp) u m) ((%asin simp) ((mtimes simp) ((mexpt simp) m ((rat simp) 1 2)) ((%jacobi_cd simp) u m)))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // integrate(jacobi_nd(u,m),u)
  //
  //  A&S 16.24.6 gives
  //    acos(jacobi_cd(u,m))/sqrt(m_1), where m + m_1 = 1
  //  but this does not pass some simple tests.
  //
  // functions.wolfram.com 09.32.21.0001.01 gives
  //  sqrt(1-jacobi_cd(u,m)^2)*acos(jacobi_cd(u,m))/((1-m)*jacobi_sd(u,m))
  // and this does pass.
  putprop(
    q_p_jacobi_nd,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) -1) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 ((mexpt simp) ((%jacobi_cd simp) u m) 2))) ((rat simp) 1 2)) ((mexpt simp) ((%jacobi_sd simp) u m) -1) ((%acos simp) ((%jacobi_cd simp) u m))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.7: integrate(jacobi_dc(u,m),u) = log(jacobi_nc(u,m)+jacobi_sc(u,m))
  putprop(
    q_p_jacobi_dc,
    lread(
      "((u m) ((%log simp) ((mplus simp) ((%jacobi_nc simp) u m) ((%jacobi_sc simp) u m))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.8: integrate(jacobi_nc(u,m),u)
  //              = log(jacobi_dc(u,m)+sqrt(m_1)*jacobi_sc(u,m))/sqrt(m_1), where m + m_1 = 1
  putprop(
    q_p_jacobi_nc,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((%jacobi_dc simp) u m) ((mtimes simp) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) ((rat simp) 1 2)) ((%jacobi_sc simp) u m))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.9: integrate(jacobi_sc(u,m),u)
  //              = log(jacobi_dc(u,m)+sqrt(m_1)*jacobi_nc(u,m))/sqrt(m_1), where m + m_1 = 1
  putprop(
    q_p_jacobi_sc,
    lread(
      "((u m) ((mtimes simp) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((%jacobi_dc simp) u m) ((mtimes simp) ((mexpt simp) ((mplus simp) 1 ((mtimes simp) -1 m)) ((rat simp) 1 2)) ((%jacobi_nc simp) u m))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.10: integrate(jacobi_ns(u,m),u)
  //               = log(jacobi_ds(u,m)-jacobi_cs(u,m))
  putprop(
    q_p_jacobi_ns,
    lread(
      "((u m) ((%log simp) ((mplus simp) ((mtimes simp) -1 ((%jacobi_cs simp) u m)) ((%jacobi_ds simp) u m))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // integrate(jacobi_ds(u,m),u)
  //
  //  A&S 16.24.11 gives
  //   log(jacobi_ds(u,m)-jacobi_cs(u,m))
  // but this does not pass some simple tests.
  //
  // functions.wolfram.com 09.30.21.0001.01 gives
  //   log((1-jacobi_cn(u,m))/jacobi_sn(u,m))
  putprop(
    q_p_jacobi_ds,
    lread(
      "((u m) ((%log simp) ((mtimes simp) ((mplus simp) 1 ((mtimes simp) -1 ((%jacobi_cn simp) u m))) ((mexpt simp) ((%jacobi_sn simp) u m) -1))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // A&S 16.24.12: integrate(jacobi_cs(u,m),u) = log(jacobi_ns(u,m)-jacobi_ds(u,m))
  putprop(
    q_p_jacobi_cs,
    lread(
      "((u m) ((%log simp) ((mplus simp) ((mtimes simp) -1 ((%jacobi_ds simp) u m)) ((%jacobi_ns simp) u m))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // functions.wolfram.com 09.48.21.0001.01
  // integrate(inverse_jacobi_sn(u,m),u) =
  //   inverse_jacobi_sn(u,m)*u
  //   - log(         jacobi_dn(inverse_jacobi_sn(u,m),m)
  //         -sqrt(m)*jacobi_cn(inverse_jacobi_sn(u,m),m)) / sqrt(m)
  putprop(
    q_p_inverse_jacobi_sn,
    lread(
      "((u m) ((mplus simp) ((mtimes simp) u ((%inverse_jacobi_sn simp) u m)) ((mtimes simp) -1 ((mexpt simp) m ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((mtimes simp) -1 ((mexpt simp) m ((rat simp) 1 2)) ((%jacobi_cn simp) ((%inverse_jacobi_sn simp) u m) m)) ((%jacobi_dn simp) ((%inverse_jacobi_sn simp) u m) m))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // functions.wolfram.com 09.38.21.0001.01
  // integrate(inverse_jacobi_cn(u,m),u) =
  //   u*inverse_jacobi_cn(u,m)
  //    -%i*log(%i*jacobi_dn(inverse_jacobi_cn(u,m),m)/sqrt(m)
  //              -jacobi_sn(inverse_jacobi_cn(u,m),m))
  //      /sqrt(m)
  putprop(
    q_p_inverse_jacobi_cn,
    lread(
      "((u m) ((mplus simp) ((mtimes simp) u ((%inverse_jacobi_cn simp) u m)) ((mtimes simp) -1 $%i ((mexpt simp) m ((rat simp) -1 2)) ((%log simp) ((mplus simp) ((mtimes simp) $%i ((mexpt simp) m ((rat simp) -1 2)) ((%jacobi_dn simp) ((%inverse_jacobi_cn simp) u m) m)) ((mtimes simp) -1 ((%jacobi_sn simp) ((%inverse_jacobi_cn simp) u m) m)))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // functions.wolfram.com 09.41.21.0001.01
  // integrate(inverse_jacobi_dn(u,m),u) =
  //   u*inverse_jacobi_dn(u,m)
  //   - %i*log(%i*jacobi_cn(inverse_jacobi_dn(u,m),m)
  //              +jacobi_sn(inverse_jacobi_dn(u,m),m))
  putprop(
    q_p_inverse_jacobi_dn,
    lread(
      "((u m) ((mplus simp) ((mtimes simp) u ((%inverse_jacobi_dn simp) u m)) ((mtimes simp) -1 $%i ((%log simp) ((mplus simp) ((mtimes simp) $%i ((%jacobi_cn simp) ((%inverse_jacobi_dn simp) u m) m)) ((%jacobi_sn simp) ((%inverse_jacobi_dn simp) u m) m))))) nil)",
    ),
    q_integral,
  )
  |> ignore
  // Real and imaginary part for Jacobi elliptic functions.
  putprop(q_p_jacobi_sn, q_risplit_sn_cn_dn, q_risplit_function) |> ignore
  putprop(q_p_jacobi_cn, q_risplit_sn_cn_dn, q_risplit_function) |> ignore
  putprop(q_p_jacobi_dn, q_risplit_sn_cn_dn, q_risplit_function) |> ignore
  // Derivative of jacobi_am wrt z and m.
  ellipt__defgrad(q_p_jacobi_am, list2(q_d_z, q_d_m), [
    // WRT z.  From  http://functions.wolfram.com/09.24.20.0001.01
    // jacobi_dn(z,m)
    maxima_lit(" jacobi_dn(z,m)"),
    // WRT m.  From http://functions.wolfram.com/09.24.20.0003.01.  There
    // are 5 different formulas listed; we chose the first, arbitrarily.
    //
    // (((m-1)*z+elliptic_e(jacobi_am(z,m),m))*jacobi_dn(z,m)
    //   - m*jacobi_cn(z,m)*jacobi_sn(z,m))/(2*m*(m-1))
    maxima_lit(
      " (jacobi_dn(z,m)*(elliptic_e(jacobi_am(z,m),m)+(m-1)*z)\n -m*jacobi_cn(z,m)*jacobi_sn(z,m))\n /(2*(m-1)*m)",
    ),
  ])
}
