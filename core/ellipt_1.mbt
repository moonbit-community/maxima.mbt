// Port of src/ellipt.lisp, part 1: the BIGFLOAT-package routines that
// compute numerical values of the Jacobian elliptic functions, the AGM,
// Carlson's integrals and the Legendre elliptic integrals.
//
// Jacobian elliptic functions and elliptic integrals.
//
// References:
//
// [1] Abramowitz and Stegun
// [2] Lawden, Elliptic Functions and Applications, Springer-Verlag, 1989
// [3] Whittaker & Watson, A Course of Modern Analysis
//
// We use the definitions from Abramowitz and Stegun where our sn(u,m) is
// sn(u|m).  That is, the second arg is the parameter, instead of the
// modulus k or modular angle alpha.
//
// Note that m = k^2 and k = sin(alpha).
//
// A&S gives several methods for computing elliptic functions including the
// AGM method (16.4) and ascending and descending Landen transformations
// (16.12 and 16.14).  The latter are actually quite fast, only requiring
// simple arithmetic and square roots for the transformation until the last
// step.  The AGM requires evaluation of several trigonometric functions at
// each stage.
//
// However, the Landen transformations appear to have some round-off
// issues.  For example, using the ascending transform to compute cn,
// cn(100,.7) > 1e10.  This is clearly not right since |cn| <= 1.

///|
/// The CL rational n/d.
fn ellipt__q(n : Int, d : Int) -> Value {
  Ratio(@bigint.BigInt::from_int(n), @bigint.BigInt::from_int(d))
}

///|
/// The CL integer n.
fn ellipt__i(n : Int) -> Value {
  Fix(n.to_int64())
}

///|
/// Landen descending transform (Gauss' transform).
fn bf_descending_transform(
  u : Value,
  m : Value,
  root_m1 : Value,
) -> (Value, Value, Value, Value) raise {
  // A&S 16.12.1 (https://dlmf.nist.gov/22.7.E1).  ROOT-M1 is sqrt(1-m).
  // Return v = u/(1+sqrt(mu)), mu, sqrt(mu), and sqrt(1-mu).
  //
  // Don't calculate mu first, as given in 16.12.1.  We should calculate
  // sqrt(mu) = (1-sqrt(m1))/(1+sqrt(m1)), and then compute mu =
  // sqrt(mu)^2.  If we calculate mu first, sqrt(mu) loses information
  // when m or m1 is complex.
  //
  // When |sqrt(m1)| > 1/2, sqrt(mu) is computed as m/(1+sqrt(m1))^2
  // instead, which avoids the cancellation in 1-sqrt(m1) for small m.
  // Otherwise m is near 1 and has an absolute error that is large
  // relative to m1, so sqrt(mu) is computed from ROOT-M1 alone.
  // sqrt(1-mu) is computed as 2*sqrt(sqrt(m1))/(1+sqrt(m1)), without the
  // cancellation in 1-mu when m is near 1.
  let den = bf_add(ellipt__i(1), root_m1)
  let root_mu = if bf_le(bf_mul(ellipt__i(2), bf_abs(root_m1)), ellipt__i(1)) {
    bf_div(bf_sub(ellipt__i(1), root_m1), den)
  } else {
    bf_div(m, bf_mul(den, den))
  }
  let mu = bf_mul(root_mu, root_mu)
  let v = bf_div(u, bf_1_plus(root_mu))
  (v, mu, root_mu, bf_div(bf_mul(ellipt__i(2), bf_sqrt(root_m1)), den))
}

///|
fn bf_descending_base_p(u : Value, m : Value) -> Value raise {
  // True if m is small enough to stop the descending transformation.  By
  // A&S 16.13.1 (https://dlmf.nist.gov/22.10.E4), 16.13.2
  // (https://dlmf.nist.gov/22.10.E5), and 16.13.3
  // (https://dlmf.nist.gov/22.10.E6):
  //
  //   sn(u|m) = sin(u) - m/4*(u-sin(u)*cos(u))*cos(u) + O(m^2)
  //   cn(u|m) = cos(u) + m/4*(u-sin(u)*cos(u))*sin(u) + O(m^2)
  //   dn(u|m) = 1 - 1/2*m*sin^2(u) + O(m^2)
  //
  // Relative to sin(u) and cos(u), the terms with sin(u)*cos(u) are
  // m/4*cos(u)^2 and m/4*sin(u)^2, which grow like exp(2*abs(imagpart(u)))
  // relative to sin(u) or cos(u).  The terms with u shift the phase by
  // about m*u/4, less than the rounding error in u when abs(m) < eps.  For
  // dn, the error is m/2*sin(u)^2, which grows like m*exp(2*|y|)/8, which
  // is still covered by the test.
  lbool(
    bf_lt(bf_abs(m), bf_epsilon(u)) &&
    (bf_realp(u) ||
    bf_zerop(m) ||
    bf_lt(
      bf_abs(m),
      bf_mul(
        bf_epsilon(u),
        bf_exp(bf_mul(ellipt__i(-2), bf_abs(bf_imagpart(u)))),
      ),
    )),
  )
}

///|
/// sn(u|m) for m /= 1.  ROOT-M1 is sqrt(1-m).
fn bf_elliptic_sn_descending(
  u : Value,
  m : Value,
  root_m1 : Value,
) -> Value raise {
  if bf_descending_base_p(u, m).truthy() {
    // A&S 16.13.1 (https://dlmf.nist.gov/22.10.E4)
    bf_sin(u)
  } else {
    // A&S 16.12.2 (https://dlmf.nist.gov/22.7.E2):
    //
    //   sn(u|m) = (1+sqrt(mu))*sn(v|mu)/(1+sqrt(mu)*sn^2(v|mu)).
    let (v, mu, root_mu, root_mu1) = bf_descending_transform(u, m, root_m1)
    let s = bf_elliptic_sn_descending(v, mu, root_mu1)
    bf_div(
      bf_mul(bf_1_plus(root_mu), s),
      bf_1_plus(bf_mul(bf_mul(root_mu, s), s)),
    )
  }
}

///|
/// sn(u|m), cn(u|m), and dn(u|m) for m /= 1.  ROOT-M1 is sqrt(1-m).
fn bf_elliptic_sn_cn_dn_descending(
  u : Value,
  m : Value,
  root_m1 : Value,
) -> (Value, Value, Value) raise {
  if bf_descending_base_p(u, m).truthy() {
    // A&S 16.13.1 (https://dlmf.nist.gov/22.10.E4) to 16.13.3
    // (https://dlmf.nist.gov/22.10.E6), dropping the linear (and higher)
    // terms in m.
    (bf_sin(u), bf_cos(u), ellipt__i(1))
  } else {
    // A&S 16.12.2 (https://dlmf.nist.gov/22.7.E2):
    //
    //   sn(u|m) = (1+sqrt(mu))*sn(v|mu)/(1+sqrt(mu)*sn^2(v|mu)).
    //
    // A&S 16.12.3 (https://dlmf.nist.gov/22.7.E3) for cn:
    //
    //   cn(u|m) = cn(v|mu)*dn(v|mu)/(1+sqrt(mu)*sn^2(v|mu))
    //
    // A&S 16.12.4 (https://dlmf.nist.gov/22.7.E4) for dn:
    //
    //   dn(u|m) = (dn^2(v|mu) - (1-sqrt(mu)))/((1+sqrt(mu))-dn^2(v|mu))
    //
    // Using dn^2(v|mu) = 1-mu*sn^2(v|mu), we get
    //
    //   dn(u|m) = (1-p)/(1+p)
    //
    // where p = sqrt(mu)*sn^2(v|mu).
    let (v, mu, root_mu, root_mu1) = bf_descending_transform(u, m, root_m1)
    let (s, c, d) = bf_elliptic_sn_cn_dn_descending(v, mu, root_mu1)
    // A&S 16.12.2 to 16.12.4
    let p = bf_mul(bf_mul(root_mu, s), s)
    let den = bf_1_plus(p)
    (
      bf_div(bf_mul(bf_1_plus(root_mu), s), den),
      bf_div(bf_mul(c, d), den),
      // 1-p cancels when p is near 1, which happens when m is near 1 and
      // u is near an odd multiple of K(m), where sn(v|mu) is near 1.  Then
      // use 1-p = 1-sqrt(mu)*sn^2 = 1-sqrt(mu)*(1-cn^2) = (1-sqrt(mu)) +
      // sqrt(mu)*cn^2, where 1-sqrt(mu) = 2*sqrt(m1)/(1+sqrt(m1)).
      bf_div(
        if bf_lt(bf_mul(ellipt__i(2), bf_abs(p)), ellipt__i(1)) {
          bf_sub(ellipt__i(1), p)
        } else {
          bf_add(
            bf_div(
              bf_mul(ellipt__i(2), root_m1),
              bf_add(ellipt__i(1), root_m1),
            ),
            bf_mul(bf_mul(root_mu, c), c),
          )
        },
        den,
      ),
    )
  }
}

///|
fn bf_sn(u : Value, m : Value) -> Value raise {
  if bf_zerop(m) {
    // jacobi_sn(u,0) = sin(u).
    bf_sin(u)
  } else if bf_eq(m, ellipt__i(1)) {
    // jacobi_sn(u,1) = tanh(u).
    bf_tanh(u)
  } else if bf_realp(m) && bf_gt(m, ellipt__i(1)) {
    // A&S 16.11.1: sn(u|m) = sn(sqrt(m)*u|1/m)/sqrt(m)
    let root_m = bf_sqrt(m)
    bf_div(
      bf_elliptic_sn_descending(
        bf_mul(root_m, u),
        bf_inv(m),
        bf_sqrt(bf_div(bf_sub(m, ellipt__i(1)), m)),
      ),
      root_m,
    )
  } else if bf_realp(m) && bf_minusp(m) {
    // A&S 16.10.2 (https://dlmf.nist.gov/22.17.E6):
    //
    //   sn(u|m) = sn(v|mu)/(sqrt(1-m)*dn(v|mu)),
    //
    // where v = sqrt(1-m)*u and mu = -m/(1-m).  sqrt(1-mu) = 1/sqrt(1-m).
    let root = bf_sqrt(bf_sub(ellipt__i(1), m))
    let (s, _, d) = bf_elliptic_sn_cn_dn_descending(
      bf_mul(root, u),
      bf_div(bf_neg(m), bf_sub(ellipt__i(1), m)),
      bf_inv(root),
    )
    bf_div(s, bf_mul(root, d))
  } else {
    bf_elliptic_sn_descending(u, m, bf_sqrt(bf_sub(ellipt__i(1), m)))
  }
}

///|
fn bf_dn(u : Value, m : Value) -> Value raise {
  if bf_zerop(m) {
    // jacobi_dn(u,0) = 1.
    ellipt__i(1)
  } else if bf_eq(m, ellipt__i(1)) {
    // jacobi_dn(u,1) = sech(u).
    bf_inv(bf_cosh(u))
  } else if bf_realp(m) && bf_gt(m, ellipt__i(1)) {
    // A&S 16.11.4 (https://dlmf.nist.gov/22.17.E4):
    //
    //   dn(u|m) = cn(sqrt(m)*u|1/m)
    let (_, c, _) = bf_elliptic_sn_cn_dn_descending(
      bf_mul(bf_sqrt(m), u),
      bf_inv(m),
      bf_sqrt(bf_div(bf_sub(m, ellipt__i(1)), m)),
    )
    c
  } else if bf_realp(m) && bf_minusp(m) {
    // A&S 16.10.4 (https://dlmf.nist.gov/22.17.E8):
    //
    //   dn(u|m) = 1/dn(v|mu),
    //
    // where v = sqrt(1-m)*u and mu = -m/(1-m).  sqrt(1-mu) = 1/sqrt(1-m).
    let root = bf_sqrt(bf_sub(ellipt__i(1), m))
    bf_inv(
      bf_elliptic_sn_cn_dn_descending(
        bf_mul(root, u),
        bf_div(bf_neg(m), bf_sub(ellipt__i(1), m)),
        bf_inv(root),
      ).2,
    )
  } else if !(bf_realp(u) && bf_realp(m) && bf_lt(m, ellipt__q(8, 9))) {
    // dn is computed from one step of the descending transformation, A&S
    // 16.12.4 (https://dlmf.nist.gov/22.7.E4),
    //
    //   dn(u|m) = (1-p)/(1+p),  p = sqrt(mu)*sn(v|mu)^2,
    //
    // with v = u/(1+sqrt(mu)) and sqrt(mu) = (1-sqrt(1-m))/(1+sqrt(1-m)).
    // For real u and 0 <= m < 8/9, sqrt(mu) < 1/2, so 0 <= p < 1/2 and 1-p
    // cannot cancel; the branch below then needs only sn.  Otherwise 1-p
    // can cancel, for example when m is near 1 and u is near an odd
    // multiple of K(m).
    let (_, _, d) = bf_elliptic_sn_cn_dn_descending(
      u,
      m,
      bf_sqrt(bf_sub(ellipt__i(1), m)),
    )
    d
  } else {
    // A&S 16.12.4 (https://dlmf.nist.gov/22.7.E4), as above.  This is also
    // the Gauss transformation of
    // http://functions.wolfram.com/09.29.16.0013.01.
    let (v, mu, root_mu, root_mu1) = bf_descending_transform(
      u,
      m,
      bf_sqrt(bf_sub(ellipt__i(1), m)),
    )
    let s = bf_elliptic_sn_descending(v, mu, root_mu1)
    let p = bf_mul(bf_mul(root_mu, s), s)
    bf_div(bf_sub(ellipt__i(1), p), bf_add(ellipt__i(1), p))
  }
}

///|
fn bf_cn(u : Value, m : Value) -> Value raise {
  if bf_zerop(m) {
    // jacobi_cn(u,0) = cos(u).
    bf_cos(u)
  } else if bf_eq(m, ellipt__i(1)) {
    // jacobi_cn(u,1) = sech(u).
    bf_inv(bf_cosh(u))
  } else if bf_realp(m) && bf_gt(m, ellipt__i(1)) {
    // A&S 16.11.3 (https://dlmf.nist.gov/22.17.E3):
    //
    //   cn(u|m) = dn(sqrt(m)*u|1/m)
    let (_, _, d) = bf_elliptic_sn_cn_dn_descending(
      bf_mul(bf_sqrt(m), u),
      bf_inv(m),
      bf_sqrt(bf_div(bf_sub(m, ellipt__i(1)), m)),
    )
    d
  } else if bf_realp(m) && bf_minusp(m) {
    // A&S 16.10.3 (https://dlmf.nist.gov/22.17.E7):
    //
    //   cn(u|m) = cn(v|mu)/dn(v|mu),
    //
    // where v = sqrt(1-m)*u and mu = -m/(1-m).  sqrt(1-mu) = 1/sqrt(1-m).
    let root = bf_sqrt(bf_sub(ellipt__i(1), m))
    let (_, c, d) = bf_elliptic_sn_cn_dn_descending(
      bf_mul(root, u),
      bf_div(bf_neg(m), bf_sub(ellipt__i(1), m)),
      bf_inv(root),
    )
    bf_div(c, d)
  } else {
    let (_, c, _) = bf_elliptic_sn_cn_dn_descending(
      u,
      m,
      bf_sqrt(bf_sub(ellipt__i(1), m)),
    )
    c
  }
}

// Arithmetic-Geometric Mean algorithm for real or complex numbers.  See
// https://dlmf.nist.gov/22.20.ii.
//
// Do not use this for computing jacobi sn.  It loses some 7 digits of
// accuracy for sn(1+%i,0.7).
//
// Instead of allocating these arrays anew each time, we reuse them and
// allow them to grow as needed.

///|
let ellipt__agm_an : Value = make_array([100], fill=0)

///|
let ellipt__agm_bn : Value = make_array([100], fill=0)

///|
let ellipt__agm_cn : Value = make_array([100], fill=0)

///|
/// Arithmetic-Geometric Mean algorithm for real or complex a0, b0, c0.
/// Algorithm continues until |c[n]| <= tol.
fn bf_agm(
  a0 : Value,
  b0 : Value,
  c0 : Value,
  tol : Value,
) -> (Value, Value, Value, Value) raise {
  let an = ellipt__agm_an
  let bn = ellipt__agm_bn
  let cn = ellipt__agm_cn
  // DLMF (https://dlmf.nist.gov/22.20.ii) says for any real or complex a0
  // and b0, b0/a0 must not be real and negative.  Let's check that.
  let q = bf_div(b0, a0)
  if bf_eq(bf_imagpart(q), ellipt__i(0)) && bf_minusp(bf_realpart(q)) {
    raise LispError::SimpleError(
      format_to_string("Invalid arguments for AGM:  ~A ~A~%", [a0, b0]),
    )
  }
  // DLMF (https://dlmf.nist.gov/22.20.ii) says that |c[n]| <= C*2^(-2^n),
  // for some constant C.  Solve C*2^(-2^n) = tol to get n =
  // log(log(C/tol)/log(2))/log(2).  Arbitrarily assume C is one to get n
  // = log(-(log(tol)/log(2)))/log(2).  Thus, the approximate number of
  // term needed is n = 1.44*log(-(1.44*log(tol))).  Round to
  // 2*log(-log2(tol)).
  let nd = bf_max(
    bf_mul(
      ellipt__i(2),
      bf_ceiling(bf_log(bf_neg(bf_log(tol, b=ellipt__i(2))))).0,
    ),
    list1(ellipt__i(8)),
  )
  set_fill_pointer(an, 0)
  set_fill_pointer(bn, 0)
  set_fill_pointer(cn, 0)
  vector_push_extend(a0, an) |> ignore
  vector_push_extend(b0, bn) |> ignore
  vector_push_extend(c0, cn) |> ignore
  let mut k = 0
  while !(bf_le(bf_abs(aref1(cn, k)), tol) || bf_ge(ellipt__i(k), nd)) {
    vector_push_extend(
      bf_div(bf_add(aref1(an, k), aref1(bn, k)), ellipt__i(2)),
      an,
    )
    |> ignore
    // DLMF (https://dlmf.nist.gov/22.20.ii) has conditions on how to
    // choose the square root depending on the phase of a[n-1] and b[n-1].
    // We don't check for that here.
    vector_push_extend(bf_sqrt(bf_mul(aref1(an, k), aref1(bn, k))), bn)
    |> ignore
    vector_push_extend(
      bf_div(bf_sub(aref1(an, k), aref1(bn, k)), ellipt__i(2)),
      cn,
    )
    |> ignore
    k = k + 1
  }
  if bf_ge(ellipt__i(k), nd) {
    raise LispError::SimpleError("Failed to converge")
  }
  (ellipt__i(k), an, bn, cn)
}

///|
/// Evaluate the jacobi_am function from real u and m with |m| <= 1.  This
/// uses the AGM method until a tolerance of TOL is reached for the error.
fn bf_jacobi_am_agm(u : Value, m : Value, tol : Value) -> Value raise {
  let (n, an, _, cn) = bf_agm(
    ellipt__i(1),
    bf_sqrt(bf_sub(ellipt__i(1), m)),
    bf_sqrt(m),
    tol,
  )
  let ni = to_int(n)
  // See DLMF (https://dlmf.nist.gov/22.20.ii) for the algorithm.
  let mut phi = bf_mul(bf_mul(u, aref1(an, ni)), bf_expt(ellipt__i(2), n))
  let mut k = ni
  while k >= 1 {
    phi = bf_div(
      bf_add(
        phi,
        bf_asin(bf_mul(bf_div(aref1(cn, k), aref1(an, k)), bf_sin(phi))),
      ),
      ellipt__i(2),
    )
    k = k - 1
  }
  phi
}

///|
/// Compute Jacobi am for real or complex values of U and M.  The args must
/// be floats or bigfloat::bigfloats.  TOL is the tolerance used by the AGM
/// algorithm.  It is ignored if the AGM algorithm is not used.
fn bf_bf_jacobi_am(u : Value, m : Value, tol : Value) -> Value raise {
  if bf_realp(u) && bf_realp(m) && bf_le(bf_abs(m), ellipt__i(1)) {
    // The case of real u and m with |m| <= 1.  We can use AGM to compute
    // the result.
    bf_jacobi_am_agm(bf_to(u), bf_to(m), tol)
  } else {
    // Otherwise, use the formula am(u,m) = asin(jacobi_sn(u,m)).  (See
    // DLMF https://dlmf.nist.gov/22.16.E1).  This appears to be what
    // functions.wolfram.com is using in this case.
    bf_asin(bf_sn(bf_to(u), bf_to(m)))
  }
}

// Translation of Jim FitzSimons' bigfloat implementation of elliptic
// integrals from http://www.getnet.com/~cherry/elliptbf3.mac.
//
// The algorithms are based on B.C. Carlson's "Numerical Computation of
// Real or Complex Elliptic Integrals".  These are updated to the
// algorithms in Journal of Computational and Applied Mathematics 118
// (2000) 71-85 "Reduction Theorems for Elliptic Integrands with the Square
// Root of two quadritic factors"
//
// NOTE: Despite the names indicating these are for bigfloat numbers, the
// algorithms and routines are generic and will work with floats and
// bigfloats.

///|
fn bf_bferrtol(args : Value) -> Value raise {
  // Compute error tolerance as sqrt(2^(-fpprec)).  Not sure this is quite
  // right, but it makes the routines more accurate as fpprec increases.
  let l = mapcar(
    x => if rationalp(bf_realpart(x)) {
      Flo(double_float_epsilon)
    } else {
      bf_epsilon(x)
    },
    args,
  )
  let mut acc = car(l)
  for x in cdr(l).iter() {
    acc = bf_min(acc, list1(x))
  }
  bf_sqrt(acc)
}

// rc(x,y) = integrate(1/2*(t+x)^(-1/2)/(t+y), t, 0, inf)
//
// log(x)  = (x-1)*rc(((1+x)/2)^2, x), x > 0
// asin(x) = x * rc(1-x^2, 1), |x|<= 1
// acos(x) = sqrt(1-x^2)*rc(x^2,1), 0 <= x <=1
// atan(x) = x * rc(1,1+x^2)
// asinh(x) = x * rc(1+x^2,1)
// acosh(x) = sqrt(x^2-1) * rc(x^2,1), x >= 1
// atanh(x) = x * rc(1,1-x^2), |x|<=1

///|
fn bf_bf_rc(x : Value, y : Value) -> Value raise {
  let mut yn = y
  let mut xn : Value = Nil
  let mut z : Value = Nil
  let mut w : Value = Nil
  if bf_zerop(bf_imagpart(yn)) && bf_minusp(bf_realpart(yn)) {
    xn = bf_sub(x, y)
    yn = bf_neg(yn)
    z = yn
    w = bf_sqrt(bf_div(x, xn))
  } else {
    xn = x
    z = yn
    w = ellipt__i(1)
  }
  let a = bf_div(bf_add(bf_add(xn, yn), yn), ellipt__i(3))
  let epslon = bf_div(bf_abs(bf_sub(a, xn)), bf_bferrtol(list2(x, y)))
  let mut an = a
  let mut pwr4 = ellipt__i(1)
  while bf_gt(bf_mul(epslon, pwr4), bf_abs(an)) {
    pwr4 = bf_div(pwr4, ellipt__i(4))
    let lambda = bf_add(
      bf_mul(bf_mul(ellipt__i(2), bf_sqrt(xn)), bf_sqrt(yn)),
      yn,
    )
    an = bf_div(bf_add(an, lambda), ellipt__i(4))
    xn = bf_div(bf_add(xn, lambda), ellipt__i(4))
    yn = bf_div(bf_add(yn, lambda), ellipt__i(4))
  }
  // c2=3/10,c3=1/7,c4=3/8,c5=9/22,c6=159/208,c7=9/8
  let sn = bf_div(bf_mul(pwr4, bf_sub(z, a)), an)
  let s = bf_mul(
    bf_mul(sn, sn),
    bf_add(
      ellipt__q(3, 10),
      bf_mul(
        sn,
        bf_add(
          ellipt__q(1, 7),
          bf_mul(
            sn,
            bf_add(
              ellipt__q(3, 8),
              bf_mul(
                sn,
                bf_add(
                  ellipt__q(9, 22),
                  bf_mul(
                    sn,
                    bf_add(ellipt__q(159, 208), bf_mul(sn, ellipt__q(9, 8))),
                  ),
                ),
              ),
            ),
          ),
        ),
      ),
    ),
  )
  bf_div(bf_mul(w, bf_add(ellipt__i(1), s)), bf_sqrt(an))
}

///|
/// The common series in the deviations used by RD and RJ:
///
///   1 - 3/14*ee2 + 1/6*ee3 + 9/88*ee2^2 - 3/22*ee4 - 9/52*ee2*ee3
///   + 3/26*ee5 - 1/16*ee2^3 + 3/10*ee3^2 + 3/20*ee2*ee4
///   + 45/272*ee2^2*ee3 - 9/68*(ee2*ee5 + ee3*ee4)
fn ellipt__rd_series(
  ee2 : Value,
  ee3 : Value,
  ee4 : Value,
  ee5 : Value,
) -> Value raise {
  bf_addn([
    ellipt__i(1),
    bf_mul(ellipt__q(-3, 14), ee2),
    bf_mul(ellipt__q(1, 6), ee3),
    bf_muln([ellipt__q(9, 88), ee2, ee2]),
    bf_mul(ellipt__q(-3, 22), ee4),
    bf_muln([ellipt__q(-9, 52), ee2, ee3]),
    bf_mul(ellipt__q(3, 26), ee5),
    bf_muln([ellipt__q(-1, 16), ee2, ee2, ee2]),
    bf_muln([ellipt__q(3, 10), ee3, ee3]),
    bf_muln([ellipt__q(3, 20), ee2, ee4]),
    bf_muln([ellipt__q(45, 272), ee2, ee2, ee3]),
    bf_mul(ellipt__q(-9, 68), bf_add(bf_mul(ee2, ee5), bf_mul(ee3, ee4))),
  ])
}

// See https://dlmf.nist.gov/19.16.E5:
//
// rd(x,y,z) = integrate(3/2/sqrt(t+x)/sqrt(t+y)/sqrt(t+z)/(t+z), t, 0, inf)
//
// rd(1,1,1) = 1
// E(K) = rf(0, 1-K^2, 1) - (K^2/3)*rd(0,1-K^2,1)
//
// B = integrate(s^2/sqrt(1-s^4), s, 0 ,1)
//   = beta(3/4,1/2)/4
//   = sqrt(%pi)*gamma(3/4)/gamma(1/4)
//   = 1/3*rd(0,2,1)

///|
fn bf_bf_rd(x : Value, y : Value, z : Value) -> Value raise {
  let mut xn = x
  let mut yn = y
  let mut zn = z
  let a = bf_div(
    bf_add(bf_add(xn, yn), bf_mul(ellipt__i(3), zn)),
    ellipt__i(5),
  )
  let epslon = bf_div(
    bf_max(
      bf_abs(bf_sub(a, xn)),
      list2(bf_abs(bf_sub(a, yn)), bf_abs(bf_sub(a, zn))),
    ),
    bf_bferrtol(list3(x, y, z)),
  )
  let mut an = a
  let mut sigma = ellipt__i(0)
  let mut power4 = ellipt__i(1)
  while bf_gt(bf_mul(power4, epslon), bf_abs(an)) {
    let xnroot = bf_sqrt(xn)
    let ynroot = bf_sqrt(yn)
    let znroot = bf_sqrt(zn)
    let lam = bf_add(
      bf_add(bf_mul(xnroot, ynroot), bf_mul(xnroot, znroot)),
      bf_mul(ynroot, znroot),
    )
    sigma = bf_add(sigma, bf_div(power4, bf_mul(znroot, bf_add(zn, lam))))
    power4 = bf_mul(power4, ellipt__q(1, 4))
    xn = bf_mul(bf_add(xn, lam), ellipt__q(1, 4))
    yn = bf_mul(bf_add(yn, lam), ellipt__q(1, 4))
    zn = bf_mul(bf_add(zn, lam), ellipt__q(1, 4))
    an = bf_mul(bf_add(an, lam), ellipt__q(1, 4))
  }
  // c1=-3/14,c2=1/6,c3=9/88,c4=9/22,c5=-3/22,c6=-9/52,c7=3/26
  let xndev = bf_div(bf_mul(bf_sub(a, x), power4), an)
  let yndev = bf_div(bf_mul(bf_sub(a, y), power4), an)
  let zndev = bf_neg(bf_mul(bf_add(xndev, yndev), ellipt__q(1, 3)))
  let ee2 = bf_sub(
    bf_mul(xndev, yndev),
    bf_muln([ellipt__i(6), zndev, zndev]),
  )
  let ee3 = bf_mul(
    bf_sub(
      bf_muln([ellipt__i(3), xndev, yndev]),
      bf_muln([ellipt__i(8), zndev, zndev]),
    ),
    zndev,
  )
  let ee4 = bf_muln([
    ellipt__i(3),
    bf_sub(bf_mul(xndev, yndev), bf_mul(zndev, zndev)),
    zndev,
    zndev,
  ])
  let ee5 = bf_muln([xndev, yndev, zndev, zndev, zndev])
  let s = ellipt__rd_series(ee2, ee3, ee4, ee5)
  bf_add(
    bf_mul(ellipt__i(3), sigma),
    bf_div(bf_mul(power4, s), bf_expt(an, ellipt__q(3, 2))),
  )
}

// See https://dlmf.nist.gov/19.16.E1
//
// rf(x,y,z) = 1/2*integrate(1/(sqrt(t+x)*sqrt(t+y)*sqrt(t+z)), t, 0, inf);
//
// rf(1,1,1) = 1

///|
fn bf_bf_rf(x : Value, y : Value, z : Value) -> Value raise {
  let mut xn = x
  let mut yn = y
  let mut zn = z
  let a = bf_div(bf_add(bf_add(xn, yn), zn), ellipt__i(3))
  let epslon = bf_div(
    bf_max(
      bf_abs(bf_sub(a, xn)),
      list2(bf_abs(bf_sub(a, yn)), bf_abs(bf_sub(a, zn))),
    ),
    bf_bferrtol(list3(x, y, z)),
  )
  let mut an = a
  let mut power4 = ellipt__i(1)
  while bf_gt(bf_mul(power4, epslon), bf_abs(an)) {
    let xnroot = bf_sqrt(xn)
    let ynroot = bf_sqrt(yn)
    let znroot = bf_sqrt(zn)
    let lam = bf_add(
      bf_add(bf_mul(xnroot, ynroot), bf_mul(xnroot, znroot)),
      bf_mul(ynroot, znroot),
    )
    power4 = bf_mul(power4, ellipt__q(1, 4))
    xn = bf_mul(bf_add(xn, lam), ellipt__q(1, 4))
    yn = bf_mul(bf_add(yn, lam), ellipt__q(1, 4))
    zn = bf_mul(bf_add(zn, lam), ellipt__q(1, 4))
    an = bf_mul(bf_add(an, lam), ellipt__q(1, 4))
  }
  // c1=-3/14,c2=1/6,c3=9/88,c4=9/22,c5=-3/22,c6=-9/52,c7=3/26
  let xndev = bf_div(bf_mul(bf_sub(a, x), power4), an)
  let yndev = bf_div(bf_mul(bf_sub(a, y), power4), an)
  let zndev = bf_neg(bf_add(xndev, yndev))
  let ee2 = bf_sub(
    bf_mul(xndev, yndev),
    bf_muln([ellipt__i(6), zndev, zndev]),
  )
  let ee3 = bf_muln([xndev, yndev, zndev])
  let s = bf_addn([
    ellipt__i(1),
    bf_mul(ellipt__q(-1, 10), ee2),
    bf_mul(ellipt__q(1, 14), ee3),
    bf_muln([ellipt__q(1, 24), ee2, ee2]),
    bf_muln([ellipt__q(-3, 44), ee2, ee3]),
  ])
  bf_div(s, bf_sqrt(an))
}

///|
fn bf_bf_rj1(x : Value, y : Value, z : Value, p : Value) -> Value raise {
  let mut xn = x
  let mut yn = y
  let mut zn = z
  let mut pn = p
  let mut en = bf_muln([bf_sub(pn, xn), bf_sub(pn, yn), bf_sub(pn, zn)])
  let mut sigma = ellipt__i(0)
  let mut power4 = ellipt__i(1)
  let a = bf_div(bf_addn([xn, yn, zn, pn, pn]), ellipt__i(5))
  let epslon = bf_div(
    bf_max(
      bf_abs(bf_sub(a, xn)),
      list3(
        bf_abs(bf_sub(a, yn)),
        bf_abs(bf_sub(a, zn)),
        bf_abs(bf_sub(a, pn)),
      ),
    ),
    bf_bferrtol(list([x, y, z, p])),
  )
  let mut an = a
  while bf_gt(bf_mul(power4, epslon), bf_abs(an)) {
    let xnroot = bf_sqrt(xn)
    let ynroot = bf_sqrt(yn)
    let znroot = bf_sqrt(zn)
    let pnroot = bf_sqrt(pn)
    let lam = bf_add(
      bf_add(bf_mul(xnroot, ynroot), bf_mul(xnroot, znroot)),
      bf_mul(ynroot, znroot),
    )
    let dn = bf_muln([
      bf_add(pnroot, xnroot),
      bf_add(pnroot, ynroot),
      bf_add(pnroot, znroot),
    ])
    sigma = bf_add(
      sigma,
      bf_div(
        bf_mul(
          power4,
          bf_bf_rc(
            ellipt__i(1),
            bf_add(ellipt__i(1), bf_div(en, bf_mul(dn, dn))),
          ),
        ),
        dn,
      ),
    )
    power4 = bf_mul(power4, ellipt__q(1, 4))
    en = bf_div(en, ellipt__i(64))
    xn = bf_mul(bf_add(xn, lam), ellipt__q(1, 4))
    yn = bf_mul(bf_add(yn, lam), ellipt__q(1, 4))
    zn = bf_mul(bf_add(zn, lam), ellipt__q(1, 4))
    pn = bf_mul(bf_add(pn, lam), ellipt__q(1, 4))
    an = bf_mul(bf_add(an, lam), ellipt__q(1, 4))
  }
  let xndev = bf_div(bf_mul(bf_sub(a, x), power4), an)
  let yndev = bf_div(bf_mul(bf_sub(a, y), power4), an)
  let zndev = bf_div(bf_mul(bf_sub(a, z), power4), an)
  let pndev = bf_mul(Flo(-0.5), bf_addn([xndev, yndev, zndev]))
  let ee2 = bf_addn([
    bf_mul(xndev, yndev),
    bf_mul(xndev, zndev),
    bf_mul(yndev, zndev),
    bf_muln([ellipt__i(-3), pndev, pndev]),
  ])
  let ee3 = bf_addn([
    bf_muln([xndev, yndev, zndev]),
    bf_muln([ellipt__i(2), ee2, pndev]),
    bf_muln([ellipt__i(4), pndev, pndev, pndev]),
  ])
  let ee4 = bf_mul(
    bf_addn([
      bf_muln([ellipt__i(2), xndev, yndev, zndev]),
      bf_mul(ee2, pndev),
      bf_muln([ellipt__i(3), pndev, pndev, pndev]),
    ]),
    pndev,
  )
  let ee5 = bf_muln([xndev, yndev, zndev, pndev, pndev])
  let s = ellipt__rd_series(ee2, ee3, ee4, ee5)
  bf_add(
    bf_mul(ellipt__i(6), sigma),
    bf_div(bf_mul(power4, s), bf_mul(an, bf_sqrt(an))),
  )
}

///|
fn bf_bf_rj(x : Value, y : Value, z : Value, p : Value) -> Value raise {
  let xn = x
  let yn = y
  let zn = z
  let qn = bf_neg(p)
  if bf_zerop(bf_imagpart(xn)) &&
    bf_ge(bf_realpart(xn), ellipt__i(0)) &&
    bf_zerop(bf_imagpart(yn)) &&
    bf_ge(bf_realpart(yn), ellipt__i(0)) &&
    bf_zerop(bf_imagpart(zn)) &&
    bf_ge(bf_realpart(zn), ellipt__i(0)) &&
    bf_zerop(bf_imagpart(qn)) &&
    bf_gt(bf_realpart(qn), ellipt__i(0)) {
    let sorted = sort_list(list3(xn, yn, zn), (a, b) => bf_lt(a, b))
    let xn = first(sorted)
    let yn = second(sorted)
    let zn = third(sorted)
    let pn = bf_add(
      yn,
      bf_mul(bf_sub(zn, yn), bf_div(bf_sub(yn, xn), bf_add(yn, qn))),
    )
    let mut s = bf_sub(
      bf_mul(bf_sub(pn, yn), bf_bf_rj1(xn, yn, zn, pn)),
      bf_mul(ellipt__i(3), bf_bf_rf(xn, yn, zn)),
    )
    s = bf_add(
      s,
      bf_muln([
        ellipt__i(3),
        bf_sqrt(
          bf_div(
            bf_muln([xn, yn, zn]),
            bf_add(bf_mul(xn, zn), bf_mul(pn, qn)),
          ),
        ),
        bf_bf_rc(bf_add(bf_mul(xn, zn), bf_mul(pn, qn)), bf_mul(pn, qn)),
      ]),
    )
    bf_div(s, bf_add(yn, qn))
  } else {
    bf_bf_rj1(x, y, z, p)
  }
}

///|
fn bf_bf_rg(x : Value, y : Value, z : Value) -> Value raise {
  bf_mul(
    Flo(0.5),
    bf_addn([
      bf_mul(z, bf_bf_rf(x, y, z)),
      bf_muln([bf_sub(z, x), bf_sub(y, z), bf_bf_rd(x, y, z), ellipt__q(1, 3)]),
      bf_sqrt(bf_div(bf_mul(x, y), z)),
    ]),
  )
}

///|
/// elliptic_f(phi,m) = sin(phi)*rf(cos(phi)^2, 1-m*sin(phi)^2,1)
fn bf_bf_elliptic_f(phi : Value, m : Value) -> Value raise {
  fn base(phi : Value, m : Value) -> Value raise {
    if bf_eq(m, ellipt__i(1)) {
      // F(z|1) = log(tan(z/2+%pi/4))
      bf_log(
        bf_tan(
          bf_add(
            bf_div(phi, ellipt__i(2)),
            bf_div(bf_p_pi(phi), ellipt__i(4)),
          ),
        ),
      )
    } else {
      let s = bf_sin(phi)
      let c = bf_cos(phi)
      bf_mul(
        s,
        bf_bf_rf(
          bf_mul(c, c),
          bf_sub(ellipt__i(1), bf_muln([m, s, s])),
          ellipt__i(1),
        ),
      )
    }
  }

  // Handle periodicity (see elliptic-f)
  let bfpi = bf_p_pi(phi)
  let period = bf_round(bf_realpart(phi), divisor=bfpi).0
  bf_add(
    base(bf_sub(phi, bf_mul(bfpi, period)), m),
    if bf_zerop(period) {
      ellipt__i(0)
    } else {
      bf_muln([ellipt__i(2), period, bf_bf_elliptic_k(m)])
    },
  )
}

// elliptic_kc(k) = rf(0, 1-k^2,1)
//
// or
// elliptic_kc(m) = rf(0, 1-m,1)

///|
fn bf_bf_elliptic_k(m : Value) -> Value raise {
  if bf_eq(m, ellipt__i(0)) {
    if d_bfloatp(m).truthy() {
      d_bfloat(div(q_d__pctpi, int(2)))
    } else {
      bf_float(bf_div(Flo(@math.PI), ellipt__i(2)), Flo(1.0))
    }
  } else if bf_eq(m, ellipt__i(1)) {
    merr("elliptic_kc: elliptic_kc(1) is undefined.", [])
  } else {
    bf_bf_rf(ellipt__i(0), bf_sub(ellipt__i(1), m), ellipt__i(1))
  }
}

// elliptic_e(phi, k) = sin(phi)*rf(cos(phi)^2,1-k^2*sin(phi)^2,1)
//    - (k^2/3)*sin(phi)^3*rd(cos(phi)^2, 1-k^2*sin(phi)^2,1)
//
// or
// elliptic_e(phi, m) = sin(phi)*rf(cos(phi)^2,1-m*sin(phi)^2,1)
//    - (m/3)*sin(phi)^3*rd(cos(phi)^2, 1-m*sin(phi)^2,1)

///|
fn bf_bf_elliptic_e(phi : Value, m : Value) -> Value raise {
  fn base(phi : Value, m : Value) -> Value raise {
    let s = bf_sin(phi)
    let c = bf_cos(phi)
    let c2 = bf_mul(c, c)
    let s2 = bf_sub(ellipt__i(1), bf_muln([m, s, s]))
    bf_sub(
      bf_mul(s, bf_bf_rf(c2, s2, ellipt__i(1))),
      bf_muln([
        bf_div(m, ellipt__i(3)),
        bf_muln([s, s, s]),
        bf_bf_rd(c2, s2, ellipt__i(1)),
      ]),
    )
  }

  // Elliptic E is quasi-periodic wrt to phi:
  //
  // E(z|m) = E(z - %pi*round(Re(z)/%pi)|m) + 2*round(Re(z)/%pi)*E(m)
  let bfpi = bf_p_pi(phi)
  let period = bf_round(bf_realpart(phi), divisor=bfpi).0
  bf_add(
    base(bf_sub(phi, bf_mul(bfpi, period)), m),
    bf_muln([ellipt__i(2), period, bf_bf_elliptic_ec(m)]),
  )
}

// elliptic_ec(k) = rf(0,1-k^2,1) - (k^2/3)*rd(0,1-k^2,1);
//
// or
// elliptic_ec(m) = rf(0,1-m,1) - (m/3)*rd(0,1-m,1);

///|
fn bf_bf_elliptic_ec(m : Value) -> Value raise {
  if bf_eq(m, ellipt__i(0)) {
    if bf_is_bigfloat(m) {
      bf_bigfloat(d_bfloat(div(q_d__pctpi, int(2))))
    } else {
      bf_float(bf_div(Flo(@math.PI), ellipt__i(2)), Flo(1.0))
    }
  } else if bf_eq(m, ellipt__i(1)) {
    if bf_is_bigfloat(m) {
      bf_bigfloat(ellipt__i(1))
    } else {
      Flo(1.0)
    }
  } else {
    let m1 = bf_sub(ellipt__i(1), m)
    bf_sub(
      bf_bf_rf(ellipt__i(0), m1, ellipt__i(1)),
      bf_muln([m, ellipt__q(1, 3), bf_bf_rd(ellipt__i(0), m1, ellipt__i(1))]),
    )
  }
}

///|
fn bf_bf_elliptic_pi_complete(n : Value, m : Value) -> Value raise {
  bf_add(
    bf_bf_rf(ellipt__i(0), bf_sub(ellipt__i(1), m), ellipt__i(1)),
    bf_muln([
      ellipt__q(1, 3),
      n,
      bf_bf_rj(
        ellipt__i(0),
        bf_sub(ellipt__i(1), m),
        ellipt__i(1),
        bf_sub(ellipt__i(1), n),
      ),
    ]),
  )
}

///|
fn bf_bf_elliptic_pi(n : Value, phi : Value, m : Value) -> Value raise {
  // Note: Carlson's DRJ has n defined as the negative of the n given in
  // A&S.
  fn base(n : Value, phi : Value, m : Value) -> Value raise {
    let nn = bf_neg(n)
    let sin_phi = bf_sin(phi)
    let cos_phi = bf_cos(phi)
    let k = bf_sqrt(m)
    let k2sin = bf_mul(
      bf_sub(ellipt__i(1), bf_mul(k, sin_phi)),
      bf_add(ellipt__i(1), bf_mul(k, sin_phi)),
    )
    bf_sub(
      bf_mul(
        sin_phi,
        bf_bf_rf(bf_expt(cos_phi, ellipt__i(2)), k2sin, Flo(1.0)),
      ),
      bf_muln([
        bf_div(nn, ellipt__i(3)),
        bf_expt(sin_phi, ellipt__i(3)),
        bf_bf_rj(
          bf_expt(cos_phi, ellipt__i(2)),
          k2sin,
          Flo(1.0),
          bf_sub(ellipt__i(1), bf_mul(n, bf_expt(sin_phi, ellipt__i(2)))),
        ),
      ]),
    )
  }

  // FIXME: Reducing the arg by pi has significant round-off.  Consider
  // doing something better.
  let bf_pi = bf_p_pi(bf_realpart(phi))
  let cycles = bf_round(bf_realpart(phi), divisor=bf_pi).0
  let rem = bf_sub(phi, bf_mul(cycles, bf_pi))
  let complete = bf_bf_elliptic_pi_complete(n, m)
  bf_add(bf_muln([ellipt__i(2), cycles, complete]), base(n, rem, m))
}

///|
/// Compute inverse_jacobi_sn, for float or bigfloat args.
fn bf_bf_inverse_jacobi_sn(u : Value, m : Value) -> Value raise {
  bf_mul(
    u,
    bf_bf_rf(
      bf_sub(ellipt__i(1), bf_mul(u, u)),
      bf_sub(ellipt__i(1), bf_muln([m, u, u])),
      ellipt__i(1),
    ),
  )
}

///|
/// Compute inverse_jacobi_dn.  We use the following identity from
/// Gradshteyn & Ryzhik, 8.153.6
///
///   w = dn(z|m) = cn(sqrt(m)*z, 1/m)
///
/// Solve for z to get
///
///   z = inverse_jacobi_dn(w,m)
///     = 1/sqrt(m) * inverse_jacobi_cn(w, 1/m)
fn bf_bf_inverse_jacobi_dn(w : Value, m : Value) -> Value raise {
  if bf_eq(w, ellipt__i(1)) {
    bf_float(ellipt__i(0), w)
  } else if bf_eq(m, ellipt__i(1)) {
    // jacobi_dn(x,1) = sech(x) so the inverse is asech(x)
    take(list1(q_p_asech), [maxima_to(w)])
  } else {
    // We should do something better to make sure that things that should
    // be real are real.
    bf_div(
      bf_to(
        take(list1(q_p_inverse_jacobi_cn), [maxima_to(w), maxima_to(bf_inv(m))]),
      ),
      bf_sqrt(m),
    )
  }
}
