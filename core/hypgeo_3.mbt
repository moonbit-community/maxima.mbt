// Port of src/hypgeo.lisp (part 3): the remaining algorithms of Algorithm 2,
// the dispatch functions that change the representation of special
// functions, the experts on Laplace transforms, the transformation to
// hypergeometric functions (Algorithm 3) and the special handling of
// Bessel Y for an integer order (Algorithm 4).

// Algorithm 2.1: Laplace transform of c*t^u
//
// Table of Integral Transforms, p. 137, formula 1:
//
// t^u
//   -> gamma(u+1)*p^(-u-1)
//
// Re(u) > -1

///|
fn lt_arbpow(expr : Value, pow : Value) -> Value raise {
  if eq(expr, hypgeo__var()) || equal(pow, int(0)) {
    f1p137test(pow)
  } else {
    hypgeo__flag(q_lt_arbow_failed)
  }
}

///|
/// Check if conditions for f1p137 hold
fn f1p137test(pow : Value) -> Value raise {
  if eq(d_asksign(d_realpart(add2(pow, int(1)))), q_d_pos) {
    f1p137(pow)
  } else {
    hypgeo__flag(q_fail_in_arbpow)
  }
}

///|
fn f1p137(pow : Value) -> Value raise {
  mul2(
    hypgeo__take(q_p_gamma, [add2(pow, int(1))]),
    power(hypgeo__par(), sub(mul2(int(-1), pow), int(1))),
  )
}

// Algorithm 2.2: Laplace transform of c*t^v*(1+t)^w

///|
fn lt_arbpow2(
  c : Value,
  a : Value,
  b : Value,
  pow1 : Value,
  pow2 : Value,
) -> Value raise {
  if eq(d_asksign(add2(pow1, int(1))), q_d_pos) {
    let par = hypgeo__par()
    if equal(pow1, int(0)) {
      // The Laplace transform is an Incomplete Gamma function.
      muln_([
        c,
        power(a, add2(pow2, int(1))),
        inv(b),
        power(mul3(par, a, inv(b)), mul2(int(-1), add2(pow2, int(1)))),
        power(q_d__pcte, mul3(par, a, inv(b))),
        hypgeo__take(q_p_gamma_incomplete, [
          add2(pow2, int(1)),
          mul3(par, a, inv(b)),
        ]),
      ])
    } else if !maxima_integerp(addn_([pow1, pow2, int(2)])).truthy() {
      // The general result is a Hypergeometric U function U(a,b,z) which can
      // be represented by two Hypergeometic 1F1 functions for the special
      // case that the index b is not an integer value.
      add2(
        muln_([
          c,
          power(a, addn_([pow1, pow2, int(1)])),
          inv(power(b, add2(pow1, int(1)))),
          hypgeo__take(q_p_gamma, [addn_([pow1, pow2, int(1)])]),
          power(mul3(par, a, inv(b)), mul2(int(-1), addn_([pow1, pow2, int(1)]))),
          hgfsimp_exec(
            list1(mul2(int(-1), pow2)),
            list1(mul2(int(-1), add2(pow1, pow2))),
            mul3(par, a, inv(b)),
          ),
        ]),
        muln_([
          c,
          power(a, addn_([pow1, pow2, int(1)])),
          inv(power(b, add2(pow1, int(1)))),
          hypgeo__take(q_p_gamma, [add2(pow1, int(1))]),
          hypgeo__take(q_p_gamma, [mul2(int(-1), addn_([pow1, pow2, int(1)]))]),
          inv(hypgeo__take(q_p_gamma, [mul2(int(-1), pow2)])),
          hgfsimp_exec(
            list1(add2(pow1, int(1))),
            list1(addn_([pow1, pow2, int(2)])),
            mul3(par, a, inv(b)),
          ),
        ]),
      )
    } else {
      // The most general case is a result with the Hypergeometric U function.
      muln_([
        c,
        power(a, addn_([pow1, pow2, int(1)])),
        inv(power(b, add2(pow1, int(1)))),
        hypgeo__take(q_p_gamma, [add2(pow1, int(1))]),
        hypgeo__take(q_d_hypergeometric_u, [
          add2(pow1, int(1)),
          addn_([pow1, pow2, int(2)]),
          mul3(par, a, inv(b)),
        ]),
      ])
    }
  } else {
    hypgeo__flag(q_lt_arbpow2_failed)
  }
}

// Algorithm 2.3: Laplace transform of the Logarithmic function
//
//    c*t^(v-1)*log(a*t)
//       -> c*gamma(v)*s^(-v)*(psi[0](v)-log(s/a))
//
// This is the formula for an expression with log(t) scaled like 1/a*F(s/a).

///|
fn lt_log(rest_ : Value, arg : Value) -> Value raise {
  let hv = hypgeo__var()
  let par = hypgeo__par()
  let l = m2_c_start_hatv(rest_, hv)
  let c = if l.truthy() { cdras(q_c, l) } else { Nil }
  let v = if l.truthy() { add2(cdras(q_v, l), int(1)) } else { Nil } // because v -> v-1
  // c*t^(v-1)*log(a*t) -> c*gamma(v)*s^(-v)*(psi[0](v) - log(s/a))
  if l.truthy() && eq(d_asksign(v), q_d_pos) {
    let l1 = m2_a_start(arg, hv)
    if l1.truthy() {
      let a = cdras(q_a, l1)
      let r = muln_([
        c,
        hypgeo__take(q_p_gamma, [v]),
        inv(power(par, v)),
        sub(
          hypgeo__take(q_mqapply, [list2(list2(q_d_psi, q_array), int(0)), v]),
          hypgeo__take(q_p_log, [div(par, a)]),
        ),
      ])
      if r.truthy() {
        return r
      }
    }
  }
  // c*log(a*t+b) with a, b > 0
  // -> c*(log(b) + %e^p*E1(p))/s with p = s*b/a
  let l2 = m2_atb(arg, hv)
  if l2.truthy() && freeof(hv, rest_).truthy() {
    let a = cdras(q_a, l2)
    let b = cdras(q_b, l2)
    if lt_pos_p(a).truthy() && lt_pos_p(b).truthy() {
      let p = div(mul2(par, b), a)
      let r = mul3(
        rest_,
        inv(par),
        add2(
          hypgeo__take(q_p_log, [b]),
          mul2(power(q_d__pcte, p), hypgeo__take(q_p_expintegral_e1, [p])),
        ),
      )
      if r.truthy() {
        return r
      }
    }
  }
  // c*log(b-a*t) with a, b > 0, imaginary part %pi for t > b/a
  // -> c*(log(b) + %e^(-p)*(%i*%pi - Ei(p)))/s with p = s*b/a
  let l2 = m2_atb(arg, hv)
  if l2.truthy() && freeof(hv, rest_).truthy() {
    let a = mul2(int(-1), cdras(q_a, l2))
    let b = cdras(q_b, l2)
    if lt_pos_p(a).truthy() && lt_pos_p(b).truthy() {
      let p = div(mul2(par, b), a)
      let r = mul3(
        rest_,
        inv(par),
        add2(
          hypgeo__take(q_p_log, [b]),
          mul2(
            power(q_d__pcte, mul2(int(-1), p)),
            sub(
              mul2(q_d__pcti, q_d__pctpi),
              hypgeo__take(q_p_expintegral_ei, [p]),
            ),
          ),
        ),
      )
      if r.truthy() {
        return r
      }
    }
  }
  hypgeo__flag(q_lt_log_failed)
}

// Algorithm 2.4: Laplace transform of the Whittaker function
//
// Test for Whittaker W function.  Simplify this if possible, or
// convert to Whittaker M function.
//
// We have r * %w[i1,i2](a)
//
// Formula 16, p. 217
//
// t^(v-1)*%w[k,u](a*t)
//   -> gamma(u+v+1/2)*gamma(v-u+1/2)*a^(u+1/2)/
//          (gamma(v-k+1)*(p+a/2)^(u+v+1/2)
//        *2f1(u+v+1/2,u-k+1/2;v-k+1;(p-a/2)/(p+a/2))
//
// For Re(v +/- mu) > -1/2

///|
fn whittest(r : Value, a : Value, i1 : Value, i2 : Value) -> Value raise {
  let f = f16p217test(r, a, i1, i2)
  if f.truthy() {
    return f
  }
  let n = sub(sub(hypgeo__r(1, 2), i2), i1)
  let c1 = maxima_integerp(n).truthy() &&
    member(d_sign(n), list([q_d_zero, q_d_neg, q_d_nz])).truthy()
  if !c1 {
    let m = sub(add2(hypgeo__r(1, 2), i2), i1)
    let c2 = maxima_integerp(m).truthy() &&
      member(d_sign(m), list([q_d_zero, q_d_neg, q_d_nz])).truthy()
    if !c2 {
      // 1/2-u-k and 1/2+u-k are not zero or a negative integer
      // Transform to Whittaker M and try again.
      return distrexecinit(d_expand(mul2(init_(r), wtm(a, i1, i2))))
    }
  }
  // Both conditions fails, return a noun form.
  hypgeo__flag(q_whittest_failed)
}

///|
fn f16p217test(r : Value, a : Value, i1 : Value, i2 : Value) -> Value raise {
  // We have r*%w[i1,i2](a)
  let l = m2_c_start_hatv(r, hypgeo__var())
  // Make sure r is of the form c*t^v
  if l.truthy() {
    let v = add2(cdras(q_v, l), int(1))
    let c = cdras(q_c, l)
    let r12 = hypgeo__r(1, 2)
    // Check that v + i2 + 1/2 > 0 and v - i2 + 1/2 > 0.
    if eq(d_asksign(add2(add2(v, i2), r12)), q_d_pos) &&
      eq(d_asksign(add2(sub(v, i2), r12)), q_d_pos) {
      // Ok, we satisfy the conditions.  Now extract the arg.
      // The transformation is only valid for an argument a*t.
      let l = m2_a_start(a, hypgeo__var())
      if l.truthy() {
        let a = cdras(q_a, l)
        let par = hypgeo__par()
        // We're ready now to compute the transform.
        return muln_([
          c,
          power(a, add2(i2, r12)),
          hypgeo__take(q_p_gamma, [add2(add2(v, i2), r12)]),
          hypgeo__take(q_p_gamma, [add2(sub(v, i2), r12)]),
          inv(
            mul2(
              hypgeo__take(q_p_gamma, [add2(sub(v, i1), int(1))]),
              power(add2(par, div(a, int(2))), add2(add2(i2, v), r12)),
            ),
          ),
          hgfsimp_exec(
            list2(addn_([i2, v, r12]), add2(sub(i2, i1), r12)),
            list1(add2(sub(v, i1), int(1))),
            div(sub(par, div(a, int(2))), add2(par, div(a, int(2)))),
          ),
        ])
      }
    }
  }
  Nil
}

// Algorithm 2.5: Laplace transform of bessel_k(0,a*t)
//
//   bessel_k(0,a*t) --> acosh(s/a)/sqrt(s^2-a^2)

///|
fn lt_bessel_k0(rest_ : Value, arg : Value) -> Value raise {
  let l = m2_c_start_hatv(rest_, hypgeo__var())
  let c = cdras(q_c, l)
  let v = cdras(q_v, l)
  let l = m2_a_start(arg, hypgeo__var())
  let a = cdras(q_a, l)
  if l.truthy() && zerop1(v).truthy() {
    let par = hypgeo__par()
    mul3(
      c,
      hypgeo__take(q_p_acosh, [div(par, a)]),
      inv(power(sub(mul2(par, par), mul2(a, a)), hypgeo__r(1, 2))),
    )
  } else {
    hypgeo__flag(q_lt_bessel_k_failed)
  }
}

// ---------------------------------------------------------------------------
// DISPATCH FUNCTIONS TO CHANGE THE REPRESENTATION OF SPECIAL FUNCTIONS

///|
/// Is X a list with header operator rat?
fn hypgeo__ratp(x : Value) -> Bool {
  listp(x) && eq(caar(x), q_rat)
}

///|
/// Laplace transform of a product of Bessel functions.  A1, A2 are
/// the args of the two functions. I1, I2 are the indices of each
/// function.  I11, I21 are secondary indices of each function, if any.
/// FLG is a symbol indicating how we should handle the special
/// functions (and also indicates what the special functions are.)
///
/// I11 and I21 are for the Hankel functions.
fn fractest(
  r : Value,
  a1 : Value,
  a2 : Value,
  i1 : Value,
  i11 : Value,
  i2 : Value,
  i21 : Value,
  flg : Value,
) -> Value raise {
  if (hypgeo__ratp(i1) && hypgeo__ratp(i2)) || eq(flg, q_n2htjory) {
    // We have to Bessel or Hankel functions. Both indizes have to be
    // rational numbers or we have two Hankel functions.
    sendexec(
      r,
      if eq(flg, q_n2ytj) {
        mul2(ytj(i1, a1), ytj(i2, a2))
      } else if eq(flg, q_n2htjory) {
        mul2(htjory(i1, i11, a1), htjory(i2, i21, a2))
      } else if eq(flg, q_ktiytj) {
        mul2(kti(i1, a1), ytj(i2, a2))
      } else if eq(flg, q_n2kti) {
        mul2(kti(i1, a1), kti(i2, a2))
      } else {
        Nil
      },
    )
  } else {
    hypgeo__flag(q_product_of_y_with_nofract_indices)
  }
}

///|
/// Laplace transform of a product of Bessel functions.  A1, A2 are
/// the args of the two functions. I1, I2 are the indices of each
/// function.  I is a secondary index to one function, if any.
/// FLG is a symbol indicating how we should handle the special
/// functions (and also indicates what the special functions are.)
///
/// I is for the kind of Hankel function.
fn fractest1(
  r : Value,
  a1 : Value,
  a2 : Value,
  i1 : Value,
  i2 : Value,
  i : Value,
  flg : Value,
) -> Value raise {
  if hypgeo__ratp(i2) || eq(flg, q_besshtjory) {
    // We have two Bessel or Hankel functions. The second index has to
    // be a rational number or one of the functions is a Hankel function
    // and the second function is Bessel J or Bessel I
    sendexec(
      r,
      if eq(flg, q_bessytj) {
        mul2(hypgeo__take(q_p_bessel_j, [i1, a1]), ytj(i2, a2))
      } else if eq(flg, q_besshtjory) {
        mul2(hypgeo__take(q_p_bessel_j, [i1, a1]), htjory(i2, i, a2))
      } else if eq(flg, q_htjoryytj) {
        mul2(htjory(i1, i, a1), ytj(i2, a2))
      } else if eq(flg, q_besskti) {
        mul2(hypgeo__take(q_p_bessel_j, [i1, a1]), kti(i2, a2))
      } else if eq(flg, q_htjorykti) {
        mul2(htjory(i1, i, a1), kti(i2, a2))
      } else {
        Nil
      },
    )
  } else {
    hypgeo__flag(q_product_of_i_y_of_nofract_index)
  }
}

///|
/// Laplace transform of a single special function.  A1 is the arg of
/// the special function. I1, I11 are the indices of the function.  FLG
/// is a symbol indicating how we should handle the special functions
/// (and also indicates what the special functions are.)
///
/// I11 is the kind of Hankel function
fn fractest2(
  r : Value,
  a1 : Value,
  i1 : Value,
  i11 : Value,
  flg : Value,
) -> Value raise {
  if hypgeo__ratp(i1) ||
    eq(flg, q_d) ||
    eq(flg, q_kbateman) ||
    eq(flg, q_gamma_incomplete) ||
    eq(flg, q_htjory) ||
    eq(flg, q_erfc) ||
    eq(flg, q_slommel) ||
    eq(flg, q_ytj) {
    // The index is a rational number or flg has the value of one of the
    // above special functions.
    sendexec(
      r,
      if eq(flg, q_ytj) {
        ytj(i1, a1)
      } else if eq(flg, q_htjory) {
        htjory(i1, i11, a1)
      } else if eq(flg, q_d) {
        dtw(i1, a1)
      } else if eq(flg, q_kbateman) {
        kbatemantw(i1, a1)
      } else if eq(flg, q_gamma_incomplete) {
        gamma_incomplete_to_gamma_incomplete_lower(a1, i1)
      } else if eq(flg, q_kti) {
        kti(i1, a1)
      } else if eq(flg, q_erfc) {
        erfctd(a1)
      } else if eq(flg, q_slommel) {
        slommeltjandy(i1, i11, a1)
      } else {
        Nil
      },
    )
  } else {
    hypgeo__flag(q_y_of_nofract_index)
  }
}

///|
fn integertest(
  r : Value,
  arg : Value,
  i1 : Value,
  i2 : Value,
  flg : Value,
) -> Value raise {
  if maxima_integerp(i1).truthy() {
    dispatchpoltrans(r, arg, i1, i2, flg)
  } else {
    hypgeo__flag(q_index_should_be_an_integer_in_polys)
  }
}

///|
fn dispatchpoltrans(
  r : Value,
  x : Value,
  i1 : Value,
  i2 : Value,
  flg : Value,
) -> Value raise {
  sendexec(
    r,
    if eq(flg, q_l) {
      ltw(x, i1, i2)
    } else if eq(flg, q_he) {
      hetd(x, i1)
    } else if eq(flg, q_c) {
      ctpjac(x, i1, i2)
    } else if eq(flg, t) {
      ttpjac(x, i1)
    } else if eq(flg, q_u) {
      utpjac(x, i1)
    } else {
      Nil
    },
  )
}

///|
/// (-1)^n*n!*laguerre(n,a,x) = U(-n,a+1,x)
///
/// W[k,u](z) = exp(-z/2)*z^(u+1/2)*U(1/2+u-k,1+2*u,z)
///
/// So
///
/// laguerre(n,a,x) = (-1)^n*U(-n,a+1,x)/n!
///
/// U(-n,a+1,x) = exp(z/2)*z^(-a/2-1/2)*W[1/2+a/2+n,a/2](z)
///
/// Finally,
///
/// laguerre(n,a,x) = (-1)^n/n!*exp(z/2)*z^(-a/2-1/2)*M[1/2+a/2+n,a/2](z)
fn ltw(x : Value, n : Value, a : Value) -> Value raise {
  let diva2 = div(a, int(2))
  muln_([
    hypgeo__take(q_p_gamma, [addn_([n, a, int(1)])]),
    inv(hypgeo__take(q_p_gamma, [add2(a, int(1))])),
    inv(hypgeo__take(q_p_gamma, [add2(n, int(1))])),
    power(x, sub(hypgeo__r(-1, 2), diva2)),
    power(q_d__pcte, div(x, int(2))),
    list3(
      list2(q_mqapply, q_simp),
      list3(
        list3(q_d__pctm, q_simp, q_array),
        addn_([hypgeo__r(1, 2), diva2, n]),
        diva2,
      ),
      x,
    ),
  ])
}

///|
/// Hermite He function as a parabolic cylinder function
///
/// D[n](z) = (-1)^n*exp(z^2/4)*diff(exp(-z^2/2),z,n);
/// He[n](x) = (-1)^n*exp(x^2/2)*diff(exp(-x^2/2),x,n)
fn hetd(x : Value, n : Value) -> Value raise {
  mul2(
    power(q_d__pcte, mul3(x, x, hypgeo__r(1, 4))),
    // At this time the Parabolic Cylinder D function is not implemented
    // as a simplifying function. We call nevertheless the simplifier.
    hypgeo__take(q_d_parabolic_cylinder_d, [n, x]),
  )
}

///|
/// Transform Gegenbauer function to Jacobi P function
/// ultraspherical(n,v,x) = gamma(2*v+n)*gamma(v+1/2)/gamma(2*v)/gamma(v+n+1/2)
///                          *jacobi_p(n,v-1/2,v-1/2,x)
fn ctpjac(x : Value, n : Value, v : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  muln_([
    hypgeo__take(q_p_gamma, [addn_([v, v, n])]),
    inv(hypgeo__take(q_p_gamma, [add2(v, v)])),
    hypgeo__take(q_p_gamma, [add2(inv2, v)]),
    inv(hypgeo__take(q_p_gamma, [addn_([v, inv2, n])])),
    pjac(x, n, sub(v, inv2), sub(v, inv2)),
  ])
}

///|
/// Transform Chebyshev T function to Jacobi P function
/// chebyshev_t(n,x) = gamma(n+1)*sqrt(%pi)/gamma(n+1/2)*jacobi_p(n,-1/2,-1/2,x)
fn ttpjac(x : Value, n : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  muln_([
    hypgeo__take(q_p_gamma, [n, int(1)]),
    power(q_d__pctpi, inv2), // gamma(1/2)
    inv(hypgeo__take(q_p_gamma, [add2(inv2, n)])),
    pjac(x, n, mul2(int(-1), inv2), mul2(int(-1), inv2)),
  ])
}

///|
/// Transform Chebyshev U function to Jacobi P function
/// chebyshev_u(n,x) = gamma(n+2)*sqrt(%pi)/2/gamma(3/2+n)*jacobi_p(n,1/2,1/2,x)
fn utpjac(x : Value, n : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  muln_([
    hypgeo__take(q_p_gamma, [add2(n, int(2))]),
    inv2,
    power(q_d__pctpi, inv2), // gamma(1/2)
    inv(hypgeo__take(q_p_gamma, [addn_([inv2, n, int(1)])])),
    pjac(x, n, inv2, inv2),
  ])
}

///|
fn pjactest(
  rest_ : Value,
  arg : Value,
  index1 : Value,
  index2 : Value,
  index3 : Value,
) -> Value raise {
  if maxima_integerp(index1).truthy() {
    lt_ltp(q_onepjac, rest_, arg, list3(index1, index2, index3))
  } else {
    hypgeo__flag(q_ind_should_be_an_integer_in_polys)
  }
}

///|
/// Laplace transform of a single Bessel Y function.
///
/// REST is the multiplier, ARG1 is the arg, and INDEX1 is the order of
/// the Bessel Y function.
fn lt1yref(rest_ : Value, arg1 : Value, index1 : Value) -> Value raise {
  // If the index is an integer, use LTY.  Otherwise, convert Bessel
  // Y to Bessel J and compute the transform of that.  We do this
  // because converting Y to J for an integer index doesn't work so
  // well without taking limits.
  if maxima_integerp(index1).truthy() {
    lty(rest_, arg1, index1)
  } else {
    fractest2(rest_, arg1, index1, Nil, q_ytj)
  }
}

// ---------------------------------------------------------------------------
// TRANSFORMATIONS TO CHANGE THE REPRESENTATION OF SPECIAL FUNCTIONS

///|
/// erfc in terms of D, parabolic cylinder function
///
/// erfc(x) = %pi^(-1/2)*2^(1/4)*exp(-x^2/2)*D[-1](x*sqrt(2))
fn erfctd(x : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  muln_([
    power(int(2), inv2), // Should this be 2^(1/4)?
    inv(power(q_d__pctpi, inv2)),
    power(q_d__pcte, muln_([int(-1), inv2, x, x])),
    hypgeo__take(q_d_parabolic_cylinder_d, [
      int(-1),
      mul2(power(int(2), inv2), x),
    ]),
  ])
}

///|
/// Lommel S function in terms of Bessel J and Bessel Y.
/// Luke gives
///
/// S[u,v](z) = s[u,v](z) + {2^(u-1)*gamma((u-v+1)/2)*gamma((u+v+1)/2)}
///                 * {sin[(u-v)*%pi/2]*bessel_j(v,z)
///                     - cos[(u-v)*%pi/2]*bessel_y(v,z)
fn slommeltjandy(m : Value, n : Value, z : Value) -> Value raise {
  let arg = mul3(hypgeo__r(1, 2), q_d__pctpi, sub(m, n))
  add2(
    littleslommel(m, n, z),
    muln_([
      power(int(2), sub(m, int(1))),
      hypgeo__take(q_p_gamma, [div(sub(add2(m, int(1)), n), int(2))]),
      hypgeo__take(q_p_gamma, [div(addn_([m, n, int(1)]), int(2))]),
      sub(
        mul2(hypgeo__take(q_p_sin, [arg]), hypgeo__take(q_p_bessel_j, [n, z])),
        mul2(hypgeo__take(q_p_cos, [arg]), hypgeo__take(q_p_bessel_y, [n, z])),
      ),
    ]),
  )
}

///|
/// Whittaker W function in terms of Whittaker M function
///
/// A&S 13.1.34
///
/// W[k,u](z) = gamma(-2*u)/gamma(1/2-u-k)*M[k,u](z)
///              + gamma(2*u)/gamma(1/2+u-k)*M[k,-u](z)
fn wtm(a : Value, i1 : Value, i2 : Value) -> Value raise {
  add2(
    mul3(
      hypgeo__take(q_p_gamma, [mul2(int(-2), i2)]),
      mwhit(a, i1, i2),
      inv(hypgeo__take(q_p_gamma, [sub(sub(hypgeo__r(1, 2), i2), i1)])),
    ),
    mul3(
      hypgeo__take(q_p_gamma, [add2(i2, i2)]),
      mwhit(a, i1, mul2(int(-1), i2)),
      inv(hypgeo__take(q_p_gamma, [sub(add2(hypgeo__r(1, 2), i2), i1)])),
    ),
  )
}

///|
/// Incomplete gamma function in terms of Whittaker W function
///
/// gamma_h_incomplete(a,x) = x^((a-1)/2)*exp(-x/2)*W[(a-1)/2,a/2](x)
fn gammaincompletetw(a : Value, x : Value) -> Value raise {
  mul3(
    power(x, div(sub(a, int(1)), int(2))),
    power(q_d__pcte, div(x, int(-2))),
    wwhit(x, div(sub(a, int(1)), int(2)), div(a, int(2))),
  )
}

///|
/// Incomplete Gamma function in terms of lower incomplete Gamma function
///
/// Only for a=0 we use the general representation as a Whittaker W function:
///
///   gamma_h_incomplete(a,x) = x^((a-1)/2)*exp(-x/2)*W[(a-1)/2,a/2](x)
///
/// In all other cases we transform to a lower incomplete Gamma function:
///
///   gamma_h_incomplete(a,x) = gamma(a)- gamma_incomplete_lower(a,x)
fn gamma_incomplete_to_gamma_incomplete_lower(
  a : Value,
  x : Value,
) -> Value raise {
  if eq(d_sign(a), q_d_zero) || (integerp(a) && minusp(a)) {
    // The representation as a Whittaker W function for a=0 or a negative
    // integer (The gamma function is not defined for this case.)
    mul3(
      power(x, div(sub(a, int(1)), int(2))),
      power(q_d__pcte, div(x, int(-2))),
      wwhit(x, div(sub(a, int(1)), int(2)), div(a, int(2))),
    )
  } else {
    // In all other cases the representation as a lower incomplete Gamma
    // function
    sub(
      hypgeo__take(q_p_gamma, [a]),
      mk_simp(q_p_gamma_incomplete_lower, [a, x]),
    )
  }
}

///|
/// Bessel Y in terms of Bessel J
///
/// A&S 9.1.2:
///
/// bessel_y(v,z) = bessel_j(v,z)*cot(v*%pi)-bessel_j(-v,z)/sin(v*%pi)
fn ytj(i : Value, a : Value) -> Value raise {
  sub(
    mul2(
      hypgeo__take(q_p_bessel_j, [i, a]),
      hypgeo__take(q_p_cot, [mul2(i, q_d__pctpi)]),
    ),
    mul2(
      hypgeo__take(q_p_bessel_j, [mul2(int(-1), i), a]),
      inv(hypgeo__take(q_p_sin, [mul2(i, q_d__pctpi)])),
    ),
  )
}

///|
/// Parabolic cylinder function in terms of Whittaker W function.
///
/// D[v](z) = 2^(v/2+1/4)*z^(-1/2)*W[v/2+1/4,1/4](z^2/2)
fn dtw(i : Value, a : Value) -> Value raise {
  mul3(
    power(int(2), add2(div(i, int(2)), hypgeo__r(1, 4))),
    power(a, hypgeo__r(-1, 2)),
    wwhit(
      mul3(a, a, hypgeo__r(1, 2)),
      add2(div(i, int(2)), hypgeo__r(1, 4)),
      hypgeo__r(1, 4),
    ),
  )
}

///|
/// Bateman's function in terms of Whittaker W function
///
/// k[2*v](z) = 1/gamma(v+1)*W[v,1/2](2*z)
fn kbatemantw(v : Value, a : Value) -> Value raise {
  div(
    wwhit(add2(a, a), div(v, int(2)), hypgeo__r(1, 2)),
    hypgeo__take(q_p_gamma, [add2(div(v, int(2)), int(1))]),
  )
}

///|
/// Bessel K in terms of Bessel I
///
/// A&S 9.6.2
///
/// bessel_k(v,z) = %pi/2*(bessel_i(-v,z)-bessel_i(v,z))/sin(v*%pi)
fn kti(i : Value, a : Value) -> Value raise {
  muln_([
    q_d__pctpi,
    hypgeo__r(1, 2),
    inv(hypgeo__take(q_p_sin, [mul2(i, q_d__pctpi)])),
    sub(
      hypgeo__take(q_p_bessel_i, [mul2(int(-1), i), a]),
      hypgeo__take(q_p_bessel_i, [i, a]),
    ),
  ])
}

///|
/// Express Hankel function in terms of Bessel J or Y function.
///
/// A&S 9.1.3
///
/// H[v,1](z) = %i*csc(v*%pi)*(exp(-v*%pi*%i)*bessel_j(v,z) - bessel_j(-v,z))
///
/// A&S 9.1.4:
/// H[v,2](z) = %i*csc(v*%pi)*(bessel_j(-v,z) - exp(-v*%pi*%i)*bessel_j(v,z))
///
/// Both formula are not valid for v an integer.
/// For this case use the definitions of the Hankel functions:
///    H[v,1](z) = bessel_j(v,z) + %i* bessel_y(v,z)
///    H[v,2](z) = bessel_j(v,z) - %i* bessel_y(v,z)
fn htjory(v : Value, sort_ : Value, z : Value) -> Value raise {
  // V is the order, SORT is the kind of Hankel function (1 or 2), Z
  // is the arg.
  if consp(v) && consp(car(v)) && eq(caar(v), q_rat) {
    // If the order is a rational number of some sort,
    //
    // (bessel_j(-v,z) - bessel_j(v,z)*exp(-v*%pi*%i))/(%i*sin(v*%pi*%i))
    div(
      numjory(v, sort_, z, q_j),
      mul2(q_d__pcti, hypgeo__take(q_p_sin, [mul2(v, q_d__pctpi)])),
    )
  } else if equal(sort_, int(1)) {
    // Transform hankel_1(v,z) to bessel_j(v,z)+%i*bessel_y(v,z)
    add2(
      hypgeo__take(q_p_bessel_j, [v, z]),
      mul2(q_d__pcti, hypgeo__take(q_p_bessel_y, [v, z])),
    )
  } else if equal(sort_, int(2)) {
    // Transform hankel_2(v,z) to bessel_j(v,z)-%i*bessel_y(v,z)
    sub(
      hypgeo__take(q_p_bessel_j, [v, z]),
      mul2(q_d__pcti, hypgeo__take(q_p_bessel_y, [v, z])),
    )
  } else {
    // We should never reach this point of code.
    merr("htjory: Called with wrong sort of Hankel functions.", [])
  }
}

// Three helper functions only used by htjory

///|
/// Bessel J or Y, depending on if FLG is 'J or not.
fn desjy(v : Value, z : Value, flg : Value) -> Value raise {
  if eq(flg, q_j) {
    hypgeo__take(q_p_bessel_j, [v, z])
  } else {
    hypgeo__take(q_p_bessel_y, [v, z])
  }
}

///|
fn numjory(v : Value, sort_ : Value, z : Value, flg : Value) -> Value raise {
  if equal(sort_, int(1)) {
    // bessel(-v, z) - exp(-v*%pi*%i)*bessel(v, z)
    //
    // Where bessel is bessel_j if FLG is 'j.  Otherwise, bessel
    // is bessel_y.
    sub(
      desjy(mul2(int(-1), v), z, flg),
      mul2(
        power(q_d__pcte, muln_([int(-1), v, q_d__pctpi, q_d__pcti])),
        desjy(v, z, flg),
      ),
    )
  } else {
    // exp(-v*%pi*%i)*bessel(v,z) - bessel(-v,z), where bessel is
    // bessel_j or bessel_y, depending on if FLG is 'j or not.
    sub(
      mul2(
        power(q_d__pcte, mul3(v, q_d__pctpi, q_d__pcti)),
        desmjy(v, z, flg),
      ),
      desmjy(mul2(int(-1), v), z, flg),
    )
  }
}

///|
fn desmjy(v : Value, z : Value, flg : Value) -> Value raise {
  if eq(flg, q_j) {
    // bessel_j(v,z)
    hypgeo__take(q_p_bessel_j, [v, z])
  } else {
    // -bessel_y(v,z)
    mul2(int(-1), hypgeo__take(q_p_bessel_y, [v, z]))
  }
}

// ---------------------------------------------------------------------------
// TRANSFORM TO HYPERGEOMETRIC FUNCTION WITHOUT USING THE ROUTINE REF
//
// This functions are called in the routine lt-sf-log to get the
// representation in terms of a hypergeometric function.

///|
/// `((mqapply simp) (($%f h1 h2) p q) pl ql arg)`
fn hypgeo__fpq_form(
  h1 : Value,
  h2 : Value,
  p : Int,
  q : Int,
  pl : Value,
  ql : Value,
  arg : Value,
) -> Value {
  list([
    list2(q_mqapply, q_simp),
    list([list3(q_d__pctf, h1, h2), int(p), int(q)]),
    pl,
    ql,
    arg,
  ])
}

///|
/// The algorithm of the implemented Hermite function %he does not work for
/// the known Laplace transforms. For an even or odd integer order, we
/// can represent the Hermite function by the Hypergeometric function 1F1.
/// With this representations we get the expected Laplace transforms.
fn hermite_to_hypergeometric(order : Value, arg : Value) -> Value raise {
  if maxima_integerp(order).truthy() && mevenp(order).truthy() {
    // Transform to 1F1 for order an even integer
    muln_([
      power(int(2), order),
      power(q_d__pctpi, div(int(1), int(2))),
      inv(hypgeo__take(q_p_gamma, [div(sub(int(1), order), int(2))])),
      hypgeo__fpq_form(
        q_array,
        q_simp,
        1,
        1,
        list2(list1(q_mlist), div(order, int(-2))),
        list2(list1(q_mlist), hypgeo__r(1, 2)),
        mul2(arg, arg),
      ),
    ])
  } else if maxima_integerp(order).truthy() && moddp(order).truthy() {
    // Transform to 1F1 for order an odd integer
    muln_([
      int(-2),
      arg,
      power(int(2), order),
      power(q_d__pctpi, hypgeo__r(1, 2)),
      inv(hypgeo__take(q_p_gamma, [div(order, int(-2))])),
      hypgeo__fpq_form(
        q_simp,
        q_array,
        1,
        1,
        list2(list2(q_mlist, q_simp), div(sub(int(1), order), int(2))),
        list2(list2(q_mlist, q_simp), hypgeo__r(3, 2)),
        mul2(arg, arg),
      ),
    ])
  } else {
    // The general case, transform to 2F0
    // For this case we have no Laplace transform.
    mul2(
      power(mul2(int(2), arg), order),
      hypgeo__fpq_form(
        q_array,
        q_simp,
        2,
        0,
        list3(
          list2(q_mlist, q_simp),
          div(order, int(2)),
          div(sub(int(1), order), int(2)),
        ),
        list1(list2(q_mlist, q_simp)),
        div(int(-1), mul2(arg, arg)),
      ),
    )
  }
}

///|
/// Hypergeometric representation of the Exponential Integral Si
/// Si(z) = z*1F2([1/2],[3/2,3/2],-z^2/4)
fn expintegral_si_to_hypergeometric(arg : Value) -> Value raise {
  mul2(
    arg,
    hypgeo__fpq_form(
      q_array,
      q_simp,
      1,
      2,
      list2(list2(q_mlist, q_simp), hypgeo__r(1, 2)),
      list3(list2(q_mlist, q_simp), hypgeo__r(3, 2), hypgeo__r(3, 2)),
      div(mul3(int(-1), arg, arg), int(4)),
    ),
  )
}

///|
/// Hypergeometric representation of the Exponential Integral Shi
/// Shi(z) = z*1F2([1/2],[3/2,3/2],z^2/4)
fn expintegral_shi_to_hypergeometric(arg : Value) -> Value raise {
  mul2(
    arg,
    hypgeo__fpq_form(
      q_simp,
      q_array,
      1,
      2,
      list2(list2(q_mlist, q_simp), hypgeo__r(1, 2)),
      list3(list2(q_mlist, q_simp), hypgeo__r(3, 2), hypgeo__r(3, 2)),
      div(mul2(arg, arg), int(4)),
    ),
  )
}

///|
/// Hypergeometric representation of the Exponential Integral Ci
/// Ci(z) = -z^2/4*2F3([1,1],[2,2,3/2],-z^2/4)+log(z)+%gamma
fn expintegral_ci_to_hypergeometric(arg : Value) -> Value raise {
  addn_([
    mul2(
      div(mul3(int(-1), arg, arg), int(4)),
      hypgeo__fpq_form(
        q_simp,
        q_array,
        2,
        3,
        list3(list2(q_mlist, q_simp), int(1), int(1)),
        list4(list2(q_mlist, q_simp), int(2), int(2), hypgeo__r(3, 2)),
        div(mul3(int(-1), arg, arg), int(4)),
      ),
    ),
    hypgeo__take(q_p_log, [arg]),
    q_d__pctgamma,
  ])
}

///|
/// Hypergeometric representation of the Exponential Integral Chi
/// Chi(z) = z^2/4*2F3([1,1],[2,2,3/2],z^2/4)+log(z)+%gamma
fn expintegral_chi_to_hypergeometric(arg : Value) -> Value raise {
  addn_([
    mul2(
      div(mul2(arg, arg), int(4)),
      hypgeo__fpq_form(
        q_array,
        q_simp,
        2,
        3,
        list3(list2(q_mlist, q_simp), int(1), int(1)),
        list4(list2(q_mlist, q_simp), int(2), int(2), hypgeo__r(3, 2)),
        div(mul2(arg, arg), int(4)),
      ),
    ),
    hypgeo__take(q_p_log, [arg]),
    q_d__pctgamma,
  ])
}

// ---------------------------------------------------------------------------
// EXPERTS ON LAPLACE TRANSFORMS
//
// LT<foo> functions are various experts on Laplace transforms of the
// function <foo>.  The expression being transformed is
// r*<foo>(args).  The first arg of each expert is r, The remaining
// args are the arg(s) and/or parameters.

///|
/// Laplace transform of one Bessel J
fn lt1j(rest_ : Value, arg : Value, index : Value) -> Value raise {
  lt_ltp(q_onej, rest_, arg, index)
}

///|
/// Laplace transform of two Bessel J functions.
/// The argument of each must be the same, but the orders may be different.
fn lt2j(
  rest_ : Value,
  arg1 : Value,
  arg2 : Value,
  index1 : Value,
  index2 : Value,
) -> Value raise {
  if !equal(arg1, arg2) {
    hypgeo__flag(q_product_of_bessel_with_different_args)
  } else {
    // Call lt-ltp two transform and integrate two Bessel J functions.
    lt_ltp(q_twoj, rest_, arg1, list3(q_list, index1, index2))
  }
}

///|
/// Laplace transform of a square of a Bessel J function
fn lt1j_hat2(rest_ : Value, arg : Value, index : Value) -> Value raise {
  if alike1(index, mk(q_rat, [int(-1), int(2)])).truthy() {
    // Special case: Laplace transform of bessel_j(v,arg)^2, v = -1/2.
    // For this case the algorithm for the product of two Bessel functions
    // does not work. Call the integrator with the hypergeometric
    // representation: 2/%pi/arg*1/2*(1+0F1([], [1/2], -arg*arg)).
    sendexec(
      mul3(div(int(2), q_d__pctpi), inv(arg), rest_),
      add2(
        hypgeo__r(1, 2),
        mul2(
          hypgeo__r(1, 2),
          hypgeo__fpq_form(
            q_simp,
            q_array,
            1,
            0,
            list1(list2(q_mlist, q_simp)),
            list2(list2(q_mlist, q_simp), hypgeo__r(1, 2)),
            mul2(int(-1), mul2(arg, arg)),
          ),
        ),
      ),
    )
  } else {
    lt_ltp(q_twoj, rest_, arg, list3(q_list, index, index))
  }
}

///|
/// Laplace transform of Incomplete Gamma function
fn lt1gamma_incomplete_lower(
  rest_ : Value,
  arg1 : Value,
  arg2 : Value,
) -> Value raise {
  lt_ltp(q_gamma_incomplete_lower, rest_, arg2, arg1)
}

///|
/// Laplace transform of Whittaker M function
fn lt1m(r : Value, a : Value, i1 : Value, i2 : Value) -> Value raise {
  lt_ltp(q_onem, r, a, list2(i1, i2))
}

///|
/// Laplace transform of Jacobi function
fn lt1p(r : Value, a : Value, i1 : Value, i2 : Value) -> Value raise {
  lt_ltp(q_hyp_onep, r, a, list2(i1, i2))
}

///|
/// Laplace transform of Associated Legendre function of the second kind
fn lt1q(r : Value, a : Value, i1 : Value, i2 : Value) -> Value raise {
  lt_ltp(q_oneq, r, a, list2(i1, i2))
}

///|
/// Laplace transform of Erf function
fn lt1erf(rest_ : Value, arg : Value) -> Value raise {
  lt_ltp(q_onerf, rest_, arg, Nil)
}

///|
/// Laplace transform of Log function
fn lt1log(rest_ : Value, arg : Value) -> Value raise {
  lt_ltp(q_onelog, rest_, arg, Nil)
}

///|
/// Laplace transform of Complete elliptic integral of the first kind
fn lt1kelliptic(rest_ : Value, arg : Value) -> Value raise {
  lt_ltp(q_onekelliptic, rest_, arg, Nil)
}

///|
/// Laplace transform of Complete elliptic integral of the second kind
fn lt1e(rest_ : Value, arg : Value) -> Value raise {
  lt_ltp(q_onee, rest_, arg, Nil)
}

///|
/// Laplace transform of Struve H function
fn lt1hstruve(rest_ : Value, arg1 : Value, index1 : Value) -> Value raise {
  lt_ltp(q_hs, rest_, arg1, index1)
}

///|
/// Laplace transform of Struve L function
fn lt1lstruve(rest_ : Value, arg1 : Value, index1 : Value) -> Value raise {
  lt_ltp(q_hl, rest_, arg1, index1)
}

///|
/// Laplace transform of Lommel s function
fn lt1s(
  rest_ : Value,
  arg1 : Value,
  index1 : Value,
  index2 : Value,
) -> Value raise {
  lt_ltp(q_s, rest_, arg1, list2(index1, index2))
}

// ---------------------------------------------------------------------------
// TRANSFORM TO HYPERGEOMETRIC FUNCTION AND DO THE INTEGRATION
//
// FLG = special function we're transforming
// REST = other stuff
// ARG = arg of special function
// INDEX = index of special function.
//
// So we're transforming REST*FLG(INDEX, ARG).

///|
fn lt_ltp(flg : Value, rest_ : Value, arg : Value, index0 : Value) -> Value raise {
  let mut index = index0
  if listp(index) && eq(car(index), q_list) {
    index = list2(cadr(index), caddr(index))
  }
  // Convert the special function to a hypgergeometric function.  L1 is
  // the special function converted to the hypergeometric function.
  // d*x^m*%e^a*x looks for that factor in the expanded form.
  let l1 = ref(flg, index, arg)
  let l = m2_d_starx_hatm_star_pcte_hata_starx(
    d_factor(mul2(rest_, car(l1))),
    hypgeo__var(),
    hypgeo__par(),
  )
  if l.truthy() {
    p__doletest(l, l1)
  } else {
    // We currently don't know how to handle this yet.
    // We add the return of a noun form.
    hypgeo__flag(q_other_ca_later)
  }
}

///|
/// Dispatch function to convert the given function to a hypergeometric
/// function.
///
/// The first arg is a symbol naming the function; the last is the
/// argument to the function.  The second arg is the index (or list of
/// indices) to the function.  Not used if the function doesn't have
/// any indices
///
/// The result is a list of 2 elements: The first element is a
/// multiplier; the second, the hypergeometric function itself.
fn ref(flg : Value, index : Value, arg : Value) -> Value raise {
  if eq(flg, q_onej) {
    j1tf(index, arg)
  } else if eq(flg, q_twoj) {
    j2tf(car(index), cadr(index), arg)
  } else if eq(flg, q_hs) {
    hstf(index, arg)
  } else if eq(flg, q_hl) {
    lstf(index, arg)
  } else if eq(flg, q_s) {
    stf(car(index), cadr(index), arg)
  } else if eq(flg, q_onerf) {
    erftf(arg)
  } else if eq(flg, q_onelog) {
    logtf(arg)
  } else if eq(flg, q_onekelliptic) {
    kelliptictf(arg) // elliptic_kc
  } else if eq(flg, q_onee) {
    etf(arg) // elliptic_ec
  } else if eq(flg, q_onem) {
    mtf(car(index), cadr(index), arg)
  } else if eq(flg, q_hyp_onep) {
    ptf(car(index), cadr(index), arg)
  } else if eq(flg, q_oneq) {
    qtf(car(index), cadr(index), arg)
  } else if eq(flg, q_gamma_incomplete_lower) {
    gamma_incomplete_lower_tf(index, arg)
  } else if eq(flg, q_onepjac) {
    pjactf(car(index), cadr(index), caddr(index), arg)
  } else if eq(flg, q_asin) {
    asintf(arg)
  } else if eq(flg, q_atan) {
    atantf(arg)
  } else if eq(flg, q_f) {
    // Transform %f to internal representation FPQ
    list2(int(1), ref_fpq(cdr(car(index)), cdr(cadr(index)), arg))
  } else {
    Nil
  }
}

// TRANSFORM FUNCTION IN TERMS OF HYPERGEOMETRIC FUNCTION

///|
/// Create a hypergeometric form that we recognize.  The function is
/// %f[n,m](p; q; arg).  We represent this as a list of the form
/// (fpq (<length p> <length q>) <p> <q> <arg>)
fn ref_fpq(p : Value, q : Value, arg : Value) -> Value raise {
  list([q_fpq, list2(int(length(p)), int(length(q))), p, q, arg])
}

///|
/// Whittaker M function in terms of hypergeometric function
///
/// A&S 13.1.32:
///
/// M[k,u](z) = exp(-z/2)*z^(1/2+u)*M(1/2+u-k,1+2*u,z)
fn mtf(i1 : Value, i2 : Value, arg : Value) -> Value raise {
  list2(
    mul2(
      power(arg, add2(i2, hypgeo__r(1, 2))),
      power(q_d__pcte, div(arg, int(-2))),
    ),
    ref_fpq(
      list1(addn_([hypgeo__r(1, 2), i2, mul2(int(-1), i1)])),
      list1(addn_([i2, i2, int(1)])),
      arg,
    ),
  )
}

///|
/// Jacobi P in terms of hypergeometric function
///
/// A&S 15.4.6:
///
/// F(-n,a+1+b+n; a+1; x) = n!/poch(a+1,n)*jacobi_p(n,a,b,1-2*x)
///
/// jacobi_p(n,a,b,x) = poch(a+1,n)/n!*F(-n,a+1+b+n; a+1; (1-x)/2)
///                   = gamma(a+n+1)/gamma(a+1)/n!*F(-n,a+1+b+n; a+1; (1-x)/2)
fn pjactf(n : Value, a : Value, b : Value, x : Value) -> Value raise {
  list2(
    mul3(
      hypgeo__take(q_p_gamma, [addn_([n, a, int(1)])]),
      inv(hypgeo__take(q_p_gamma, [add2(a, int(1))])),
      inv(hypgeo__take(q_p_gamma, [add2(n, int(1))])),
    ),
    ref_fpq(
      list2(mul2(int(-1), n), addn_([n, a, b, int(1)])),
      list1(add2(a, int(1))),
      sub(hypgeo__r(1, 2), div(x, int(2))),
    ),
  )
}

///|
/// ArcSin in terms of hypergeometric function
///
/// asin(z) = z*F(1/2,1/2; 3/2; z^2)
fn asintf(arg : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  list2(
    arg,
    ref_fpq(list2(inv2, inv2), list1(hypgeo__r(3, 2)), mul2(arg, arg)),
  )
}

///|
/// ArcTan in terms of hypergeometric function
///
/// atan(z) = z*F(1/2,1; 3/2; -z^2)
fn atantf(arg : Value) -> Value raise {
  list2(
    arg,
    ref_fpq(
      list2(hypgeo__r(1, 2), int(1)),
      list1(hypgeo__r(3, 2)),
      mul3(int(-1), arg, arg),
    ),
  )
}

///|
/// Associated Legendre function P in terms of hypergeometric function
///
/// A&S 8.1.2
///
/// assoc_legendre_p(v,u,z) = ((z+1)/(z-2))^(u/2)/gamma(1-u)*F(-v,v+1;1-u,(1-z)/2)
fn ptf(n : Value, m : Value, z : Value) -> Value raise {
  list2(
    mul2(
      inv(hypgeo__take(q_p_gamma, [sub(int(1), m)])),
      power(div(add2(z, int(1)), sub(z, int(1))), div(m, int(2))),
    ),
    ref_fpq(
      list2(mul2(int(-1), n), add2(n, int(1))),
      list1(sub(int(1), m)),
      sub(hypgeo__r(1, 2), div(z, int(2))),
    ),
  )
}

///|
/// Associated Legendre function Q in terms of hypergeometric function
///
/// A&S 8.1.3:
///
/// assoc_legendre_q(v,u,z)
///    = exp(%i*u*%pi)*2^(-v-1)*sqrt(%pi) *
///       gamma(v+u+1)/gamma(v+3/2)*z^(-v-u-1)*(z^2-1)^(u/2) *
///        F(1+v/2+u/2, 1/2+v/2+u/2; v+3/2; 1/z^2)
fn qtf(n : Value, m : Value, z : Value) -> Value raise {
  list2(
    muln_([
      power(q_d__pcte, mul3(m, q_d__pctpi, q_d__pcti)),
      power(q_d__pctpi, hypgeo__r(1, 2)),
      hypgeo__take(q_p_gamma, [addn_([m, n, int(1)])]),
      power(int(2), sub(int(-1), n)),
      inv(hypgeo__take(q_p_gamma, [add2(n, hypgeo__r(3, 2))])),
      power(z, mul2(int(-1), addn_([m, n, int(1)]))),
      power(sub(mul2(z, z), int(1)), div(m, int(2))),
    ]),
    ref_fpq(
      list2(
        div(addn_([m, n, int(1)]), int(2)),
        div(addn_([m, n, int(2)]), int(2)),
      ),
      list1(add2(n, hypgeo__r(3, 2))),
      power(z, int(-2)),
    ),
  )
}

///|
/// Incomplete lower Gamma in terms of hypergeometric function
///
/// A&S 13.6.10:
///
/// M(a,a+1,-x) = a*x^(-a)*gamma_incomplete_lower(a,x)
///
/// gamma_incomplete_lower(a,x) = x^a/a*M(a,a+1,-x)
fn gamma_incomplete_lower_tf(a : Value, x : Value) -> Value raise {
  list2(
    mul2(inv(a), power(x, a)),
    ref_fpq(list1(a), list1(add2(a, int(1))), mul2(int(-1), x)),
  )
}

///|
/// Complete elliptic K in terms of hypergeometric function
///
/// A&S 17.3.9
///
/// K(k) = %pi/2*2F1(1/2,1/2; 1; k^2)
fn kelliptictf(k : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  list2(
    mul2(inv2, q_d__pctpi),
    ref_fpq(list2(inv2, inv2), list1(int(1)), mul2(k, k)),
  )
}

///|
/// Complete elliptic E in terms of hypergeometric function
///
/// A&S 17.3.10
///
/// E(k) = %pi/2*2F1(-1/2,1/2;1;k^2)
fn etf(k : Value) -> Value raise {
  let inv2 = hypgeo__r(1, 2)
  list2(
    mul2(inv2, q_d__pctpi),
    ref_fpq(list2(mul2(int(-1), inv2), inv2), list1(int(1)), mul2(k, k)),
  )
}

///|
/// erf in terms of hypgeometric function.
///
/// A&S 7.1.21 gives
///
/// erf(z) = 2*z/sqrt(%pi)*M(1/2,3/2,-z^2)
///        = 2*z/sqrt(%pi)*exp(-z^2)*M(1,3/2,z^2)
fn erftf(arg : Value) -> Value raise {
  list2(
    mul3(int(2), arg, power(q_d__pctpi, hypgeo__r(-1, 2))),
    ref_fpq(
      list1(hypgeo__r(1, 2)),
      list1(hypgeo__r(3, 2)),
      mul3(int(-1), arg, arg),
    ),
  )
}

///|
/// log in terms of hypergeometric function
///
/// We know from A&S 15.1.3 that
///
/// F(1,1;2;z) = -log(1-z)/z.
///
/// So log(z) = (z-1)*F(1,1;2;1-z)
fn logtf(arg : Value) -> Value raise {
  list2(
    sub(arg, int(1)),
    ref_fpq(list2(int(1), int(1)), list1(int(2)), sub(int(1), arg)),
  )
}

///|
/// Bessel J function expressed as a hypergeometric function.
///
/// A&S 9.1.10:
///                         inf
/// bessel_j(v,z) = (z/2)^v*sum (-z^2/4)^k/k!/gamma(v+k+1)
///                         k=0
///
///               = (z/2)^v/gamma(v+1)*sum 1/poch(v+1,k)*(-z^2/4)^k/k!
///
///               = (z/2)^v/gamma(v+1) * 0F1(; v+1; -z^2/4)
fn j1tf(v : Value, z : Value) -> Value raise {
  list2(
    mul3(
      inv(power(int(2), v)),
      power(z, v),
      inv(hypgeo__take(q_p_gamma, [add2(v, int(1))])),
    ),
    ref_fpq(
      Nil,
      list1(add2(v, int(1))),
      mul2(hypgeo__r(-1, 4), power(z, int(2))),
    ),
  )
}

///|
/// Product of 2 Bessel J functions in terms of hypergeometric function
///
/// See Y. L. Luke, formula 39, page 216:
///
/// bessel_j(u,z)*bessel_j(v,z)
///    = (z/2)^(u+v)/gamma(u+1)/gamma(v+1) *
///        2F3((u+v+1)/2, (u+v+2)/2; u+1, v+1, u+v+1; -z^2)
fn j2tf(n : Value, m : Value, arg : Value) -> Value raise {
  list2(
    muln_([
      inv(hypgeo__take(q_p_gamma, [add2(n, int(1))])),
      inv(hypgeo__take(q_p_gamma, [add2(m, int(1))])),
      inv(power(int(2), add2(n, m))),
      power(arg, add2(n, m)),
    ]),
    ref_fpq(
      list2(
        addn_([hypgeo__r(1, 2), div(n, int(2)), div(m, int(2))]),
        addn_([int(1), div(n, int(2)), div(m, int(2))]),
      ),
      list3(add2(int(1), n), add2(int(1), m), addn_([int(1), n, m])),
      mul2(int(-1), power(arg, int(2))),
    ),
  )
}

///|
/// Struve H function in terms of hypergeometric function.
///
/// H[v](z) = 2/sqrt(%pi)*(z/2)^(v+1)/gamma(v+3/2) * 1F2(1;3/2,v+3/2;(-z^2/4))
///
/// See also A&S 12.1.2 and 12.1.21.
fn hstf(v : Value, z : Value) -> Value raise {
  let d32 = div(int(3), int(2))
  list2(
    mul3(
      power(div(z, int(2)), add2(v, int(1))),
      inv(hypgeo__take(q_p_gamma, [d32])),
      inv(hypgeo__take(q_p_gamma, [add2(v, d32)])),
    ),
    ref_fpq(
      list1(int(1)),
      list2(d32, add2(v, d32)),
      mul3(hypgeo__r(-1, 4), z, z),
    ),
  )
}

///|
/// Struve L function in terms of hypergeometric function
///
/// A&S 12.2.1:
///
/// L[v](z) = -%i*exp(-v*%i*%pi/2)*H[v](%i*z)
///
/// L[v](z) = 2/sqrt(%pi)*(z/2)^(v+1)/gamma(v+3/2) * 1F2(1;3/2,v+3/2;(z^2/4))
fn lstf(v : Value, z : Value) -> Value raise {
  let d32 = div(int(3), int(2))
  list2(
    mul3(
      power(div(z, int(2)), add2(v, int(1))),
      inv(hypgeo__take(q_p_gamma, [d32])),
      inv(hypgeo__take(q_p_gamma, [add2(v, d32)])),
    ),
    ref_fpq(
      list1(int(1)),
      list2(d32, add2(v, d32)),
      mul3(hypgeo__r(1, 4), z, z),
    ),
  )
}

///|
/// Lommel s function in terms of hypergeometric function
///
/// See Y. L. Luke, p 217, formula 1
///
/// s(u,v,z) = z^(u+1)/(u-v+1)/(u+v+1)*1F2(1; (u-v+3)/2, (u+v+3)/2; -z^2/4)
fn stf(m : Value, n : Value, z : Value) -> Value raise {
  list2(
    mul3(
      power(z, add2(m, int(1))),
      inv(sub(add2(m, int(1)), n)),
      inv(addn_([m, n, int(1)])),
    ),
    ref_fpq(
      list1(int(1)),
      list2(
        div(sub(add2(m, int(3)), n), int(2)),
        div(addn_([m, n, int(3)]), int(2)),
      ),
      mul3(hypgeo__r(-1, 4), z, z),
    ),
  )
}

// ---------------------------------------------------------------------------
// Algorithm 3: Laplace transform of a hypergeometric function

///|
fn p__doletest(l : Value, l1 : Value) -> Value raise {
  let q = cdras(q_q, l)
  let a = if equal(q, int(1)) { int(0) } else { cdras(q_a, l) }
  substl(sub(hypgeo__par(), a), hypgeo__par(), execf19(l, cadr(l1)))
}

///|
fn execf19(l1 : Value, l2 : Value) -> Value raise {
  let ans = execargmatch(car(cddddr(l2)))
  if eq(car(ans), q_dionimo) {
    return dionarghyp(l1, l2, cadr(ans))
  }
  // We specialized the pattern for the argument. Now the test fails
  // correctly and we have to add the return of a noun form.
  hypgeo__flag(q_next_for_other_args)
}

///|
/// Executive for recognizing the sort of argument to the
/// hypergeometric function.  We look to see if the arg is of the form
/// a*x^m + c.  Return a list of 'dionimo and the match.
fn execargmatch(arg : Value) -> Value raise {
  let l1 = m2_a_starx_hatm_plusc(d_factor(arg), hypgeo__var())
  if l1.truthy() {
    return list2(q_dionimo, l1)
  }
  let l1 = m2_a_starx_hatm_plusc(d_expand(arg), hypgeo__var())
  if l1.truthy() {
    return list2(q_dionimo, l1)
  }
  // The return value has to be a list.
  list1(q_other_case_args_to_follow)
}

///|
/// We have hypergeometric function whose arg looks like a*x^m+c.  L1
/// matches the d*x^m... part, L2 is the hypergeometric function and
/// arg is the match for a*x^m+c.
fn dionarghyp(l1 : Value, l2 : Value, arg : Value) -> Value raise {
  let a = cdras(q_a, arg)
  let m = cdras(q_m, arg)
  let c = cdras(q_c, arg)
  if integerp(m) && // The power of the argument has to be
    plusp(m) && // a positive integer.
    equal(int(0), c) { // No const term to the argument.
    f19cond(a, m, l1, l2)
  } else {
    hypgeo__flag(q_prop4_and_other_cases_to_follow)
  }
}

///|
fn f19cond(a : Value, m : Value, l1 : Value, l2 : Value) -> Value raise {
  let p = caadr(l2)
  let q = cadadr(l2)
  let s = cdras(q_m, l1)
  let d = cdras(q_d, l1)
  let l1 = caddr(l2)
  let l2 = cadddr(l2)
  // At this point, we have the function d*x^s*%f[p,q](l1, l2, (a*t)^m).
  // Check to see if Formula 19, p 220 applies.
  if !eq(d_asksign(sub(addn_([p, m, int(-1)]), q)), q_d_pos) &&
    eq(d_asksign(add2(s, int(1))), q_d_pos) {
    return mul2(d, f19p220_simp(add2(s, int(1)), l1, l2, a, m))
  }
  hypgeo__flag(q_failed_on_f19cond_multiply_the_other_cases_with_d)
}

///|
/// Table of Laplace transforms, p 220, formula 19:
///
/// If m + k <= n + 1, and Re(s) > 0, the Laplace transform of
///
///    t^(s-1)*%f[m,n]([a1,...,am],[p1,...,pn],(c*t)^k)
/// is
///
///    gamma(s)/p^s*%f[m+k,n]([a1,...,am,s/k,(s+1)/k,...,(s+k-1)/k],[p1,...,pm],(k*c/p)^k)
///
/// with Re(p) > 0 if m + k <= n, Re(p+k*c*exp(2*%pi*%i*r/k)) > 0 for r
/// = 0, 1,...,k-1, if m + k = n + 1.
///
/// The args below are s, [a's], [p's], c^k, k.
fn f19p220_simp(
  s : Value,
  l1 : Value,
  l2 : Value,
  cf : Value,
  k : Value,
) -> Value raise {
  mul3(
    hypgeo__take(q_p_gamma, [s]),
    inv(power(hypgeo__par(), s)),
    hgfsimp_exec(
      append(l1, addarglist(s, k)),
      l2,
      mul3(cf, power(k, k), power(inv(hypgeo__par()), k)),
    ),
  )
}

///|
/// Return a list of s/k, (s+1)/k, ..., (s+|k|-1)/k
fn addarglist(s : Value, k : Value) -> Value raise {
  let abs_k = to_int(num_abs(k))
  let res = Collector::new()
  for n in 0..<abs_k {
    res.add(div(add2(s, int(n)), k))
  }
  res.result()
}

// ---------------------------------------------------------------------------
// Algorithm 4: SPECIAL HANDLING OF Bessel Y for an integer order
//
// This is called for one Bessel Y function, when the order is an integer.

///|
fn lty(rest_ : Value, arg : Value, index : Value) -> Value raise {
  let l = m2_d_starx_hatm_star_pcte_hata_starx(
    rest_,
    hypgeo__var(),
    hypgeo__par(),
  )
  if l.truthy() {
    return execfy(l, arg, index)
  }
  hypgeo__flag(q_fail_in_lty)
}

///|
fn execfy(l : Value, arg : Value, index : Value) -> Value raise {
  let ans = execargmatch(arg)
  if eq(car(ans), q_dionimo) {
    return dionarghyp_y(l, index, cadr(ans))
  }
  hypgeo__flag(q_fail_in_execfy)
}

///|
fn dionarghyp_y(l : Value, index : Value, arg : Value) -> Value raise {
  let a = cdras(q_a, arg)
  let m = cdras(q_m, arg)
  let c = cdras(q_c, arg)
  if zerp(c).truthy() && equal(m, int(1)) {
    let ans = f2p105v2cond(a, l, index)
    if !symbolp(ans) {
      return ans
    }
  }
  if zerp(c).truthy() && equal(m, hypgeo__r(1, 2)) {
    let ans = f50cond(a, l, index)
    if !symbolp(ans) {
      return ans
    }
  }
  hypgeo__flag(q_fail_in_dionarghyp_y)
}

// Algorithm 4.1: Laplace transform of t^n*bessel_y(v,a*t)
//                v is an integer and n>=v
//
// Table of Integral Transforms, Volume 2, p 105, formula 2 gives the
// Y-transform of x^(u-3/2)*exp(-a*x).  Thus, the Laplace transform of
// x^(u-1/2)*bessel_y(v,x) is
//
//    -2/%pi*gamma(u+v)*sqrt(a)*(a^2+p^2)^(-u/2)
//          *assoc_legendre_q(u-1,-v,p/sqrt(a^2+p^2))

///|
fn f2p105v2cond(a : Value, l : Value, index : Value) -> Value raise {
  let d = cdras(q_d, l) // contains constant part of integrand
  let m = add2(cdras(q_m, l), int(1))
  if eq(d_asksign(d_realpart(sub(m, index))), q_d_pos) {
    return mul2(d, f2p105v2cond_simp(m, index, a))
  }
  hypgeo__flag(q_fail_in_f2p105v2cond)
}

///|
fn f2p105v2cond_simp(m : Value, v : Value, a : Value) -> Value raise {
  let par = hypgeo__par()
  muln_([
    int(-2),
    power(q_d__pctpi, int(-1)),
    hypgeo__take(q_p_gamma, [add2(m, v)]),
    power(
      add2(mul2(a, a), mul2(par, par)),
      mul3(int(-1), hypgeo__r(1, 2), m),
    ),
    // Call Associated Legendre Q function, which simplifies accordingly.
    mfuncall(
      q_d_assoc_legendre_q,
      list3(
        sub(m, int(1)),
        mul2(int(-1), v),
        mul2(
          par,
          power(add2(mul2(a, a), mul2(par, par)), hypgeo__r(-1, 2)),
        ),
      ),
    ),
  ])
}

// Algorithm 4.2: Laplace transform of t^n*bessel_y(v, a*sqrt(t))
//
// Table of Integral Transforms, p. 188, formula 50:
//
// t^(u-1/2)*bessel_y(2*v,2*sqrt(a)*sqrt(t))
//    -> a^(-1/2)*p^(-u)*exp(-a/2/p)
//       * [tan((u-v)*%pi)*gamma(u+v+1/2)/gamma(2*v+1)*M[u,v](a/p)
//          -sec((u-v)*%pi)*W[u,v](a/p)]

///|
fn f50cond(a : Value, l : Value, v : Value) -> Value raise {
  let d = cdras(q_d, l)
  let m = add2(cdras(q_m, l), hypgeo__r(1, 2))
  let v = div(v, int(2))
  if eq(
      d_asksign(d_realpart(addn_([m, v, hypgeo__r(1, 2)]))),
      q_d_pos,
    ) &&
    eq(d_asksign(d_realpart(sub(add2(m, hypgeo__r(1, 2)), v))), q_d_pos) &&
    !maxima_integerp(
      mul2(sub(add2(m, m), addn_([v, v, int(1)])), hypgeo__r(1, 2)),
    ).truthy() {
    let a = mul3(a, a, hypgeo__r(1, 4))
    return f50p188_simp(d, m, v, a)
  }
  hypgeo__flag(q_fail_in_f50cond)
}

///|
fn f50p188_simp(d : Value, u : Value, v : Value, a : Value) -> Value raise {
  let par = hypgeo__par()
  muln_([
    d,
    power(a, hypgeo__r(-1, 2)),
    power(par, mul2(int(-1), u)),
    power(q_d__pcte, div(a, mul2(int(-2), par))),
    sub(
      muln_([
        hypgeo__take(q_p_tan, [mul2(q_d__pctpi, sub(u, v))]),
        hypgeo__take(q_p_gamma, [addn_([u, v, hypgeo__r(1, 2)])]),
        inv(hypgeo__take(q_p_gamma, [addn_([v, v, int(1)])])),
        mwhit(div(a, par), u, v),
      ]),
      mul2(
        hypgeo__take(q_p_sec, [mul2(q_d__pctpi, sub(u, v))]),
        wwhit(div(a, par), u, v),
      ),
    ),
  ])
}

///|
fn init_hypgeo() -> Unit raise {
  // The properties NOUN and VERB give correct linear display
  putprop(q_d_specint, q_p_specint, q_verb) |> ignore
  putprop(q_p_specint, q_d_specint, q_noun) |> ignore
}
