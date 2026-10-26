// Port of src/bessel.lisp, part 2: Bessel I and Bessel K, the expansions
// of half-integral order, realpart/imagpart, the scaled Bessel I functions
// and the Hankel functions.

// ---------------------------------------------------------------------------
// Implementation of the Bessel I function

///|
/// Integral of the Bessel I function wrt z
/// http://functions.wolfram.com/Bessel-TypeFunctions/BesselI/21/01/01/
fn bessel_i_integral_2(v : Value, z : Value) -> Value raise {
  if eql(v, Fix(0L)) {
    // integrate(bessel_i(0,z),z)
    // = (1/2)*z*(bessel_i(0,z)*(%pi*struve_l(1,z)+2)
    //            -%pi*bessel_i(1,z)*struve_l(0,z))
    mk(q_mtimes, [
      bessel__urat(1, 2),
      z,
      mk(q_mplus, [
        mk(q_mtimes, [
          Fix(-1L),
          q_d__pctpi,
          mk(q_p_bessel_i, [Fix(1L), z]),
          mk(q_p_struve_l, [Fix(0L), z]),
        ]),
        mk(q_mtimes, [
          mk(q_p_bessel_i, [Fix(0L), z]),
          mk(q_mplus, [
            Fix(2L),
            mk(q_mtimes, [q_d__pctpi, mk(q_p_struve_l, [Fix(1L), z])]),
          ]),
        ]),
      ]),
    ])
  } else if eql(v, Fix(1L)) {
    // integrate(bessel_i(1,z),z) = bessel_i(0,z)
    mk(q_p_bessel_i, [Fix(0L), z])
  } else {
    // http://functions.wolfram.com/03.02.21.0002.01
    // integrate(bessel_i(v,z),z)
    //  = 2^(-v)*z^(v+1)*hypergeometric([v/2+1/2],[v+1,v/2+3/2],z^2/4)
    //   / gamma(v+2)
    mk(q_mtimes, [
      mk(q_p_hypergeometric, [
        mk(q_mlist, [
          mk(q_mplus, [bessel__urat(1, 2), mk(q_mtimes, [bessel__urat(1, 2), v])]),
        ]),
        mk(q_mlist, [
          mk(q_mplus, [bessel__urat(3, 2), mk(q_mtimes, [bessel__urat(1, 2), v])]),
          mk(q_mplus, [Fix(1L), v]),
        ]),
        mk(q_mtimes, [bessel__urat(1, 4), mk(q_mexpt, [z, Fix(2L)])]),
      ]),
      mk(q_mexpt, [Fix(2L), mk(q_mtimes, [Fix(-1L), v])]),
      mk(q_mexpt, [mk(q_p_gamma, [mk(q_mplus, [Fix(2L), v])]), Fix(-1L)]),
      // The Lisp uses the symbol Z here, not the argument.
      mk(q_mexpt, [q_z, mk(q_mplus, [Fix(1L), v])]),
    ])
  }
}

///|
/// Support a simplim%bessel_i function to handle specific limits
fn simplim_pctbessel_i(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let v = limit(cadr(expr), var_, val, q_think)
  let z = limit(caddr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    // Handle an argument 0 at this place.
    let sgn = d_sign(d_realpart(v))
    if eq(sgn, q_d_neg) && !maxima_integerp(v).truthy() {
      // bessel_i(v,0), Re(v)<0 and v not an integer
      q_d_infinity
    } else if eq(sgn, q_d_zero) && !zerop1(v).truthy() {
      // bessel_i(v,0), Re(v)=0 and v #0
      q_d_und
    } else {
      // Call the simplifier of the function.
      simplify(list3(list1(q_p_bessel_i), v, z))
    }
  } else if eq(z, q_d_inf) {
    // bessel_i(v,inf)
    q_d_inf
  } else if eq(z, q_d_minf) {
    // bessel_i(v,minf). For an integer order bessel_i(v,-x) equals
    // (-1)^v bessel_i(v,x), so the limit along the negative real axis is
    // signed by the parity of the order. For any other order the negative
    // axis is a branch cut and the limit is complex infinity.
    if !integerp(v) {
      q_d_infinity
    } else if evenp(v) {
      q_d_inf
    } else {
      q_d_minf
    }
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list3(list1(q_p_bessel_i), v, z))
  }
}

///|
/// (def-simplifier bessel_i (order arg) ...)
fn simp__pctbessel_i(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_bessel_i, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_bessel_i), list2(order, arg)),
    form,
  )
  if zerop1(arg).truthy() {
    // We handle the different case for zero arg carefully.
    let sgn = d_sign(d_realpart(order))
    if eq(sgn, q_d_zero) && zerop1(d_imagpart(order)).truthy() {
      // bessel_i(0,0) = 1
      bessel__exact_or_float(order, arg, 1L)
    } else if eq(sgn, q_d_pos) || maxima_integerp(order).truthy() {
      // bessel_i(v,0) and Re(v)>0 or v an integer
      bessel__exact_or_float(order, arg, 0L)
    } else if eq(sgn, q_d_neg) && !maxima_integerp(order).truthy() {
      // bessel_i(v,0) and Re(v)<0 and v not an integer
      simp_domain_error(
        list([Str("bessel_i: bessel_i(~:M,~:M) is undefined."), order, arg]),
      )
    } else if eq(sgn, q_d_zero) && !zerop1(d_imagpart(order)).truthy() {
      // bessel_i(v,0) and Re(v)=0 and v # 0
      simp_domain_error(
        list([Str("bessel_i: bessel_i(~:M,~:M) is undefined."), order, arg]),
      )
    } else {
      // No information about the sign of the order
      give_up()
    }
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    if num_eq(Fix(0L), d_imagpart(order)) {
      // order is real, arg is real or complex
      complexify(bessel_i(d_float(order), bessel__cfloat(arg)))
    } else {
      // order is complex, arg is real or complex
      bessel__complex_order_eval(order, arg, bessel_i_hypergeometric)
    }
  } else if bigfloat_numerical_eval_p(list2(order, arg)).truthy() ||
    complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    // We have the order or arg being a bigfloat, so evaluate it
    // numerically using the hypergeometric representation bessel_j.
    //
    // When the order is a negative integer, the hypergeometric
    // representation is invalid. However,
    // https://dlmf.nist.gov/10.27.E1 says bessel_i(-n,z) = bessel_i(n,z).
    let ri = risplit(order)
    let re = car(ri)
    let im = cdr(ri)
    if zerop(im) &&
      zerop1(sub(re, take(list1(q_d_floor), [re]))).truthy() &&
      mminusp(re).truthy() {
      d_rectform(
        d_bfloat(bessel_i_hypergeometric(mul2(Fix(-1L), order), arg)),
      )
    } else {
      d_rectform(d_bfloat(bessel_i_hypergeometric(order, arg)))
    }
  } else if integerp(order) && minusp(order) {
    // Some special cases when the order is an integer
    // A&S 9.6.6: I[-n](x) = I[n](x)
    take(list1(q_p_bessel_i), [num_neg(order), arg])
  } else if symval(q_d_besselexpand).truthy() &&
    max_numeric_ratio_p(order, Fix(2L)).truthy() {
    // When order is a fraction with a denominator of 2, we can express the
    // result in terms of elementary functions. From A&S 10.2.13 and
    // 10.2.14:
    //
    // I[1/2](z) = sqrt(2/%pi/z)*sinh(z)
    // I[-1/2](z) = sqrt(2/%pi/z)*cosh(z)
    bessel_i_half_order(max_numeric_ratio_p(order, Fix(2L)), arg)
  } else if symval(q_d_bessel_reduce).truthy() &&
    integerp(order) &&
    plusp(order) &&
    num_gt(order, Fix(1L)) {
    // Reduce a bessel function of order > 2 to order 1 and 0.
    // A&S 9.6.26: bessel_i(v,z) = -2*(v-1)/z*bessel_i(v-1,z)+bessel_i(v-2,z)
    add2(
      muln_([
        Fix(-2L),
        num_sub(order, Fix(1L)),
        inv(arg),
        take(list1(q_p_bessel_i), [num_sub(order, Fix(1L)), arg]),
      ]),
      take(list1(q_p_bessel_i), [num_sub(order, Fix(2L)), arg]),
    )
  } else if symval(q_d__pctiargs).truthy() &&
    multiplep(arg, q_d__pcti).truthy() {
    // bessel_i(v, %i*x) = (%i*x)^v/(x^v) * bessel_j(v, x)
    // (From http://functions.wolfram.com/03.02.27.0002.01)
    let x = coeff(arg, q_d__pcti, Fix(1L))
    muln_([
      power(mul2(q_d__pcti, x), order),
      inv(power(x, order)),
      take(list1(q_p_bessel_j), [order, x]),
    ])
  } else if symval(q_d_hypergeometric_representation).truthy() {
    bessel_i_hypergeometric(order, arg)
  } else {
    give_up()
  }
}

///|
/// Returns the hypergeometric representation of bessel_i
fn bessel_i_hypergeometric(order : Value, arg : Value) -> Value raise {
  // A&S 9.6.47 / http://functions.wolfram.com/03.02.26.0002.01
  // hypergeometric([],[v+1],z^2/4)*(z/2)^v/gamma(v+1)
  muln_([
    inv(take(list1(q_p_gamma), [add2(order, Fix(1L))])),
    power(div(arg, Fix(2L)), order),
    bessel__hyp0f1(add2(order, Fix(1L)), div(mul2(arg, arg), Fix(4L))),
  ])
}

///|
/// Compute value of Modified Bessel function of the first kind of order
/// ORDER
fn bessel_i(order : Value, arg : Value) -> Value raise {
  if zerop(imagpart(arg)) {
    // We have numeric args and the first arg is purely real. Call the
    // real-valued Bessel function. Use special routines for order 0 and 1,
    // when possible
    let arg = realpart(arg)
    if zerop(order) {
      bessel__fl(@slatec.dbesi0(to_double(arg)))
    } else if num_eq(order, Fix(1L)) {
      bessel__fl(@slatec.dbesi1(to_double(arg)))
    } else if minusp(order) || num_lt(arg, Fix(0L)) {
      let (order_int, order_frac) = num_floor(order)
      if zerop(order_frac) {
        // Order is an integer. From A&S 9.6.6 and 9.6.30 we have
        //   I[-n](z) = I[n](z)
        // and
        //   I[n](-z) = (-1)^n*I[n](z)
        if num_lt(arg, Fix(0L)) {
          if evenp(order_int) {
            bessel_i(num_abs(order), num_abs(arg))
          } else {
            num_neg(bessel_i(num_abs(order), num_abs(arg)))
          }
        } else {
          bessel_i(num_abs(order), arg)
        }
      } else {
        // Order or arg is negative and order is not an integer, use the
        // bessel-j function for calculation. We know from the definition
        // I[v](x) = x^v/(%i*x)^v * J[v](%i*x).
        let arg = lfloat(arg)
        let result = num_mul(
          num_mul(
            bessel__chk(expt(arg, order)),
            bessel__chk(expt(complex(Fix(0L), i=arg), num_neg(order))),
          ),
          bessel_j(order, complex(Fix(0L), i=arg)),
        )
        // Try to clean up result if we know the result is purely real or
        // purely imaginary.
        if num_ge(arg, Fix(0L)) {
          // Result is purely real for arg >= 0
          realpart(result)
        } else if zerop(order_frac) {
          // Order is an integer or a float representation of an integer,
          // the result is purely real.
          realpart(result)
        } else if bessel__eq_half(order_frac) {
          // Order is half-integral-value or a float representation and
          // arg < 0, the result is purely imaginary.
          complex(Fix(0L), i=imagpart(result))
        } else {
          result
        }
      }
    } else {
      // Now the case order > 0 and arg >= 0
      let (n, alpha) = bessel__floor_split(to_double(order))
      let jvals : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
      bessel__dbesi(to_double(realpart(arg)), alpha, 1, n + 1, jvals)
      bessel__fl(jvals[n])
    }
  } else if zerop(realpart(arg)) && zerop(num_rem(order, Fix(1L))) {
    // Handle the case for a pure imaginary arg and integer order. In this
    // case, the result is purely real or purely imaginary, so we want to
    // make sure that happens.
    //
    // bessel_i(n, %i*x) = (%i*x)^n/x^n * bessel_j(n,x)
    //    = %i^n * bessel_j(n,x)
    let n = floor1(order)
    let result = bessel_j(lfloat(n), imagpart(arg))
    if evenp(n) {
      // %i^(2*m) = (-1)^m, where n=2*m
      if evenp(num_div(n, Fix(2L))) {
        result
      } else {
        num_neg(result)
      }
    } else if oddp(n) {
      // %i^(2*m+1) = %i*(-1)^m, where n = 2*m+1
      if evenp(num_floor(n, b=Fix(2L)).0) {
        complex(Fix(0L), i=result)
      } else {
        complex(Fix(0L), i=num_neg(result))
      }
    } else {
      Nil
    }
  } else {
    // The arg is complex. Use the complex-valued Bessel function.
    let (n, alpha) = bessel__floor_split(to_double(order).abs())
    // Evaluate the function for positive order and fixup the result later.
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let (_nz, ierr) = @slatec.zbesi(
      to_double(realpart(arg)),
      to_double(imagpart(arg)),
      alpha,
      1,
      n + 1,
      cyr,
      cyi,
      0,
      0,
    )
    // We should check for errors here based on the value of v-ierr.
    bessel__report_ierr("zbesi", ierr)
    // We have evaluated I[|order|](arg), now we look at the the sign of
    // the order.
    if minusp(order) {
      // From A&S 9.6.2:
      // I[-a](z) = I[a](z) + (2/%pi)*sin(%pi*a)*K[a](z)
      let i = bessel__cfl(cyr[n], cyi[n])
      let dpi : Value = Flo(bessel__pi)
      num_add(
        i,
        num_mul(
          num_mul(
            num_div(Flo(2.0), dpi),
            lsin(num_mul(dpi, num_neg(order))),
          ),
          bessel_k(num_neg(order), arg),
        ),
      )
    } else {
      bessel__cfl(cyr[n], cyi[n])
    }
  }
}

// ---------------------------------------------------------------------------
// Implementation of the Bessel K function

///|
/// Integral of the Bessel K function wrt z
/// http://functions.wolfram.com/Bessel-TypeFunctions/BesselK/21/01/01/
fn bessel_k_integral_2(n : Value, z : Value) -> Value raise {
  if d_integerp(n).truthy() && num_le(Fix(0L), n) {
    if d_oddp(n).truthy() {
      // integrate(bessel_k(2*N+1,z),z) , N > 0
      // = -(-1)^((n-1)/2)*bessel_k(0,z)
      //   + 2*sum((-1)^(k+(n-1)/2-1)*bessel_k(2*k,z),k,1,(n-1)/2)
      let k = gensym()
      let answer = mk(q_mplus, [
        mk(q_mtimes, [
          Fix(-1L),
          mk(q_p_bessel_k, [Fix(0L), z]),
          mk(q_mexpt, [
            Fix(-1L),
            mk(q_mtimes, [bessel__urat(1, 2), mk(q_mplus, [Fix(-1L), n])]),
          ]),
        ]),
        mk(q_mtimes, [
          Fix(2L),
          mk(q_p_sum, [
            mk(q_mtimes, [
              mk(q_p_bessel_k, [mk(q_mtimes, [Fix(2L), k]), z]),
              mk(q_mexpt, [
                Fix(-1L),
                mk(q_mplus, [
                  Fix(-1L),
                  k,
                  mk(q_mtimes, [bessel__urat(1, 2), mk(q_mplus, [Fix(-1L), n])]),
                ]),
              ]),
            ]),
            k,
            Fix(1L),
            mk(q_mtimes, [bessel__urat(1, 2), mk(q_mplus, [Fix(-1L), n])]),
          ]),
        ]),
      ])
      bessel__expand_sum(n, answer)
    } else if d_evenp(n).truthy() {
      // integrate(bessel_k(2*N,z),z) , N > 0
      // = (1/2)*(-1)^(n/2)*%pi*z*(bessel_k(0,z)*struve_l(-1,z)
      //               +bessel_k(1,z)*struve_l(0,z))
      //    + 2 * sum((-1)^(k+n/2)*bessel_k(2*k+1,z),k,0,n/2-1)
      let k = gensym()
      let answer = mk(q_mplus, [
        mk(q_mtimes, [
          Fix(2L),
          mk(q_p_sum, [
            mk(q_mtimes, [
              mk(q_p_bessel_k, [
                mk(q_mplus, [Fix(1L), mk(q_mtimes, [Fix(2L), k])]),
                z,
              ]),
              mk(q_mexpt, [
                Fix(-1L),
                mk(q_mplus, [k, mk(q_mtimes, [bessel__urat(1, 2), n])]),
              ]),
            ]),
            k,
            Fix(0L),
            mk(q_mplus, [Fix(-1L), mk(q_mtimes, [bessel__urat(1, 2), n])]),
          ]),
        ]),
        mk(q_mtimes, [
          bessel__urat(1, 2),
          q_d__pctpi,
          mk(q_mexpt, [Fix(-1L), mk(q_mtimes, [bessel__urat(1, 2), n])]),
          // The Lisp uses the symbol Z here, not the argument.
          q_z,
          mk(q_mplus, [
            mk(q_mtimes, [
              mk(q_p_bessel_k, [Fix(0L), z]),
              mk(q_p_struve_l, [Fix(-1L), z]),
            ]),
            mk(q_mtimes, [
              mk(q_p_bessel_k, [Fix(1L), z]),
              mk(q_p_struve_l, [Fix(0L), z]),
            ]),
          ]),
        ]),
      ])
      bessel__expand_sum(n, answer)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Support a simplim%bessel_k function to handle specific limits
fn simplim_pctbessel_k(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let v = limit(cadr(expr), var_, val, q_think)
  let z = limit(caddr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    // Handle an argument 0 at this place.
    if zerop1(v).truthy() {
      // bessel_k(0,0)
      q_d_inf
    } else if integerp(v) {
      // bessel_k(n,0), n an integer
      if evenp(v) {
        q_d_inf
      } else if eq(z, q_d_zeroa) {
        q_d_inf
      } else if eq(z, q_d_zerob) {
        q_d_minf
      } else {
        q_d_infinity
      }
    } else if !zerop1(d_realpart(v)).truthy() {
      // bessel_k(v,0), Re(v)#0
      q_d_infinity
    } else if zerop1(d_realpart(v)).truthy() && !zerop1(v).truthy() {
      // bessel_k(v,0), Re(v)=0 and v#0
      q_d_und
    } else {
      // Call the simplifier of the function.
      simplify(list3(list1(q_p_bessel_k), v, z))
    }
  } else if eq(z, q_d_inf) {
    // bessel_k(v,inf)
    Fix(0L)
  } else if eq(z, q_d_minf) {
    // bessel_k(v,minf)
    q_d_infinity
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list3(list1(q_p_bessel_k), v, z))
  }
}

///|
/// (def-simplifier bessel_k (order arg) ...)
fn simp__pctbessel_k(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_bessel_k, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_bessel_k), list2(order, arg)),
    form,
  )
  if zerop1(arg).truthy() {
    // Domain error for a zero argument.
    simp_domain_error(
      list([Str("bessel_k: bessel_k(~:M,~:M) is undefined."), order, arg]),
    )
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    if num_eq(Fix(0L), d_imagpart(order)) {
      // order is real, arg is real or complex
      complexify(bessel_k(d_float(order), bessel__cfloat(arg)))
    } else {
      // order is complex, arg is real or complex
      bessel__complex_order_eval(order, arg, bessel_k_hypergeometric)
    }
  } else if bigfloat_numerical_eval_p(list2(order, arg)).truthy() ||
    complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    // When the order is not an integer, we can use the hypergeometric
    // representation to evaluate it.
    let ri = risplit(order)
    let re = car(ri)
    let im = cdr(ri)
    if zerop1(im).truthy() &&
      !zerop1(sub(re, take(list1(q_d_floor), [re]))).truthy() {
      d_rectform(d_bfloat(bessel_k_hypergeometric(re, arg)))
    } else {
      give_up()
    }
  } else if mminusp(order).truthy() {
    // A&S 9.6.6: K[-v](x) = K[v](x)
    take(list1(q_p_bessel_k), [mul2(Fix(-1L), order), arg])
  } else if symval(q_d_besselexpand).truthy() &&
    max_numeric_ratio_p(order, Fix(2L)).truthy() {
    // When order is a fraction with a denominator of 2, we can express the
    // result in terms of elementary functions. From A&S 10.2.16 and
    // 10.2.17:
    //
    // K[1/2](z) = sqrt(%pi/2/z)*exp(-z)
    //           = K[-1/2](z)
    bessel_k_half_order(max_numeric_ratio_p(order, Fix(2L)), arg)
  } else if symval(q_d_bessel_reduce).truthy() &&
    integerp(order) &&
    plusp(order) &&
    num_gt(order, Fix(1L)) {
    // Reduce a bessel function of order > 2 to order 1 and 0.
    // A&S 9.6.26: bessel_k(v,z) = 2*(v-1)/z*bessel_k(v-1,z)+bessel_k(v-2,z)
    add2(
      muln_([
        Fix(2L),
        num_sub(order, Fix(1L)),
        inv(arg),
        take(list1(q_p_bessel_k), [num_sub(order, Fix(1L)), arg]),
      ]),
      take(list1(q_p_bessel_k), [num_sub(order, Fix(2L)), arg]),
    )
  } else if symval(q_d_hypergeometric_representation).truthy() {
    bessel_k_hypergeometric(order, arg)
  } else {
    give_up()
  }
}

///|
/// Returns the hypergeometric representation of bessel_k
fn bessel_k_hypergeometric(order : Value, arg : Value) -> Value raise {
  // http://functions.wolfram.com/03.04.26.0002.01
  // hypergeometric([],[1-v],z^2/4)*2^(v-1)*gamma(v)/z^v
  //   + hypergeometric([],[v+1],z^2/4)*2^(-v-1)*gamma(-v)*z^v
  add2(
    muln_([
      power(Fix(2L), sub(order, Fix(1L))),
      take(list1(q_p_gamma), [order]),
      inv(power(arg, order)),
      bessel__hyp0f1(sub(Fix(1L), order), div(mul2(arg, arg), Fix(4L))),
    ]),
    muln_([
      inv(power(Fix(2L), add2(order, Fix(1L)))),
      power(arg, order),
      take(list1(q_p_gamma), [neg(order)]),
      bessel__hyp0f1(add2(order, Fix(1L)), div(mul2(arg, arg), Fix(4L))),
    ]),
  )
}

///|
/// Compute value of Modified Bessel function of the second kind of order
/// ORDER
fn bessel_k(order : Value, arg : Value) -> Value raise {
  if zerop(imagpart(arg)) {
    // We have numeric args and the first arg is purely real. Call the
    // real-valued Bessel function. Handle orders 0 and 1 specially, when
    // possible.
    let arg = realpart(arg)
    if num_lt(arg, Fix(0L)) {
      // This is the extension for negative arg.
      // We use A&S 9.6.6 and 9.6.31 for evaluation:
      // K[v](-z) = K[|v|](-z)
      //          = exp(-%i*%pi*|v|)*K[|v|](z) - %i*%pi*I[|v|](z)
      let dpi : Value = Flo(bessel__pi)
      let s1 = cis(num_mul(dpi, num_neg(num_abs(order))))
      let s2 = num_mul(complex(Fix(0L), i=Fix(-1L)), dpi)
      let result = num_add(
        num_mul(s1, bessel_k(num_abs(order), num_neg(arg))),
        num_mul(s2, bessel_i(num_abs(order), num_neg(arg))),
      )
      let rem = num_floor(order).1
      if zerop(rem) {
        // order is an integer or a float representation of an integer,
        // the result is a general complex
        result
      } else if bessel__eq_half(rem) {
        // order is half-integral-value or an float representation and
        // arg < 0, the result is pure imaginary
        complex(Fix(0L), i=imagpart(result))
      } else {
        // in all other cases general complex result
        result
      }
    } else if num_eq(order, Fix(0L)) {
      bessel__fl(@slatec.dbesk0(to_double(arg)))
    } else if num_eq(order, Fix(1L)) {
      bessel__fl(@slatec.dbesk1(to_double(arg)))
    } else {
      // From A&S 9.6.6, K[-v](z) = K[v](z), so take the absolute value of
      // the order.
      let (n, alpha) = bessel__floor_split(to_double(order).abs())
      let jvals : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
      bessel__dbesk(to_double(arg), alpha, 1, n + 1, jvals)
      bessel__fl(jvals[n])
    }
  } else {
    // The arg is complex. Use the complex-valued Bessel function. From
    // A&S 9.6.6, K[-v](z) = K[v](z), so take the absolute value of the
    // order.
    let (n, alpha) = bessel__floor_split(to_double(order).abs())
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let (_nz, ierr) = @slatec.zbesk(
      to_double(realpart(arg)),
      to_double(imagpart(arg)),
      alpha,
      1,
      n + 1,
      cyr,
      cyi,
      0,
      0,
    )
    // We should check for errors here based on the value of v-ierr.
    bessel__report_ierr("zbesk", ierr)
    bessel__cfl(cyr[n], cyi[n])
  }
}

// ---------------------------------------------------------------------------
// Expansion of Bessel J and Y functions of half-integral order.
//
// From A&S 10.1.1, we have
//
// J[n+1/2](z) = sqrt(2*z/%pi)*j[n](z)
// Y[n+1/2](z) = sqrt(2*z/%pi)*y[n](z)
//
// where j[n](z) is the spherical bessel function of the first kind and
// y[n](z) is the spherical bessel function of the second kind.
//
// A&S 10.1.8 and 10.1.9 give
//
// j[n](z) = 1/z*[P(n+1/2,z)*sin(z-n*%pi/2) + Q(n+1/2,z)*cos(z-n*%pi/2)]
//
// y[n](z) = (-1)^(n+1)*1/z*[P(n+1/2,z)*cos(z+n*%pi/2) - Q(n+1/2,z)*sin(z+n*%pi/2)]

///|
/// A&S 10.1.10
///
/// j[n](z) = f[n](z)*sin(z) + (-1)^(n+1)*f[-n-1](z)*cos(z)
///
/// f[0](z) = 1/z, f[1](z) = 1/z^2
///
/// f[n-1](z) + f[n+1](z) = (2*n+1)/z*f[n](z)
fn f_fun(n : Value, z : Value) -> Value raise {
  if num_eq(n, Fix(0L)) {
    div(Fix(1L), z)
  } else if num_eq(n, Fix(1L)) {
    div(Fix(1L), mul2(z, z))
  } else if num_eq(n, Fix(-1L)) {
    Fix(0L)
  } else if num_ge(n, Fix(2L)) {
    // f[n+1](z) = (2*n+1)/z*f[n](z) - f[n-1](z) or
    // f[n](z) = (2*n-1)/z*f[n-1](z) - f[n-2](z)
    sub(
      mul2(
        div(num_add(num_add(n, n), Fix(-1L)), z),
        f_fun(num_sub(n, Fix(1L)), z),
      ),
      f_fun(num_sub(n, Fix(2L)), z),
    )
  } else {
    // Negative n
    //
    // f[n-1](z) = (2*n+1)/z*f[n](z) - f[n+1](z) or
    // f[n](z) = (2*n+3)/z*f[n+1](z) - f[n+2](z)
    sub(
      mul2(
        div(num_add(num_add(n, n), Fix(3L)), z),
        f_fun(num_add(n, Fix(1L)), z),
      ),
      f_fun(num_add(n, Fix(2L)), z),
    )
  }
}

///|
/// Compute sqrt(2*z/%pi)
fn root_2z_slpi(z : Value) -> Value raise {
  power(muln_([Fix(2L), z, inv(q_d__pctpi)]), bessel__rat(1, 2))
}

///|
/// Compute J[n+1/2](z)
fn bessel_j_half_order(order : Value, arg : Value) -> Value raise {
  let n = floor1(order)
  let sign : Value = if oddp(n) { Fix(-1L) } else { Fix(1L) }
  let jn = sub(
    mul2(d_expand(f_fun(n, arg)), take(list1(q_p_sin), [arg])),
    muln_([
      sign,
      d_expand(f_fun(num_sub(num_neg(n), Fix(1L)), arg)),
      take(list1(q_p_cos), [arg]),
    ]),
  )
  mul2(root_2z_slpi(arg), jn)
}

///|
/// Compute Y[n+1/2](z)
fn bessel_y_half_order(order : Value, arg : Value) -> Value raise {
  // A&S 10.1.1:
  // Y[n+1/2](z) = sqrt(2*z/%pi)*y[n](z)
  //
  // A&S 10.1.15:
  // y[n](z) = (-1)^(n+1)*j[-n-1](z)
  //
  // So
  // Y[n+1/2](z) = sqrt(2*z/%pi)*(-1)^(n+1)*j[-n-1](z)
  //             = (-1)^(n+1)*sqrt(2*z/%pi)*j[-n-1](z)
  //             = (-1)^(n+1)*J[-n-1/2](z)
  let n = floor1(order)
  let jn = bessel_j_half_order(
    num_sub(num_neg(order), num_div(Fix(1L), Fix(2L))),
    arg,
  )
  if evenp(n) {
    mul2(Fix(-1L), jn)
  } else {
    jn
  }
}

// ---------------------------------------------------------------------------
// Expansion of Bessel I and K functions of half-integral order.

///|
/// See A&S 10.2.12
///
/// I[n+1/2](z) = sqrt(2*z/%pi)*[g[n](z)*sinh(z) + g[-n-1](z)*cosh(z)]
///
/// g[0](z) = 1/z, g[1](z) = -1/z^2
///
/// g[n-1](z) - g[n+1](z) = (2*n+1)/z*g[n](z)
fn g_fun(n : Value, z : Value) -> Value raise {
  if num_eq(n, Fix(0L)) {
    div(Fix(1L), z)
  } else if num_eq(n, Fix(1L)) {
    div(Fix(-1L), mul2(z, z))
  } else if num_ge(n, Fix(2L)) {
    // g[n](z) = g[n-2](z) - (2*n-1)/z*g[n-1](z)
    sub(
      g_fun(num_sub(n, Fix(2L)), z),
      mul2(
        div(num_add(num_add(n, n), Fix(-1L)), z),
        g_fun(num_sub(n, Fix(1L)), z),
      ),
    )
  } else {
    // n is negative
    //
    // g[n](z) = (2*n+3)/z*g[n+1](z) + g[n+2](z)
    add2(
      mul2(
        div(num_add(num_add(n, n), Fix(3L)), z),
        g_fun(num_add(n, Fix(1L)), z),
      ),
      g_fun(num_add(n, Fix(2L)), z),
    )
  }
}

///|
/// See A&S 10.2.12
///
/// I[n+1/2](z) = sqrt(2*z/%pi)*[g[n](z)*sinh(z) + g[-n-1](z)*cosh(z)]
fn bessel_i_half_order(order : Value, arg : Value) -> Value raise {
  let order = floor1(order)
  mul2(
    root_2z_slpi(arg),
    add2(
      mul2(d_expand(g_fun(order, arg)), take(list1(q_p_sinh), [arg])),
      mul2(
        d_expand(g_fun(num_neg(num_add(order, Fix(1L))), arg)),
        take(list1(q_p_cosh), [arg]),
      ),
    ),
  )
}

///|
/// See A&S 10.2.15
///
/// sqrt(%pi/2/z)*K[n+1/2](z) = (%pi/2/z)*exp(-z)*sum((n+1/2,k)/(2*z)^k,k,0,n)
///
/// or
///
/// K[n+1/2](z) = sqrt(%pi/2)/sqrt(z)*exp(-z)*sum((n+1/2,k)/(2*z)^k,k,0,n)
///
/// where (A&S 10.1.9)
///
/// (n+1/2,k) = (n+k)!/k!/(n-k)!
///
/// Computes the sum above.
fn k_fun(n : Value, z : Value) -> Value raise {
  let mut sum : Value = Fix(1L)
  let mut term : Value = Fix(1L)
  let mut k : Value = Fix(0L)
  while num_le(k, n) {
    term = mul2(
      term,
      div(
        div(
          num_mul(num_sub(n, k), num_add(num_add(n, k), Fix(1L))),
          num_add(k, Fix(1L)),
        ),
        mul2(Fix(2L), z),
      ),
    )
    sum = add2(sum, term)
    k = num_add(k, Fix(1L))
  }
  sum
}

///|
fn bessel_k_half_order(order : Value, arg : Value) -> Value raise {
  let order = num_truncate(num_abs(order)).0
  mul2(
    muln_([
      power(div(q_d__pctpi, Fix(2L)), bessel__rat(1, 2)),
      power(arg, bessel__rat(-1, 2)),
      power(q_d__pcte, neg(arg)),
    ]),
    k_fun(num_abs(order), arg),
  )
}

// ---------------------------------------------------------------------------
// Realpart und imagpart of Bessel functions
//
// We handle the special cases when we know that the Bessel function is pure
// real or pure imaginary. In all other cases Maxima generates a general
// noun form as result.
//
// To get the complex sign of the order an argument of the Bessel function
// the function $csign is used which calls $sign in a complex mode.
//
// This is an extension of of the algorithm of the function risplit in the
// file rpart.lisp. risplit looks for a risplit-function on the property
// list and call it if available.

///|
/// realpart und imagpart for Bessel J and Bessel I function
fn risplit_bessel_j_or_i(expr : Value) -> Value raise {
  if symval(q_ear_debug_bessel).truthy() {
    format(t, "~&RISPLIT-BESSEL-J with ~A~%", [expr]) |> ignore
  }
  let order = cadr(expr)
  let arg = caddr(expr)
  let sign_order = d_csign(cadr(expr))
  let sign_arg = d_csign(caddr(expr))
  if symval(q_ear_debug_bessel).truthy() {
    format(t, "~&   : order      = ~A~%", [order]) |> ignore
    format(t, "~&   : arg        = ~A~%", [arg]) |> ignore
    format(t, "~&   : sign-order = ~A~%", [sign_order]) |> ignore
    format(t, "~&   : sign-arg   = ~A~%", [sign_arg]) |> ignore
  }
  if memq(sign_order, list2(q_d_complex, q_d_imaginary)).truthy() ||
    eq(sign_arg, q_d_complex) {
    // order or arg are complex, return general noun-form
    risplit_noun(expr)
  } else if eq(sign_arg, q_d_imaginary) {
    // arg is pure imaginary
    if d_oddp(order).truthy() || d_featurep(order, q_d_odd).truthy() {
      // order is an odd integer, pure imaginary noun-form
      cons(Fix(0L), muln_([Fix(-1L), q_d__pcti, expr]))
    } else if d_evenp(order).truthy() || d_featurep(order, q_d_even).truthy() {
      // order is an even integer, real noun-form
      cons(expr, Fix(0L))
    } else {
      // order is not an odd or even integer, or Maxima can not determine
      // it, return general noun-form
      risplit_noun(expr)
    }
  } else if maxima_integerp(order).truthy() ||
    memq(sign_arg, list2(q_d_pos, q_d_pz)).truthy() {
    // At this point order and arg are real. We have to look for some
    // special cases involing a negative arg.
    // arg is positive or order an integer, real noun-form
    cons(expr, Fix(0L))
  } else if zerop1(
      sub(
        ftake(q_p_truncate, [d_multthru(Fix(2L), e2=order)]),
        d_multthru(Fix(2L), e2=order),
      ),
    ).truthy() {
    // At this point we know that arg is negative or the sign is not known.
    // order is half integral
    if eq(sign_arg, q_d_neg) {
      // order is half integral and arg negative, imaginary noun-form
      cons(Fix(0L), muln_([Fix(-1L), q_d__pcti, expr]))
    } else {
      // the sign of arg or order is not known
      risplit_noun(expr)
    }
  } else {
    // the sign of arg or order is not known
    risplit_noun(expr)
  }
}

///|
/// realpart und imagpart for Bessel K and Bessel Y function
fn risplit_bessel_k_or_y(expr : Value) -> Value raise {
  if symval(q_ear_debug_bessel).truthy() {
    format(t, "~&RISPLIT-BESSEL-K with ~A~%", [expr]) |> ignore
  }
  let order = cadr(expr)
  let arg = caddr(expr)
  let sign_order = d_csign(cadr(expr))
  let sign_arg = d_csign(caddr(expr))
  if symval(q_ear_debug_bessel).truthy() {
    format(t, "~&   : order      = ~A~%", [order]) |> ignore
    format(t, "~&   : arg        = ~A~%", [arg]) |> ignore
    format(t, "~&   : sign-order = ~A~%", [sign_order]) |> ignore
    format(t, "~&   : sign-arg   = ~A~%", [sign_arg]) |> ignore
  }
  if memq(sign_order, list2(q_d_complex, q_d_imaginary)).truthy() ||
    memq(sign_arg, list2(q_d_complex, q_d_imaginary)).truthy() {
    risplit_noun(expr)
  } else if memq(sign_arg, list2(q_d_pos, q_d_pz)).truthy() {
    // At this point order and arg are real valued. We have to look for
    // some special cases involing a negative arg.
    // arg is positive
    cons(expr, Fix(0L))
  } else if !maxima_integerp(order).truthy() &&
    zerop1(
      sub(
        ftake(q_p_truncate, [d_multthru(Fix(2L), e2=order)]),
        d_multthru(Fix(2L), e2=order),
      ),
    ).truthy() {
    // At this point we know that arg is negative or the sign is not known.
    // order is half integral
    if eq(sign_arg, q_d_neg) {
      cons(Fix(0L), muln_([Fix(-1L), q_d__pcti, expr]))
    } else {
      // the sign of arg is not known
      risplit_noun(expr)
    }
  } else {
    // the sign of arg is not known
    risplit_noun(expr)
  }
}

// ---------------------------------------------------------------------------
// Implementation of scaled Bessel I functions
//
// FIXME: The following scaled functions need work. They should be extended
// to match bessel_i, but still carefully compute the scaled value.
//
// I think g0(x) = exp(-x)*I[0](x), g1(x) = exp(-x)*I[1](x), and
// gn(x,n) = exp(-x)*I[n](x), based on some simple numerical evaluations.

///|
/// `(mul (power '$%e (neg (simplifya `((mabs) ,x) nil))) ($bessel_i n x))`
fn bessel__scaled_noun(n : Value, x : Value) -> Value raise {
  mul2(
    power(q_d__pcte, neg(simplifya(mk(q_mabs, [x]), Nil))),
    ftake(q_p_bessel_i, [n, x]),
  )
}

///|
fn d_scaled_bessel_i0(d_x : Value) -> Value raise {
  if mnump(d_x).truthy() && !d_bfloatp(d_x).truthy() {
    // XXX Should we return noun forms if $x is rational?
    bessel__fl(@slatec.dbsi0e(to_double(d_float(d_x))))
  } else {
    bessel__scaled_noun(Fix(0L), d_x)
  }
}

///|
fn d_scaled_bessel_i1(d_x : Value) -> Value raise {
  if mnump(d_x).truthy() && !d_bfloatp(d_x).truthy() {
    // XXX Should we return noun forms if $x is rational?
    bessel__fl(@slatec.dbsi1e(to_double(d_float(d_x))))
  } else {
    bessel__scaled_noun(Fix(1L), d_x)
  }
}

///|
fn d_scaled_bessel_i(d_n : Value, d_x : Value) -> Value raise {
  if mnump(d_x).truthy() &&
    mnump(d_n).truthy() &&
    !d_bfloatp(d_x).truthy() &&
    !d_bfloatp(d_n).truthy() {
    // XXX Should we return noun forms if $n and $x are rational?
    let (n, alpha) = bessel__floor_split(to_double(d_float(d_n)))
    let iarray : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    bessel__dbesi(to_double(d_float(d_x)), alpha, 2, n + 1, iarray)
    bessel__fl(iarray[n])
  } else {
    bessel__scaled_noun(d_n, d_x)
  }
}

// ---------------------------------------------------------------------------
// Implementation of the Hankel 1 and Hankel 2 functions

///|
/// The common simplifier of hankel_1 (sign 1) and hankel_2 (sign -1).
fn bessel__simp_hankel(
  form : Value,
  p__pctsimpflag : Value,
  noun : Value,
  name : String,
  numeric : (Value, Value) -> Value raise,
  plus : Bool,
) -> Value raise {
  bessel__check_arity(form, noun, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let combine = (a : Value, b : Value) => if plus { add2(a, b) } else { sub(a, b) }
  if zerop1(arg).truthy() {
    simp_domain_error(
      list([Str(name + ": " + name + "(~:M,~:M) is undefined."), order, arg]),
    )
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    if num_eq(Fix(0L), d_imagpart(order)) {
      // order is real, arg is real or complex
      complexify(numeric(d_float(order), bessel__cfloat(arg)))
    } else {
      // The order is complex. Use
      //   hankel_1(v,z) = bessel_j(v,z) + %i*bessel_y(v,z)
      //   hankel_2(v,z) = bessel_j(v,z) - %i*bessel_y(v,z)
      // and evaluate using the hypergeometric function
      bessel__complex_order_eval(order, arg, (order, arg) => combine(
        bessel_j_hypergeometric(order, arg),
        mul2(q_d__pcti, bessel_y_hypergeometric(order, arg)),
      ))
    }
  } else if symval(q_d_besselexpand).truthy() &&
    max_numeric_ratio_p(order, Fix(2L)).truthy() {
    // When order is a fraction with a denominator of 2, we can express the
    // result in terms of elementary functions. Use the definition
    // hankel_1(v,z) = bessel_j(v,z)+%i*bessel_y(v,z) (or
    // hankel_2(v,z) = bessel_j(v,z)-%i*bessel_y(v,z))
    let rat_order = max_numeric_ratio_p(order, Fix(2L))
    sratsimp(
      combine(
        bessel_j_half_order(rat_order, arg),
        mul2(q_d__pcti, bessel_y_half_order(rat_order, arg)),
      ),
    )
  } else {
    eqtest(cons(list1(noun), list2(order, arg)), form)
  }
}

///|
/// (def-simplifier hankel_1 (order arg) ...)
fn simp__pcthankel_1(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__simp_hankel(
    form, p__pctsimpflag, q_p_hankel_1, "hankel_1", hankel_1, true,
  )
}

///|
/// `(coerce z '(complex flonum))` as its real and imaginary doubles.
fn bessel__cparts(z : Value) -> (Double, Double) raise {
  (to_double(realpart(z)), to_double(imagpart(z)))
}

///|
/// Numerically compute H1[v](z).
///
/// A&S 9.1.3 says H1[v](z) = J[v](z) + %i * Y[v](z)
fn hankel_1(v : Value, z : Value) -> Value raise {
  let v = to_double(v)
  let z = complex(lfloat(realpart(z)), i=lfloat(imagpart(z)))
  if v < 0.0 {
    // A&S 9.1.6:
    //
    // H1[-v](z) = exp(v*%pi*%i)*H1[v](z)
    //
    // or
    //
    // H1[v](z) = exp(-v*%pi*%i)*H1[-v](z)
    num_mul(cis(Flo(bessel__pi * -v)), hankel_1(Flo(-v), z))
  } else {
    let (n, fnu) = bessel__floor_split(v)
    let (zr, zi) = bessel__cparts(z)
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    @slatec.zbesh(zr, zi, fnu, 1, 1, n + 1, cyr, cyi, 0, 0) |> ignore
    bessel__cfl(cyr[n], cyi[n])
  }
}

///|
/// (def-simplifier hankel_2 (order arg) ...)
fn simp__pcthankel_2(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__simp_hankel(
    form, p__pctsimpflag, q_p_hankel_2, "hankel_2", hankel_2, false,
  )
}

///|
/// Numerically compute H2[v](z).
///
/// A&S 9.1.4 says H2[v](z) = J[v](z) - %i * Y[v](z)
fn hankel_2(v : Value, z : Value) -> Value raise {
  let v = to_double(v)
  let z = complex(lfloat(realpart(z)), i=lfloat(imagpart(z)))
  if v < 0.0 {
    // A&S 9.1.6:
    //
    // H2[-v](z) = exp(-v*%pi*%i)*H2[v](z)
    //
    // or
    //
    // H2[v](z) = exp(v*%pi*%i)*H2[-v](z)
    num_mul(cis(Flo(bessel__pi * v)), hankel_2(Flo(-v), z))
  } else {
    let (n, fnu) = bessel__floor_split(v)
    let (zr, zi) = bessel__cparts(z)
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    @slatec.zbesh(zr, zi, fnu, 1, 2, n + 1, cyr, cyi, 0, 0) |> ignore
    bessel__cfl(cyr[n], cyi[n])
  }
}
