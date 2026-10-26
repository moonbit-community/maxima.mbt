// Port of src/bessel.lisp, part 1: helpers, Bessel J and Bessel Y.
//
// Copyright (c) 1984,1987 by William Schelter, University of Texas.
//
// The numerical routines call the SLATEC/AMOS translations in
// moonbit-community/maxima/slatec. SBCL traps floating-point overflow and invalid
// operations, while the MoonBit SLATEC code computes with raw doubles; a
// result that comes back infinite or NaN is where the Lisp would have
// signalled, so it is turned into the same condition (bessel__fl).

// ---------------------------------------------------------------------------
// Helpers

///|
let bessel__q_d_order : Value = sym("$order")

///|
let bessel__q_d_arg : Value = sym("$arg")

///|
/// The double-float value of CL `pi`.
let bessel__pi : Double = 3.141592653589793

///|
/// Wrap a double computed by SLATEC code: SBCL would have signalled
/// FLOATING-POINT-OVERFLOW (or INVALID-OPERATION) where the result is
/// infinite (or NaN).
fn bessel__fl(d : Double) -> Value raise {
  if d.is_nan() {
    raise LispError::Condition(
      intern("floating-point-invalid-operation"),
      "arithmetic error FLOATING-POINT-INVALID-OPERATION signalled",
      Nil,
    )
  }
  if d.is_inf() {
    raise LispError::Condition(
      intern("floating-point-overflow"),
      "arithmetic error FLOATING-POINT-OVERFLOW signalled",
      Nil,
    )
  }
  Flo(d)
}

///|
/// SBCL's trapped FLOATING-POINT-OVERFLOW.
fn bessel__overflow() -> Unit raise {
  raise LispError::Condition(
    intern("floating-point-overflow"),
    "arithmetic error FLOATING-POINT-OVERFLOW signalled",
    Nil,
  )
}

///|
/// A CL number computed by runtime arithmetic that does not trap (such as
/// EXPT through complex logarithms): raise where SBCL would have signalled.
fn bessel__chk(v : Value) -> Value raise {
  match v {
    Flo(d) => bessel__fl(d) |> ignore
    Cplx(Flo(re), Flo(im)) => {
      bessel__fl(re) |> ignore
      bessel__fl(im) |> ignore
    }
    _ => ()
  }
  v
}

///|
/// The SLATEC routines below compute intermediate values whose overflow SBCL
/// traps even when the routine's result would come out finite; the MoonBit
/// translation computes on with infinities. These checks reproduce the first
/// such trap for huge arguments.
///
/// D9B0MP and D9B1MP (used by DBESJ0, DBESJ1, DBESY0 and DBESY1 for x > 4)
/// form x*x for x > 8, after their own "no precision" message.
fn bessel__d9mp_trap(x : Double) -> Unit raise {
  let y = x.abs()
  if y > 8.0 && (y * y).is_inf() {
    bessel__overflow()
  }
}

///|
fn bessel__dbesj0(x : Double) -> Value raise {
  let r = @slatec.dbesj0(x)
  bessel__d9mp_trap(x)
  bessel__fl(r)
}

///|
fn bessel__dbesj1(x : Double) -> Value raise {
  let r = @slatec.dbesj1(x)
  bessel__d9mp_trap(x)
  bessel__fl(r)
}

///|
fn bessel__dbesy0(x : Double) -> Value raise {
  let r = @slatec.dbesy0(x)
  bessel__d9mp_trap(x)
  bessel__fl(r)
}

///|
fn bessel__dbesy1(x : Double) -> Value raise {
  let r = @slatec.dbesy1(x)
  bessel__d9mp_trap(x)
  bessel__fl(r)
}

///|
/// `(slatec:dbesj x alpha n y 0)` with DBESJ's traps: (x/2)^2 overflows,
/// and for large x the order shift INT(ALPHA-TAU+2) does not fit the
/// INTEGER4 variable (a TYPE-ERROR in the Lisp).
fn bessel__dbesj(
  x : Double,
  alpha : Double,
  n : Int,
  y : FixedArray[Double],
) -> Unit raise {
  if x > 0.0 && alpha >= 0.0 && n >= 1 {
    let xo2 = x * 0.5
    let sxo2 = xo2 * xo2
    if sxo2.is_inf() {
      bessel__overflow()
    }
    let ialp = alpha.trunc()
    let fnu = (ialp + (n - 1).to_double()) + (alpha - ialp)
    if sxo2 > fnu + 1.0 && x > (if fnu > 20.0 { fnu } else { 20.0 }) {
      let tau = 1.34839972492648 * x.sqrt()
      let fnulim = if n == 1 { 60.0 } else { 100.0 }
      if fnu <= tau + fnulim {
        let v = (alpha - tau + 2.0).trunc()
        if v < -2147483648.0 || v > 2147483647.0 {
          raise LispError::Condition(
            intern("type-error"),
            "The value\n  " +
            bessel__int_string(v) +
            "\nis not of type\n  (SIGNED-BYTE 32)",
            Nil,
          )
        }
      }
    }
  }
  @slatec.dbesj(x, alpha, n, y, 0) |> ignore
}

///|
/// The integer printed for the TYPE-ERROR of bessel__dbesj.
fn bessel__int_string(v : Double) -> String raise {
  princ_to_string(floor1(Flo(v)))
}

///|
/// `(slatec:dbesi x alpha kode n y 0)`: DBESI forms (x/2)^2 for x > 0.
fn bessel__dbesi(
  x : Double,
  alpha : Double,
  kode : Int,
  n : Int,
  y : FixedArray[Double],
) -> Unit raise {
  if x > 0.0 && alpha >= 0.0 && n >= 1 && (kode == 1 || kode == 2) {
    let xo2 = x * 0.5
    if (xo2 * xo2).is_inf() {
      bessel__overflow()
    }
  }
  @slatec.dbesi(x, alpha, kode, n, y, 0) |> ignore
}

///|
/// `(slatec:dbesy x fnu n y)`: DBESY forms (x/(fnu+n-1))^2 when
/// fnu+n-1 >= 2.
fn bessel__dbesy(
  x : Double,
  fnu : Double,
  n : Int,
  y : FixedArray[Double],
) -> Unit raise {
  let fn_ = fnu + n.to_double() - 1.0
  if fnu >= 0.0 && x > 0.0 && n >= 1 && fn_ >= 2.0 {
    let xxn = x / fn_
    if (xxn * xxn).is_inf() {
      bessel__overflow()
    }
  }
  @slatec.dbesy(x, fnu, n, y)
}

///|
/// `(slatec:dbesk x fnu kode n y 0)`: DBESK forms (x/(fnu+n-1))^2 when
/// fnu+n-1 >= 2.
fn bessel__dbesk(
  x : Double,
  fnu : Double,
  kode : Int,
  n : Int,
  y : FixedArray[Double],
) -> Unit raise {
  let fn_ = fnu + n.to_double() - 1.0
  if fnu >= 0.0 && x > 0.0 && n >= 1 && fn_ >= 2.0 {
    let zn = x / fn_
    if (zn * zn).is_inf() {
      bessel__overflow()
    }
  }
  @slatec.dbesk(x, fnu, kode, n, y, 0) |> ignore
}

///|
/// `(complex re im)` from two doubles computed by SLATEC code.
fn bessel__cfl(re : Double, im : Double) -> Value raise {
  complex(bessel__fl(re), i=bessel__fl(im))
}

///|
/// `(multiple-value-bind (n alpha) (floor x))` for a double x >= 0, as the
/// number of terms (an Int) and the fractional order.
fn bessel__floor_split(x : Double) -> (Int, Double) raise {
  let (n, alpha) = num_floor(Flo(x))
  (to_int(n), to_double(alpha))
}

///|
/// `(= x 1/2)`
fn bessel__eq_half(x : Value) -> Bool raise {
  num_eq(x, num_div(Fix(1L), Fix(2L)))
}

///|
/// `(zerop (nth-value 1 (truncate x)))`
fn bessel__int_valued(x : Value) -> Bool raise {
  zerop(num_truncate(x).1)
}

///|
/// `(complex ($float ($realpart arg)) ($float ($imagpart arg)))`
fn bessel__cfloat(arg : Value) -> Value raise {
  complex(d_float(d_realpart(arg)), i=d_float(d_imagpart(arg)))
}

///|
/// `'((rat simp) n d)`
fn bessel__rat(n : Int64, d : Int64) -> Value {
  mk_simp(q_rat, [Fix(n), Fix(d)])
}

///|
/// `'((rat) n d)` (unsimplified literal inside backquoted templates)
fn bessel__urat(n : Int64, d : Int64) -> Value {
  mk(q_rat, [Fix(n), Fix(d)])
}

///|
/// The arity check of def-simplifier.
fn bessel__check_arity(
  form : Value,
  noun : Value,
  names : Array[Value],
) -> Unit raise {
  if length(cdr(form)) != names.length() {
    wna_err(
      form,
      required_arg_count=int(names.length()),
      pretty_name=cons(list1(noun), list(names)),
    )
    |> ignore
  }
}

///|
/// The value of bessel_j(0,0) = 1 or bessel_j(v,0) = 0 in the precision of
/// the arguments.
fn bessel__exact_or_float(order : Value, arg : Value, v : Int64) -> Value raise {
  if d_bfloatp(order).truthy() || d_bfloatp(arg).truthy() {
    d_bfloat(Fix(v))
  } else if floatp(order) || floatp(arg) {
    Flo(v.to_double())
  } else {
    Fix(v)
  }
}

///|
/// `(when (plusp ierr) (format t "<name> ierr = ~A~%" ierr))`
fn bessel__report_ierr(name : String, ierr : Int) -> Unit raise {
  if ierr > 0 {
    format(t, name + " ierr = ~A~%", [int(ierr)]) |> ignore
  }
}

///|
/// `(let (($numer t) ($float t) (order ($float order)) (arg ($float arg)))
///    ($float ($rectform (f order arg))))`
fn bessel__complex_order_eval(
  order : Value,
  arg : Value,
  f : (Value, Value) -> Value raise,
) -> Value raise {
  let order = d_float(order)
  let arg = d_float(arg)
  with_specials([(q_d_numer, t), (q_d_float, t)], () => d_float(
    d_rectform(f(order, arg)),
  ))
}

///|
/// The `(%hypergeometric ((mlist)) ((mlist) b) z)` form, simplified.
fn bessel__hyp0f1(b : Value, z : Value) -> Value raise {
  take(list1(q_p_hypergeometric), [list1(list1(q_mlist)), list2(list1(q_mlist), b), z])
}

// ---------------------------------------------------------------------------
// Helper functions for this file

///|
/// If E is a maxima ratio with a denominator of DEN, return the ratio as a
/// Lisp rational. Otherwise NIL.
fn max_numeric_ratio_p(e : Value, den : Value) -> Value raise {
  if listp(e) &&
    eq(caar(e), q_rat) &&
    num_eq(den, third(e)) &&
    integerp(second(e)) {
    num_div(second(e), third(e))
  } else {
    Nil
  }
}

///|
/// Return non-NIL if we should numerically evaluate a bessel function.
/// Basically, both args have to be numbers. If both args are integers, we
/// don't evaluate unless $numer is true.
fn bessel_numerical_eval_p(order : Value, arg : Value) -> Value raise {
  if numberp(order) &&
    complex_number_p(arg).truthy() &&
    (floatp(order) ||
    floatp(d_realpart(arg)) ||
    floatp(d_imagpart(arg))) {
    return t
  }
  lbool(
    symval(q_d_numer).truthy() &&
    numberp(order) &&
    complex_number_p(arg).truthy(),
  )
}

// ---------------------------------------------------------------------------
// Implementation of the Bessel J function

///|
/// Integral of the Bessel function wrt z
fn bessel_j_integral_2(v : Value, z : Value) -> Value raise {
  if eql(v, Fix(0L)) {
    // integrate(bessel_j(0,z),z)
    // = (1/2)*z*(%pi*bessel_j(1,z)*struve_h(0,z)
    //            +bessel_j(0,z)*(2-%pi*struve_h(1,z)))
    mk(q_mtimes, [
      bessel__urat(1, 2),
      z,
      mk(q_mplus, [
        mk(q_mtimes, [
          q_d__pctpi,
          mk(q_p_bessel_j, [Fix(1L), z]),
          mk(q_p_struve_h, [Fix(0L), z]),
        ]),
        mk(q_mtimes, [
          mk(q_p_bessel_j, [Fix(0L), z]),
          mk(q_mplus, [
            Fix(2L),
            mk(q_mtimes, [Fix(-1L), q_d__pctpi, mk(q_p_struve_h, [Fix(1L), z])]),
          ]),
        ]),
      ]),
    ])
  } else if eql(v, Fix(1L)) {
    // integrate(bessel_j(1,z),z) = -bessel_j(0,z)
    mk(q_mtimes, [Fix(-1L), mk(q_p_bessel_j, [Fix(0L), z])])
  } else {
    // http://functions.wolfram.com/03.01.21.0002.01
    // integrate(bessel_j(v,z),z)
    //  = 2^(-v)*z^(v+1)*hypergeometric([v/2+1/2],[v+1,v/2+3/2],-z^2/4)
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
        mk(q_mtimes, [bessel__urat(-1, 4), mk(q_mexpt, [z, Fix(2L)])]),
      ]),
      mk(q_mexpt, [Fix(2L), mk(q_mtimes, [Fix(-1L), v])]),
      mk(q_mexpt, [mk(q_p_gamma, [mk(q_mplus, [Fix(2L), v])]), Fix(-1L)]),
      // The Lisp uses the symbol Z here, not the argument.
      mk(q_mexpt, [q_z, mk(q_mplus, [Fix(1L), v])]),
    ])
  }
}

///|
/// Support a simplim%bessel_j function to handle specific limits
fn simplim_pctbessel_j(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let v = limit(cadr(expr), var_, val, q_think)
  let z = limit(caddr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    // Handle an argument 0 at this place.
    let sgn = d_sign(d_realpart(v))
    if eq(sgn, q_d_neg) && !maxima_integerp(v).truthy() {
      // bessel_j(v,0), Re(v)<0 and v not an integer
      q_d_infinity
    } else if eq(sgn, q_d_zero) && !zerop1(v).truthy() {
      // bessel_j(v,0), Re(v)=0 and v #0
      q_d_und
    } else {
      // Call the simplifier of the function.
      simplify(list3(list1(q_p_bessel_j), v, z))
    }
  } else if eq(z, q_d_inf) || eq(z, q_d_minf) {
    // bessel_j(v,inf) or bessel_j(v,minf)
    Fix(0L)
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list3(list1(q_p_bessel_j), v, z))
  }
}

///|
/// (def-simplifier bessel_j (order arg) ...)
fn simp__pctbessel_j(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_bessel_j, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_bessel_j), list2(order, arg)),
    form,
  )
  if zerop1(arg).truthy() {
    // We handle the different case for zero arg carefully.
    let sgn = d_sign(d_realpart(order))
    if eq(sgn, q_d_zero) && zerop1(d_imagpart(order)).truthy() {
      // bessel_j(0,0) = 1
      bessel__exact_or_float(order, arg, 1L)
    } else if eq(sgn, q_d_pos) || maxima_integerp(order).truthy() {
      // bessel_j(v,0) and Re(v)>0 or v an integer
      bessel__exact_or_float(order, arg, 0L)
    } else if eq(sgn, q_d_neg) && !maxima_integerp(order).truthy() {
      // bessel_j(v,0) and Re(v)<0 and v not an integer
      simp_domain_error(
        list([Str("bessel_j: bessel_j(~:M,~:M) is undefined."), order, arg]),
      )
    } else if eq(sgn, q_d_zero) && !zerop1(d_imagpart(order)).truthy() {
      // bessel_j(v,0) and Re(v)=0 and v # 0
      simp_domain_error(
        list([Str("bessel_j: bessel_j(~:M,~:M) is undefined."), order, arg]),
      )
    } else {
      // No information about the sign of the order
      give_up()
    }
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    // We have numeric order and arg and $numer is true, or we have either
    // the order or arg being floating-point, so let's evaluate it
    // numerically. The numerical routine bessel-j returns a CL number, so
    // we have to add the conversion to a Maxima-complex-number.
    if num_eq(Fix(0L), d_imagpart(order)) {
      // order is real, arg is real or complex
      complexify(bessel_j(d_float(order), bessel__cfloat(arg)))
    } else {
      // order is complex, arg is real or complex
      bessel__complex_order_eval(order, arg, bessel_j_hypergeometric)
    }
  } else if bigfloat_numerical_eval_p(list2(order, arg)).truthy() ||
    complex_bigfloat_numerical_eval_p(list2(order, arg)).truthy() {
    // We have the order or arg being a bigfloat, so evaluate it
    // numerically using the hypergeometric representation bessel_j.
    let ri = risplit(order)
    let re = car(ri)
    let im = cdr(ri)
    if zerop1(im).truthy() &&
      zerop1(sub(re, take(list1(q_d_floor), [re]))).truthy() &&
      mminusp(re).truthy() {
      // bessel_j(-n,z) = (-1)^n*bessel_j(n,z)
      d_rectform(
        mul2(
          power(Fix(-1L), re),
          d_bfloat(bessel_j_hypergeometric(mul2(Fix(-1L), re), arg)),
        ),
      )
    } else {
      d_rectform(d_bfloat(bessel_j_hypergeometric(order, arg)))
    }
  } else if integerp(order) && minusp(order) {
    // Some special cases when the order is an integer.
    // A&S 9.1.5: J[-n](x) = (-1)^n*J[n](x)
    if evenp(order) {
      take(list1(q_p_bessel_j), [num_neg(order), arg])
    } else {
      mul2(Fix(-1L), take(list1(q_p_bessel_j), [num_neg(order), arg]))
    }
  } else if symval(q_d_besselexpand).truthy() &&
    max_numeric_ratio_p(order, Fix(2L)).truthy() {
    // When order is a fraction with a denominator of 2, we can express the
    // result in terms of elementary functions.
    bessel_j_half_order(max_numeric_ratio_p(order, Fix(2L)), arg)
  } else if symval(q_d_bessel_reduce).truthy() &&
    integerp(order) &&
    plusp(order) &&
    num_gt(order, Fix(1L)) {
    // Reduce a bessel function of order > 2 to order 1 and 0.
    // A&S 9.1.27: bessel_j(v,z) = 2*(v-1)/z*bessel_j(v-1,z)-bessel_j(v-2,z)
    sub(
      muln_([
        Fix(2L),
        num_sub(order, Fix(1L)),
        inv(arg),
        take(list1(q_p_bessel_j), [num_sub(order, Fix(1L)), arg]),
      ]),
      take(list1(q_p_bessel_j), [num_sub(order, Fix(2L)), arg]),
    )
  } else if symval(q_d__pctiargs).truthy() &&
    multiplep(arg, q_d__pcti).truthy() {
    // bessel_j(v, %i*x) = (%i*x)^v/(x^v) * bessel_i(v, x)
    // (From http://functions.wolfram.com/03.01.27.0002.01)
    let x = coeff(arg, q_d__pcti, Fix(1L))
    muln_([
      power(mul2(q_d__pcti, x), order),
      inv(power(x, order)),
      take(list1(q_p_bessel_i), [order, x]),
    ])
  } else if symval(q_d_hypergeometric_representation).truthy() {
    bessel_j_hypergeometric(order, arg)
  } else {
    give_up()
  }
}

///|
/// Returns the hypergeometric representation of bessel_j
fn bessel_j_hypergeometric(order : Value, arg : Value) -> Value raise {
  // A&S 9.1.69 / http://functions.wolfram.com/03.01.26.0002.01
  // hypergeometric([],[v+1],-z^2/4)*(z/2)^v/gamma(v+1)
  muln_([
    inv(take(list1(q_p_gamma), [add2(order, Fix(1L))])),
    power(div(arg, Fix(2L)), order),
    bessel__hyp0f1(add2(order, Fix(1L)), neg(div(mul2(arg, arg), Fix(4L)))),
  ])
}

///|
/// Compute value of Bessel function of the first kind of order ORDER.
fn bessel_j(order : Value, arg : Value) -> Value raise {
  if zerop(imagpart(arg)) {
    // We have numeric args and the arg is purely real. Call the
    // real-valued Bessel function when possible.
    let arg = realpart(arg)
    if num_eq(order, Fix(0L)) {
      bessel__dbesj0(to_double(arg))
    } else if num_eq(order, Fix(1L)) {
      bessel__dbesj1(to_double(arg))
    } else if minusp(order) {
      if bessel__int_valued(order) {
        // The order is a negative integer. We use A&S 9.1.5:
        //   J[-n](z) = (-1)^n*J[n](z)
        // and not the Hankel functions.
        if evenp(floor1(order)) {
          bessel_j(num_neg(order), arg)
        } else {
          num_neg(bessel_j(num_neg(order), arg))
        }
      } else {
        // Bessel function of negative order. We use the Hankel functions
        // to compute this:
        //   J[v](z) = (H1[v](z) + H2[v](z)) / 2.
        // This works for negative and positive arg and handles special
        // cases correctly.
        let result = num_mul(
          Flo(0.5),
          num_add(hankel_1(order, arg), hankel_2(order, arg)),
        )
        if bessel__eq_half(num_floor(order).1) {
          // ORDER is a half-integral-value or a float representation,
          // thereof.
          if minusp(arg) {
            // arg is negative, the result is purely imaginary
            complex(Fix(0L), i=imagpart(result))
          } else {
            // arg is positive, the result is purely real
            realpart(result)
          }
        } else {
          // in all other cases general complex result
          result
        }
      }
    } else {
      // We have a real arg and order > 0 and order not 0 or 1 for this
      // case we can call the function dbesj
      let (n, alpha) = bessel__floor_split(to_double(order))
      let jvals : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
      bessel__dbesj(to_double(arg).abs(), alpha, n + 1, jvals)
      let jn = bessel__fl(jvals[n])
      if num_ge(arg, Fix(0L)) {
        jn
      } else if bessel__int_valued(order) {
        // Use analytic continuation formula A&S 9.1.35:
        // J[v](z*exp(m*%pi*%i)) = exp(m*%pi*%i*v)*J[v](z)
        // for an integer m. In particular, for m = 1:
        // J[v](-x) = exp(v*%pi*%i)*J[v](x)
        // and handle special cases: order is an integer
        if evenp(floor1(order)) {
          jn
        } else {
          num_neg(jn)
        }
      } else if bessel__eq_half(num_floor(order).1) {
        // Order is a half-integral-value and we know that arg < 0, so the
        // result is purely imginary.
        if evenp(floor1(order)) {
          complex(Fix(0L), i=jn)
        } else {
          complex(Fix(0L), i=num_neg(jn))
        }
      } else {
        // In all other cases a general complex result
        num_mul(cis(num_mul(order, Flo(bessel__pi))), jn)
      }
    }
  } else if mminusp(order).truthy() {
    // The arg is complex. Use the complex-valued Bessel function.
    // Bessel function of negative order. We use the Hankel function to
    // compute this, because A&S 9.1.3 and 9.1.4 say
    //   H1[v](z) = J[v](z) + %i * Y[v](z)
    // and
    //   H2[v](z) = J[v](z) - %i * Y[v](z).
    // Thus
    //   J[v](z) = (H1[v](z) + H2[v](z)) / 2.
    num_mul(Flo(0.5), num_add(hankel_1(order, arg), hankel_2(order, arg)))
  } else {
    let (n, alpha) = bessel__floor_split(to_double(order))
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let (_nz, ierr) = @slatec.zbesj(
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
    // Should check the return status in v-ierr of this routine.
    bessel__report_ierr("zbesj", ierr)
    bessel__cfl(cyr[n], cyi[n])
  }
}

// ---------------------------------------------------------------------------
// Implementation of the Bessel Y function

///|
/// `(meval `(($ev) ,answer $sum))` or `(simplify ($niceindices answer))`
fn bessel__expand_sum(n : Value, answer : Value) -> Value raise {
  // Expand out the sum if n < 10. Otherwise fix up the indices
  if num_lt(n, Fix(10L)) {
    meval(list3(list1(q_d_ev), answer, q_d_sum))
  } else {
    simplify(d_niceindices(answer))
  }
}

///|
/// Integral of the Bessel Y function wrt z
/// http://functions.wolfram.com/Bessel-TypeFunctions/BesselY/21/01/01/
fn bessel_y_integral_2(n : Value, z : Value) -> Value raise {
  if d_integerp(n).truthy() && num_le(Fix(0L), n) {
    if d_oddp(n).truthy() {
      // integrate(bessel_y(2*N+1,z),z) , N > 0
      // = -bessel_y(0,z) - 2 * sum(bessel_y(2*k,z),k,1,N)
      let k = gensym()
      let answer = mk(q_mplus, [
        mk(q_mtimes, [Fix(-1L), mk(q_p_bessel_y, [Fix(0L), z])]),
        mk(q_mtimes, [
          Fix(-2L),
          mk(q_p_sum, [
            mk(q_p_bessel_y, [mk(q_mtimes, [Fix(2L), k]), z]),
            k,
            Fix(1L),
            mk(q_mtimes, [bessel__urat(1, 2), mk(q_mplus, [Fix(-1L), n])]),
          ]),
        ]),
      ])
      bessel__expand_sum(n, answer)
    } else if d_evenp(n).truthy() {
      // integrate(bessel_y(2*N,z),z) , N > 0
      // = (1/2)*%pi*z*(bessel_y(0,z)*struve_h(-1,z)
      //               +bessel_y(1,z)*struve_h(0,z))
      //    - 2 * sum(bessel_y(2*k+1,z),k,0,N-1)
      let k = gensym()
      let answer = mk(q_mplus, [
        mk(q_mtimes, [
          Fix(-2L),
          mk(q_p_sum, [
            mk(q_p_bessel_y, [
              mk(q_mplus, [Fix(1L), mk(q_mtimes, [Fix(2L), k])]),
              z,
            ]),
            k,
            Fix(0L),
            mk(q_mplus, [Fix(-1L), mk(q_mtimes, [bessel__urat(1, 2), n])]),
          ]),
        ]),
        mk(q_mtimes, [
          bessel__urat(1, 2),
          q_d__pctpi,
          z,
          mk(q_mplus, [
            mk(q_mtimes, [
              mk(q_p_bessel_y, [Fix(0L), z]),
              mk(q_p_struve_h, [Fix(-1L), z]),
            ]),
            mk(q_mtimes, [
              mk(q_p_bessel_y, [Fix(1L), z]),
              mk(q_p_struve_h, [Fix(0L), z]),
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
/// Support a simplim%bessel_y function to handle specific limits
fn simplim_pctbessel_y(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the arguments.
  let v = limit(cadr(expr), var_, val, q_think)
  let z = limit(caddr(expr), var_, val, q_think)
  if zerop1(z).truthy() || eq(z, q_d_zeroa) || eq(z, q_d_zerob) {
    // Handle an argument 0 at this place.
    if zerop1(v).truthy() {
      // bessel_y(0,0)
      q_d_minf
    } else if integerp(v) {
      // bessel_y(n,0), n an integer
      if evenp(v) {
        q_d_minf
      } else if eq(z, q_d_zeroa) {
        q_d_minf
      } else if eq(z, q_d_zerob) {
        q_d_inf
      } else {
        q_d_infinity
      }
    } else if !zerop1(d_realpart(v)).truthy() {
      // bessel_y(v,0), Re(v)#0
      q_d_infinity
    } else if zerop1(d_realpart(v)).truthy() && !zerop1(v).truthy() {
      // bessel_y(v,0), Re(v)=0 and v#0
      q_d_und
    } else {
      // Call the simplifier of the function.
      simplify(list3(list1(q_p_bessel_y), v, z))
    }
  } else if eq(z, q_d_inf) || eq(z, q_d_minf) {
    // bessel_y(v,inf) or bessel_y(v,minf)
    Fix(0L)
  } else {
    // All other cases are handled by the simplifier of the function.
    simplify(list3(list1(q_p_bessel_y), v, z))
  }
}

///|
/// (def-simplifier bessel_y (order arg) ...)
fn simp__pctbessel_y(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  bessel__check_arity(form, q_p_bessel_y, [bessel__q_d_order, bessel__q_d_arg])
  let order = simpcheck(nth(1, form), p__pctsimpflag)
  let arg = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(
    cons(list1(q_p_bessel_y), list2(order, arg)),
    form,
  )
  if zerop1(arg).truthy() {
    // Domain error for a zero argument.
    simp_domain_error(
      list([Str("bessel_y: bessel_y(~:M,~:M) is undefined."), order, arg]),
    )
  } else if complex_float_numerical_eval_p(list2(order, arg)).truthy() {
    // We have numeric order and arg and $numer is true, or we have either
    // the order or arg being floating-point, so let's evaluate it
    // numerically.
    if num_eq(Fix(0L), d_imagpart(order)) {
      // order is real, arg is real or complex
      complexify(bessel_y(d_float(order), bessel__cfloat(arg)))
    } else {
      // order is complex, arg is real or complex
      bessel__complex_order_eval(order, arg, bessel_y_hypergeometric)
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
      d_rectform(d_bfloat(bessel_y_hypergeometric(re, arg)))
    } else {
      give_up()
    }
  } else if integerp(order) && minusp(order) {
    // Special case when the order is an integer.
    // A&S 9.1.5: Y[-n](x) = (-1)^n*Y[n](x)
    if evenp(order) {
      take(list1(q_p_bessel_y), [num_neg(order), arg])
    } else {
      mul2(Fix(-1L), take(list1(q_p_bessel_y), [num_neg(order), arg]))
    }
  } else if symval(q_d_besselexpand).truthy() &&
    max_numeric_ratio_p(order, Fix(2L)).truthy() {
    // When order is a fraction with a denominator of 2, we can express the
    // result in terms of elementary functions. From A&S 10.1.1,
    // 10.1.11-12 and 10.1.15:
    //
    // Y[1/2](z) = -J[-1/2](z) is a function of cos(z).
    // Y[-1/2](z) = J[1/2](z) is a function of sin(z).
    bessel_y_half_order(max_numeric_ratio_p(order, Fix(2L)), arg)
  } else if symval(q_d_bessel_reduce).truthy() &&
    integerp(order) &&
    plusp(order) &&
    num_gt(order, Fix(1L)) {
    // Reduce a bessel function of order > 2 to order 1 and 0.
    // A&S 9.1.27: bessel_y(v,z) = 2*(v-1)/z*bessel_y(v-1,z)-bessel_y(v-2,z)
    sub(
      muln_([
        Fix(2L),
        num_sub(order, Fix(1L)),
        inv(arg),
        take(list1(q_p_bessel_y), [num_sub(order, Fix(1L)), arg]),
      ]),
      take(list1(q_p_bessel_y), [num_sub(order, Fix(2L)), arg]),
    )
  } else if symval(q_d_hypergeometric_representation).truthy() {
    bessel_y_hypergeometric(order, arg)
  } else {
    give_up()
  }
}

///|
/// Returns the hypergeometric representation of bessel_y
fn bessel_y_hypergeometric(order : Value, arg : Value) -> Value raise {
  // http://functions.wolfram.com/03.03.26.0002.01
  // -hypergeometric([],[1-v],-z^2/4)*(2/z)^v*gamma(v)/%pi
  //   - hypergeometric([],[v+1],-z^2/4)*gamma(-v)*cos(%pi*v)*(z/2)^v/%pi
  add2(
    muln_([
      Fix(-1L),
      power(Fix(2L), order),
      inv(power(arg, order)),
      take(list1(q_p_gamma), [order]),
      inv(q_d__pctpi),
      bessel__hyp0f1(sub(Fix(1L), order), neg(div(mul2(arg, arg), Fix(4L)))),
    ]),
    muln_([
      Fix(-1L),
      inv(power(Fix(2L), order)),
      power(arg, order),
      take(list1(q_p_cos), [mul2(order, q_d__pctpi)]),
      take(list1(q_p_gamma), [neg(order)]),
      inv(q_d__pctpi),
      bessel__hyp0f1(add2(Fix(1L), order), neg(div(mul2(arg, arg), Fix(4L)))),
    ]),
  )
}

///|
/// Bessel function of the second kind, Y[n](z), for real or complex z
fn bessel_y(order : Value, arg : Value) -> Value raise {
  if zerop(imagpart(arg)) {
    // We have numeric args and the first arg is purely real. Call the
    // real-valued Bessel function.
    //
    // For negative values, use the analytic continuation formula
    // A&S 9.1.36:
    //
    // Y[v](z*exp(m*%pi*%i)) = exp(-v*m*%pi*%i) * Y[v](z)
    //       + 2*%i*sin(m*v*%pi)*cot(v*%pi)*J[v](z)
    //
    // In particular for m = 1:
    // Y[v](-z) = exp(-v*%pi*%i) * Y[v](z) + 2*%i*cos(v*%pi)*J[v](z)
    let arg = realpart(arg)
    if zerop(order) {
      if num_ge(arg, Fix(0L)) {
        bessel__dbesy0(to_double(arg))
      } else {
        // For v = 0, this simplifies to
        // Y[0](-z) = Y[0](z) + 2*%i*J[0](z)
        // the return value has to be a CL number
        let y0 = bessel__dbesy0(to_double(num_neg(arg)))
        let j0 = bessel__dbesj0(to_double(num_neg(arg)))
        num_add(y0, complex(Fix(0L), i=num_mul(Fix(2L), j0)))
      }
    } else if num_eq(order, Fix(1L)) {
      if num_ge(arg, Fix(0L)) {
        bessel__dbesy1(to_double(arg))
      } else {
        // For v = 1, this simplifies to
        // Y[1](-z) = -Y[1](z) - 2*%i*J[1](v)
        // the return value has to be a CL number
        let y1 = num_neg(bessel__dbesy1(to_double(num_neg(arg))))
        let j1 = bessel__dbesj1(to_double(num_neg(arg)))
        num_add(y1, complex(Fix(0L), i=num_mul(Fix(-2L), j1)))
      }
    } else if minusp(order) {
      if bessel__int_valued(order) {
        // Order is a negative integer or float representation.
        // Use A&S 9.1.5: Y[-n](z) = (-1)^n*Y[n](z).
        if evenp(floor1(order)) {
          bessel_y(num_neg(order), arg)
        } else {
          num_neg(bessel_y(num_neg(order), arg))
        }
      } else {
        // Bessel function of negative order. We use the Hankel functions
        // to compute this:
        //   Y[v](z) = (H1[v](z) - H2[v](z)) / 2 / %i
        let result = num_div(
          num_sub(hankel_1(order, arg), hankel_2(order, arg)),
          complex(Fix(0L), i=Fix(2L)),
        )
        if bessel__eq_half(num_floor(order).1) {
          // ORDER is half-integral-value or a float representation
          // thereof.
          if minusp(arg) {
            // arg is negative, the result is purely imaginary
            complex(Fix(0L), i=imagpart(result))
          } else {
            // arg is positive, the result is purely real
            realpart(result)
          }
        } else {
          // in all other cases general complex result
          result
        }
      }
    } else {
      let (n, alpha) = bessel__floor_split(to_double(order))
      let jvals : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
      // First we do the calculation for an positive argument.
      bessel__dbesy(to_double(arg).abs(), alpha, n + 1, jvals)
      let yn = bessel__fl(jvals[n])
      // Now we look at the sign of the argument
      if num_ge(arg, Fix(0L)) {
        yn
      } else {
        let dpi : Value = Flo(bessel__pi)
        let s1 = cis(num_neg(num_mul(order, dpi)))
        let s2 = num_mul(complex(Fix(0L), i=Fix(2L)), lcos(num_mul(order, dpi)))
        let result = num_add(
          num_mul(s1, yn),
          num_mul(s2, bessel_j(order, num_neg(arg))),
        )
        if bessel__int_valued(order) {
          // ORDER is an integer or a float representation of an integer,
          // and the arg is positive the result is general complex.
          result
        } else if bessel__eq_half(num_floor(order).1) {
          // ORDER is a half-integral-value or an float representation and
          // we have arg < 0. The result is purely imaginary.
          complex(Fix(0L), i=imagpart(result))
        } else {
          // in all other cases general complex result
          result
        }
      }
    }
  } else if minusp(order) {
    // Bessel function of negative order. We use the Hankel function to
    // compute this, because A&S 9.1.3 and 9.1.4 say
    //   H1[v](z) = J[v](z) + %i * Y[v](z)
    // and
    //   H2[v](z) = J[v](z) - %i * Y[v](z).
    // Thus
    //   Y[v](z) = (H1[v](z) - H2[v](z)) / 2 / %i
    num_div(
      num_sub(hankel_1(order, arg), hankel_2(order, arg)),
      complex(Fix(0L), i=Fix(2L)),
    )
  } else {
    let (n, alpha) = bessel__floor_split(to_double(order))
    let cyr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cyi : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cwrkr : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let cwrki : FixedArray[Double] = FixedArray::make(n + 1, 0.0)
    let (_nz, ierr) = @slatec.zbesy(
      to_double(realpart(arg)),
      to_double(imagpart(arg)),
      alpha,
      1,
      n + 1,
      cyr,
      cyi,
      0,
      cwrkr,
      cwrki,
      0,
    )
    // We should check for errors based on the value of v-ierr.
    bessel__report_ierr("zbesy", ierr)
    bessel__cfl(cyr[n], cyi[n])
  }
}
