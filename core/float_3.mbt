// Port of src/float.lisp, part 3: bigfloat implementations of special
// functions.
//
// Some functions here take bigfloat numbers, represented by
// ((bigfloat) <mant> <exp>), but others want just the FP number,
// represented by (<mant> <exp>).  Likewise, some return a bigfloat, some
// return just the FP.
//
// The implementation for the special functions for a complex argument are
// mostly taken from W. Kahan, "Branch Cuts for Complex Elementary Functions
// or Much Ado About Nothing's Sign Bit", in Iserles and Powell (eds.) "The
// State of the Art in Numerical Analysis", pp 165-211, Clarendon Press, 1987

///|
fn float__fpzero() -> Value {
  list([Fix(0L), Fix(0L)])
}

///|
/// Compute exp(x) - 1, but do it carefully to preserve precision when |x|
/// is small.  X is a FP number, and a FP number is returned.
fn fpexpm1(x : Value) -> Value raise {
  if fpgreaterp(fpabs(x), fpone()).truthy() {
    // exp(x) - 1
    fpdifference(fpexp(x), fpone())
  } else {
    // Use Taylor series for exp(x) - 1
    let mut ans = x
    let mut oans = Value::Nil
    let mut term = x
    let mut n = 2
    while !equal(ans, oans) {
      term = fpquotient(fptimes_star(x, term), intofp(int(n)))
      oans = ans
      ans = fpplus(ans, term)
      n += 1
    }
    ans
  }
}

///|
/// log(1+x) for small x.  X is FP number, and a FP number is returned.
fn fplog1p(x : Value) -> Value raise {
  // Use the series (the same one as for FPLOG) only for -1/2 <= x <= 1,
  // where the term ratio u^2 = (x/(x+2))^2 is at most 1/9.  Otherwise, fall
  // back to FPLOG(1+x).
  if fpgreaterp(x, fpone()).truthy() ||
    fplessp(x, fpminus(cdr(symval(q_ear_bfhalf)))).truthy() {
    fplog(fpplus(x, fpone()))
  } else {
    let mut sum = intofp(Fix(0L))
    let mut term = fpquotient(x, fpplus(x, intofp(Fix(2L))))
    let f = fptimes_star(term, term)
    let mut oldans = Value::Nil
    let mut n = 1
    while !equal(sum, oldans) {
      oldans = sum
      sum = fpplus(sum, fpquotient(term, intofp(int(n))))
      term = fptimes_star(term, f)
      n += 2
    }
    fptimes_star(sum, intofp(Fix(2L)))
  }
}

///|
/// sinh(x) for real x.  X is a bigfloat, and a bigfloat is returned.
fn fpsinh(x : Value) -> Value raise {
  // sinh(x) = 1/2*(D(x) + D(x)/(1+D(x))), where D(x) = exp(x) - 1.  But for
  // negative x, use sinh(x) = -sinh(-x) because D(x) approaches -1 for
  // large negative x.
  if equal(Fix(0L), cadr(x)) {
    // Special case: x=0. Return immediately.
    bigfloatp(x)
  } else if fpposp(cdr(x)).truthy() {
    // x is positive.
    let d = fpexpm1(cdr(bigfloatp(x)))
    bcons(
      fpquotient(
        fpplus(d, fpquotient(d, fpplus(d, fpone()))),
        intofp(Fix(2L)),
      ),
    )
  } else {
    // x is negative.
    bcons(fpminus(cdr(fpsinh(bcons(fpminus(cdr(bigfloatp(x))))))))
  }
}

///|
fn big_float_sinh(x : Value, y? : Value = Nil) -> Value raise {
  // The rectform for sinh for complex args should be numerically accurate,
  // so return nil in that case.
  if y is Nil {
    fpsinh(x)
  } else {
    Nil
  }
}

///|
/// asinh(x) for real x.  X is a bigfloat, and a bigfloat is returned.
fn fpasinh(x : Value) -> Value raise {
  // asinh(x) = sign(x) * log(|x| + sqrt(1+x*x))
  //          = sign(x) * log(2*|x| + 1/(|x|+sqrt(1+x*x))), if |x| > 2
  //          = sign(x) * log1p(|x|+x^2/(1+sqrt(1+x*x))), otherwise.
  let fp_x = cdr(bigfloatp(x))
  let absx = fpabs(fp_x)
  let one = fpone()
  let two = intofp(Fix(2L))
  let minus = minusp(car(fp_x))
  let result = if fpgreaterp(absx, two).truthy() {
    // |x| > 2: log(2*|x| + 1/(|x|+sqrt(1+x^2)))
    fplog(
      fpplus(
        fptimes_star(absx, two),
        fpquotient(
          one,
          fpplus(
            absx,
            fproot(bcons(fpplus(one, fptimes_star(absx, absx))), Fix(2L)),
          ),
        ),
      ),
    )
  } else {
    // |x| <= 2: log1p(|x|+x^2/(1+sqrt(1+x^2)))
    let x_starx = fptimes_star(absx, absx)
    fplog1p(
      fpplus(
        absx,
        fpquotient(
          x_starx,
          fpplus(one, fproot(bcons(fpplus(one, x_starx)), Fix(2L))),
        ),
      ),
    )
  }
  if minus {
    bcons(fpminus(result))
  } else {
    bcons(result)
  }
}

///|
fn complex_asinh(x : Value, y : Value) -> (Value, Value) raise {
  // asinh(z) = -%i * asin(%i*z)
  let (u, v) = complex_asin(mul2(Fix(-1L), y), x)
  (v, bcons(fpminus(cdr(u))))
}

///|
fn big_float_asinh(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_asinh(x, y)
    add2(u, mul2(q_d__pcti, v))
  } else {
    fpasinh(x)
  }
}

///|
fn fpasin_core(x : Value) -> Value raise {
  // asin(x) = atan(x/(sqrt(1-x^2))
  //         = sgn(x)*[%pi/2 - atan(sqrt(1-x^2)/abs(x))]
  //
  // Use the first for  0 <= x < 1/2 and the latter for 1/2 < x <= 1.
  //
  // If |x| > 1: asin(x) = %pi/2 - %i*log(|x+sqrt(x^2-1)|)
  let fp_x = cdr(bigfloatp(x))
  if minusp(car(fp_x)) {
    // asin(-x) = -asin(x);
    mul2(Fix(-1L), fpasin(bcons(fpminus(fp_x))))
  } else if fplessp(fp_x, cdr(symval(q_ear_bfhalf))).truthy() {
    // 0 <= x < 1/2: asin(x) = atan(x/sqrt(1-x^2))
    bcons(
      fpatan(
        fpquotient(
          fp_x,
          fproot(
            bcons(
              fptimes_star(fpdifference(fpone(), fp_x), fpplus(fpone(), fp_x)),
            ),
            Fix(2L),
          ),
        ),
      ),
    )
  } else if fpgreaterp(fp_x, fpone()).truthy() {
    // x > 1: asin(x) = %pi/2 - %i*log(|x+sqrt(x^2-1)|)
    let arg = fpplus(
      fp_x,
      fproot(
        bcons(fptimes_star(fpdifference(fp_x, fpone()), fpplus(fp_x, fpone()))),
        Fix(2L),
      ),
    )
    add2(
      div(q_d__pctpi, Fix(2L)),
      muln_([Fix(-1L), q_d__pcti, bcons(fplog(arg))]),
    )
  } else {
    // 1/2 <= x <= 1: asin(x) = %pi/2 - atan(sqrt(1-x^2)/x)
    add2(
      div(q_d__pctpi, Fix(2L)),
      mul2(
        Fix(-1L),
        bcons(
          fpatan(
            fpquotient(
              fproot(
                bcons(
                  fptimes_star(
                    fpdifference(fpone(), fp_x),
                    fpplus(fpone(), fp_x),
                  ),
                ),
                Fix(2L),
              ),
              fp_x,
            ),
          ),
        ),
      ),
    )
  }
}

///|
/// asin(x) for real x.  X is a bigfloat, and a maxima number (real or
/// complex) is returned.
fn fpasin(x : Value) -> Value raise {
  d_bfloat(fpasin_core(x))
}

///|
/// Square root of a complex number (xx, yy).  Both are bigfloats.  FP
/// (non-bigfloat) numbers are returned.
fn complex_sqrt(xx : Value, yy : Value) -> (Value, Value) raise {
  let x = cdr(bigfloatp(xx))
  let y = cdr(bigfloatp(yy))
  let mut rho = fpplus(fptimes_star(x, x), fptimes_star(y, y))
  rho = fpplus(fpabs(x), fproot(bcons(rho), Fix(2L)))
  rho = fpplus(rho, rho)
  rho = fpquotient(fproot(bcons(rho), Fix(2L)), intofp(Fix(2L)))
  let mut eta = rho
  let mut nu = y
  if fpgreaterp(rho, intofp(Fix(0L))).truthy() {
    nu = fpquotient(fpquotient(nu, rho), intofp(Fix(2L)))
    if fplessp(x, intofp(Fix(0L))).truthy() {
      eta = fpabs(nu)
      nu = if minusp(car(y)) { fpminus(rho) } else { rho }
    }
  }
  (eta, nu)
}

///|
/// asin(z) for complex z = x + %i*y.  X and Y are bigfloats.  The real and
/// imaginary parts are returned as bigfloat numbers.
fn complex_asin(x0 : Value, y0 : Value) -> (Value, Value) raise {
  let x = cdr(bigfloatp(x0))
  let y = cdr(bigfloatp(y0))
  let (re_sqrt_1_z, im_sqrt_1_z) = complex_sqrt(
    bcons(fpdifference(intofp(Fix(1L)), x)),
    bcons(fpminus(y)),
  )
  let (re_sqrt_1_plusz, im_sqrt_1_plusz) = complex_sqrt(
    bcons(fpplus(intofp(Fix(1L)), x)),
    bcons(y),
  )
  // Realpart is atan(x/Re(sqrt(1-z)*sqrt(1+z)))
  // Imagpart is asinh(Im(conj(sqrt(1-z))*sqrt(1+z)))
  let re = bcons({
    let d = fpdifference(
      fptimes_star(re_sqrt_1_z, re_sqrt_1_plusz),
      fptimes_star(im_sqrt_1_z, im_sqrt_1_plusz),
    )
    // Check for division by zero.  If we would divide by zero, return pi/2
    // or -pi/2 according to the sign of X.
    if equal(d, float__fpzero()) {
      if fplessp(x, float__fpzero()).truthy() {
        fpminus(fpquotient(float__fppi(), intofp(Fix(2L))))
      } else {
        fpquotient(float__fppi(), intofp(Fix(2L)))
      }
    } else {
      fpatan(fpquotient(x, d))
    }
  })
  let im = fpasinh(
    bcons(
      fpdifference(
        fptimes_star(re_sqrt_1_z, im_sqrt_1_plusz),
        fptimes_star(im_sqrt_1_z, re_sqrt_1_plusz),
      ),
    ),
  )
  (re, im)
}

///|
fn big_float_asin(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_asin(x, y)
    add2(u, mul2(q_d__pcti, v))
  } else {
    fpasin(x)
  }
}

///|
/// tanh(x) for real x.  X is a bigfloat, and a bigfloat is returned.
fn fptanh(x : Value) -> Value raise {
  // tanh(x) = D(2*x)/(2+D(2*x))
  let two = intofp(Fix(2L))
  let fp = cdr(bigfloatp(x))
  let d = fpexpm1(fptimes_star(fp, two))
  bcons(fpquotient(d, fpplus(d, two)))
}

///|
/// tanh(z), z = x + %i*y.  X, Y are bigfloats, and a maxima number is
/// returned.
fn complex_tanh(x : Value, y : Value) -> (Value, Value) raise {
  let tv = cdr(tanbigfloat(list1(y)))
  let beta = fpplus(fpone(), fptimes_star(tv, tv))
  let s = cdr(fpsinh(x))
  let s_hat2 = fptimes_star(s, s)
  let rho = fproot(bcons(fpplus(fpone(), s_hat2)), Fix(2L))
  let den = fpplus(fpone(), fptimes_star(beta, s_hat2))
  (
    bcons(fpquotient(fptimes_star(beta, fptimes_star(rho, s)), den)),
    bcons(fpquotient(tv, den)),
  )
}

///|
fn big_float_tanh(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_tanh(x, y)
    add2(u, mul2(q_d__pcti, v))
  } else {
    fptanh(x)
  }
}

///|
/// tan(z), z = x + %i*y, as -%i*tanh(%i*z), since the rectform() form of
/// tan cancels near its poles. For real z it declines, leaving it to
/// TANBIGFLOAT.
fn big_float_tan(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_tanh(neg(y), x)
    add2(v, mul2(q_d__pcti, neg(u)))
  } else {
    Nil
  }
}

///|
/// atanh(x) for real x, |x| <= 1.  X is a bigfloat, and a bigfloat is
/// returned.
fn fpatanh(x : Value) -> Value raise {
  // atanh(x) = -atanh(-x)
  //          = 1/2*log1p(2*x/(1-x)), x >= 0.5
  //          = 1/2*log1p(2*x+2*x*x/(1-x)), x <= 0.5
  let fp_x = cdr(bigfloatp(x))
  let half = cdr(symval(q_ear_bfhalf))
  if fplessp(fp_x, intofp(Fix(0L))).truthy() {
    // atanh(x) = -atanh(-x)
    mul2(Fix(-1L), fpatanh(bcons(fpminus(fp_x))))
  } else if fpgreaterp(fp_x, fpone()).truthy() {
    // x > 1, so use complex version.
    let (u, v) = complex_atanh(x, bcons(intofp(Fix(0L))))
    add2(u, mul2(q_d__pcti, v))
  } else if fpgreaterp(fp_x, half).truthy() {
    // atanh(x) = 1/2*log1p(2*x/(1-x))
    bcons(
      fptimes_star(
        half,
        fplog1p(
          fpquotient(
            fptimes_star(intofp(Fix(2L)), fp_x),
            fpdifference(fpone(), fp_x),
          ),
        ),
      ),
    )
  } else {
    // atanh(x) = 1/2*log1p(2*x + 2*x*x/(1-x))
    let n2x = fptimes_star(intofp(Fix(2L)), fp_x)
    bcons(
      fptimes_star(
        half,
        fplog1p(
          fpplus(
            n2x,
            fpquotient(fptimes_star(n2x, fp_x), fpdifference(fpone(), fp_x)),
          ),
        ),
      ),
    )
  }
}

///|
/// Derived from atanh z = (log(1 + z) - log(1 - z))/2, following Kahan's
/// "Much ado" paper:
///
///   eta = log(1+4*x/((1-x)^2+y^2))/4
///   nu  = 1/2*atan2(2*y,(1-x)*(1+x)-y^2), or for y = 0, %pi/2, -%pi/2 or 0
///         according to x < -1, x > 1 or |x| <= 1.
fn complex_atanh(x0 : Value, y0 : Value) -> (Value, Value) raise {
  let fpx = cdr(bigfloatp(x0))
  let fpy = cdr(bigfloatp(y0))
  let fp1 = fpone()
  let fp4 = intofp(Fix(4L))
  let beta = if minusp(car(fpx)) { fpminus(fp1) } else { fp1 }
  let y_equals_0 = zerop(car(fpy))
  let x = fptimes_star(beta, fpx)
  let y = fptimes_star(beta, fpminus(fpy))
  let t1_hat2 = fptimes_star(y, y)
  let n1_x = fpdifference(fp1, x)
  // eta = log(1+4*x/((1-x)^2+y^2))/4
  let eta = fpquotient(
    fplog1p(
      fpquotient(fptimes_star(fp4, x), fpplus(fptimes_star(n1_x, n1_x), t1_hat2)),
    ),
    fp4,
  )
  let nu = if y_equals_0 {
    let x_gt_plus_1 = minusp(car(n1_x))
    let x_lt_minus_1 = if x_gt_plus_1 {
      false
    } else {
      minusp(car(fpplus(fpx, fp1)))
    }
    let fppi_val = float__fppi()
    if x_lt_minus_1 {
      fptimes_star(fppi_val, cdr(symval(q_ear_bfhalf)))
    } else if x_gt_plus_1 {
      fptimes_star(fppi_val, cdr(symval(q_ear_bfmhalf)))
    } else {
      float__fpzero()
    }
  } else {
    fptimes_star(
      cdr(symval(q_ear_bfmhalf)),
      fpatan2(
        fptimes_star(intofp(Fix(2L)), y),
        fpdifference(fptimes_star(n1_x, fpplus(fp1, x)), t1_hat2),
      ),
    )
  }
  (bcons(fptimes_star(beta, eta)), bcons(fptimes_star(beta, nu)))
}

///|
fn big_float_atanh(x : Value, y? : Value = Nil) -> Value raise {
  // The poles at +/-1.
  if (y is Nil || zerop1(y).truthy()) && onep1(ftake(q_mabs, [x])).truthy() {
    domain_error(x, q_atanh) |> ignore
  }
  if y.truthy() {
    let (u, v) = complex_atanh(x, y)
    add2(u, mul2(q_d__pcti, v))
  } else {
    fpatanh(x)
  }
}

///|
/// acos(x) for real x.  X is a bigfloat, and a maxima number is returned.
fn fpacos(x : Value) -> Value raise {
  // acos(x) = %pi/2 - asin(x)
  d_bfloat(add2(div(q_d__pctpi, Fix(2L)), mul2(Fix(-1L), fpasin_core(x))))
}

///|
fn complex_acos(x0 : Value, y0 : Value) -> (Value, Value) raise {
  let x = cdr(bigfloatp(x0))
  let y = cdr(bigfloatp(y0))
  let (re_sqrt_1_z, im_sqrt_1_z) = complex_sqrt(
    bcons(fpdifference(intofp(Fix(1L)), x)),
    bcons(fpminus(y)),
  )
  let (re_sqrt_1_plusz, im_sqrt_1_plusz) = complex_sqrt(
    bcons(fpplus(intofp(Fix(1L)), x)),
    bcons(y),
  )
  (
    bcons(
      fptimes_star(
        intofp(Fix(2L)),
        fpatan(fpquotient(re_sqrt_1_z, re_sqrt_1_plusz)),
      ),
    ),
    fpasinh(
      bcons(
        fpdifference(
          fptimes_star(re_sqrt_1_plusz, im_sqrt_1_z),
          fptimes_star(im_sqrt_1_plusz, re_sqrt_1_z),
        ),
      ),
    ),
  )
}

///|
fn big_float_acos(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_acos(x, y)
    add2(u, mul2(q_d__pcti, v))
  } else {
    fpacos(x)
  }
}

///|
/// acosh(w) from w-1 = RE-W-1+%i*IM-W-1 and w+1 = RE-W+1+%i*IM-W+1, which
/// are bigfloats, following Kahan: the real part is
/// asinh(Re(conj(sqrt(w-1))*sqrt(w+1))), the imaginary part
/// 2*atan2(Im(sqrt(w-1)),Re(sqrt(w+1))). A Maxima number is returned.
fn kahan_acosh(
  re_w_1 : Value,
  im_w_1 : Value,
  re_w_plus1 : Value,
  im_w_plus1 : Value,
) -> Value raise {
  let (re_sqrt_w_1, im_sqrt_w_1) = complex_sqrt(re_w_1, im_w_1)
  let (re_sqrt_w_plus1, im_sqrt_w_plus1) = complex_sqrt(re_w_plus1, im_w_plus1)
  add2(
    fpasinh(
      bcons(
        fpplus(
          fptimes_star(re_sqrt_w_1, re_sqrt_w_plus1),
          fptimes_star(im_sqrt_w_1, im_sqrt_w_plus1),
        ),
      ),
    ),
    mul2(
      q_d__pcti,
      bcons(
        fptimes_star(intofp(Fix(2L)), fpatan2(im_sqrt_w_1, re_sqrt_w_plus1)),
      ),
    ),
  )
}

///|
fn big_float_acosh(x : Value, y? : Value = Nil) -> Value raise {
  let y = if y.truthy() { y } else { bcons(intofp(Fix(0L))) }
  kahan_acosh(sub(x, Fix(1L)), y, add2(x, Fix(1L)), y)
}

///|
/// asech(z) = acosh(1/z), from 1/z-1 = (1-z)/z and 1/z+1 = (1+z)/z. These
/// keep the digits that rounding 1/z would lose near z = 1 and z = -1. At 0
/// decline.
fn big_float_asech(x : Value, y? : Value = Nil) -> Value raise {
  let y = if y.truthy() { y } else { bcons(intofp(Fix(0L))) }
  let d = add2(mul2(x, x), mul2(y, y))
  if zerop1(d).truthy() {
    Nil
  } else {
    let im = div(neg(y), d)
    kahan_acosh(
      div(sub(mul2(sub(Fix(1L), x), x), mul2(y, y)), d),
      im,
      div(add2(mul2(add2(Fix(1L), x), x), mul2(y, y)), d),
      im,
    )
  }
}

///|
fn complex_log(x0 : Value, y0 : Value) -> (Value, Value) raise {
  let x = cdr(bigfloatp(x0))
  let y = cdr(bigfloatp(y0))
  let t2 = intofp(Fix(3L))
  let rho = fpplus(fptimes_star(x, x), fptimes_star(y, y))
  let abs_x = fpabs(x)
  let abs_y = fpabs(y)
  let beta = fpmax(abs_x, list1(abs_y))
  let theta = fpmin(abs_x, list1(abs_y))
  // Use the log1p form only when rho = |z|^2 is near 1.  There, forming
  // rho-1 as (beta-1)*(beta+1)+theta^2 avoids the cancellation that
  // log(rho) would suffer.
  let re = if fplessp(cdr(symval(q_ear_bfhalf)), rho).truthy() &&
    fplessp(rho, t2).truthy() {
    fpquotient(
      fplog1p(
        fpplus(
          fptimes_star(fpdifference(beta, fpone()), fpplus(beta, fpone())),
          fptimes_star(theta, theta),
        ),
      ),
      intofp(Fix(2L)),
    )
  } else {
    fpquotient(fplog(rho), intofp(Fix(2L)))
  }
  (re, fpatan2(y, x))
}

///|
/// log(x) of the FP number x = (mantissa exp), where mantissa =
/// frac*2^fpprec, with 1/2 < frac <= 1 and x is frac*2^exp:
/// log(x) = log(frac) + exp*log(2).
fn float__pct_log(x : Value) -> Value raise {
  cdr({
    let extra = 8
    with_special(q_fpprec, float__addi(float__prec(), extra), () => {
      let log_frac = fplog(list([ash(car(x), extra), Fix(0L)]))
      let log_exp = fptimes_star(intofp(second(x)), float__fplog2())
      let result = bcons(fpplus(log_frac, log_exp))
      with_special(q_fpprec, float__addi(float__prec(), -extra), () => bigfloatp(
        result,
      ))
    })
  })
}

///|
fn big_float_log(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_log(x, y)
    add2(bcons(u), mul2(q_d__pcti, bcons(v)))
  } else {
    let fp_x = cdr(bigfloatp(x))
    if onep1(x).truthy() {
      // Special case for log(1).
      bcons(intofp(Fix(0L)))
    } else if fplessp(fp_x, intofp(Fix(0L))).truthy() {
      add2(
        big_float_log(bcons(fpminus(fp_x))),
        mul2(q_d__pcti, bcons(float__fppi())),
      )
    } else {
      bcons(float__pct_log(fp_x))
    }
  }
}

///|
fn big_float_sqrt(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() {
    let (u, v) = complex_sqrt(x, y)
    add2(bcons(u), mul2(q_d__pcti, bcons(v)))
  } else {
    let fp_x = cdr(bigfloatp(x))
    if fplessp(fp_x, intofp(Fix(0L))).truthy() {
      mul2(q_d__pcti, bcons(fproot(bcons(fpminus(fp_x)), Fix(2L))))
    } else {
      bcons(fproot(x, Fix(2L)))
    }
  }
}
