// Port of src/numeric.lisp, part 2: elementary functions, parts,
// rounding, EXPT, TO, EPSILON and the other generic functions, plus the
// continued-fraction / power-series helpers and the ~E/~F/~G formatters.

// ---------------------------------------------------------------------------
// Special functions for real-valued arguments

///|
/// The COMPLEX-BIGFLOAT methods of EXP, SIN, ... that go through MEVAL of
/// the Maxima function `max_op` and convert the result with TO.
fn numeric__cbf_meval(max_op : Value, a : Value) -> Value raise {
  // We should do something better than calling meval
  let arg = add2(bf_real_value(a), mul2(q_d__pcti, bf_imag_value(a)))
  let result = meval(cons(list2(max_op, q_simp), list1(arg)))
  bf_to(result)
}

///|
/// The COMPLEX-BIGFLOAT methods that use float.lisp's BIG-FLOAT-<op>.
fn numeric__cbf_big(
  big_op : (Value, Value) -> Value raise,
  a : Value,
) -> Value raise {
  let res = big_op(bf_real_value(a), bf_imag_value(a))
  bf_to(res)
}

///|
/// bigfloat::abs
fn bf_abs(x : Value) -> Value raise {
  if numeric__clnump(x) {
    return num_abs(x)
  }
  if numeric__bfp(x) {
    return numeric__mkbf(bcons(fpabs(numeric__rvc(x))))
  }
  if numeric__cbfp(x) {
    let re = numeric__mkbf(bf_real_value(x))
    let im = numeric__mkbf(bf_imag_value(x))
    // Bigfloats don't overflow, so we don't need anything special.
    return bf_sqrt(bf_add(bf_mul(re, re), bf_mul(im, im)))
  }
  numeric__no_method("abs", [x])
}

///|
/// bigfloat::sqrt.  NOTE: a CL rational argument gives a machine float, as
/// cl:sqrt does; there is no contagion to bigfloats.
fn bf_sqrt(x : Value) -> Value raise {
  if numeric__clnump(x) {
    return lsqrt(x)
  }
  if numeric__bfp(x) {
    if bf_minusp(x) {
      let re = bf_intofp(Fix(0L))
      return numeric__mkcbf(
        re,
        bcons(fproot(bcons(fpabs(numeric__rvc(x))), Fix(2L))),
      )
    }
    return numeric__mkbf(bcons(fproot(bf_real_value(x), Fix(2L))))
  }
  if numeric__cbfp(x) {
    let (rx, ry) = complex_sqrt(bf_real_value(x), bf_imag_value(x))
    let re = bcons(rx)
    return numeric__mkcbf(re, bcons(ry))
  }
  numeric__no_method("sqrt", [x])
}

///|
/// bigfloat::exp
fn bf_exp(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lexp(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(bcons(fpexp(numeric__rvc(x))))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_exp, x)
  } else {
    numeric__no_method("exp", [x])
  }
}

///|
/// bigfloat::sin
fn bf_sin(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lsin(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(bcons(fpsin(numeric__rvc(x), t)))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_sin, x)
  } else {
    numeric__no_method("sin", [x])
  }
}

///|
/// bigfloat::cos
fn bf_cos(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lcos(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(bcons(fpsin(numeric__rvc(x), Nil)))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_cos, x)
  } else {
    numeric__no_method("cos", [x])
  }
}

///|
/// bigfloat::tan
fn bf_tan(x : Value) -> Value raise {
  if numeric__clnump(x) {
    ltan(x)
  } else if numeric__bfp(x) {
    let r = numeric__rvc(x)
    let s = fpsin(r, t)
    numeric__mkbf(bcons(fpquotient(s, fpsin(r, Nil))))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_tan, x)
  } else {
    numeric__no_method("tan", [x])
  }
}

///|
/// bigfloat::asin
fn bf_asin(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lasin(x)
  } else if numeric__bfp(x) {
    bf_bigfloat(fpasin(bf_real_value(x)))
  } else if numeric__cbfp(x) {
    numeric__cbf_big((a, b) => big_float_asin(a, y=b), x)
  } else {
    numeric__no_method("asin", [x])
  }
}

///|
/// bigfloat::acos
fn bf_acos(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lacos(x)
  } else if numeric__bfp(x) {
    bf_bigfloat(fpacos(bf_real_value(x)))
  } else if numeric__cbfp(x) {
    numeric__cbf_big((a, b) => big_float_acos(a, y=b), x)
  } else {
    numeric__no_method("acos", [x])
  }
}

///|
/// bigfloat::sinh
fn bf_sinh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lsinh(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(fpsinh(bf_real_value(x)))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_sinh, x)
  } else {
    numeric__no_method("sinh", [x])
  }
}

///|
/// bigfloat::cosh
fn bf_cosh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lcosh(x)
  } else if numeric__bfp(x) {
    let r = bf_real_value(x)
    numeric__mkbf(d_bfloat(mk(q_p_cosh, [r])))
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_cosh, x)
  } else {
    numeric__no_method("cosh", [x])
  }
}

///|
/// bigfloat::tanh
fn bf_tanh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    ltanh(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(fptanh(bf_real_value(x)))
  } else if numeric__cbfp(x) {
    numeric__cbf_big((a, b) => big_float_tanh(a, y=b), x)
  } else {
    numeric__no_method("tanh", [x])
  }
}

///|
/// bigfloat::asinh
fn bf_asinh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lasinh(x)
  } else if numeric__bfp(x) {
    numeric__mkbf(fpasinh(bf_real_value(x)))
  } else if numeric__cbfp(x) {
    numeric__cbf_big((a, b) => big_float_asinh(a, y=b), x)
  } else {
    numeric__no_method("asinh", [x])
  }
}

///|
/// bigfloat::atanh
fn bf_atanh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    latanh(x)
  } else if numeric__bfp(x) {
    let r = big_float_atanh(bf_real_value(x))
    if bigfloatp(r).truthy() {
      numeric__mkbf(r)
    } else {
      let re = d_realpart(r)
      numeric__mkcbf(re, d_imagpart(r))
    }
  } else if numeric__cbfp(x) {
    numeric__cbf_big((a, b) => big_float_atanh(a, y=b), x)
  } else {
    numeric__no_method("atanh", [x])
  }
}

///|
/// bigfloat::acosh
fn bf_acosh(x : Value) -> Value raise {
  if numeric__clnump(x) {
    lacosh(x)
  } else if numeric__bfp(x) {
    let r = bf_real_value(x)
    let value = meval(mk_simp(q_p_acosh, [r]))
    if bigfloatp(value).truthy() {
      numeric__mkbf(value)
    } else {
      let re = d_realpart(value)
      numeric__mkcbf(re, d_imagpart(value))
    }
  } else if numeric__cbfp(x) {
    numeric__cbf_meval(q_d_acosh, x)
  } else {
    numeric__no_method("acosh", [x])
  }
}

// ---------------------------------------------------------------------------
// LOG and ATAN

///|
/// ONE-ARG-LOG
fn bf_log1(a : Value) -> Value raise {
  if numeric__clnump(a) {
    return llog(a)
  }
  if numeric__bfp(a) {
    if bf_minusp(a) {
      let re = bcons(fplog(fpabs(numeric__rvc(a))))
      return numeric__mkcbf(re, bcons(numeric__fppi()))
    }
    return numeric__mkbf(bcons(fplog(numeric__rvc(a))))
  }
  if numeric__cbfp(a) {
    let res = big_float_log(bf_real_value(a), y=bf_imag_value(a))
    return bf_bigfloat(res)
  }
  numeric__no_method("one-arg-log", [a])
}

///|
/// TWO-ARG-LOG: log of a to base b.
fn bf_log2(a : Value, b : Value) -> Value raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return llog2(a, b)
  }
  if numeric__numericp(a) && numeric__numericp(b) {
    return bf_div(bf_log1(a), bf_log1(b))
  }
  if numeric__numericp(a) && numeric__clnump(b) {
    let la = bf_log1(a)
    return bf_div(la, bf_log1(bf_bigfloat(b)))
  }
  if numeric__clnump(a) && numeric__numericp(b) {
    let la = bf_log1(bf_bigfloat(a))
    return bf_div(la, bf_log1(b))
  }
  numeric__no_method("two-arg-log", [a, b])
}

///|
/// bigfloat::log (a &optional b)
fn bf_log(a : Value, b? : Value = Nil) -> Value raise {
  if b.truthy() {
    bf_log2(a, b)
  } else {
    bf_log1(a)
  }
}

///|
/// ONE-ARG-ATAN
fn bf_atan1(a : Value) -> Value raise {
  if numeric__clnump(a) {
    return latan(a)
  }
  if numeric__bfp(a) {
    return numeric__mkbf(bcons(fpatan(numeric__rvc(a))))
  }
  if numeric__cbfp(a) {
    // atan(z) = -i * atanh(i*z)
    let iz = bf_complex(bf_neg(bf_imagpart(a)), b=bf_realpart(a))
    let result = bf_atanh(iz)
    return bf_complex(bf_imagpart(result), b=bf_neg(bf_realpart(result)))
  }
  numeric__no_method("one-arg-atan", [a])
}

///|
/// TWO-ARG-ATAN: atan(a/b) with the quadrant of (b, a).
fn bf_atan2(a : Value, b : Value) -> Value raise {
  if numeric__clrealp(a) && numeric__clrealp(b) {
    return latan(a, x=b)
  }
  let abf = numeric__bfp(a)
  let bbf = numeric__bfp(b)
  if (abf && (bbf || numeric__clrealp(b))) || (bbf && numeric__clrealp(a)) {
    let af = if abf { numeric__rvc(a) } else { numeric__fpc(a) }
    let bf = if bbf { numeric__rvc(b) } else { numeric__fpc(b) }
    return numeric__mkbf(bcons(fpatan2(af, bf)))
  }
  numeric__no_method("two-arg-atan", [a, b])
}

///|
/// bigfloat::atan (a &optional b)
fn bf_atan(a : Value, b? : Value = Nil) -> Value raise {
  if b.truthy() {
    bf_atan2(a, b)
  } else {
    bf_atan1(a)
  }
}

///|
/// bigfloat::scale-float (a n): a * 2^n for floats and BIGFLOATs.
fn bf_scale_float(a : Value, n : Value) -> Value raise {
  if a is Flo(d) && integerp(n) {
    return Flo(scale_float(d, to_int(n)))
  }
  if numeric__bfp(a) && integerp(n) {
    let rv = bf_real_value(a)
    if zerop(second(rv)) {
      return numeric__mkbf(bcons(numeric__zero_fp()))
    }
    let mantissa = second(rv)
    let exp = third(rv)
    return numeric__mkbf(bcons(list2(mantissa, bf_add(exp, n))))
  }
  numeric__no_method("scale-float", [a, n])
}

// ---------------------------------------------------------------------------
// REALPART, IMAGPART, CONJUGATE, PHASE, CIS

///|
/// bigfloat::realpart
fn bf_realpart(a : Value) -> Value raise {
  if numeric__clnump(a) {
    realpart(a)
  } else if numeric__numericp(a) {
    numeric__mkbf(bf_real_value(a))
  } else {
    numeric__no_method("realpart", [a])
  }
}

///|
/// bigfloat::imagpart
fn bf_imagpart(a : Value) -> Value raise {
  if numeric__clnump(a) {
    imagpart(a)
  } else if numeric__bfp(a) {
    numeric__mkbf(bf_intofp(Fix(0L)))
  } else if numeric__cbfp(a) {
    numeric__mkbf(bf_imag_value(a))
  } else {
    numeric__no_method("imagpart", [a])
  }
}

///|
/// bigfloat::conjugate
fn bf_conjugate(a : Value) -> Value raise {
  if numeric__clnump(a) {
    conjugate(a)
  } else if numeric__bfp(a) {
    numeric__mkbf(bf_real_value(a))
  } else if numeric__cbfp(a) {
    let re = bf_real_value(a)
    numeric__mkcbf(re, bcons(fpminus(numeric__ivc(a))))
  } else {
    numeric__no_method("conjugate", [a])
  }
}

///|
/// bigfloat::phase
fn bf_phase(a : Value) -> Value raise {
  if numeric__clnump(a) {
    return phase(a)
  }
  if numeric__bfp(a) {
    let r = numeric__rvc(a)
    if num_ge(car(r), Fix(0L)) {
      return numeric__mkbf(bcons(numeric__zero_fp()))
    } else {
      return numeric__mkbf(bcons(numeric__fppi()))
    }
  }
  if numeric__cbfp(a) {
    return numeric__mkbf(bcons(fpatan2(numeric__ivc(a), numeric__rvc(a))))
  }
  numeric__no_method("phase", [a])
}

///|
/// bigfloat::cis: cos(a) + %i*sin(a) for real a.
fn bf_cis(a : Value) -> Value raise {
  if numeric__clrealp(a) {
    return cis(a)
  }
  if numeric__bfp(a) {
    let re = bcons(fpsin(numeric__rvc(a), Nil))
    return numeric__mkcbf(re, bcons(fpsin(numeric__rvc(a), t)))
  }
  numeric__no_method("cis", [a])
}

// ---------------------------------------------------------------------------
// COMPLEX

///|
/// ONE-ARG-COMPLEX
fn bf_complex1(a : Value) -> Value raise {
  if numeric__clrealp(a) {
    make_complex(a, Fix(0L))
  } else if numeric__bfp(a) {
    let re = bf_real_value(a)
    numeric__mkcbf(re, bf_intofp(Fix(0L)))
  } else {
    numeric__no_method("one-arg-complex", [a])
  }
}

///|
/// TWO-ARG-COMPLEX
fn bf_complex2(a : Value, b : Value) -> Value raise {
  if numeric__clrealp(a) && numeric__clrealp(b) {
    return make_complex(a, b)
  }
  let abf = numeric__bfp(a)
  let bbf = numeric__bfp(b)
  if (abf && (bbf || numeric__clrealp(b))) || (bbf && numeric__clrealp(a)) {
    let re = if abf { bf_real_value(a) } else { bf_intofp(a) }
    let im = if bbf { bf_real_value(b) } else { bf_intofp(b) }
    return numeric__mkcbf(re, im)
  }
  numeric__no_method("two-arg-complex", [a, b])
}

///|
/// bigfloat::complex (a &optional b)
fn bf_complex(a : Value, b? : Value = Nil) -> Value raise {
  if b.truthy() {
    bf_complex2(a, b)
  } else {
    bf_complex1(a)
  }
}

// ---------------------------------------------------------------------------
// FLOOR, CEILING, TRUNCATE, ROUND and their F-variants.  Each returns the
// two CL values (quotient, remainder) as a tuple.

///|
/// Float version of a CL integer quotient (for FFLOOR and friends).
fn numeric__fquot(q : Value) -> Value raise {
  Flo(to_double(q))
}

///|
/// UNARY-FLOOR of a BIGFLOAT: an integer.
fn bf_unary_floor(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-floor", [a])
  }
  // fpentier truncates to zero, so adjust for negative numbers
  let trunc = fpentier(bf_real_value(a))
  if bf_minusp(a) {
    // If the truncated value is the same as the original, there's nothing
    // to do because A was an integer.  Otherwise, we need to subtract 1 to
    // make it the floor.
    if bf_eq(a, trunc) {
      trunc
    } else {
      bf_sub1(trunc)
    }
  } else {
    trunc
  }
}

///|
/// UNARY-FFLOOR of a BIGFLOAT.
fn bf_unary_ffloor(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-ffloor", [a])
  }
  // We can probably do better than converting to an integer and
  // converting back to a float.
  numeric__mkbf(bf_intofp(bf_unary_floor(a)))
}

///|
/// UNARY-TRUNCATE of a BIGFLOAT.
fn bf_unary_truncate(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-truncate", [a])
  }
  fpentier(bf_real_value(a))
}

///|
/// UNARY-FTRUNCATE of a BIGFLOAT.
fn bf_unary_ftruncate(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-ftruncate", [a])
  }
  numeric__mkbf(bf_intofp(bf_unary_truncate(a)))
}

///|
/// UNARY-CEILING of a BIGFLOAT.
fn bf_unary_ceiling(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-ceiling", [a])
  }
  // fpentier truncates to zero, so adjust for positive numbers.
  if bf_minusp(a) {
    fpentier(bf_real_value(a))
  } else {
    fpentier(bf_real_value(bf_add(a, Fix(1L))))
  }
}

///|
/// UNARY-FCEILING of a BIGFLOAT.
fn bf_unary_fceiling(a : Value) -> Value raise {
  if !numeric__bfp(a) {
    return numeric__no_method("unary-fceiling", [a])
  }
  numeric__mkbf(bf_intofp(bf_unary_ceiling(a)))
}

///|
/// The BIGFLOAT method shared by FLOOR, FFLOOR, TRUNCATE, ...: `unary` is
/// the matching UNARY-xxx function; `eql_test` selects the (EQL DIVISOR 1)
/// test of TRUNCATE/CEILING instead of (= DIVISOR 1).
fn numeric__bf_rounding(
  a : Value,
  divisor : Value,
  unary : (Value) -> Value raise,
  eql_test : Bool,
) -> (Value, Value) raise {
  let one = if eql_test { eql(divisor, Fix(1L)) } else { bf_eq(Fix(1L), divisor) }
  if one {
    let int = unary(a)
    (int, bf_sub(a, int))
  } else {
    let q = unary(bf_div(a, divisor))
    (q, bf_sub(a, bf_mul(q, divisor)))
  }
}

///|
/// bigfloat::floor (a &optional (divisor 1))
fn bf_floor(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    num_floor(a, b=divisor)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_floor, false)
  } else {
    numeric__no_method("floor", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::ffloor (a &optional (divisor 1))
fn bf_ffloor(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    let (q, r) = num_floor(a, b=divisor)
    (numeric__fquot(q), r)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_ffloor, false)
  } else {
    numeric__no_method("ffloor", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::truncate (a &optional (divisor 1))
fn bf_truncate(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    num_truncate(a, b=divisor)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_truncate, true)
  } else {
    numeric__no_method("truncate", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::ftruncate (a &optional (divisor 1))
fn bf_ftruncate(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    let (q, r) = num_truncate(a, b=divisor)
    (numeric__fquot(q), r)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_ftruncate, true)
  } else {
    numeric__no_method("ftruncate", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::ceiling (a &optional (divisor 1))
fn bf_ceiling(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    num_ceiling(a, b=divisor)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_ceiling, true)
  } else {
    numeric__no_method("ceiling", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::fceiling (a &optional (divisor 1))
fn bf_fceiling(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    let (q, r) = num_ceiling(a, b=divisor)
    (numeric__fquot(q), r)
  } else if numeric__bfp(a) {
    numeric__bf_rounding(a, divisor, bf_unary_fceiling, true)
  } else {
    numeric__no_method("fceiling", [a, divisor]) |> ignore
    (Nil, Nil)
  }
}

///|
/// bigfloat::round (a &optional (divisor 1)); the BIGFLOAT method is
/// stolen from CMUCL.
fn bf_round(a : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(a) {
    return num_round(a, b=divisor)
  }
  if !numeric__bfp(a) {
    numeric__no_method("round", [a, divisor]) |> ignore
    return (Nil, Nil)
  }
  let (tru, rem) = bf_truncate(a, divisor~)
  if bf_zerop(rem) {
    return (tru, rem)
  }
  let thresh = bf_div(bf_abs(divisor), Fix(2L))
  if bf_gt(rem, thresh) || (bf_eq(thresh, rem) && oddp(tru)) {
    if bf_minusp(divisor) {
      (bf_sub(tru, Fix(1L)), bf_add(rem, divisor))
    } else {
      (bf_add(tru, Fix(1L)), bf_sub(rem, divisor))
    }
  } else {
    let mthresh = bf_neg(thresh)
    if bf_lt(rem, mthresh) || (bf_eq(mthresh, rem) && oddp(tru)) {
      if bf_minusp(divisor) {
        (bf_add(tru, Fix(1L)), bf_sub(rem, divisor))
      } else {
        (bf_sub(tru, Fix(1L)), bf_add(rem, divisor))
      }
    } else {
      (tru, rem)
    }
  }
}

///|
/// bigfloat::fround: same as ROUND, but returns the first value as a float.
fn bf_fround(number : Value, divisor? : Value = Fix(1L)) -> (Value, Value) raise {
  if numeric__clnump(number) {
    let (q, r) = num_round(number, b=divisor)
    return (numeric__fquot(q), r)
  }
  if !numeric__bfp(number) {
    numeric__no_method("fround", [number, divisor]) |> ignore
    return (Nil, Nil)
  }
  let (res, rem) = bf_round(number, divisor~)
  (bf_bigfloat(res), rem)
}

// ---------------------------------------------------------------------------
// EXPT

///|
/// `(complex (bigfloat 1))` or `(bigfloat 1)`: the value of x^0.
fn numeric__expt_one(cplx : Bool) -> Value raise {
  if cplx {
    bf_complex(bf_bigfloat(Fix(1L)))
  } else {
    bf_bigfloat(Fix(1L))
  }
}

///|
/// x^n for small |n| by multiplication; None for other n.
fn numeric__expt_small(a : Value, b : Value) -> Value? raise {
  let eqk = (k : Int64) => bf_eq(Fix(k), b)
  if eqk(1L) {
    Some(a)
  } else if eqk(-1L) {
    Some(bf_inv(a))
  } else if eqk(2L) {
    Some(bf_mul(a, a))
  } else if eqk(-2L) {
    Some(bf_inv(bf_mul(a, a)))
  } else if eqk(3L) {
    Some(bf_mul(bf_mul(a, a), a))
  } else if eqk(-3L) {
    Some(bf_inv(bf_mul(bf_mul(a, a), a)))
  } else if eqk(4L) {
    let a2 = bf_mul(a, a)
    Some(bf_mul(a2, a2))
  } else if eqk(-4L) {
    let a2 = bf_mul(a, a)
    Some(bf_inv(bf_mul(a2, a2)))
  } else {
    None
  }
}

///|
/// exp(b*log(a)) with extra precision.
fn numeric__expt_by_log(a : Value, b : Value) -> Value raise {
  bf_with_extra_precision(bf_expt_extra_bits(a, b), [a, b], vs => bf_exp(
    bf_mul(vs[1], bf_log(vs[0])),
  ))
}

///|
/// bigfloat::expt (a b)
fn bf_expt(a : Value, b : Value) -> Value raise {
  if numeric__clnump(a) && numeric__clnump(b) {
    return expt(a, b)
  }
  if numeric__bfp(a) && integerp(b) {
    // Handle a^b a little more carefully because the result is known to be
    // real when a is real and b is an integer.
    if zerop(b) {
      return bf_bigfloat(Fix(1L))
    }
    if bf_zerop(a) && plusp(b) {
      // 0^b, for positive b
      return bf_mul(a, b)
    }
    // Handle a few special cases using multiplication.
    if b is Fix(n) && n >= -4L && n <= 4L {
      match numeric__expt_small(a, b) {
        Some(v) => return v
        None => ()
      }
    }
    if bf_minusp(a) {
      // a^b = exp(b*log(|a|) + %i*%pi*b) = (-1)^b*exp(b*log(|a|))
      return bf_with_extra_precision(bf_expt_extra_bits(a, b), [a, b], vs => bf_mul(
        bf_exp(bf_mul(vs[1], bf_log(bf_abs(vs[0])))),
        if oddp(vs[1]) {
          Fix(-1L)
        } else {
          Fix(1L)
        },
      ))
    }
    return numeric__expt_by_log(a, b)
  }
  if numeric__numericp(a) && numeric__numericp(b) {
    // This needs more work
    if bf_zerop(b) {
      // CLHS says if the power is 0, the answer is 1 of the appropriate
      // type.
      return numeric__expt_one(numeric__cbfp(a) || numeric__cbfp(b))
    }
    if bf_zerop(a) && bf_plusp(bf_realpart(b)) {
      return bf_mul(a, b)
    }
    if bf_realp(b) {
      let tb = bf_truncate(b).0
      if bf_eq(tb, b) {
        // Use the numeric^number method because it can be much more
        // accurate when b is an integer.
        return bf_expt(a, bf_truncate(b).0)
      }
    }
    return numeric__expt_by_log(a, b)
  }
  if numeric__clnump(a) && numeric__numericp(b) {
    if bf_zerop(b) {
      return numeric__expt_one(a is Cplx(_, _) || numeric__cbfp(b))
    }
    if zerop(a) && bf_plusp(bf_realpart(b)) {
      return bf_mul(a, b)
    }
    if bf_realp(b) {
      let tb = bf_truncate(b).0
      if bf_eq(tb, b) {
        return bf_with_extra_precision(bf_expt_extra_bits(a, b), [a, b], vs => bf_intofp(
          bf_expt(vs[0], bf_truncate(vs[1]).0),
        ))
      }
    }
    return bf_with_extra_precision(bf_expt_extra_bits(a, b), [a, b], vs => bf_exp(
      bf_mul(vs[1], bf_log(bf_bigfloat(vs[0]))),
    ))
  }
  if numeric__numericp(a) && numeric__clnump(b) {
    if zerop(b) {
      return numeric__expt_one(numeric__cbfp(a) || b is Cplx(_, _))
    }
    if bf_zerop(a) && plusp(realpart(b)) {
      return bf_mul(a, b)
    }
    // Handle a few special cases using multiplication.
    match numeric__expt_small(a, b) {
      Some(v) => return v
      None => ()
    }
    return bf_with_extra_precision(bf_expt_extra_bits(a, b), [a, b], vs => bf_exp(
      bf_mul(bf_bigfloat(vs[1]), bf_log(vs[0])),
    ))
  }
  numeric__no_method("expt", [a, b])
}

// ---------------------------------------------------------------------------
// TO, MAYBE-TO, %TO

///|
/// TO takes a maxima number and converts it.  Floats remain floats, maxima
/// rationals are converted to CL rationals.  Maxima bigfloats are converted
/// to BIGFLOATs.  Maxima complex numbers are converted to CL complex
/// numbers or to COMPLEX-BIGFLOATs.
fn bf_to(maxima_num : Value, imag? : Value = Nil) -> Value raise {
  let result = match errset(() => bf_p_to(maxima_num, imag~)) {
    Some(v) => v
    None => Nil
  }
  if result.truthy() {
    result
  } else {
    merror(
      Str("BIGFLOAT: unable to convert ~M to a CL or BIGFLOAT number."),
      list1(
        if imag.truthy() {
          add2(maxima_num, mul2(imag, q_d__pcti))
        } else {
          maxima_num
        },
      ),
    )
  }
}

///|
/// Like TO, but if the maxima number can't be converted to a CL number or
/// BIGFLOAT, just return the maxima number.
fn bf_maybe_to(maxima_num : Value, imag? : Value = Nil) -> Value raise {
  let result = match errset(() => bf_p_to(maxima_num, imag~)) {
    Some(v) => v
    None => Nil
  }
  if result.truthy() {
    result
  } else if imag.truthy() {
    add2(maxima_num, imag)
  } else {
    maxima_num
  }
}

///|
/// The predicate passed to COMPLEX-NUMBER-P by %TO: a CL real, a bfloat,
/// or a Maxima rational.
fn numeric__to_part_p(x : Value) -> Bool raise {
  numeric__clrealp(x) || d_bfloatp(x).truthy() || is_op(x, q_rat)
}

///|
/// %TO: the conversion done by TO, without the error handling.
fn bf_p_to(maxima_num : Value, imag? : Value = Nil) -> Value raise {
  if imag.truthy() {
    let re = bf_to(maxima_num)
    return bf_complex(re, b=bf_to(imag))
  }
  if numeric__clnump(maxima_num) {
    return maxima_num
  }
  if eq(maxima_num, q_d__pcti) {
    // Convert %i to an exact complex rational.
    return Cplx(Fix(0L), Fix(1L))
  }
  if maxima_num is Cons(_) {
    // Some kind of maxima number
    if ratnump(maxima_num).truthy() {
      return bf_div(second(maxima_num), third(maxima_num))
    }
    if d_bfloatp(maxima_num).truthy() {
      return bf_bigfloat(maxima_num)
    }
    if complex_number_p(
        maxima_num,
        ntypep=lfunc("%to-lambda", args => lbool(
          numeric__to_part_p(arg(args, 0)),
        )),
      ).truthy() {
      // We have some kind of complex number whose parts are a real, a
      // bfloat, or a Maxima rational.
      let re = d_realpart(maxima_num)
      let im = d_imagpart(maxima_num)
      return bf_to(re, imag=im)
    }
    return Nil
  }
  if numeric__numericp(maxima_num) {
    return maxima_num
  }
  raise LispError::SimpleError(
    "BIGFLOAT: unable to convert to a CL or BIGFLOAT number.",
  )
}

// ---------------------------------------------------------------------------
// EPSILON, decoding, FLOAT, RANDOM, SIGNUM, ...

///|
/// EPSILON: the float epsilon value for the given float type.
fn bf_epsilon(x : Value) -> Value raise {
  match x {
    Flo(_) => Flo(double_float_epsilon)
    Cplx(r, _) => bf_epsilon(r)
    _ =>
      if numeric__bfp(x) {
        // epsilon is just above 2^(-fpprec).
        let p = symval(q_fpprec)
        numeric__mkbf(
          bcons(
            list2(
              one_plus(ash(Fix(1L), to_int(one_minus(p)))),
              num_neg(one_minus(p)),
            ),
          ),
        )
      } else if numeric__cbfp(x) {
        bf_epsilon(bf_realpart(x))
      } else {
        numeric__no_method("epsilon", [x])
      }
  }
}

///|
/// bigfloat::integer-decode-float: (mantissa, exponent, sign).
fn bf_integer_decode_float(x : Value) -> (Value, Value, Value) raise {
  if x is Flo(d) {
    let (m, e, s) = integer_decode_float(d)
    return (from_big(m), int(e), int(s))
  }
  if numeric__bfp(x) {
    let r = bf_real_value(x)
    return (
      num_abs(second(r)),
      num_sub(third(r), third(first(r))),
      signum(second(r)),
    )
  }
  numeric__no_method("integer-decode-float", [x]) |> ignore
  (Nil, Nil, Nil)
}

///|
/// bigfloat::decode-float: (significand, exponent, sign).
fn bf_decode_float(x : Value) -> (Value, Value, Value) raise {
  if x is Flo(d) {
    let (m, e, s) = decode_float(d)
    return (Flo(m), int(e), Flo(s))
  }
  if numeric__bfp(x) {
    let r = bf_real_value(x)
    return (
      numeric__mkbf(bcons(list2(num_abs(second(r)), Fix(0L)))),
      third(r),
      bf_bigfloat(signum(second(r))),
    )
  }
  numeric__no_method("decode-float", [x]) |> ignore
  (Nil, Nil, Nil)
}

///|
/// Like Maxima's fp2flo, but for single-float numbers.  The port has no
/// single floats: the result is a double rounded to 24 bits.
fn bf_fp2single(l : Value) -> Value raise {
  let precision = caddar(l)
  let exponent = caddr(l)
  let fpprec_single : Value = Fix(24L)
  with_specials([(q_fpprec, fpprec_single), (q_n_starm, Fix(0L))], () => {
    // Round the mantissa to the number of bits of precision of the
    // machine, and then convert it to a floating point fraction.  We have
    // 0.5 <= mantissa < 1
    let mantissa = quot(fpround(cadr(l)), expt(Flo(2.0), fpprec_single))
    // Multiply the mantissa by the exponent portion.
    let e = bf_op_plus(
      list([exponent, num_neg(precision), symval(q_n_starm), fpprec_single]),
    )
    if num_ge(num_abs(e), Fix(129L)) {
      merror(
        Str("FP2SINGLE: floating point overflow converting ~:M to float."),
        list1(l),
      )
    } else {
      Flo(scale_float(to_double(mantissa), to_int(e)))
    }
  })
}

///|
/// bigfloat::float (x y): x converted to the float format of y.
fn bf_float(x : Value, y : Value) -> Value raise {
  if numeric__clrealp(x) && y is Flo(_) {
    return Flo(to_double(x))
  }
  if numeric__clrealp(x) && numeric__bfp(y) {
    return bf_bigfloat(x)
  }
  if numeric__bfp(x) && y is Flo(_) {
    // Every float in the port is a maxima::flonum (double-float).
    return fp2flo(bf_real_value(x))
  }
  numeric__no_method("float", [x, y])
}

///|
/// bigfloat::random (x &optional state)
fn bf_random(x : Value, state? : Value) -> Value raise {
  match x {
    Flo(_) | Fix(_) | Big(_) => mt_random(x, state?)
    _ =>
      if numeric__bfp(x) {
        // Generate an integer with fpprec bits, and convert to a bigfloat
        // by making the exponent 0.  Then multiply by the arg to get the
        // correct range.
        if bf_plusp(x) {
          let int = mt_random(ash(Fix(1L), to_int(symval(q_fpprec))), state?)
          bf_mul(x, bf_bigfloat(bcons(list2(int, Fix(0L)))))
        } else {
          raise LispError::SimpleError(
            "Argument is not a positive bigfloat: " + prin1_to_string(x),
          )
        }
      } else {
        numeric__no_method("random", [x])
      }
  }
}

///|
/// bigfloat::signum
fn bf_signum(x : Value) -> Value raise {
  if numeric__clnump(x) {
    signum(x)
  } else if numeric__bfp(x) {
    if bf_minusp(x) {
      bf_bigfloat(Fix(-1L))
    } else if bf_plusp(x) {
      bf_bigfloat(Fix(1L))
    } else {
      x
    }
  } else if numeric__cbfp(x) {
    bf_div(x, bf_abs(x))
  } else {
    numeric__no_method("signum", [x])
  }
}

///|
/// bigfloat::float-sign (one-argument form)
fn bf_float_sign(x : Value) -> Value raise {
  if x is Flo(d) {
    Flo(if dsignbit(d) { -1.0 } else { 1.0 })
  } else if numeric__bfp(x) {
    if bf_minusp(x) {
      bf_bigfloat(Fix(-1L))
    } else {
      bf_bigfloat(Fix(1L))
    }
  } else {
    numeric__no_method("float-sign", [x])
  }
}

///|
/// bigfloat::float-digits
fn bf_float_digits(x : Value) -> Value raise {
  if x is Flo(_) {
    Fix(53L)
  } else if numeric__bfp(x) {
    // We return the actual number of bits in the bigfloat number in case
    // the number and fpprec don't match.
    third(first(struct_ref(x, 0)))
  } else {
    numeric__no_method("float-digits", [x])
  }
}

///|
/// bigfloat::rational: the exact rational value.
fn bf_rational(x : Value) -> Value raise {
  if numeric__clrealp(x) {
    rational(x)
  } else if numeric__bfp(x) {
    let r = bf_real_value(x)
    let prec = third(first(r))
    let mantissa = second(r)
    let exp = third(r)
    bf_mul(mantissa, bf_expt(Fix(2L), bf_sub(exp, prec)))
  } else {
    numeric__no_method("rational", [x])
  }
}

///|
/// bigfloat::rationalize.  The BIGFLOAT method is the CLISP algorithm (via
/// CMUCL): a continued fraction expansion finding the rational with the
/// smallest numerator and denominator in the interval of numbers that
/// round to x.
fn bf_rationalize(x : Value) -> Value raise {
  if numeric__clrealp(x) {
    return rationalize(x)
  }
  if !numeric__bfp(x) {
    return numeric__no_method("rationalize", [x])
  }
  let (frac, expo, sign) = bf_integer_decode_float(x)
  if zerop(frac) || num_ge(expo, Fix(0L)) {
    let v = ash(frac, to_int(expo))
    return if minusp(sign) { num_neg(v) } else { v }
  }
  // expo < 0 and (2*m-1) and (2*m+1) are coprime to 2^(1-e), so build the
  // fraction up immediately, without having to do a gcd.
  let den = ash(Fix(1L), to_int(num_sub(Fix(1L), expo)))
  let mut a = num_div(num_sub(num_mul(Fix(2L), frac), Fix(1L)), den)
  let mut b = num_div(num_add(num_mul(Fix(2L), frac), Fix(1L)), den)
  let mut p0 : Value = Fix(0L)
  let mut q0 : Value = Fix(1L)
  let mut p1 : Value = Fix(1L)
  let mut q1 : Value = Fix(0L)
  while true {
    let c = ceiling1(a)
    if num_lt(c, b) {
      let top = num_add(num_mul(c, p1), p0)
      let bot = num_add(num_mul(c, q1), q0)
      return num_div(if minusp(sign) { num_neg(top) } else { top }, bot)
    }
    let k = num_sub(c, Fix(1L))
    let p2 = num_add(num_mul(k, p1), p0)
    let q2 = num_add(num_mul(k, q1), q0)
    let na = num_div(Fix(1L), num_sub(b, k))
    let nb = num_div(Fix(1L), num_sub(a, k))
    a = na
    b = nb
    p0 = p1
    q0 = q1
    p1 = p2
    q1 = q2
  }
  Nil
}

// ---------------------------------------------------------------------------
// COERCE

///|
/// Classify a CL type designator for bigfloat::coerce: "bigfloat",
/// "complex-bigfloat", "float", "complex" (any complex type), or the
/// symbol name for other types.
fn numeric__type_kind(type_ : Value) -> String raise {
  match type_ {
    Sym(_) =>
      match symbol_name(type_) {
        "bigfloat" | "bigfloat::bigfloat" => "bigfloat"
        "complex-bigfloat" | "bigfloat::complex-bigfloat" => "complex-bigfloat"
        "float"
        | "double-float"
        | "single-float"
        | "short-float"
        | "long-float"
        | "flonum" => "float"
        "complex" => "complex"
        s => s
      }
    Cons(_) =>
      if eq(car(type_), sym("complex")) {
        "complex"
      } else {
        "?"
      }
    _ => "?"
  }
}

///|
/// `(typep obj type)` for the type designators bigfloat::coerce handles.
fn numeric__typep(obj : Value, type_ : Value) -> Bool raise {
  match numeric__type_kind(type_) {
    "bigfloat" => numeric__bfp(obj)
    "complex-bigfloat" => numeric__cbfp(obj)
    "float" => obj is Flo(_)
    "complex" =>
      match type_ {
        Cons(_) =>
          match obj {
            Cplx(r, _) =>
              if cdr(type_) is Nil {
                true
              } else if numeric__type_kind(cadr(type_)) == "float" {
                r is Flo(_)
              } else {
                false
              }
            _ => false
          }
        _ => obj is Cplx(_, _)
      }
    "real" => numeric__clrealp(obj)
    "rational" => numeric__ratp(obj)
    "integer" => integerp(obj)
    "number" => numeric__clnump(obj)
    "t" => true
    _ => false
  }
}

///|
/// bigfloat::coerce (obj type)
fn bf_coerce(obj : Value, type_ : Value) -> Value raise {
  fn coerce_error() -> Value raise {
    raise LispError::SimpleError(
      "Cannot coerce " +
      princ_to_string(obj) +
      " to type " +
      prin1_to_string(type_),
    )
  }
  let kind = numeric__type_kind(type_)
  if numeric__typep(obj, type_) {
    return obj
  }
  if kind == "bigfloat" {
    // (coerce foo 'bigfloat).  Foo has to be a real
    return if numeric__clrealp(obj) { bf_bigfloat(obj) } else { coerce_error() }
  }
  if kind == "complex-bigfloat" {
    // (coerce foo 'complex-bigfloat).  Foo has to be a real or complex
    return if numeric__clrealp(obj) {
      bf_bigfloat(obj, im=Fix(0L))
    } else if obj is Cplx(_, _) {
      bf_bigfloat(obj)
    } else if numeric__bfp(obj) {
      bf_bigfloat(obj, im=Fix(0L))
    } else {
      coerce_error()
    }
  }
  if numeric__bfp(obj) {
    // (coerce bigfloat foo)
    return if kind == "float" {
      bf_float(obj, Flo(0.0))
    } else if kind == "complex" {
      let re = bf_float(bf_realpart(obj), Flo(1.0))
      make_complex(re, bf_float(bf_imagpart(obj), Flo(1.0)))
    } else {
      coerce_error()
    }
  }
  if numeric__cbfp(obj) {
    // (coerce complex-bigfloat foo)
    return if kind == "complex" {
      let re = bf_float(bf_realpart(obj), Flo(1.0))
      make_complex(re, bf_float(bf_imagpart(obj), Flo(1.0)))
    } else {
      coerce_error()
    }
  }
  // (cl:coerce obj type)
  if kind == "float" && numeric__clrealp(obj) {
    return Flo(to_double(obj))
  }
  if kind == "complex" && numeric__clnump(obj) {
    match type_ {
      Cons(_) if cdr(type_) is Cons(_) &&
        numeric__type_kind(cadr(type_)) == "float" => return lfloat(make_complex(realpart(obj), imagpart(obj)))
      _ => return obj
    }
  }
  coerce_error()
}

// ---------------------------------------------------------------------------
// %PI and %E

///|
/// %PI: a value of pi with the same precision as the argument.  For
/// rationals, we return a double-float approximation.
fn bf_p_pi(x : Value) -> Value raise {
  if numeric__clnump(x) {
    Flo(@math.PI)
  } else if numeric__numericp(x) {
    bf_to(bcons(numeric__fppi()))
  } else {
    numeric__no_method("%pi", [x])
  }
}

///|
/// The double value of %e (maxima::%e-val).
fn numeric__e_val() -> Double raise {
  match symval(q_p_e_val) {
    Flo(d) => d
    _ => 2.718281828459045
  }
}

///|
/// %E: a value of e with the same precision as the argument.  For
/// rationals, we return a double-float approximation.
fn bf_p_e(x : Value) -> Value raise {
  if numeric__clnump(x) {
    Flo(numeric__e_val())
  } else if numeric__numericp(x) {
    bf_to(bcons(numeric__fpe()))
  } else {
    numeric__no_method("%e", [x])
  }
}

// ---------------------------------------------------------------------------
// Useful routines: evaluation of continued fractions and power series

///|
/// LENTZ: Lentz's algorithm for evaluating continued fractions.
///
/// Let the continued fraction be:
///
///      a1    a2    a3
/// b0 + ----  ----  ----
///      b1 +  b2 +  b3 +
///
/// Then LENTZ expects two functions, each taking a single fixnum index.
/// The first returns the b term and the second returns the a terms as above
/// for a given n.  Returns (value, iterations, tiny-value-count).
fn bf_lentz_mv(bf : Value, af : Value) -> (Value, Value, Value) raise {
  let tiny_value_count = Ref(0)
  let value_or_tiny = (v : Value) => {
    // If v is zero, return a "tiny" number.
    if bf_zerop(v) {
      tiny_value_count.val += 1
      match v {
        Flo(_) | Cplx(_, _) =>
          lsqrt(Flo(least_positive_normalized_double_float))
        _ =>
          if numeric__numericp(v) {
            // What is a "tiny" bigfloat?  Bigfloats have unbounded
            // exponents, so we need something small, but not zero.
            // Arbitrarily choose an exponent of 50 times the precision.
            bf_expt(Fix(10L), num_neg(num_mul(Fix(50L), symval(q_d_fpprec))))
          } else {
            raise LispError::SimpleError(
              prin1_to_string(v) +
              " fell through ETYPECASE expression.",
            )
          }
      }
    } else {
      v
    }
  }
  let debug = () => symval(numeric__q_debug_cf_eval).truthy()
  let mut f = value_or_tiny(funcall(bf, [Fix(0L)]))
  let mut c = f
  let mut d : Value = Fix(0L)
  let eps = bf_epsilon(f)
  let max_iter = to_int(symval(numeric__q_max_cf_iterations))
  for j = 1; j <= max_iter; j = j + 1 {
    let an = funcall(af, [int(j)])
    let bn = funcall(bf, [int(j)])
    d = value_or_tiny(bf_add(bn, bf_mul(an, d)))
    c = value_or_tiny(bf_add(bn, bf_div(an, c)))
    if debug() {
      format(t, "~&j = ~d~%", [int(j)]) |> ignore
      format(t, "  an = ~s~%", [an]) |> ignore
      format(t, "  bn = ~s~%", [bn]) |> ignore
      format(t, "  c  = ~s~%", [c]) |> ignore
      format(t, "  d  = ~s~%", [d]) |> ignore
    }
    let delta = bf_div(c, d)
    d = bf_inv(d)
    f = bf_mul(f, delta)
    if debug() {
      format(t, "  dl= ~S (|dl - 1| = ~S)~%", [delta, bf_abs(bf_sub1(delta))])
      |> ignore
      format(t, "  f = ~S~%", [f]) |> ignore
    }
    if bf_le(bf_abs(bf_sub(delta, Fix(1L))), eps) {
      return (f, int(j), int(tiny_value_count.val))
    }
  }
  raise LispError::SimpleError(
    format_to_string(
      "Continued fraction failed to converge after ~D iterations.~%    Delta = ~S",
      [int(max_iter), bf_div(c, d)],
    ),
  )
}

///|
/// LENTZ (primary value only); see `bf_lentz_mv`.
fn bf_lentz(bf : Value, af : Value) -> Value raise {
  bf_lentz_mv(bf, af).0
}

///|
/// SUM-POWER-SERIES sums the given power series, adding terms until the
/// next term would not change the sum.  The series to be summed is
///
///   S = 1 + sum(c[k]*x^k, k, 1, inf)
///     = 1 + sum(prod(f[n]*x, n, 1, k), k, 1, inf)
///
/// where f[n] = c[n]/c[n-1].
fn bf_sum_power_series(x : Value, f : Value) -> Value raise {
  let eps = bf_epsilon(x)
  let mut k = 1
  let mut sum : Value = Fix(1L)
  let mut term = bf_mul(x, funcall(f, [Fix(1L)]))
  while !bf_lt(bf_abs(term), bf_mul(eps, bf_abs(sum))) {
    k = k + 1
    sum = bf_add(sum, term)
    term = bf_op_star(list([term, x, funcall(f, [int(k)])]))
  }
  sum
}

// ---------------------------------------------------------------------------
// ~E, ~F and ~G formatting of bigfloats (suitable as ~// format functions)

///|
/// `(format s "'~C," ch)` or "," for an absent character parameter.
fn numeric__fmt_char_param(sb : StringBuilder, ch : Value) -> Unit {
  match ch {
    Char(c) => {
      sb.write_char('\'')
      sb.write_char(c)
      sb.write_char(',')
    }
    _ => sb.write_char(',')
  }
}

///|
/// Format bigfloats using ~E format.  (A modified version of
/// FORMAT-EXPONENTIAL from CMUCL to support printing of bfloats.)
fn bf_format_e(
  stream : Value,
  number : Value,
  colonp : Value,
  atp : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  e? : Value = Nil,
  k? : Value = Nil,
  overflowchar? : Value = Nil,
  padchar? : Value = Nil,
  exponentchar? : Value = Nil,
) -> Value raise {
  if numeric__bfp(number) {
    bfloat_format_e(
      stream,
      bf_real_value(number),
      colonp,
      atp,
      w~,
      d~,
      e~,
      k=if k.truthy() { k } else { Fix(1L) },
      overflowchar~,
      padchar=if padchar.truthy() { padchar } else { Char(' ') },
      exponentchar=if exponentchar.truthy() { exponentchar } else { Char('b') },
    )
  } else if numeric__cbfp(number) {
    // FIXME: Do something better than this since this doesn't honor any
    // of the parameters.
    princ(number, stream~)
  } else {
    // We were given some other kind of object.  Just use CL's normal ~E
    // printer to print it.
    let sb = StringBuilder()
    sb.write_string("~V,V,V,V,")
    numeric__fmt_char_param(sb, overflowchar)
    numeric__fmt_char_param(sb, padchar)
    if exponentchar is Char(c) {
      sb.write_char('\'')
      sb.write_char(c)
    }
    if colonp.truthy() {
      sb.write_char(':')
    }
    if atp.truthy() {
      sb.write_char('@')
    }
    sb.write_char('E')
    format(stream, sb.to_string(), [w, d, e, k, number])
  }
}

///|
/// Format bigfloats using ~F format.  (A modified version of FORMAT-FIXED
/// from CMUCL to support printing of bfloats.)
fn bf_format_f(
  stream : Value,
  number : Value,
  colonp : Value,
  atp : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  k? : Value = Nil,
  overflowchar? : Value = Nil,
  padchar? : Value = Nil,
) -> Value raise {
  if numeric__bfp(number) {
    bfloat_format_f(
      stream,
      bf_real_value(number),
      colonp,
      atp,
      w~,
      d~,
      k=if k.truthy() { k } else { Fix(0L) },
      ovf=overflowchar,
      pad=if padchar.truthy() { padchar } else { Char(' ') },
    )
  } else if numeric__cbfp(number) {
    // FIXME: Do something better than this since this doesn't honor any
    // of the parameters.
    princ(number, stream~)
  } else {
    // We were given some other kind of object.  Just use CL's normal ~F
    // printer to print it.
    let sb = StringBuilder()
    sb.write_string("~V,V,V,")
    numeric__fmt_char_param(sb, overflowchar)
    match padchar {
      Char(' ') => sb.write_string(",")
      Char(c) => {
        sb.write_char('\'')
        sb.write_char(c)
        sb.write_char(',')
      }
      _ => raise type_error(padchar, "character")
    }
    if colonp.truthy() {
      sb.write_char(':')
    }
    if atp.truthy() {
      sb.write_char('@')
    }
    sb.write_char('F')
    format(stream, sb.to_string(), [w, d, k, number])
  }
}

///|
/// Format bigfloats using ~G format.  (A modified version of
/// FORMAT-GENERAL from CMUCL to support printing of bfloats.)
fn bf_format_g(
  stream : Value,
  number : Value,
  colonp : Value,
  atp : Value,
  w? : Value = Nil,
  d? : Value = Nil,
  e? : Value = Nil,
  k? : Value = Nil,
  overflowchar? : Value = Nil,
  padchar? : Value = Nil,
  marker? : Value = Nil,
) -> Value raise {
  if numeric__bfp(number) {
    bfloat_format_g(
      stream,
      bf_real_value(number),
      colonp,
      atp,
      w~,
      d~,
      e~,
      k=if k.truthy() { k } else { Fix(1L) },
      ovf=overflowchar,
      pad=if padchar.truthy() { padchar } else { Char(' ') },
      exponentchar=if marker.truthy() { marker } else { Char('b') },
    )
  } else if numeric__cbfp(number) {
    // FIXME: Do something better than this since this doesn't honor any
    // of the parameters.
    princ(number, stream~)
  } else {
    // We were given some other kind of object.  Just use CL's normal ~G
    // printer to print it.
    let sb = StringBuilder()
    sb.write_string("~V,V,V,V,")
    numeric__fmt_char_param(sb, overflowchar)
    numeric__fmt_char_param(sb, padchar)
    if marker is Char(c) {
      sb.write_char('\'')
      sb.write_char(c)
    }
    if colonp.truthy() {
      sb.write_char(':')
    }
    if atp.truthy() {
      sb.write_char('@')
    }
    sb.write_char('G')
    format(stream, sb.to_string(), [w, d, e, k, number])
  }
}

// ---------------------------------------------------------------------------
// Init: special variables and the function cells of the generic functions

///|
/// Install `f` as the function of the bigfloat-package symbol `name`.
fn numeric__defgeneric(name : String, f : (Array[Value]) -> Value raise) -> Unit {
  defun(sym("bigfloat::" + name), f, name="bigfloat::" + name)
}

///|
/// Optional argument `i` of a Lisp call, or None.
fn numeric__opt(args : Array[Value], i : Int) -> Value? {
  if i < args.length() {
    Some(args[i])
  } else {
    None
  }
}

///|
fn init_numeric() -> Unit raise {
  defvar_init(numeric__q_use_accurate_complex_div, t)
  defvar_init(numeric__q_debug_cf_eval, Nil)
  defvar_init(numeric__q_max_cf_iterations, Fix(10000L))
  // MAXIMA::TO (called by funcall from simp.lisp and others).
  defun(q_to, args => maxima_to(arg(args, 0)), name="to")
  let g1 : Array[(String, (Value) -> Value raise)] = [
    ("real-value", bf_real_value),
    ("imag-value", bf_imag_value),
    ("max-exponent", bf_max_exponent),
    ("add1", bf_add1),
    ("sub1", bf_sub1),
    ("unary-minus", bf_neg),
    ("unary-divide", bf_inv),
    ("abs", bf_abs),
    ("sqrt", bf_sqrt),
    ("exp", bf_exp),
    ("sin", bf_sin),
    ("cos", bf_cos),
    ("tan", bf_tan),
    ("asin", bf_asin),
    ("acos", bf_acos),
    ("sinh", bf_sinh),
    ("cosh", bf_cosh),
    ("tanh", bf_tanh),
    ("asinh", bf_asinh),
    ("acosh", bf_acosh),
    ("atanh", bf_atanh),
    ("one-arg-log", bf_log1),
    ("one-arg-atan", bf_atan1),
    ("realpart", bf_realpart),
    ("imagpart", bf_imagpart),
    ("conjugate", bf_conjugate),
    ("phase", bf_phase),
    ("cis", bf_cis),
    ("one-arg-complex", bf_complex1),
    ("unary-floor", bf_unary_floor),
    ("unary-ffloor", bf_unary_ffloor),
    ("unary-truncate", bf_unary_truncate),
    ("unary-ftruncate", bf_unary_ftruncate),
    ("unary-ceiling", bf_unary_ceiling),
    ("unary-fceiling", bf_unary_fceiling),
    ("epsilon", bf_epsilon),
    ("signum", bf_signum),
    ("float-sign", bf_float_sign),
    ("float-digits", bf_float_digits),
    ("rational", bf_rational),
    ("rationalize", bf_rationalize),
    ("%pi", bf_p_pi),
    ("%e", bf_p_e),
  ]
  for e in g1 {
    let f = e.1
    numeric__defgeneric(e.0, args => f(arg(args, 0)))
  }
  let g2 : Array[(String, (Value, Value) -> Value raise)] = [
    ("two-arg-+", bf_add),
    ("two-arg--", bf_sub),
    ("two-arg-*", bf_mul),
    ("two-arg-/", bf_div),
    ("two-arg-log", bf_log2),
    ("two-arg-atan", bf_atan2),
    ("two-arg-complex", bf_complex2),
    ("expt", bf_expt),
    ("scale-float", bf_scale_float),
    ("float", bf_float),
    ("cdiv-double-float", bf_cdiv_double_float),
  ]
  for e in g2 {
    let f = e.1
    numeric__defgeneric(e.0, args => f(arg(args, 0), arg(args, 1)))
  }
  let preds : Array[(String, (Value) -> Bool raise)] = [
    ("realp", x => bf_realp(x)),
    ("complexp", x => bf_complexp(x)),
    ("numberp", x => bf_numberp(x)),
    ("zerop", bf_zerop),
    ("plusp", bf_plusp),
    ("minusp", bf_minusp),
  ]
  for e in preds {
    let f = e.1
    numeric__defgeneric(e.0, args => lbool(f(arg(args, 0))))
  }
  let cmps : Array[(String, (Value, Value) -> Bool raise)] = [
    ("two-arg-<", bf_lt),
    ("two-arg->", bf_gt),
    ("two-arg-<=", bf_le),
    ("two-arg->=", bf_ge),
    ("two-arg-=", bf_eq),
  ]
  for e in cmps {
    let f = e.1
    numeric__defgeneric(e.0, args => lbool(f(arg(args, 0), arg(args, 1))))
  }
  let nary : Array[(String, (Value, Value) -> Value raise)] = [
    ("<", bf_op_lt),
    (">", bf_op_gt),
    ("<=", bf_op_lt_eq),
    (">=", bf_op_gt_eq),
  ]
  for e in nary {
    let f = e.1
    numeric__defgeneric(e.0, args => f(arg(args, 0), rest_args(args, 1)))
  }
  // Rounding functions: (a &optional (divisor 1)); primary value only.
  let rounding : Array[(String, (Value, Value) -> (Value, Value) raise)] = [
    ("floor", (a, d) => bf_floor(a, divisor=d)),
    ("ffloor", (a, d) => bf_ffloor(a, divisor=d)),
    ("ceiling", (a, d) => bf_ceiling(a, divisor=d)),
    ("fceiling", (a, d) => bf_fceiling(a, divisor=d)),
    ("truncate", (a, d) => bf_truncate(a, divisor=d)),
    ("ftruncate", (a, d) => bf_ftruncate(a, divisor=d)),
    ("round", (a, d) => bf_round(a, divisor=d)),
    ("fround", (a, d) => bf_fround(a, divisor=d)),
  ]
  for e in rounding {
    let f = e.1
    numeric__defgeneric(e.0, args => {
      let d = if args.length() > 1 { args[1] } else { Fix(1L) }
      f(arg(args, 0), d).0
    })
  }
  numeric__defgeneric("integer-decode-float", args => bf_integer_decode_float(
    arg(args, 0),
  ).0)
  numeric__defgeneric("decode-float", args => bf_decode_float(arg(args, 0)).0)
  numeric__defgeneric("random", args => bf_random(
    arg(args, 0),
    state?=numeric__opt(args, 1),
  ))
  // (defmethod print-object ((x bigfloat) stream) ...)
  @lisp.struct_print_functions["bigfloat"] = lfunc("print-object", args => {
    let r = cdr(bf_real_value(args[0]))
    let (sign, output_list) = if minusp(car(r)) {
      ("-", fpformat(bcons(list([num_neg(car(r)), cadr(r)]))))
    } else {
      ("+", fpformat(bcons(r)))
    }
    format(args[1], "~A~{~D~}", [Str(sign), output_list])
  })
  // (defmethod print-object ((x complex-bigfloat) stream) ...)
  @lisp.struct_print_functions["complex-bigfloat"] = lfunc("print-object", args => format(
    args[1],
    "~A~A*%i",
    [bf_realpart(args[0]), bf_imagpart(args[0])],
  ))
}
