// Port of src/numerical-utils.lisp: utilities for determining if
// numerical evaluation should be done.
//
// The functions take a list of arguments. All arguments have to be a CL or
// Maxima number. If all arguments are numbers we have two cases:
// 1. $numer is T we return T. The function has to be evaluated numerically.
// 2. One of the args is a float or a bigfloat. Evaluate numerically.

///|
fn float_or_rational_p(x : Value) -> Value raise {
  if floatp(x) {
    t
  } else {
    d_ratnump(x)
  }
}

///|
fn bigfloat_or_number_p(x : Value) -> Value raise {
  let b = d_bfloatp(x)
  if b.truthy() {
    b
  } else if numberp(x) {
    t
  } else {
    d_ratnump(x)
  }
}

///|
/// Apply the type predicate NTYPEP (a function designator).
fn numerical_utils__ntype(ntypep : Value, x : Value) -> Value raise {
  if eq(ntypep, q_numberp) {
    lbool(numberp(x))
  } else if eq(ntypep, q_float_or_rational_p) {
    float_or_rational_p(x)
  } else if eq(ntypep, q_bigfloat_or_number_p) {
    bigfloat_or_number_p(x)
  } else {
    funcall(ntypep, [x])
  }
}

///|
/// Is argument u a complex number with real and imagpart satisfying
/// predicate ntypep?  Primary value only; see `complex_number_p_mv`.
fn complex_number_p(u : Value, ntypep? : Value = q_numberp) -> Value raise {
  complex_number_p_mv(u, ntypep~).0
}

///|
/// COMPLEX-NUMBER-P with all three CL values (flag, realpart, imagpart).
fn complex_number_p_mv(
  u : Value,
  ntypep? : Value = q_numberp,
) -> (Value, Value, Value) raise {
  let mut r : Value = Fix(0L)
  let mut i : Value = Fix(0L)
  let n = (x : Value) => numerical_utils__ntype(ntypep, x).truthy()
  let i_p = (x : Value) => eq(x, q_d__pcti) && n(Fix(1L))
  let n_star_i = (x : Value) => {
    if cdddr(x) is Nil {
      i = cadr(x)
      n(i) && eq(caddr(x), q_d__pcti)
    } else {
      false
    }
  }
  let n_plus_i = (x : Value) => {
    if cdddr(x) is Nil {
      r = cadr(x)
      if n(r) {
        if i_p(caddr(x)) {
          i = Fix(1L)
          true
        } else {
          mtimesp(caddr(x)).truthy() && n_star_i(caddr(x))
        }
      } else {
        false
      }
    } else {
      false
    }
  }
  if n(u) {
    (t, u, Fix(0L))
  } else if atom(u) {
    if i_p(u) {
      (t, Fix(0L), Fix(1L))
    } else {
      (Nil, Nil, Nil)
    }
  } else if mplusp(u).truthy() {
    if n_plus_i(u) {
      (t, r, i)
    } else {
      (Nil, Nil, Nil)
    }
  } else if mtimesp(u).truthy() {
    if n_star_i(u) {
      (t, r, i)
    } else {
      (Nil, Nil, Nil)
    }
  } else {
    (Nil, Nil, Nil)
  }
}

///|
/// Check for an integer or a float or bigfloat representation. When we
/// have a float or bigfloat representation return the integer value.
fn integer_representation_p(x : Value) -> Value raise {
  if integerp(x) {
    x
  } else if floatp(x) && zerop(num_truncate(x).1) {
    num_truncate(x).0
  } else if d_bfloatp(x).truthy() {
    let val = ftake(q_p_truncate, [x])
    if eq(d_sign(sub(val, x)), q_d_zero) {
      val
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Convert a Lisp number to a maxima number
fn complexify(x : Value) -> Value raise {
  if realp(x) {
    x
  } else if complexp(x) {
    add2(realpart(x), mul2(q_d__pcti, imagpart(x)))
  } else {
    merr(
      "COMPLEXIFY: argument must be a Lisp real or complex number.~%COMPLEXIFY: found: ~:M",
      [x],
    )
  }
}

///|
fn cmul(x : Value, y : Value) -> Value raise {
  d_rectform(mul2(x, y))
}

///|
fn cdiv(x : Value, y : Value) -> Value raise {
  d_rectform(div(x, y))
}

///|
fn cpower(x : Value, y : Value) -> Value raise {
  d_rectform(power(x, y))
}

///|
/// Test for numerically evaluation in float precision
fn float_numerical_eval_p(args : Value) -> Value raise {
  let mut flag = false
  for ll in args.iter() {
    if !float_or_rational_p(ll).truthy() {
      return Nil
    }
    if floatp(ll) {
      flag = true
    }
  }
  if symval(q_d_numer).truthy() || flag {
    t
  } else {
    Nil
  }
}

///|
/// Determine if ARGS consists of numerical values by determining if
/// the real and imaginary parts of each arg are numerical (but not
/// bigfloats).  A non-NIL result is returned if at least one of args is
/// a floating-point value or if numer is true.  If the result is
/// non-NIL, it is a list of the arguments reduced via COMPLEX-NUMBER-P
fn complex_float_numerical_eval_p(args : Value) -> Value raise {
  let mut flag = false
  let mut values : Value = Nil
  for ll in args.iter() {
    let (bool, rll, ill) = complex_number_p_mv(
      ll,
      ntypep=q_float_or_rational_p,
    )
    if !bool.truthy() {
      return Nil
    }
    values = cons(add2(rll, mul2(ill, q_d__pcti)), values)
    flag = flag || floatp(rll) || floatp(ill)
  }
  if symval(q_d_numer).truthy() || flag {
    nreverse(values)
  } else {
    Nil
  }
}

///|
/// Test for numerically evaluation in bigfloat precision
fn bigfloat_numerical_eval_p(args : Value) -> Value raise {
  let mut flag = false
  for ll in args.iter() {
    if !bigfloat_or_number_p(ll).truthy() {
      return Nil
    }
    if d_bfloatp(ll).truthy() {
      flag = true
    }
  }
  if symval(q_d_numer).truthy() || flag {
    t
  } else {
    Nil
  }
}

///|
/// Like COMPLEX-FLOAT-NUMERICAL-EVAL-P, but including bigfloats.
fn complex_bigfloat_numerical_eval_p(args : Value) -> Value raise {
  let mut flag = false
  let mut values : Value = Nil
  for ll in args.iter() {
    let (bool, rll, ill) = complex_number_p_mv(
      ll,
      ntypep=q_bigfloat_or_number_p,
    )
    if !bool.truthy() {
      return Nil
    }
    values = cons(add2(rll, mul2(ill, q_d__pcti)), values)
    if d_bfloatp(rll).truthy() || d_bfloatp(ill).truthy() {
      flag = true
    }
  }
  if symval(q_d_numer).truthy() || flag {
    nreverse(values)
  } else {
    Nil
  }
}

///|
/// Test for numerical evaluation in any precision, real or complex.
fn numerical_eval_p(args : Value) -> Value raise {
  let a = float_numerical_eval_p(args)
  if a.truthy() {
    return a
  }
  let b = complex_float_numerical_eval_p(args)
  if b.truthy() {
    return b
  }
  let c = bigfloat_numerical_eval_p(args)
  if c.truthy() {
    return c
  }
  complex_bigfloat_numerical_eval_p(args)
}

///|
/// Signal a domain error for the special functions.  ARGS should be
/// appropriate for MERROR.
fn simp_domain_error(args : Value) -> Value raise {
  if symval(q_errorsw).truthy() {
    throw_tag(q_errorsw, t)
  } else {
    merror(car(args), cdr(args))
  }
}

///|
fn init_numerical_utils() -> Unit raise {
  ()
}
