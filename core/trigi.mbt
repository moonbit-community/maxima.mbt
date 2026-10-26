// Port of src/trigi.lisp: simplifiers for the circular functions sin, cos,
// tan, cot, csc, sec, atan and atan2, numerical evaluation tables, %piargs
// handling, and assorted arithmetic utilities.

// ;;; Arithmetic utilities.

///|
fn sqrt1_x_hat2(x : Value) -> Value raise {
  power(sub(Fix(1L), power(x, Fix(2L))), symval(q_n1_sl_sl2))
}

///|
fn sqrt1_plusx_hat2(x : Value) -> Value raise {
  power(add2(Fix(1L), power(x, Fix(2L))), symval(q_n1_sl_sl2))
}

///|
fn sqrtx_hat2_1(x : Value) -> Value raise {
  power(add2(power(x, Fix(2L)), Fix(-1L)), symval(q_n1_sl_sl2))
}

///|
fn sq_sumsq(x : Value, y : Value) -> Value raise {
  power(add2(power(x, Fix(2L)), power(y, Fix(2L))), symval(q_n1_sl_sl2))
}

///|
fn trigp(func : Value) -> Value raise {
  if memq(
      func,
      list([
        q_p_sin, q_p_cos, q_p_tan, q_p_csc, q_p_sec, q_p_cot, q_p_sinh, q_p_cosh,
        q_p_tanh, q_p_csch, q_p_sech, q_p_coth,
      ]),
    ).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn arcp(func : Value) -> Value raise {
  if memq(
      func,
      list([
        q_p_asin, q_p_acos, q_p_atan, q_p_acsc, q_p_asec, q_p_acot, q_p_asinh,
        q_p_acosh, q_p_atanh, q_p_acsch, q_p_asech, q_p_acoth,
      ]),
    ).truthy() {
    t
  } else {
    Nil
  }
}

///|
fn domain_error(x : Value, f : Value) -> Value raise {
  merr("~A: argument ~:M isn't in the domain of ~A.", [
    f,
    if complexp(x) {
      complexify(x)
    } else {
      x
    },
    f,
  ])
}

///|
/// Handle errors from calling %piargs-tan/cot and %piargs-csc/sec. Any
/// errors from these functions get resignaled with a domain-error with the
/// given Y value and NAME.
///
/// FORM should basically be a call to %piargs-tan/cot or %piargs-csc/sec,
/// possibly with a different arg than Y.
fn handle__pctpiargs_trig(form : Value, y : Value, name : Value) -> Value raise {
  with_specials([(q_errcatch, t), (q_d_errormsg, Nil)], () => funcall0(form)) catch {
    e => if is_maxima_error(e) { domain_error(y, name) } else { raise e }
  }
}

// Some Lisp implementations goof up branch cuts for ASIN, ACOS, ASINH,
// and/or ATANH. Here are definitions which have the right branch cuts
// (assuming LOG, PHASE, and SQRT have the right branch cuts).

///|
/// Apply formula from CLHS if X falls on a branch cut.
/// Otherwise punt to CL:ASIN.
fn maxima_branch_asin(x : Value) -> Value raise {
  // Test for (IMAGPART X) is EQUAL because signed zero is EQUAL to zero.
  if num_gt(num_abs(realpart(x)), Flo(1.0)) && equal(imagpart(x), Flo(0.0)) {
    // asin(x) = %pi/2*sign(x) - %i*[log(abs(x)*(1+abs(x)/x*sqrt(1-1/x^2))]
    // evaluated as described in trigi.lisp, using
    // sqrt(1-1/x^2) = sqrt(1+1/x)*sqrt(1-1/x) for accuracy.
    let absx = num_abs(x)
    let recip = num_div(Fix(1L), absx)
    let result = complex(
      Flo(@math.PI / 2.0),
      i=num_neg(
        llog(
          num_mul(
            absx,
            one_plus(
              num_mul(
                lsqrt(num_add(Fix(1L), recip)),
                lsqrt(num_sub(Fix(1L), recip)),
              ),
            ),
          ),
        ),
      ),
    )
    if minusp(x) {
      num_neg(result)
    } else {
      result
    }
  } else {
    lasin(x)
  }
}

///|
/// Apply formula from CLHS if X falls on a branch cut.
/// Otherwise punt to CL:ACOS.
fn maxima_branch_acos(x : Value) -> Value raise {
  if num_gt(num_abs(realpart(x)), Flo(1.0)) && equal(imagpart(x), Flo(0.0)) {
    num_sub(Flo(@math.PI / 2.0), maxima_branch_asin(x))
  } else {
    lacos(x)
  }
}

///|
/// On the branch cut (imaginary axis beyond +/-%i), use
/// atan(%i*y) = %i*atanh(y) with MAXIMA-BRANCH-ATANH. Return NIL at the
/// poles +/-%i, otherwise punt to CL:ATAN.
fn maxima_branch_atan(x : Value) -> Value raise {
  let re = realpart(x)
  let im = imagpart(x)
  if !zerop(re) || num_lt(num_abs(im), Fix(1L)) {
    latan(x)
  } else if num_eq(num_abs(im), Fix(1L)) {
    Nil
  } else {
    // %i*(u+%i*v) = -v+%i*u
    let w = maxima_branch_atanh(im)
    complex(num_neg(imagpart(w)), i=realpart(w))
  }
}

///|
fn maxima_branch_acot(x : Value) -> Value raise {
  // Allow 0.0 in domain of acot, otherwise use atan(1/x)
  if zerop(x) {
    Flo(@math.PI / 2.0)
  } else {
    maxima_branch_atan(num_div(Fix(1L), x))
  }
}

///|
/// On the branch cut (imaginary axis beyond +/-%i), use
/// asinh(%i*y) = %i*asin(y) with MAXIMA-BRANCH-ASIN, and
/// asinh(-x) = -asinh(x). Otherwise punt to CL:ASINH.
fn maxima_branch_asinh(x : Value) -> Value raise {
  let re = realpart(x)
  let im = imagpart(x)
  if zerop(re) && num_gt(num_abs(im), Fix(1L)) {
    // %i*(u+%i*v) = -v+%i*u
    let w = maxima_branch_asin(num_abs(im))
    let v = complex(num_neg(imagpart(w)), i=realpart(w))
    if minusp(im) {
      num_neg(v)
    } else {
      v
    }
  } else {
    lasinh(x)
  }
}

///|
/// Apply formula from CLHS if X falls on a branch cut.
/// Return NIL at the poles +/-1. Otherwise punt to CL:ATANH.
fn maxima_branch_atanh(x : Value) -> Value raise {
  if num_eq(num_abs(realpart(x)), Fix(1L)) && zerop(imagpart(x)) {
    Nil
  } else if num_gt(num_abs(realpart(x)), Flo(1.0)) &&
    equal(imagpart(x), Flo(0.0)) {
    num_div(
      num_sub(llog(num_add(Fix(1L), x)), llog(num_sub(Fix(1L), x))),
      Fix(2L),
    )
  } else {
    latanh(x)
  }
}

///|
fn maxima_branch_acoth(x : Value) -> Value raise {
  // Allow 0.0 in domain of acoth, otherwise use atanh(1/x)
  if zerop(x) {
    complex(Flo(0.0), i=Flo(@math.PI / -2.0))
  } else {
    maxima_branch_atanh(num_div(Fix(1L), x))
  }
}

///|
/// `(ignore-errors form)`: the value, or nil if an error was signalled.
fn trigi__ignore_errors(f : () -> Value raise) -> Value raise {
  match errset(f) {
    Some(v) => v
    None => Nil
  }
}

///|
/// CL `(float-sign x y)`: |y| with the sign of x.
fn trigi__float_sign(x : Value, y : Value) -> Value raise {
  let xd = to_double(x)
  let yd = to_double(y).abs()
  Flo(if xd < 0.0 || (xd == 0.0 && dsignbit(xd)) { -yd } else { yd })
}

///|
/// CL `ffloor`/`fceiling` of a real.
fn trigi__ffloor(x : Value) -> Value raise {
  match x {
    Flo(d) => Flo(d.floor())
    _ => lfloat(floor1(x))
  }
}

///|
fn trigi__fceiling(x : Value) -> Value raise {
  match x {
    Flo(d) => Flo(d.ceil())
    _ => lfloat(ceiling1(x))
  }
}

///|
/// A one-argument flonum op that signals a domain error for F when the
/// computation fails.
fn trigi__guarded(
  name : String,
  f : Value,
  g : (Value) -> Value raise,
) -> Value {
  lfunc(name, args => {
    let x = arg(args, 0)
    let y = trigi__ignore_errors(() => g(x))
    if y.truthy() {
      y
    } else {
      domain_error(x, f)
    }
  })
}

///|
fn trigi__fn1(name : String, g : (Value) -> Value raise) -> Value {
  lfunc(name, args => g(arg(args, 0)))
}

///|
/// Fill the *flonum-op* hash table.
fn trigi__fill_flonum_op() -> Unit raise {
  let tbl = symval(q_ear_flonum_op)
  fn frob(k : Value, f : Value) -> Unit raise {
    sethash(k, tbl, f) |> ignore
  }

  frob(
    q_mplus,
    lfunc("+", args => {
      let mut s : Value = Fix(0L)
      for a in args {
        s = num_add(s, a)
      }
      s
    }),
  )
  frob(
    q_mtimes,
    lfunc("*", args => {
      let mut s : Value = Fix(1L)
      for a in args {
        s = num_mul(s, a)
      }
      s
    }),
  )
  frob(
    q_mquotient,
    lfunc("/", args => {
      if args.length() == 1 {
        num_div(Fix(1L), args[0])
      } else {
        let mut s = args[0]
        for i in 1..<args.length() {
          s = num_div(s, args[i])
        }
        s
      }
    }),
  )
  frob(
    q_mminus,
    lfunc("-", args => {
      if args.length() == 1 {
        num_neg(args[0])
      } else {
        let mut s = args[0]
        for i in 1..<args.length() {
          s = num_sub(s, args[i])
        }
        s
      }
    }),
  )
  frob(q_p_cos, trigi__fn1("cos", x => lcos(x)))
  frob(q_p_sin, trigi__fn1("sin", x => lsin(x)))
  frob(q_p_tan, trigi__fn1("tan", x => ltan(x)))
  frob(q_p_sec, trigi__guarded("sec", q_sec, x => num_div(Fix(1L), lcos(x))))
  frob(q_p_csc, trigi__guarded("csc", q_csc, x => num_div(Fix(1L), lsin(x))))
  frob(q_p_cot, trigi__guarded("cot", q_cot, x => num_div(Fix(1L), ltan(x))))
  frob(q_p_acos, trigi__fn1("maxima-branch-acos", x => maxima_branch_acos(x)))
  frob(q_p_asin, trigi__fn1("maxima-branch-asin", x => maxima_branch_asin(x)))
  frob(q_p_atan, trigi__guarded("atan", q_atan, x => maxima_branch_atan(x)))
  frob(
    q_p_asec,
    trigi__guarded("asec", q_asec, x => maxima_branch_acos(num_div(Fix(1L), x))),
  )
  frob(
    q_p_acsc,
    trigi__guarded("acsc", q_acsc, x => maxima_branch_asin(num_div(Fix(1L), x))),
  )
  frob(q_p_acot, trigi__guarded("acot", q_acot, x => maxima_branch_acot(x)))
  frob(q_p_cosh, trigi__fn1("cosh", x => lcosh(x)))
  frob(q_p_sinh, trigi__fn1("sinh", x => lsinh(x)))
  frob(q_p_tanh, trigi__fn1("tanh", x => ltanh(x)))
  frob(
    q_p_sech,
    trigi__guarded("sech", q_sech, x => {
      // For large x > 0, cosh(x) ~= exp(x)/2. Hence, sech(x) ~= 2*exp(-x).
      // 710.4758600739439d0 = (acosh most-positive-double-float).
      if floatp(x) && num_ge(num_abs(x), Flo(710.4758600739439)) {
        num_mul(Fix(2L), lexp(num_neg(num_abs(x))))
      } else {
        num_div(Fix(1L), lcosh(x))
      }
    }),
  )
  frob(
    q_p_csch,
    trigi__guarded("csch", q_csch, x => {
      // For large x > 0, sinh(x) ~= exp(x)/2. Hence csch(x) = 2*exp(-x).
      // Since sinh(x) is odd, csch(x) = -2*exp(x) when x < 0 and |x| is large.
      if floatp(x) && num_ge(num_abs(x), Flo(710.4758600739439)) {
        trigi__float_sign(x, num_mul(Fix(2L), lexp(num_neg(num_abs(x)))))
      } else {
        num_div(Fix(1L), lsinh(x))
      }
    }),
  )
  frob(q_p_coth, trigi__guarded("coth", q_coth, x => num_div(Fix(1L), ltanh(x))))
  frob(q_p_acosh, trigi__fn1("acosh", x => lacosh(x)))
  frob(q_p_asinh, trigi__fn1("maxima-branch-asinh", x => maxima_branch_asinh(x)))
  frob(q_p_atanh, trigi__guarded("atanh", q_atanh, x => maxima_branch_atanh(x)))
  frob(
    q_p_asech,
    trigi__guarded("asech", q_asech, x => lacosh(num_div(Fix(1L), x))),
  )
  frob(
    q_p_acsch,
    trigi__guarded("acsch", q_acsch, x => {
      // logarc(acsch(x)) = log(1/x+sqrt(1/x^2+1)). For very small x use
      // log(2)-log(x) to avoid overflow of 2/x.
      let absx = num_abs(x)
      if floatp(x) &&
        num_lt(absx, Flo(least_positive_normalized_double_float)) {
        trigi__float_sign(
          x,
          num_sub(llog(Flo(2.0)), llog(num_abs(x))),
        )
      } else {
        maxima_branch_asinh(num_div(Fix(1L), x))
      }
    }),
  )
  frob(q_p_acoth, trigi__guarded("acoth", q_acoth, x => maxima_branch_acoth(x)))
  frob(q_mabs, trigi__fn1("abs", x => num_abs(x)))
  frob(q_p_exp, trigi__fn1("exp", x => lexp(x)))
  frob(q_mexpt, lfunc("expt", args => expt(arg(args, 0), arg(args, 1))))
  frob(q_p_sqrt, trigi__fn1("sqrt", x => lsqrt(x)))
  frob(q_p_log, trigi__guarded("log", q_log, x => llog(x)))
  frob(q_p_plog, trigi__guarded("log", q_log, x => llog(x)))
  frob(q_d_conjugate, trigi__fn1("conjugate", x => conjugate(x)))
  frob(q_d_floor, trigi__fn1("ffloor", x => trigi__ffloor(x)))
  frob(q_d_ceiling, trigi__fn1("fceiling", x => trigi__fceiling(x)))
  frob(q_d_realpart, trigi__fn1("realpart", x => realpart(x)))
  frob(q_d_imagpart, trigi__fn1("imagpart", x => imagpart(x)))
  frob(
    q_d_max,
    lfunc("max", args => {
      let mut s = args[0]
      for i in 1..<args.length() {
        s = num_max(s, args[i])
      }
      s
    }),
  )
  frob(
    q_d_min,
    lfunc("min", args => {
      let mut s = args[0]
      for i in 1..<args.length() {
        s = num_min(s, args[i])
      }
      s
    }),
  )
  frob(q_p_signum, trigi__fn1("signum", x => signum(x)))
  frob(
    q_p_atan2,
    lfunc("atan2", args => {
      let y = arg(args, 0)
      let x = arg(args, 1)
      // CL:ATAN is defined at (0, 0), Maxima's atan2 is not.
      if zerop(y) && zerop(x) {
        merr("atan2: atan2(0,0) is undefined.", [])
      } else {
        latan(y, x~)
      }
    }),
  )
}

///|
/// Return *BIG-FLOAT-OP* function for F that applies BOP to 1/z. Used for
/// acsc, asec, acot, acsch and acoth. At 0 it declines, and where BOP fails,
/// at a pole of F, it signals a domain error for F.
fn big_float_recip(bop : Value, f : Value) -> Value raise {
  lfunc("big-float-recip", args => {
    let x = arg(args, 0)
    let y = arg(args, 1)
    if zerop1(x).truthy() && (y is Nil || zerop1(y).truthy()) {
      Nil
    } else {
      let ans = trigi__ignore_errors(() => if y.truthy() {
        let d = add2(mul2(x, x), mul2(y, y))
        funcall(bop, [div(x, d), div(neg(y), d)])
      } else {
        funcall(bop, [div(Fix(1L), x)])
      })
      if ans.truthy() {
        ans
      } else {
        domain_error(
          if y.truthy() {
            add2(x, mul2(q_d__pcti, y))
          } else {
            x
          },
          f,
        )
      }
    }
  })
}

///|
/// Return a *BIG-FLOAT-OP* function for F that computes 1/BOP(z). Used for
/// cot, coth and csch. It declines where BOP declines. Where BOP is 0, at a
/// pole of F, it signals a domain error for F.
fn big_float_inverse(bop : Value, f : Value) -> Value raise {
  lfunc("big-float-inverse", args => {
    let x = arg(args, 0)
    let y = arg(args, 1)
    let w = funcall(bop, [x, y])
    if w.truthy() {
      let uv = trisplit(w)
      let u = car(uv)
      let v = cdr(uv)
      let d = add2(mul2(u, u), mul2(v, v))
      if zerop1(d).truthy() {
        domain_error(
          if y.truthy() {
            add2(x, mul2(q_d__pcti, y))
          } else {
            x
          },
          f,
        )
      } else {
        add2(div(u, d), mul2(q_d__pcti, div(neg(v), d)))
      }
    } else {
      Nil
    }
  })
}

///|
fn trigi__fill_big_float_op() -> Unit raise {
  let tbl = symval(q_ear_big_float_op)
  fn frob(k : Value, f : Value) -> Unit raise {
    sethash(k, tbl, f) |> ignore
  }

  // All big-float implementation functions MUST support a required x arg
  // and an optional y arg for the real and imaginary parts.
  frob(q_p_asin, q_big_float_asin)
  frob(q_p_sinh, q_big_float_sinh)
  frob(q_p_asinh, q_big_float_asinh)
  frob(q_p_tanh, q_big_float_tanh)
  frob(q_p_atanh, q_big_float_atanh)
  frob(q_p_acos, q_big_float_acos)
  frob(q_p_acosh, q_big_float_acosh)
  frob(q_p_asech, q_big_float_asech)
  frob(q_p_log, q_big_float_log)
  frob(q_p_sqrt, q_big_float_sqrt)
  frob(q_p_atan, q_big_float_atan)
  frob(q_p_acsc, big_float_recip(q_big_float_asin, q_acsc))
  frob(q_p_asec, big_float_recip(q_big_float_acos, q_asec))
  frob(q_p_acot, big_float_recip(q_big_float_atan, q_acot))
  frob(q_p_acsch, big_float_recip(q_big_float_asinh, q_acsch))
  frob(q_p_acoth, big_float_recip(q_big_float_atanh, q_acoth))
  frob(q_p_tan, q_big_float_tan)
  frob(q_p_cot, big_float_inverse(q_big_float_tan, q_cot))
  frob(q_p_coth, big_float_inverse(q_big_float_tanh, q_coth))
  frob(q_p_csch, big_float_inverse(q_big_float_sinh, q_csch))
}

// Here is a general scheme for defining and applying reflection rules. A
// reflection rule is something like f(-x) --> f(x), or f(-x) --> %pi - f(x).

///|
fn odd_function_reflect(op : Value, x : Value) -> Value raise {
  neg(take(list1(op), [neg(x)]))
}

///|
fn even_function_reflect(op : Value, x : Value) -> Value raise {
  take(list1(op), [neg(x)])
}

///|
/// Reflect only when X is known to be nonzero. Used for acot and acoth,
/// which are non-zero at zero, but odd everywhere else.
fn odd_function_reflect_nonzero(op : Value, x : Value) -> Value raise {
  if eq(t, mnqp(x, Fix(0L))) {
    odd_function_reflect(op, x)
  } else {
    Nil
  }
}

///|
/// When b is nil, do not apply the reflection rule. For trigonometric like
/// functions, b is $trigsign. This function uses 'great' to decide when to
/// apply the rule.
fn apply_reflection_simp(op : Value, x : Value, b? : Value = t) -> Value raise {
  let f = get(op, q_reflection_rule)
  if b.truthy() && f.truthy() && great(neg(x), x).truthy() {
    funcall(f, [op, x])
  } else {
    Nil
  }
}

///|
fn taylorize(op : Value, x : Value) -> Value raise {
  if d_taylorp(x).truthy() {
    mfuncall(
      q_d_apply,
      list([
        q_d_taylor,
        cons(
          list1(q_mlist),
          cons(cons(list1(op), list1(d_ratdisrep(x))), cdr(d_taylorinfo(x))),
        ),
      ]),
    )
  } else {
    Nil
  }
}

///|
/// COMPLEX-NUMBER-P with its multiple values (bool R I).
fn trigi__complex_number_p(
  u : Value,
  ntypep : (Value) -> Bool raise,
) -> (Bool, Value, Value) raise {
  let mut r : Value = Fix(0L)
  let mut im : Value = Fix(0L)
  fn is_i(x : Value) -> Bool raise {
    eq(x, q_d__pcti) && ntypep(Fix(1L))
  }

  fn n_times_i(x : Value) -> Bool raise {
    if cdddr(x) is Nil && ntypep(cadr(x)) {
      im = cadr(x)
      eq(caddr(x), q_d__pcti)
    } else {
      false
    }
  }

  fn n_plus_i(x : Value) -> Bool raise {
    if cdddr(x) is Nil && ntypep(cadr(x)) {
      r = cadr(x)
      if is_i(caddr(x)) {
        im = Fix(1L)
        true
      } else {
        mtimesp(caddr(x)).truthy() && n_times_i(caddr(x))
      }
    } else {
      false
    }
  }

  if ntypep(u) {
    (true, u, Fix(0L))
  } else if atom(u) {
    if is_i(u) {
      (true, Fix(0L), Fix(1L))
    } else {
      (false, Nil, Nil)
    }
  } else if mplusp(u).truthy() {
    if n_plus_i(u) {
      (true, r, im)
    } else {
      (false, Nil, Nil)
    }
  } else if mtimesp(u).truthy() {
    if n_times_i(u) {
      (true, r, im)
    } else {
      (false, Nil, Nil)
    }
  } else {
    (false, Nil, Nil)
  }
}

///|
/// When z is a Maxima complex float or when 'numer' is true and z is a
/// Maxima complex number, evaluate (op z) by applying the mapping from the
/// Maxima operator 'op' to the operator in the hash table '*flonum-op*'.
/// When z isn't a Maxima complex number, return nil.
fn flonum_eval(op : Value, z : Value) -> Value raise {
  let op = gethash(op, symval(q_ear_flonum_op))
  if op.truthy() {
    let (bool, r0, i0) = trigi__complex_number_p(z, x => float_or_rational_p(x).truthy())
    if bool && (symval(q_d_numer).truthy() || floatp(r0) || floatp(i0)) {
      let r = d_float(r0)
      let i = d_float(i0)
      complexify(
        funcall(op, [
          if zerop(i) {
            r
          } else {
            complex(r, i~)
          },
        ]),
      )
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// Big float evaluation of trig-like functions for complex big floats uses
/// rectform, unless the *big-float-op* hash table contains a special case.
fn big_float_eval(op : Value, z : Value) -> Value raise {
  if complex_number_p(z, ntypep=q_bigfloat_or_number_p).truthy() {
    let xy = trisplit(z)
    let x = car(xy)
    let y = cdr(xy)
    let bop = gethash(op, symval(q_ear_big_float_op))
    // If bop is non-NIL, we want to try that first. If bop declines (by
    // returning NIL), we silently give up and use the rectform version.
    if d_bfloatp(x).truthy() && eql(Fix(0L), y) {
      let v : Value = if bop.truthy() { funcall(bop, [x]) } else { Nil }
      if v.truthy() {
        v
      } else {
        d_bfloat(cons(list2(op, q_simp), list1(x)))
      }
    } else if d_bfloatp(x).truthy() || d_bfloatp(y).truthy() {
      let v : Value = if bop.truthy() {
        funcall(bop, [d_bfloat(x), d_bfloat(y)])
      } else {
        Nil
      }
      if v.truthy() {
        v
      } else {
        let mut z = add2(d_bfloat(x), mul2(q_d__pcti, d_bfloat(y)))
        z = d_rectform(cons(list2(op, q_simp), list1(z)))
        d_bfloat(z)
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// The local GIVE-UP of a def-simplifier.
fn trigi__give_up(op : Value, args : Array[Value], form : Value) -> Value raise {
  eqtest(cons(list1(op), list(args)), form)
}

///|
/// Argument count check of a one-argument def-simplifier with parameter y.
fn trigi__check1(form : Value, op : Value) -> Unit raise {
  if length(cdr(form)) != 1 {
    wna_err(form, required_arg_count=Fix(1L), pretty_name=list2(list1(op), q_d_y))
    |> ignore
  }
}

///|
fn trigi__simp_flag_set(form : Value) -> Bool {
  memq(q_simp, cdar(form)).truthy()
}

///|
fn simp__pctsin(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_sin)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      Fix(0L)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      p_piargs_sin_slcos(y)
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_sinh, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_asin, z) {
      cadr(y)
    } else if eq(q_p_acos, z) {
      sqrt1_x_hat2(cadr(y))
    } else if eq(q_p_atan, z) {
      div(cadr(y), sqrt1_plusx_hat2(cadr(y)))
    } else if eq(q_p_acot, z) {
      div(Fix(1L), mul2(sqrt1_plusx_hat2(div(Fix(1L), cadr(y))), cadr(y)))
    } else if eq(q_p_asec, z) {
      sqrt1_x_hat2(div(Fix(1L), cadr(y)))
    } else if eq(q_p_acsc, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_atan2, z) {
      div(cadr(y), sq_sumsq(cadr(y), caddr(y)))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_sin, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_sin, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_sin, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_sin, [y], form)
}

///|
fn simp__pctcos(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_cos)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      Fix(1L)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      p_piargs_sin_slcos(add2(symval(q_p_pi_sl_sl2), y))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return ftake_star(q_p_cosh, [coeff(y, q_d__pcti, Fix(1L))])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_acos, z) {
      cadr(y)
    } else if eq(q_p_asin, z) {
      sqrt1_x_hat2(cadr(y))
    } else if eq(q_p_atan, z) {
      div(Fix(1L), sqrt1_plusx_hat2(cadr(y)))
    } else if eq(q_p_acot, z) {
      div(Fix(1L), sqrt1_plusx_hat2(div(Fix(1L), cadr(y))))
    } else if eq(q_p_asec, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_acsc, z) {
      sqrt1_x_hat2(div(Fix(1L), cadr(y)))
    } else if eq(q_p_atan2, z) {
      div(caddr(y), sq_sumsq(cadr(y), caddr(y)))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_cos, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_cos, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_cos, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_cos, [y], form)
}

///|
fn p_piargs_sin_slcos(x : Value) -> Value raise {
  let b = bind(q_d_float, Nil)
  defer unbind(b)
  let ratcoeff = get_const_or_int_terms(x, q_d__pctpi)
  let coeff = linearize(ratcoeff)
  let zl_rem = get_not_const_or_int_terms(x, q_d__pctpi)
  if zerop1(zl_rem).truthy() {
    p_piargs(coeff, ratcoeff)
  } else if integerp(car(coeff)) && oddp(car(coeff)) {
    // COEFF = (K . Y) with K odd: sin(x+(K*n+Y)*%pi) for an integer n is
    // (-1)^(K*n)*sin(x+Y*%pi).
    let s = p_piargs_sin_slcos(add2(zl_rem, mul2(cdr(coeff), q_d__pctpi)))
    if s.truthy() {
      mul2(power(Fix(-1L), sub(ratcoeff, cdr(coeff))), s)
    } else {
      Nil
    }
  } else if !mevenp(car(coeff)).truthy() {
    Nil
  } else {
    let x = mmod(cdr(coeff), Fix(2L))
    if equal(Fix(0L), x) {
      ftake_star(q_p_sin, [zl_rem])
    } else if equal(Fix(1L), x) {
      neg(ftake_star(q_p_sin, [zl_rem]))
    } else if alike1(symval(q_n1_sl_sl2), x).truthy() {
      ftake_star(q_p_cos, [zl_rem])
    } else if alike1(mk(q_rat, [Fix(3L), Fix(2L)]), x).truthy() {
      neg(ftake_star(q_p_cos, [zl_rem]))
    } else {
      Nil
    }
  }
}

///|
/// Takes form to be a sum and a sum of the summands for which pred is true.
/// Passes simp-flag through to addn if there is more than one term in the
/// sum.
fn filter_sum(pred : Value, form : Value, simp_flag : Value) -> Value raise {
  if mplusp(form).truthy() {
    addn(
      mapcan(
        term => if funcall(pred, [term]).truthy() { list1(term) } else { Nil },
        cdr(form),
      ),
      simp_flag,
    )
  } else if funcall(pred, [form]).truthy() {
    form
  } else {
    Fix(0L)
  }
}

///|
fn trigi__const_or_int_coeff_p(term : Value, var_ : Value) -> Bool raise {
  let coeff = coeff(term, var_, Fix(1L))
  !zerop1(coeff).truthy() &&
  (d_constantp(coeff).truthy() || maxima_integerp(coeff).truthy())
}

///|
/// collect terms of form A*var where A is a constant or integer.
/// returns sum of all such A.
/// does not expand form, so does not find constant term in (x+1)*var.
fn get_const_or_int_terms(form : Value, var_ : Value) -> Value raise {
  coeff(
    filter_sum(
      lfunc("get-const-or-int-terms", args => lbool(
        trigi__const_or_int_coeff_p(arg(args, 0), var_),
      )),
      form,
      Fix(0L),
    ),
    var_,
    Fix(1L),
  )
}

///|
/// collect terms skipped by get-const-or-int-terms
fn get_not_const_or_int_terms(form : Value, var_ : Value) -> Value raise {
  filter_sum(
    lfunc("get-not-const-or-int-terms", args => lbool(
      !trigi__const_or_int_coeff_p(arg(args, 0), var_),
    )),
    form,
    Fix(0L),
  )
}

///|
/// Tests whether form has at least some term of the form a*var where a is
/// constant or integer
fn has_const_or_int_term(form : Value, var_ : Value) -> Value raise {
  lbool(!zerop1(get_const_or_int_terms(form, var_)).truthy())
}

///|
fn simp__pcttan(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_tan)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      Fix(0L)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      p_piargs_tan_slcot(y)
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_tanh, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_atan, z) {
      cadr(y)
    } else if eq(q_p_asin, z) {
      div(cadr(y), sqrt1_x_hat2(cadr(y)))
    } else if eq(q_p_acos, z) {
      div(sqrt1_x_hat2(cadr(y)), cadr(y))
    } else if eq(q_p_acot, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_asec, z) {
      mul2(sqrt1_x_hat2(div(Fix(1L), cadr(y))), cadr(y))
    } else if eq(q_p_acsc, z) {
      div(Fix(1L), mul2(sqrt1_x_hat2(div(Fix(1L), cadr(y))), cadr(y)))
    } else if eq(q_p_atan2, z) {
      div(cadr(y), caddr(y))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_tan, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_tan, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_tan, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_tan, [y], form)
}

///|
fn simp__pctcot(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_cot)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      domain_error(y, q_cot)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      let z = handle__pctpiargs_trig(
        lfunc("%piargs-tan/cot", _ => p_piargs_tan_slcot(
          add2(symval(q_p_pi_sl_sl2), y),
        )),
        y,
        q_p_cot,
      )
      if z.truthy() {
        neg(z)
      } else {
        Nil
      }
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_coth, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_acot, z) {
      cadr(y)
    } else if eq(q_p_asin, z) {
      div(sqrt1_x_hat2(cadr(y)), cadr(y))
    } else if eq(q_p_acos, z) {
      div(cadr(y), sqrt1_x_hat2(cadr(y)))
    } else if eq(q_p_atan, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_asec, z) {
      div(Fix(1L), mul2(sqrt1_x_hat2(div(Fix(1L), cadr(y))), cadr(y)))
    } else if eq(q_p_acsc, z) {
      mul2(sqrt1_x_hat2(div(Fix(1L), cadr(y))), cadr(y))
    } else if eq(q_p_atan2, z) {
      div(caddr(y), cadr(y))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_cot, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_cot, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_cot, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_cot, [y], form)
}

///|
/// If x is of the form tan(u) where u has a nonzero constant linear term in
/// %pi, then %piargs-tan/cot returns a simplified version of x without this
/// constant term.
fn p_piargs_tan_slcot(x : Value) -> Value raise {
  // Set coeff to be the coefficient of $%pi collecting terms with no other
  // atoms, so given %pi(x+1/2), coeff = 1/2. Let zl-rem be the remainder.
  let nice_terms = get_const_or_int_terms(x, q_d__pctpi)
  let coeff = linearize(nice_terms)
  let zl_rem = get_not_const_or_int_terms(x, q_d__pctpi)
  // sin-of-coeff-pi and cos-of-coeff-pi are only non-nil if they are
  // constants that %piargs-offset could compute.
  if zerop1(zl_rem).truthy() {
    let sin_of_coeff_pi = p_piargs(coeff, nice_terms)
    if sin_of_coeff_pi.truthy() {
      let cos_of_coeff_pi = p_piargs(
        cons(car(coeff), rplus(symval(q_n1_sl_sl2), cdr(coeff))),
        add2(nice_terms, symval(q_n1_sl_sl2)),
      )
      return if zerop1(sin_of_coeff_pi).truthy() {
        Fix(0L) // tan(integer*%pi)
      } else if zerop1(cos_of_coeff_pi).truthy() {
        domain_error(x, q_tan)
      } else if cos_of_coeff_pi.truthy() {
        div(sin_of_coeff_pi, cos_of_coeff_pi)
      } else {
        Nil
      }
    }
  }
  // Sets x to the coeff of %pi (mod 1); if this is zero, returns tan of the
  // rest, because tan has periodicity %pi.
  let x = mmod(cdr(coeff), Fix(1L))
  if zerop1(x).truthy() {
    ftake_star(q_p_tan, [zl_rem])
  } else if alike1(symval(q_n1_sl_sl2), x).truthy() {
    // Similarly, if x = 1/2 then return -cot(x).
    neg(ftake_star(q_p_cot, [zl_rem]))
  } else {
    Nil
  }
}

///|
fn simp__pctcsc(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_csc)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      domain_error(y, q_csc)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      handle__pctpiargs_trig(
        lfunc("%piargs-csc/sec", _ => p_piargs_csc_slsec(y)),
        y,
        q_p_csc,
      )
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_csch, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_acsc, z) {
      cadr(y)
    } else if eq(q_p_asin, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_acos, z) {
      div(Fix(1L), sqrt1_x_hat2(cadr(y)))
    } else if eq(q_p_atan, z) {
      div(sqrt1_plusx_hat2(cadr(y)), cadr(y))
    } else if eq(q_p_acot, z) {
      mul2(sqrt1_plusx_hat2(div(Fix(1L), cadr(y))), cadr(y))
    } else if eq(q_p_asec, z) {
      div(Fix(1L), sqrt1_x_hat2(div(Fix(1L), cadr(y))))
    } else if eq(q_p_atan2, z) {
      div(sq_sumsq(cadr(y), caddr(y)), cadr(y))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_csc, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_csc, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_csc, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_csc, [y], form)
}

///|
fn simp__pctsec(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_sec)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      Fix(1L)
    } else if has_const_or_int_term(y, q_d__pctpi).truthy() {
      handle__pctpiargs_trig(
        lfunc("%piargs-csc/sec", _ => p_piargs_csc_slsec(
          add2(symval(q_p_pi_sl_sl2), y),
        )),
        y,
        q_p_sec,
      )
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return ftake_star(q_p_sech, [coeff(y, q_d__pcti, Fix(1L))])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let z = caar(y)
    let v : Value = if eq(q_p_asec, z) {
      cadr(y)
    } else if eq(q_p_asin, z) {
      div(Fix(1L), sqrt1_x_hat2(cadr(y)))
    } else if eq(q_p_acos, z) {
      div(Fix(1L), cadr(y))
    } else if eq(q_p_atan, z) {
      sqrt1_plusx_hat2(cadr(y))
    } else if eq(q_p_acot, z) {
      sqrt1_plusx_hat2(div(Fix(1L), cadr(y)))
    } else if eq(q_p_acsc, z) {
      div(Fix(1L), sqrt1_x_hat2(div(Fix(1L), cadr(y))))
    } else if eq(q_p_atan2, z) {
      div(sq_sumsq(cadr(y), caddr(y)), caddr(y))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(q_p_sec, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(q_p_sec, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(q_p_sec, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_sec, [y], form)
}

///|
fn p_piargs_csc_slsec(x : Value) -> Value raise {
  let b = bind(q_d_float, Nil)
  defer unbind(b)
  let ratcoeff = get_const_or_int_terms(x, q_d__pctpi)
  let coeff = linearize(ratcoeff)
  let mut zl_rem = get_not_const_or_int_terms(x, q_d__pctpi)
  if zerop1(zl_rem).truthy() {
    zl_rem = p_piargs(coeff, ratcoeff)
    if zl_rem.truthy() {
      return div(Fix(1L), zl_rem)
    }
  }
  // As in %PIARGS-SIN/COS, unless the above set ZL-REM to NIL
  if zl_rem.truthy() && integerp(car(coeff)) && oddp(car(coeff)) {
    let s = p_piargs_csc_slsec(add2(zl_rem, mul2(cdr(coeff), q_d__pctpi)))
    if s.truthy() {
      mul2(power(Fix(-1L), sub(ratcoeff, cdr(coeff))), s)
    } else {
      Nil
    }
  } else if !mevenp(car(coeff)).truthy() {
    Nil
  } else {
    let x = mmod(cdr(coeff), Fix(2L))
    if equal(Fix(0L), x) {
      ftake_star(q_p_csc, [zl_rem])
    } else if equal(Fix(1L), x) {
      neg(ftake_star(q_p_csc, [zl_rem]))
    } else if alike1(symval(q_n1_sl_sl2), x).truthy() {
      ftake_star(q_p_sec, [zl_rem])
    } else if alike1(mk(q_rat, [Fix(3L), Fix(2L)]), x).truthy() {
      neg(ftake_star(q_p_sec, [zl_rem]))
    } else {
      Nil
    }
  }
}

///|
fn trigi__sqrt3() -> Value {
  mk(q_mexpt, [Fix(3L), mk(q_rat, [Fix(1L), Fix(2L)])])
}

///|
fn trigi__sqrt2() -> Value {
  mk(q_mexpt, [Fix(2L), mk(q_rat, [Fix(1L), Fix(2L)])])
}

///|
fn trigi__invsqrt3() -> Value {
  mk(q_mexpt, [Fix(3L), mk(q_rat, [Fix(-1L), Fix(2L)])])
}

///|
fn simp__pctatan(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_atan)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  let v = taylorize(mop(form), second(form))
  if v.truthy() {
    return v
  }
  // Simplification for special values
  if zerop1(y).truthy() {
    return y
  }
  if eq(y, q_d_inf) || alike1(y, mk(q_mtimes, [Fix(-1L), q_d_minf])).truthy() {
    return div(q_d__pctpi, Fix(2L))
  }
  if eq(y, q_d_minf) || alike1(y, mk(q_mtimes, [Fix(-1L), q_d_inf])).truthy() {
    return div(q_d__pctpi, Fix(-2L))
  }
  if symval(q_d__pctpiargs).truthy() {
    // Recognize more special values
    let v : Value = if equal(Fix(1L), y) {
      div(q_d__pctpi, Fix(4L))
    } else if equal(Fix(-1L), y) {
      div(q_d__pctpi, Fix(-4L))
    } else if alike1(y, trigi__sqrt3()).truthy() {
      // sqrt(3)
      div(q_d__pctpi, Fix(3L))
    } else if alike1(y, mk(q_mtimes, [Fix(-1L), trigi__sqrt3()])).truthy() {
      // -sqrt(3)
      div(q_d__pctpi, Fix(-3L))
    } else if alike1(y, trigi__invsqrt3()).truthy() {
      // 1/sqrt(3)
      div(q_d__pctpi, Fix(6L))
    } else if alike1(y, mk(q_mtimes, [Fix(-1L), trigi__invsqrt3()])).truthy() {
      // -1/sqrt(3)
      div(q_d__pctpi, Fix(-6L))
    } else if alike1(y, mk(q_mplus, [Fix(-1L), trigi__sqrt2()])).truthy() {
      div(q_d__pctpi, Fix(8L))
    } else if alike1(y, mk(q_mplus, [Fix(1L), trigi__sqrt2()])).truthy() {
      mul2(Fix(3L), div(q_d__pctpi, Fix(8L)))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    // atan(%i*y) -> %i*atanh(y)
    return mul2(q_d__pcti, take(list1(q_p_atanh), [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if !atom(y) && memq(caar(y), list2(q_p_cot, q_p_tan)).truthy() {
    let v : Value = if d_constantp(cadr(y)).truthy() {
      let y_val = mfuncall(
        q_d_mod,
        list2(
          if eq(caar(y), q_p_tan) {
            cadr(y)
          } else {
            sub(symval(q_p_pi_sl_sl2), cadr(y))
          },
          q_d__pctpi,
        ),
      )
      if eq(mlsp(y_val, symval(q_p_pi_sl_sl2)), t) {
        y_val
      } else if eq(mlsp(y_val, q_d__pctpi), t) {
        sub(y_val, q_d__pctpi)
      } else {
        Nil
      }
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if eq(symval(q_d_triginverses), q_d_all) && !atom(y) {
    let v : Value = if eq(caar(y), q_p_tan) { cadr(y) } else { Nil }
    if v.truthy() {
      return v
    }
  }
  if eq(symval(q_d_triginverses), t) && !atom(y) && eq(caar(y), q_p_tan) {
    // Check if y in [-%pi/2, %pi/2]
    let v : Value = if memq(
        csign(sub(cadr(y), symval(q_p_pi_sl_sl2))),
        list2(q_d_nz, q_d_neg),
      ).truthy() &&
      memq(
        csign(add2(cadr(y), symval(q_p_pi_sl_sl2))),
        list2(q_d_pz, q_d_pos),
      ).truthy() {
      cadr(y)
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_logarc).truthy() {
    return logarc(q_p_atan, y)
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(q_p_atan, [y], form)
}

///|
fn p_piargs(x : Value, ratcoeff : Value) -> Value raise {
  if integerp(car(x)) && integerp(cdr(x)) {
    Fix(0L)
  } else if !mevenp(car(x)).truthy() {
    if ratcoeff is Nil {
      Nil
    } else if integerp(car(x)) {
      let offset_result = p_piargs_offset(cdr(x))
      if offset_result.truthy() {
        mul2(power(Fix(-1L), sub(ratcoeff, cdr(x))), offset_result)
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else {
    p_piargs_offset(mmod(cdr(x), Fix(2L)))
  }
}

///|
fn trigi__rat_is(x : Value, n : Int64, d : Int64) -> Bool raise {
  alike1(mk(q_rat, [Fix(n), Fix(d)]), x).truthy()
}

///|
/// simplifies sin(%pi * x) where x is between 0 and 1
/// returns nil if can't simplify
fn p_piargs_offset(x : Value) -> Value raise {
  if trigi__rat_is(x, 1L, 6L) || trigi__rat_is(x, 5L, 6L) {
    symval(q_n1_sl_sl2)
  } else if trigi__rat_is(x, 1L, 4L) || trigi__rat_is(x, 3L, 4L) {
    div(power(Fix(2L), symval(q_n1_sl_sl2)), Fix(2L))
  } else if trigi__rat_is(x, 1L, 3L) || trigi__rat_is(x, 2L, 3L) {
    div(power(Fix(3L), symval(q_n1_sl_sl2)), Fix(2L))
  } else if alike1(symval(q_n1_sl_sl2), x).truthy() {
    Fix(1L)
  } else if trigi__rat_is(x, 7L, 6L) || trigi__rat_is(x, 11L, 6L) {
    symval(q_n_1_sl_sl2)
  } else if trigi__rat_is(x, 4L, 3L) || trigi__rat_is(x, 5L, 3L) {
    div(power(Fix(3L), symval(q_n1_sl_sl2)), Fix(-2L))
  } else if trigi__rat_is(x, 5L, 4L) || trigi__rat_is(x, 7L, 4L) {
    mul2(symval(q_n_1_sl_sl2), power(Fix(2L), symval(q_n1_sl_sl2)))
  } else if trigi__rat_is(x, 3L, 2L) {
    Fix(-1L)
  } else {
    Nil
  }
}

///|
/// identifies integer part of form
/// returns (X . Y) if form can be written as X*some_integer + Y
/// returns nil otherwise
fn linearize(form : Value) -> Value raise {
  if integerp(form) {
    cons(Fix(0L), form)
  } else if numberp(form) {
    Nil
  } else if atom(form) {
    let dum = evod(form)
    if dum.truthy() {
      if eq(q_d_even, dum) {
        cons(Fix(2L), Fix(0L))
      } else {
        cons(Fix(2L), Fix(1L))
      }
    } else if maxima_integerp(form).truthy() {
      cons(Fix(1L), Fix(0L))
    } else {
      Nil
    }
  } else if eq(q_rat, caar(form)) {
    cons(Fix(0L), form)
  } else if eq(q_mplus, caar(form)) {
    lin_mplus(form)
  } else if eq(q_mtimes, caar(form)) {
    lin_mtimes(form)
  } else if eq(q_mexpt, caar(form)) {
    lin_mexpt(form)
  } else {
    Nil
  }
}

///|
fn lin_mplus(form : Value) -> Value raise {
  let mut coeff : Value = Fix(0L)
  let mut zl_rem : Value = Fix(0L)
  let mut tl = cdr(form)
  while tl is Cons(_) {
    let dummy = linearize(car(tl))
    if dummy is Nil {
      return Nil
    }
    coeff = rgcd(car(dummy), coeff)
    zl_rem = rplus(cdr(dummy), zl_rem)
    tl = cdr(tl)
  }
  cons(coeff, mmod(zl_rem, coeff))
}

///|
fn lin_mtimes(form : Value) -> Value raise {
  let mut coeff : Value = Fix(0L)
  let mut zl_rem : Value = Fix(1L)
  let mut fl = cdr(form)
  while fl is Cons(_) {
    let dummy = linearize(car(fl))
    if dummy is Nil {
      return Nil
    }
    coeff = rgcd(
      rtimes(coeff, car(dummy)),
      rgcd(rtimes(coeff, cdr(dummy)), rtimes(zl_rem, car(dummy))),
    )
    zl_rem = rtimes(cdr(dummy), zl_rem)
    fl = cdr(fl)
  }
  cons(coeff, mmod(zl_rem, coeff))
}

///|
fn lin_mexpt(form : Value) -> Value raise {
  if integerp(caddr(form)) && !minusp(caddr(form)) {
    let dummy = linearize(cadr(form))
    if dummy.truthy() {
      return cons(car(dummy), mmod(power(cdr(dummy), caddr(form)), car(dummy)))
    }
  }
  Nil
}

///|
fn rgcd(x : Value, y : Value) -> Value raise {
  if integerp(x) {
    if integerp(y) {
      num_gcd(x, y)
    } else {
      mk(q_rat, [num_gcd(x, cadr(y)), caddr(y)])
    }
  } else if integerp(y) {
    mk(q_rat, [num_gcd(cadr(x), y), caddr(x)])
  } else {
    mk(q_rat, [num_gcd(cadr(x), cadr(y)), num_lcm(caddr(x), caddr(y))])
  }
}

///|
fn maxima_reduce(x : Value, y : Value) -> Value raise {
  let gcd = num_gcd(x, y)
  let mut x = num_truncate(x, b=gcd).0
  let mut y = num_truncate(y, b=gcd).0
  if minusp(y) {
    x = num_neg(x)
    y = num_neg(y)
  }
  if eql(y, Fix(1L)) {
    x
  } else {
    mk_simp(q_rat, [x, y])
  }
}

// The following four functions are generated in code by TRANSL.

///|
fn rplus(x : Value, y : Value) -> Value raise {
  addk(x, y)
}

///|
fn rdifference(x : Value, y : Value) -> Value raise {
  addk(x, timesk(Fix(-1L), y))
}

///|
fn rtimes(x : Value, y : Value) -> Value raise {
  timesk(x, y)
}

///|
fn rremainder(x : Value, y : Value) -> Value raise {
  if equal(Fix(0L), y) {
    dbz_err()
  } else if integerp(x) {
    if integerp(y) {
      maxima_reduce(x, y)
    } else {
      maxima_reduce(num_mul(x, caddr(y)), cadr(y))
    }
  } else if integerp(y) {
    maxima_reduce(cadr(x), num_mul(caddr(x), y))
  } else {
    maxima_reduce(num_mul(cadr(x), caddr(y)), num_mul(caddr(x), cadr(y)))
  }
}

///|
fn d_exponentialize(exp_ : Value) -> Value raise {
  with_special(q_d_demoivre, Nil, () => if atom(exp_) {
    exp_
  } else if trigp(caar(exp_)).truthy() {
    exponentialize(caar(exp_), d_exponentialize(cadr(exp_)))
  } else {
    recur_apply(
      lfunc("$exponentialize", args => d_exponentialize(arg(args, 0))),
      exp_,
    )
  })
}

///|
fn exponentialize(op : Value, arg : Value) -> Value raise {
  let e = q_d__pcte
  let i = q_d__pcti
  if eq(q_p_sin, op) {
    div(
      sub(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
      mul2(Fix(2L), i),
    )
  } else if eq(q_p_cos, op) {
    div(
      add2(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
      Fix(2L),
    )
  } else if eq(q_p_tan, op) {
    div(
      sub(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
      mul2(
        i,
        add2(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
      ),
    )
  } else if eq(q_p_cot, op) {
    div(
      mul2(
        i,
        add2(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
      ),
      sub(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
    )
  } else if eq(q_p_csc, op) {
    div(
      mul2(Fix(2L), i),
      sub(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
    )
  } else if eq(q_p_sec, op) {
    div(
      Fix(2L),
      add2(power(e, mul2(i, arg)), power(e, muln_([Fix(-1L), i, arg]))),
    )
  } else if eq(q_p_sinh, op) {
    div(sub(power(e, arg), power(e, neg(arg))), Fix(2L))
  } else if eq(q_p_cosh, op) {
    div(add2(power(e, arg), power(e, mul2(Fix(-1L), arg))), Fix(2L))
  } else if eq(q_p_tanh, op) {
    div(
      sub(power(e, arg), power(e, neg(arg))),
      add2(power(e, arg), power(e, mul2(Fix(-1L), arg))),
    )
  } else if eq(q_p_coth, op) {
    div(
      add2(power(e, arg), power(e, mul2(Fix(-1L), arg))),
      sub(power(e, arg), power(e, neg(arg))),
    )
  } else if eq(q_p_csch, op) {
    div(Fix(2L), sub(power(e, arg), power(e, neg(arg))))
  } else if eq(q_p_sech, op) {
    div(Fix(2L), add2(power(e, arg), power(e, mul2(Fix(-1L), arg))))
  } else {
    Nil
  }
}

///|
fn coefficient(exp_ : Value, var_ : Value, pow : Value) -> Value raise {
  coeff(exp_, var_, pow)
}

///|
fn mmod(x : Value, mod_ : Value) -> Value raise {
  if integerp(x) && integerp(mod_) {
    let mut x = x
    let v : Value = if zerop(mod_) {
      x
    } else {
      x = num_sub(x, num_mul(mod_, num_truncate(x, b=mod_).0))
      x
    }
    if minusp(v) {
      num_add(x, mod_)
    } else {
      x
    }
  } else if d_ratnump(x).truthy() && d_ratnump(mod_).truthy() {
    let d = num_lcm(d_denom(x), d_denom(mod_))
    let x = mul_star(list2(d, x))
    let mod_ = mul_star(list2(d, mod_))
    div(num_mod(x, mod_), d)
  } else {
    Nil
  }
}

///|
fn linearp(exp_ : Value, var_ : Value) -> Value raise {
  let exp_ = islinear(exp_, var_)
  if exp_.truthy() {
    lbool(!equal(car(exp_), Fix(0L)))
  } else {
    Nil
  }
}

///|
fn mminusp(x : Value) -> Value raise {
  lbool(num_eq(Fix(-1L), signum1(x)))
}

///|
fn mminusp_star(x : Value) -> Value raise {
  let sign = csign(x)
  let m = memq(sign, list2(q_d_neg, q_d_nz))
  if m.truthy() {
    m
  } else {
    lbool(
      mminusp(x).truthy() && !memq(sign, list2(q_d_pos, q_d_pz)).truthy(),
    )
  }
}

///|
/// This should give more information somehow.
fn dbz_err() -> Value raise {
  if !symval(q_errorsw).truthy() {
    merr("Division by zero attempted.", [])
  } else {
    throw_tag(q_errorsw, t)
  }
}

///|
fn dbz_err1(func : Value) -> Value raise {
  if !symval(q_errorsw).truthy() {
    merr("~A: division by zero attempted.", [func])
  } else {
    throw_tag(q_errorsw, t)
  }
}

// ;;;; ATAN2

///|
/// Reduce the input `mod 2 pi` to a value in the interval `(-pi, pi]`.
/// Thus -pi reduces to pi, and pi reduces to pi.
fn reduce_angle_mod_2pi(theta : Value) -> Value raise {
  // The range of both atan2 and carg is `(-pi,pi]`, so give a free pass for
  // such expressions.
  if consp(theta) && (eq(caar(theta), q_p_atan2) || eq(caar(theta), q_p_carg)) {
    theta
  } else {
    let n = ftake(q_d_ceiling, [
      div(sub(theta, q_d__pctpi), mul2(Fix(2L), q_d__pctpi)),
    ])
    sub(theta, muln_([Fix(2L), q_d__pctpi, n]))
  }
}

///|
fn trigi__factors(e : Value) -> Value raise {
  if mtimesp(e).truthy() {
    if mnegp(cadr(e)).truthy() {
      // Split a negative numerical factor into two factors, e.g., -5 is
      // split into factors -1 and 5.
      cons(Fix(-1L), cons(neg(cadr(e)), cddr(e)))
    } else {
      cdr(e)
    }
  } else {
    list1(e)
  }
}

///|
/// Return the product of the absolute values of the nonvanishing factors
/// that are common to p and q. This code doesn't factor p or q, so it only
/// considers factors that are explicit. When there are no such factors,
/// return one, that is, the empty product.
fn nonvanishing_common_factor(p : Value, q : Value) -> Value raise {
  let p_factors = trigi__factors(p)
  let q_factors = trigi__factors(q)
  let pp = fapply(q_d_set, p_factors)
  let qq = fapply(q_d_set, q_factors)
  let ss = cdr(d_intersection(pp, list1(qq)))
  let mut ll : Value = Nil
  for sx in ss.iter() {
    if eq(t, mnqp(sx, Fix(0L))) {
      ll = cons(ftake(q_mabs, [sx]), ll)
    }
  }
  fapply(q_mtimes, ll)
}

///|
fn trigi__sinusoid_p(x : Value) -> Bool raise {
  cosp(x).truthy() ||
  cosp(neg(x)).truthy() ||
  sinp(x).truthy() ||
  sinp(neg(x)).truthy()
}

///|
/// When both `x` and `y` have the form `(+/-) sin(X)` or `(+/-) cos(X)` and
/// the point (x,y) is on the unit circle, return the principal polar angle
/// of the point `(x,y)`. Otherwise, return nil. The principal polar angle is
/// a member of the interval `(-pi,pi]`.
fn polar_angle_if_sinusoids(x : Value, y : Value) -> Value raise {
  if trigi__sinusoid_p(x) && trigi__sinusoid_p(y) {
    let z = d_expand(d_exponentialize(add2(x, mul2(q_d__pcti, y))))
    fn fn_(x : Value) -> Value raise {
      if eql(x, Fix(-1L)) {
        q_d__pctpi
      } else if eq(x, q_d__pcti) {
        div(q_d__pctpi, Fix(2L))
      } else if mexptp(x).truthy() && eq(cadr(x), q_d__pcte) {
        div(caddr(x), q_d__pcti)
      } else {
        Nil
      }
    }

    // When `(x,y)` isn't on the unit circle `z` will not be a product of
    // terms that are on the unit circle, and the `every` check will fail.
    let theta = mapcar(
      fn_,
      if mtimesp(z).truthy() {
        cdr(z)
      } else {
        list1(z)
      },
    )
    if every(v => v.truthy(), theta) {
      reduce_angle_mod_2pi(fapply(q_mplus, theta))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn initialize_atan2_hashtable() -> Value raise {
  let pi_over_two = div(q_d__pctpi, Fix(2L))
  let neg_pi_over_two = div(q_d__pctpi, Fix(-2L))
  let minus_pi = mul2(Fix(-1L), q_d__pctpi)
  let tbl = symval(q_ear_atan2_extended_real_hashtable)
  mapcar(
    z => sethash(list2(first(z), second(z)), tbl, third(z)),
    list([
      list3(q_d_minf, q_d_zerob, neg_pi_over_two),
      list3(q_d_minf, q_d_zeroa, neg_pi_over_two),
      list3(q_d_minf, q_d_ind, neg_pi_over_two),
      list3(q_d_zerob, q_d_minf, minus_pi),
      list3(q_d_zerob, q_d_inf, Fix(0L)),
      list3(q_d_zeroa, q_d_minf, q_d__pctpi),
      list3(q_d_zeroa, q_d_inf, Fix(0L)),
      list3(q_d_ind, q_d_inf, Fix(0L)),
      list3(q_d_inf, q_d_zerob, pi_over_two),
      list3(q_d_inf, q_d_zeroa, pi_over_two),
      list3(q_d_inf, q_d_ind, pi_over_two),
    ]),
  )
}

///|
fn simp__pctatan2(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=Fix(2L),
      pretty_name=list3(list1(q_p_atan2), q_d_y, q_d_x),
    )
    |> ignore
  }
  let mut y = simpcheck(nth(1, form), p__pctsimpflag)
  let mut x = simpcheck(nth(2, form), p__pctsimpflag)
  fn give_up() -> Value raise {
    trigi__give_up(q_p_atan2, [y, x], form)
  }

  // for both x & y, convert -inf to minf and -minf to inf.
  y = canonicalize_plus_inf(y)
  x = canonicalize_plus_inf(x)
  let extended_reals = symval(q_ear_extended_reals)

  // Divide both x & y by the absolute value of common factors that are
  // nonvanishing. Skip this when either x or y depend on an extended real.
  if freeofl(y, extended_reals).truthy() && freeofl(x, extended_reals).truthy() {
    let w = nonvanishing_common_factor(y, x)
    y = div(y, w)
    x = div(x, w)
  }
  let mut signy : Value = Nil
  let mut signx : Value = Nil
  if zerop1(y).truthy() && zerop1(x).truthy() {
    return merr("atan2: atan2(0,0) is undefined.", [])
  }
  if (numberp(x) || ratnump(x).truthy()) && // both numbers
    (numberp(y) || ratnump(y).truthy()) && // ... but not bigfloats
    (symval(q_d_numer).truthy() || floatp(x) || floatp(y)) { // at least one float
    // float contagion
    return latan(d_float(y), x=d_float(x))
  }
  if mnump(x).truthy() &&
    mnump(y).truthy() &&
    (d_bfloatp(x).truthy() || d_bfloatp(y).truthy()) {
    // bfloat contagion
    x = d_bfloat(x)
    y = d_bfloat(y)
    return n_starfpatan(y, list1(x))
  }
  // Look up atan(extended real, extended real) in a hashtable. When the
  // value isn't found in the hashtable, return a nounform.
  if memq(x, extended_reals).truthy() && memq(y, extended_reals).truthy() {
    let default = give_up()
    let (v, found) = gethash2(
      list2(y, x),
      symval(q_ear_atan2_extended_real_hashtable),
    )
    return if found { v } else { default }
  }
  // When either `x` or `y` is in ($und infinity $ind), give up
  let uii = list3(q_d_und, q_d_infinity, q_d_ind)
  if memq(x, uii).truthy() || memq(y, uii).truthy() {
    return give_up()
  }
  if eq(x, q_d_inf) {
    // Simplify atan2(y,inf) -> 0
    return Fix(0L)
  }
  if eq(x, q_d_minf) {
    // Simplify atan2(y,minf) -> %pi for realpart(y)>=0 or -%pi for
    // realpart(y)<0. When sign of y unknown, return noun form.
    let sgn = d_sign(d_realpart(y))
    return if memq(sgn, list3(q_d_pos, q_d_pz, q_d_zero)).truthy() {
      q_d__pctpi
    } else if eq(sgn, q_d_neg) {
      mul2(Fix(-1L), q_d__pctpi)
    } else {
      give_up()
    }
  }
  if eq(y, q_d_inf) {
    return div(q_d__pctpi, Fix(2L))
  }
  if eq(y, q_d_minf) {
    return div(q_d__pctpi, Fix(-2L))
  }
  if free(x, q_d__pcti).truthy() {
    signx = with_special(q_limitp, Nil, () => d_sign(x))
    if signx.truthy() && free(y, q_d__pcti).truthy() {
      signy = with_special(q_limitp, Nil, () => d_sign(y))
      if signy.truthy() {
        let v : Value = if eq(signy, q_d_zero) {
          // Handle atan2(0, x) which is %pi or -%pi depending on the sign of
          // x. We assume that x is never actually zero since atan2(0,0) is
          // undefined.
          if memq(signx, list2(q_d_neg, q_d_nz)).truthy() {
            q_d__pctpi
          } else if memq(signx, list2(q_d_pos, q_d_pz)).truthy() {
            Fix(0L)
          } else if eq(signx, q_d_zero) {
            merr("atan2: atan2(0,0) is undefined.", [])
          } else {
            Nil
          }
        } else if eq(signx, q_d_zero) {
          // Handle atan2(y, 0) which is %pi/2 or -%pi/2, depending on the
          // sign of y.
          if eq(signy, q_d_neg) {
            div(q_d__pctpi, Fix(-2L))
          } else if memq(signy, list2(q_d_pos, q_d_pz)).truthy() {
            div(q_d__pctpi, Fix(2L))
          } else {
            Nil
          }
        } else if alike1(y, x).truthy() {
          // Handle atan2(x,x) which is %pi/4 or -3*%pi/4 depending on the
          // sign of x.
          if eq(signx, q_d_neg) {
            mul2(Fix(-3L), div(q_d__pctpi, Fix(4L)))
          } else if memq(signx, list2(q_d_pos, q_d_pz)).truthy() {
            div(q_d__pctpi, Fix(4L))
          } else {
            Nil
          }
        } else if alike1(y, mul2(Fix(-1L), x)).truthy() {
          // Handle atan2(-x,x) which is 3*%pi/4 or -%pi/4 depending on the
          // sign of x.
          if eq(signx, q_d_neg) {
            mul2(Fix(3L), div(q_d__pctpi, Fix(4L)))
          } else if memq(signx, list2(q_d_pos, q_d_pz)).truthy() {
            div(q_d__pctpi, Fix(-4L))
          } else {
            Nil
          }
        } else {
          Nil
        }
        if v.truthy() {
          return v
        }
      }
    }
  }

  // If $TRIGINVERSES is '$ALL, convert
  // atan2(sin(x), cos(x)) to x,
  // atan2(sin(x), -cos(x)) to %pi - x,
  // atan2(-sin(x), cos(x)) to -x,
  // atan2(-sin(x), -cos(x)) to x - %pi,
  // atan2(cos(x), sin(x)) to %pi/2 - x,
  // atan2(cos(x), -sin(x)) to %pi/2 + x,
  // atan2(-cos(x), sin(x)) to x - %pi/2,
  // atan2(-cos(x), -sin(x)) to -x - %pi/2.
  // At this point, X and Y have already been freed of common factors.
  if eq(symval(q_d_triginverses), q_d_all) {
    let pm1 = list2(Fix(1L), Fix(-1L))
    let sc = list2(q_p_sin, q_p_cos)
    let x_numfactor = d_numfactor(x)
    if member_equal(x_numfactor, pm1).truthy() {
      let x_rest = div(x, x_numfactor)
      if consp(x_rest) {
        let x_op = caar(x_rest)
        if memq(x_op, sc).truthy() {
          let y_numfactor = d_numfactor(y)
          if member_equal(y_numfactor, pm1).truthy() {
            let y_rest = div(y, y_numfactor)
            if consp(y_rest) {
              let y_op = caar(y_rest)
              if memq(y_op, sc).truthy() &&
                !eq(x_op, y_op) &&
                alike1(ftake(q_mabs, [x_numfactor]), ftake(q_mabs, [y_numfactor])).truthy() {
                let arg = cadr(x_rest)
                if alike1(arg, cadr(y_rest)).truthy() {
                  return if eq(x_op, q_p_sin) {
                    // atan2(+-cos(arg), +-sin(arg))
                    mul2(
                      y_numfactor,
                      sub(div(q_d__pctpi, Fix(2L)), mul2(x_numfactor, arg)),
                    )
                  } else {
                    // atan2(+-sin(arg), +-cos(arg))
                    mul2(
                      y_numfactor,
                      if num_eq(Fix(1L), x_numfactor) {
                        arg
                      } else {
                        sub(q_d__pctpi, arg)
                      },
                    )
                  }
                }
              }
            }
          }
        }
      }
    }
  }

  // atan2((+/-)sin(angle),(+/-)cos(angle)) = angle reduced to (-pi,pi]
  // mod 2 pi, and similarly for atan2((+/-)cos(angle),(+/-)sin(angle))
  let v = polar_angle_if_sinusoids(x, y)
  if v.truthy() {
    return v
  }
  if symval(q_d_logarc).truthy() {
    return logarc(q_p_atan2, list2(d_logarc(y), d_logarc(x)))
  }
  // atan2(-y,x) = -atan2(y,x) provided (a) trigsign is true, (b)
  // (great (neg y) y), and (c) (x,y) is off the negative real axis.
  if symval(q_d_trigsign).truthy() &&
    eq(t, mminusp(y)) &&
    (eq(t, mnqp(y, Fix(0L))) || eq(t, mgrp(x, Fix(0L)))) {
    return neg(ftake(q_p_atan2, [neg(y), x]))
  }
  if eq(signx, q_d_pos) {
    // atan2(y,x) = atan(y/x) when x is positive.
    return take(list1(q_p_atan), [div(y, x)])
  }
  if eq(signx, q_d_neg) &&
    memq(signy, list4(q_d_pos, q_d_neg, q_d_pz, q_d_zero)).truthy() {
    return if eq(signy, q_d_neg) {
      sub(ftake(q_p_atan, [div(y, x)]), q_d__pctpi)
    } else if memq(signy, list3(q_d_pos, q_d_pz, q_d_zero)).truthy() {
      add2(ftake(q_p_atan, [div(y, x)]), q_d__pctpi)
    } else {
      give_up()
    }
  }
  give_up()
}

///|
fn init_trigi() -> Unit raise {
  // The trigonometric functions distribute over lists, matrices and
  // equations.
  let dist = list([q_mlist, q_d_matrix, q_mequal])
  for x in [
      q_p_sin, q_p_cos, q_p_tan, q_p_cot, q_p_csc, q_p_sec, q_p_sinh, q_p_cosh,
      q_p_tanh, q_p_coth, q_p_csch, q_p_sech, q_p_asin, q_p_acos, q_p_atan, q_p_acot,
      q_p_acsc, q_p_asec, q_p_asinh, q_p_acosh, q_p_atanh, q_p_acoth, q_p_acsch,
      q_p_asech,
    ] {
    setf_get(x, q_distribute_u_over, dist) |> ignore
  }
  trigi__fill_flonum_op()
  trigi__fill_big_float_op()

  // Put the reflection rule on the property list of the exponential-like
  // functions.
  let pi_minus = lfunc("reflection-rule", args => sub(
    q_d__pctpi,
    take(list1(arg(args, 0)), [neg(arg(args, 1))]),
  ))
  setf_get(q_p_cos, q_reflection_rule, q_even_function_reflect) |> ignore
  setf_get(q_p_sin, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_tan, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_sec, q_reflection_rule, q_even_function_reflect) |> ignore
  setf_get(q_p_csc, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_cot, q_reflection_rule, q_odd_function_reflect) |> ignore
  // See A&S 4.4.14--4.4.19
  setf_get(q_p_acos, q_reflection_rule, pi_minus) |> ignore
  setf_get(q_p_asin, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_atan, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_asec, q_reflection_rule, pi_minus) |> ignore
  setf_get(q_p_acsc, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_acot, q_reflection_rule, q_odd_function_reflect_nonzero)
  |> ignore
  setf_get(q_p_cosh, q_reflection_rule, q_even_function_reflect) |> ignore
  setf_get(q_p_sinh, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_tanh, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_sech, q_reflection_rule, q_even_function_reflect) |> ignore
  setf_get(q_p_csch, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_coth, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_asinh, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_atanh, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_acsch, q_reflection_rule, q_odd_function_reflect) |> ignore
  setf_get(q_p_acoth, q_reflection_rule, q_odd_function_reflect_nonzero)
  |> ignore
  defvar_init(
    q_ear_atan2_extended_real_hashtable,
    make_hash_table(kind=HashTest::Equal),
  )
  defvar_init(
    q_ear_extended_reals,
    list([
      q_d_minf, q_d_zerob, q_d_zeroa, q_d_ind, q_d_und, q_d_inf, q_d_infinity,
    ]),
  )
  // atan2 distributes over lists, matrices, and equations
  putprop(q_p_atan2, list([q_mlist, q_d_matrix, q_mequal]), q_distribute_u_over)
  |> ignore
}
