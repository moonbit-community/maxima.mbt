// Port of src/airy.lisp: Airy functions Ai(z) and Bi(z) - A&S 10.4
//
// airy_ai(z)   - Airy function Ai(z)
// airy_dai(z)  - Derivative of Airy function Ai(z)
// airy_bi(z)   - Airy function Bi(z)
// airy_dbi(z)  - Derivative of Airy function Bi(z)
//
// Copyright (C) 2005 David Billinghurst (GPL)

///|
/// `(bind-fpprec val body)` from float.lisp.
fn[T] airy__bind_fpprec(val : Value, f : () -> T raise) -> T raise {
  let bs = bind_all([
    (q_fpprec, Nil),
    (q_ear_bigfloatzero, Nil),
    (q_ear_bigfloatone, Nil),
    (q_ear_bfhalf, Nil),
    (q_ear_bfmhalf, Nil),
  ])
  defer unbind_all(bs)
  let b = bind(q_d_fpprec, fpprec1(Nil, val))
  defer unbind(b)
  f()
}

///|
/// The arity check and argument of `(def-simplifier name (z) ...)`.
fn airy__arg(form : Value, noun : Value, p__pctsimpflag : Value) -> Value raise {
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(noun), q_d_z),
    )
    |> ignore
  }
  simpcheck(nth(1, form), p__pctsimpflag)
}

///|
/// A double computed by SLATEC code, checked for the overflow SBCL traps.
fn airy__fl(d : Double) -> Value raise {
  bessel__fl(d)
}

///|
/// `(div (power z 3) 9)`
fn airy__z3_9(z : Value) -> Value raise {
  div(power(z, Fix(3L)), Fix(9L))
}

///|
/// `(ftake '%hypergeometric (list '(mlist)) (list '(mlist) b) w)`
fn airy__hyp0f1(b : Value, w : Value) -> Value raise {
  ftake(q_p_hypergeometric, [list1(list1(q_mlist)), list2(list1(q_mlist), b), w])
}

// ---------------------------------------------------------------------------
// Airy Ai function

///|
fn airy_ai(z : Value) -> Value raise {
  if floatp(z) {
    airy_ai_real(z)
  } else if complexp(z) {
    airy_ai_complex(z)
  } else {
    Nil
  }
}

///|
fn simplim_pctairy_ai(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) || eq(z, q_d_minf) {
    // A&S 10.4.59, A&S 10.4.60
    Fix(0L)
  } else {
    // Handle other cases with the function simplifier
    simplify(list2(list1(q_p_airy_ai), z))
  }
}

///|
/// Returns the hypergeometric representation of Airy Ai
fn airy_ai_hypergeometric(z : Value) -> Value raise {
  // See http://functions.wolfram.com/03.05.26.0001.01 and
  // https://fungrim.org/entry/01bbb6/:
  //
  //   Ai(z) = Ai(0)*hypergeometric([],[2/3],z^3/9)
  //     + z*Ai'(0)*hypergeometric([],[4/3],z^3/9)
  add2(
    mul2(
      ftake(q_p_airy_ai, [Fix(0L)]),
      airy__hyp0f1(div(Fix(2L), Fix(3L)), airy__z3_9(z)),
    ),
    muln_([
      z,
      ftake(q_p_airy_dai, [Fix(0L)]),
      airy__hyp0f1(div(Fix(4L), Fix(3L)), airy__z3_9(z)),
    ]),
  )
}

///|
/// Decimal digits destroyed by cancellation in the hypergeometric form of
/// Ai and Ai'. Both terms there grow like Bi, that is like
/// exp(2/3*z^(3/2)), while the combination decays like exp(-2/3*z^(3/2)),
/// so the sum sheds about 2*realpart(2/3*z^(3/2)) nepers, or that over
/// log(10) digits. On the negative real axis, realpart(z^(3/2)) is zero and
/// nothing is lost.
fn airy_cancellation_digits(z : Value) -> Value raise {
  let w = try {
    realpart(
      num_mul(
        num_div(Fix(4L), Fix(3L)),
        expt(
          complex(d_float(d_realpart(z)), i=d_float(d_imagpart(z))),
          num_div(Fix(3L), Fix(2L)),
        ),
      ),
    )
  } catch {
    _ => Nil
  }
  if realp(w) && plusp(w) {
    ceiling1(num_div(w, llog(Flo(10.0))))
  } else {
    Fix(0L)
  }
}

///|
/// Evaluate BUILDER's hypergeometric form of an Airy function at enough
/// extra precision to survive the cancellation, then round back to the
/// caller's FPPREC. Without this, bfloat(airy_ai(20)) returned 0.0b0, and
/// bfloat(airy_ai(30)) returned 2.097152b6 = 2^21 - pure roundoff residue,
/// where the true values are 1.69b-27 and 3.21b-49.
///
/// HYPERGEOMETRIC-BY-SERIES has its own precision loop, but it cannot see
/// this cancellation: Each series is computed to full relative accuracy,
/// and the digits die in the outer sum. That loop doubles its working
/// precision twice before giving up at $MAX_FPPREC, so anything needing
/// more than a quarter of $MAX_FPPREC is out of reach - there we return
/// NIL and let the caller give up, leaving the expression unevaluated
/// rather than handing back a number that is wrong by hundreds of orders
/// of magnitude.
fn airy_bfloat_with_guard_digits(z : Value, builder : Value) -> Value raise {
  let needed = num_add(
    num_add(symval(q_d_fpprec), airy_cancellation_digits(z)),
    Fix(10L),
  )
  if num_lt(num_mul(Fix(4L), needed), symval(q_d_max_fpprec)) {
    // BUILDER is called inside the widened scope on purpose: It forms
    // z^3/9, and building that at the caller's FPPREC would round the
    // argument before the extra digits could do any good.
    let hi = airy__bind_fpprec(needed, () => d_rectform(
      d_bfloat(funcall(builder, [z])),
    ))
    d_rectform(d_bfloat(hi))
  } else {
    Nil
  }
}

///|
/// (def-simplifier airy_ai (z) ...)
fn simp__pctairy_ai(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = airy__arg(form, q_p_airy_ai, p__pctsimpflag)
  if equal(z, Fix(0L)) {
    // A&S 10.4.4: Ai(0) = 3^(-2/3)/gamma(2/3)
    return div(
      power(Fix(3L), div(Fix(-2L), Fix(3L))),
      take(list1(q_p_gamma), [div(Fix(2L), Fix(3L))]),
    )
  }
  let v = flonum_eval(mop(form), z)
  if v.truthy() {
    return v
  }
  if bigfloat_numerical_eval_p(list1(z)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    let v = airy_bfloat_with_guard_digits(z, q_airy_ai_hypergeometric)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    airy_ai_hypergeometric(z)
  } else {
    eqtest(cons(list1(q_p_airy_ai), list1(z)), form)
  }
}

// ---------------------------------------------------------------------------
// Derivative dAi/dz of Airy function Ai(z)

///|
fn airy_dai(z : Value) -> Value raise {
  if floatp(z) {
    airy_dai_real(z)
  } else if complexp(z) {
    airy_dai_complex(z)
  } else {
    Nil
  }
}

///|
fn simplim_pctairy_dai(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    // A&S 10.4.61
    Fix(0L)
  } else if eq(z, q_d_minf) {
    // A&S 10.4.62
    q_d_und
  } else {
    // Handle other cases with the function simplifier
    simplify(list2(list1(q_p_airy_dai), z))
  }
}

///|
/// Returns the hypergeometric representation of Ai'(x), the derivative of
/// the Airy function Ai(x)
fn airy_dai_hypergeometric(z : Value) -> Value raise {
  // See http://functions.wolfram.com/03.07.26.0001.01 and
  // https://fungrim.org/entry/20e530/.
  //
  //   Ai'(z) = Ai'(0)*hypergeometric([],[1/3],z^3/9)
  //     + z^2/2*Ai(0)*hypergeometric([],[5/3],z^3/9)
  add2(
    mul2(
      ftake(q_p_airy_dai, [Fix(0L)]),
      airy__hyp0f1(div(Fix(1L), Fix(3L)), airy__z3_9(z)),
    ),
    muln_([
      z,
      z,
      mk_simp(q_rat, [Fix(1L), Fix(2L)]),
      ftake(q_p_airy_ai, [Fix(0L)]),
      airy__hyp0f1(div(Fix(5L), Fix(3L)), airy__z3_9(z)),
    ]),
  )
}

///|
/// (def-simplifier airy_dai (z) ...)
fn simp__pctairy_dai(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = airy__arg(form, q_p_airy_dai, p__pctsimpflag)
  if equal(z, Fix(0L)) {
    // A&S 10.4.5: Ai'(0) = -3^(-1/3)/gamma(1/3)
    return div(
      Fix(-1L),
      mul2(
        power(Fix(3L), div(Fix(1L), Fix(3L))),
        take(list1(q_p_gamma), [div(Fix(1L), Fix(3L))]),
      ),
    )
  }
  let v = flonum_eval(mop(form), z)
  if v.truthy() {
    return v
  }
  if bigfloat_numerical_eval_p(list1(z)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    let v = airy_bfloat_with_guard_digits(z, q_airy_dai_hypergeometric)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_hypergeometric_representation).truthy() {
    airy_dai_hypergeometric(z)
  } else {
    eqtest(cons(list1(q_p_airy_dai), list1(z)), form)
  }
}

// ---------------------------------------------------------------------------
// Airy Bi function

///|
fn airy_bi(z : Value) -> Value raise {
  if floatp(z) {
    airy_bi_real(z)
  } else if complexp(z) {
    airy_bi_complex(z)
  } else {
    Nil
  }
}

///|
fn simplim_pctairy_bi(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    // A&S 10.4.63
    q_d_inf
  } else if eq(z, q_d_minf) {
    // A&S 10.4.64
    Fix(0L)
  } else {
    // Handle other cases with the function simplifier
    simplify(list2(list1(q_p_airy_bi), z))
  }
}

///|
/// Returns the hypergeometric representation of Airy Bi
fn airy_bi_hypergeometric(z : Value) -> Value raise {
  // See http://functions.wolfram.com/03.06.26.0001.01 and
  // https://fungrim.org/entry/bd319e/
  //
  //  Bi(z) = Bi(0)*hypergeometric([],[2/3],z^3/9)
  //    + z*Bi'(0)*hypergeometric([],[4/2],z^3/9)
  add2(
    mul2(
      ftake(q_p_airy_bi, [Fix(0L)]),
      airy__hyp0f1(div(Fix(2L), Fix(3L)), airy__z3_9(z)),
    ),
    muln_([
      z,
      ftake(q_p_airy_dbi, [Fix(0L)]),
      airy__hyp0f1(div(Fix(4L), Fix(3L)), airy__z3_9(z)),
    ]),
  )
}

///|
/// (def-simplifier airy_bi (z) ...)
fn simp__pctairy_bi(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = airy__arg(form, q_p_airy_bi, p__pctsimpflag)
  if equal(z, Fix(0L)) {
    // A&S 10.4.4: Bi(0) = sqrt(3) 3^(-2/3)/gamma(2/3)
    return div(
      mul2(
        power(Fix(3L), mk_simp(q_rat, [Fix(1L), Fix(2L)])),
        power(Fix(3L), div(Fix(-2L), Fix(3L))),
      ),
      take(list1(q_p_gamma), [div(Fix(2L), Fix(3L))]),
    )
  }
  let v = flonum_eval(mop(form), z)
  if v.truthy() {
    v
  } else if bigfloat_numerical_eval_p(list1(z)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    d_rectform(d_bfloat(airy_bi_hypergeometric(z)))
  } else if symval(q_d_hypergeometric_representation).truthy() {
    airy_bi_hypergeometric(z)
  } else {
    eqtest(cons(list1(q_p_airy_bi), list1(z)), form)
  }
}

// ---------------------------------------------------------------------------
// Derivative dBi/dz of Airy function Bi(z)

///|
fn airy_dbi(z : Value) -> Value raise {
  if floatp(z) {
    airy_dbi_real(z)
  } else if complexp(z) {
    airy_dbi_complex(z)
  } else {
    Nil
  }
}

///|
fn simplim_pctairy_dbi(expr : Value, var_ : Value, val : Value) -> Value raise {
  // Look for the limit of the argument
  let z = limit(cadr(expr), var_, val, q_think)
  if eq(z, q_d_inf) {
    // A&S 10.4.66
    q_d_inf
  } else if eq(z, q_d_minf) {
    // A&S 10.4.67
    q_d_und
  } else {
    // Handle other cases with the function simplifier
    simplify(list2(list1(q_p_airy_dbi), z))
  }
}

///|
/// Returns the hypergeometric representation of Bi'(z), the derivative of
/// Airy Bi
fn airy_dbi_hypergeometric(z : Value) -> Value raise {
  // See http://functions.wolfram.com/03.08.26.0001.01 and
  // https://fungrim.org/entry/4d65e5/.
  //
  //  Bi'(z) = Bi'(0)*hypergeometric([],[1/3],z^3/9)
  //    + z^2/2*Bi(0)*hypergeometric([],[5/3],z^3/9)
  add2(
    mul2(
      ftake(q_p_airy_dbi, [Fix(0L)]),
      airy__hyp0f1(div(Fix(1L), Fix(3L)), airy__z3_9(z)),
    ),
    muln_([
      z,
      z,
      mk_simp(q_rat, [Fix(1L), Fix(2L)]),
      ftake(q_p_airy_bi, [Fix(0L)]),
      airy__hyp0f1(div(Fix(5L), Fix(3L)), airy__z3_9(z)),
    ]),
  )
}

///|
/// (def-simplifier airy_dbi (z) ...)
fn simp__pctairy_dbi(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  let z = airy__arg(form, q_p_airy_dbi, p__pctsimpflag)
  if equal(z, Fix(0L)) {
    // A&S 10.4.5: Bi'(0) = sqrt(3) 3^(-1/3)/gamma(1/3)
    return div(
      mul2(
        power(Fix(3L), mk_simp(q_rat, [Fix(1L), Fix(2L)])),
        power(Fix(3L), div(Fix(-1L), Fix(3L))),
      ),
      take(list1(q_p_gamma), [div(Fix(1L), Fix(3L))]),
    )
  }
  let v = flonum_eval(mop(form), z)
  if v.truthy() {
    v
  } else if bigfloat_numerical_eval_p(list1(z)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(z)).truthy() {
    d_rectform(d_bfloat(airy_dbi_hypergeometric(z)))
  } else if symval(q_d_hypergeometric_representation).truthy() {
    airy_dbi_hypergeometric(z)
  } else {
    eqtest(cons(list1(q_p_airy_dbi), list1(z)), form)
  }
}

// ---------------------------------------------------------------------------
// Numerical routines using slatec functions

///|
/// The C library's pow, which SBCL's EXPT of a double-float calls.
extern "C" fn airy__c_pow(x : Double, y : Double) -> Double = "pow"

///|
/// The C library's exp, which SBCL's EXP of a double-float calls.
extern "C" fn airy__c_exp(x : Double) -> Double = "exp"

///|
/// `(sqrt (abs z))` and `(* 2/3 (expt (abs z) 3/2))` for the real Airy
/// derivative routines.
fn airy__rz_c(z : Double) -> (Double, Double) raise {
  let az = z.abs()
  let rz = az.sqrt()
  // (expt az 3/2) is libm pow(az, 1.5d0), trapped on overflow.
  let p = airy__fl(airy__c_pow(az, 1.5))
  let c = num_mul(num_div(Fix(2L), Fix(3L)), p)
  (rz, to_double(c))
}

///|
/// Airy function Ai(z) for real z
fn airy_ai_real(z : Value) -> Value raise {
  let z = to_double(z)
  // slatec:dai gives up at 92.5747007268, but Ai(z) is an ordinary double
  // up to about 107.3. Above dai's cutoff use the formula dai itself uses
  // there, see dai.f label 30. The upper test keeps z*sqrt(z) from
  // overflowing for a huge z.
  if z < 92.5747007268 {
    airy__fl(@slatec.dai(z))
  } else if z < 108.0 {
    num_mul(
      airy__fl(@slatec.daie(z)),
      airy__fl(airy__c_exp(-2.0 * z * z.sqrt() / 3.0)),
    )
  } else {
    Flo(0.0)
  }
}

///|
/// Airy function Ai(z) for complex z
fn airy_ai_complex(z : Value) -> Value raise {
  let (air, aii, nz, ierr) = @slatec.zairy(
    to_double(realpart(z)),
    to_double(imagpart(z)),
    0,
    1,
    0.0,
    0.0,
    0,
    0,
  )
  // Check nz and ierr for errors
  if nz == 0 && ierr == 0 {
    complex(airy__fl(air), i=airy__fl(aii))
  } else {
    Nil
  }
}

///|
/// Derivative dAi/dz of Airy function Ai(z) for real z
fn airy_dai_real(z : Value) -> Value raise {
  let z = to_double(z)
  let (rz, c) = airy__rz_c(z)
  let (_ai, dai) = @slatec.djairy(z, rz, c, 0.0, 0.0)
  airy__fl(dai)
}

///|
/// Derivative dAi/dz of Airy function Ai(z) for complex z
fn airy_dai_complex(z : Value) -> Value raise {
  let (air, aii, nz, ierr) = @slatec.zairy(
    to_double(realpart(z)),
    to_double(imagpart(z)),
    1,
    1,
    0.0,
    0.0,
    0,
    0,
  )
  // Check nz and ierr for errors
  if nz == 0 && ierr == 0 {
    complex(airy__fl(air), i=airy__fl(aii))
  } else {
    Nil
  }
}

///|
/// Airy function Bi(z) for real z
fn airy_bi_real(z : Value) -> Value raise {
  let z = to_double(z)
  // slatec:dbi issues overflows for z > zmax. See dbi.{f,lisp}
  // This value is correct for IEEE double precision
  let zmax = 104.2179765192136
  if z < zmax {
    airy__fl(@slatec.dbi(z))
  } else {
    Nil
  }
}

///|
/// Airy function Bi(z) for complex z
fn airy_bi_complex(z : Value) -> Value raise {
  let (bir, bii, ierr) = @slatec.zbiry(
    to_double(realpart(z)),
    to_double(imagpart(z)),
    0,
    1,
    0.0,
    0.0,
    0,
  )
  // Check ierr for errors
  if ierr == 0 {
    complex(airy__fl(bir), i=airy__fl(bii))
  } else {
    Nil
  }
}

///|
/// Derivative dBi/dz of Airy function Bi(z) for real z
fn airy_dbi_real(z : Value) -> Value raise {
  let z = to_double(z)
  // Overflows for z > zmax.
  // This value is correct for IEEE double precision
  let zmax = 104.1525
  if z < zmax {
    let (rz, c) = airy__rz_c(z)
    let (_rx, _c, _bi, dbi) = @slatec.dyairy(z, rz, c, 0.0, 0.0)
    airy__fl(dbi)
  } else {
    // Will overflow. Return unevaluated.
    Nil
  }
}

///|
/// Derivative dBi/dz of Airy function Bi(z) for complex z
fn airy_dbi_complex(z : Value) -> Value raise {
  let (bir, bii, ierr) = @slatec.zbiry(
    to_double(realpart(z)),
    to_double(imagpart(z)),
    1,
    1,
    0.0,
    0.0,
    0,
  )
  // Check ierr for errors
  if ierr == 0 {
    complex(airy__fl(bir), i=airy__fl(bii))
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Top-level forms

///|
fn airy__defgrad(name : Value, derivs : Array[Value]) -> Unit {
  push_special(name, q_ear_defgrad_syms) |> ignore
  setf_get(name, q_grad, cons(list1(q_d_z), list(derivs))) |> ignore
}

///|
fn init_airy() -> Unit raise {
  let bags = () => list([q_mlist, q_d_matrix, q_mequal])
  let flonum_op = symval(q_ear_flonum_op)

  // Airy Ai function
  putprop(q_p_airy_ai, q_simplim_pctairy_ai, q_simplim_pctfunction) |> ignore
  airy__defgrad(q_p_airy_ai, [maxima_lit("$airy_dai(z)")])
  // airy_ai distributes over lists, matrices, and equations
  putprop(q_p_airy_ai, bags(), q_distribute_u_over) |> ignore
  // airy_ai has mirror symmetry
  putprop(q_p_airy_ai, t, q_commutes_with_conjugate) |> ignore
  // Integral of Ai(z)
  // http://functions.wolfram.com/03.05.21.0002.01
  // (z/(3^(2/3)*gamma(2/3)))*hypergeometric([1/3],[2/3,4/3],z^3/9)
  // - (3^(1/6)/(4*%pi))*z^2*gamma(2/3)*hypergeometric([2/3],[4/3,5/3],z^3/9);
  putprop(
    q_p_airy_ai,
    lread(
      "((z) ((mplus) ((mtimes) ((mexpt) 3 ((rat) -2 3)) ((mexpt) ((%gamma) ((rat) 2 3)) -1) ((%hypergeometric) ((mlist) ((rat) 1 3)) ((mlist) ((rat) 2 3) ((rat) 4 3)) ((mtimes) ((rat) 1 9) ((mexpt) z 3))) z) ((mtimes) ((rat) -1 4) ((mexpt) 3 ((rat) 1 6)) ((mexpt) $%pi -1) ((%gamma) ((rat) 2 3)) ((%hypergeometric) ((mlist) ((rat) 2 3)) ((mlist) ((rat) 4 3) ((rat) 5 3)) ((mtimes) ((rat) 1 9) ((mexpt) z 3))) ((mexpt) z 2))))",
    ),
    q_integral,
  )
  |> ignore
  sethash(q_p_airy_ai, flonum_op, q_airy_ai) |> ignore

  // Derivative dAi/dz of Airy function Ai(z)
  putprop(q_p_airy_dai, q_simplim_pctairy_dai, q_simplim_pctfunction)
  |> ignore
  airy__defgrad(q_p_airy_dai, [maxima_lit("$z*airy_ai(z)")])
  putprop(q_p_airy_dai, lread("((z) ((%airy_ai) z))"), q_integral) |> ignore
  putprop(q_p_airy_dai, bags(), q_distribute_u_over) |> ignore
  putprop(q_p_airy_dai, t, q_commutes_with_conjugate) |> ignore
  sethash(q_p_airy_dai, flonum_op, q_airy_dai) |> ignore

  // Airy Bi function
  putprop(q_p_airy_bi, q_simplim_pctairy_bi, q_simplim_pctfunction) |> ignore
  airy__defgrad(q_p_airy_bi, [maxima_lit("$ airy_dbi(z)")])
  putprop(q_p_airy_bi, bags(), q_distribute_u_over) |> ignore
  putprop(q_p_airy_bi, t, q_commutes_with_conjugate) |> ignore
  // Integral of Bi(z)
  // http://functions.wolfram.com/03.06.21.0002.01
  // (z/(3^(1/6)*gamma(2/3)))*hypergeometric([1/3],[2/3,4/3],z^3/9)
  // + (3^(2/3)/(4*%pi))*z^2*gamma(2/3)*hypergeometric([2/3],[4/3,5/3],z^3/9);
  putprop(
    q_p_airy_bi,
    lread(
      "((z) ((mplus) ((mtimes) ((mexpt) 3 ((rat) -1 6)) ((mexpt) ((%gamma) ((rat) 2 3)) -1) ((%hypergeometric) ((mlist) ((rat) 1 3)) ((mlist) ((rat) 2 3) ((rat) 4 3)) ((mtimes) ((rat) 1 9) ((mexpt) z 3))) z) ((mtimes) ((rat) 1 4) ((mexpt) 3 ((rat) 2 3)) ((mexpt) $%pi -1) ((%gamma) ((rat) 2 3)) ((%hypergeometric) ((mlist) ((rat) 2 3)) ((mlist) ((rat) 4 3) ((rat) 5 3)) ((mtimes) ((rat) 1 9) ((mexpt) z 3))) ((mexpt) z 2))))",
    ),
    q_integral,
  )
  |> ignore
  sethash(q_p_airy_bi, flonum_op, q_airy_bi) |> ignore

  // Derivative dBi/dz of Airy function Bi(z)
  putprop(q_p_airy_dbi, q_simplim_pctairy_dbi, q_simplim_pctfunction)
  |> ignore
  airy__defgrad(q_p_airy_dbi, [maxima_lit("$z*airy_bi(z)")])
  putprop(q_p_airy_dbi, lread("((z) ((%airy_bi) z))"), q_integral) |> ignore
  putprop(q_p_airy_dbi, bags(), q_distribute_u_over) |> ignore
  putprop(q_p_airy_dbi, t, q_commutes_with_conjugate) |> ignore
  sethash(q_p_airy_dbi, flonum_op, q_airy_dbi) |> ignore
}
