// Port of src/specfn.lisp: Macsyma special function routines --
// polylogarithms li[s](z), polygamma psi[s](z) (with their taylor
// routines), the Lambert W function, generalized_lambert_w and the
// Bateman function kbateman[v](z), plus the bigfloat-package numerical
// code for li[s] and Catalan's constant.

///|
/// `(mnumericalp arg)`: `(or (floatp arg) (and (or $numer $float) (integerp arg)))`
fn mnumericalp(arg : Value) -> Value raise {
  lbool(
    floatp(arg) ||
    ((symval(q_d_numer).truthy() || symval(q_d_float).truthy()) && integerp(arg)),
  )
}

// ---------------------------------------------------------------------------
// Literals

///|
let specfn__lit_rat_half : Value = try! lread("((rat) 1 2)")

///|
let specfn__lit_neg_half_log2 : Value = try! lread(
  "((mtimes simp) ((rat simp) -1 2) ((%log simp) 2))",
)

///|
let specfn__lit_neg_log2 : Value = try! lread(
  "((mtimes simp) -1 ((%log simp) 2))",
)

///|
let specfn__lit_neg_inv_e : Value = try! lread(
  "((mtimes simp) -1 ((mexpt simp) $%e -1))",
)

///|
let specfn__lit_neg_half_pi : Value = try! lread("((mtimes) ((rat) -1 2) $%pi)")

///|
let specfn__lit_half_i_pi : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 2) $%i $%pi)",
)

///|
let specfn__lit_psi_m1 : Value = try! lread("(($psi) -1)")

///|
let specfn__lit_expgam_terms : Value = try! lread("(((-1 . 1) 1 . 1))")

///|
let specfn__lit_neg_gamma : Value = try! lread("((mtimes) -1 $%gamma)")

///|
let specfn__lit_m1_m1 : Value = try! lread("((-1 . 1) -1 . 1)")

///|
let specfn__lit_zero_one : Value = try! lread("((0 . 1) 0 . 1)")

///|
fn specfn__rat(n : Int64, d : Int64) -> Value {
  mk_simp(q_rat, [Fix(n), Fix(d)])
}

///|
fn specfn__log(n : Int64) -> Value {
  mk(q_p_log, [Fix(n)])
}

// ---------------------------------------------------------------------------
// subtitle polylogarithm routines

///|
/// Simplifier for li[s](a).
fn simp__pctli(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let pretty_name = list([
    list1(q_mqapply),
    list2(list2(q_d_li, q_array), q_s),
    q_a,
  ])
  sub_arg_count_check(int(1), int(1), form, pretty_name) |> ignore
  let s = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunsubs(form)))
  let a = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunargs(form)))
  let give_up = () => eqtest(subfunmakes(q_d_li, list1(s), list1(a)), form)
  with_special(q_d_zerobern, t, () => {
    let r = specfn__li_cases(s, a)
    if r.truthy() {
      r
    } else {
      give_up()
    }
  })
}

///|
/// The COND of the li simplifier.
fn specfn__li_cases(s : Value, a : Value) -> Value raise {
  if zerop1(a).truthy() {
    return a
  }
  if mnump(s).truthy() && ratgreaterp(s, int(1)).truthy() && eql(a, int(1)) {
    // li[s](a) = zeta(s) if s > 1 and if a = 1.  We simplify this only
    // if s is a rational number and a is the integer 1.
    return ftake(q_p_zeta, [s])
  }
  if !integerp(s) {
    return Nil
  }
  if num_eq(s, int(1)) {
    return if onep1(a).truthy() {
      simp_domain_error(list([Str("li: li[~:M](~:M) is undefined."), s, a]))
    } else {
      neg(take(list1(q_p_log), [sub(int(1), a)]))
    }
  }
  if num_eq(s, int(0)) {
    return div(a, sub(int(1), a))
  }
  if num_lt(s, int(0)) {
    return lisimp_negative_integer(s, a)
  }
  if integerp(a) && num_gt(s, int(1)) {
    let v = if num_eq(a, int(1)) {
      take(list1(q_p_zeta), [s])
    } else if num_eq(a, int(-1)) {
      // li[s](-1) = (2^(1-s)-1)*zeta(s)
      mul(
        list2(
          add(list2(int(-1), inv(expt(int(2), num_sub(s, int(1)))))),
          take(list1(q_p_zeta), [s]),
        ),
      )
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if num_eq(s, int(2)) {
    return li2simp(a)
  }
  if num_eq(s, int(3)) {
    return li3simp(a)
  }
  if complex_float_numerical_eval_p(list1(a)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(a)).truthy() {
    if bf_eq(int(1), bf_to(a)) {
      // li[s](1) -> zeta(s)
      let result = ftake(q_p_zeta, [s])
      return if floatp(a) { d_float(result) } else { d_bfloat(result) }
    } else if bf_eq(int(-1), bf_to(a)) {
      // li[s](-1) = (2^(1-s)-1)*zeta(s)
      let result = mul(
        list2(
          add(list2(int(-1), inv(expt(int(2), num_sub(s, int(1)))))),
          take(list1(q_p_zeta), [s]),
        ),
      )
      return if floatp(a) { d_float(result) } else { d_bfloat(result) }
    } else if integerp(s) {
      return maxima_to(bf_li_s_simp(s, bf_to(a)))
    }
    return Nil
  }
  Nil
}

///|
/// Expand the Polylogarithm li[s](z) for a negative integer parameter s.
fn lisimp_negative_integer(s : Value, z : Value) -> Value raise {
  let n = num_neg(s)
  let f1 = inv(power(sub(int(1), z), num_add(n, int(1))))
  let index1 = gensumindex()
  let f2 = with_special(q_d_simpsum, t, () => dosum(
    mul(
      list2(power(z, index1), {
        let index2 = gensumindex()
        dosum(
          mul(
            list3(
              power(int(-1), add(list2(index2, int(1)))),
              take(list1(q_p_binomial), [num_add(n, int(1)), sub(index2, int(1))]),
              power(add(list2(int(1), sub(index1, index2))), n),
            ),
          ),
          index2,
          int(1),
          index1,
          t,
        )
      }),
    ),
    index1,
    int(1),
    n,
    t,
  ))
  mul(list2(f1, f2))
}

///|
fn li2simp(arg : Value) -> Value raise {
  if mnumericalp(arg).truthy() {
    // When arg is a float or rational, use the original li2numer using
    // Spences function.
    li2numer(lfloat(arg))
  } else if complex_float_numerical_eval_p(list1(arg)).truthy() {
    // For complex args that should should result in float answers, use
    // bigfloat::li2numer.
    maxima_to(bf_li2numer(bf_to(d_rectform(d_float(arg)))))
  } else if bigfloat_numerical_eval_p(list1(arg)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    maxima_to(bf_li2numer(bf_to(d_rectform(d_bfloat(arg)))))
  } else if alike1(arg, specfn__lit_rat_half).truthy() {
    // li[2](1/2) = zeta(2)/2-log(2)^2/2
    //            = %pi^2/12-log(2)^2/2
    add(
      list2(
        div(take(list1(q_p_zeta), [int(2)]), int(2)),
        mul(
          list2(specfn__rat(-1L, 2L), power(take(list1(q_p_log), [int(2)]), int(2))),
        ),
      ),
    )
  } else if eql(arg, int(2)) {
    // li[2](2) = %pi^2/4 - %i*%pi*log(2)
    //
    // See http://functions.wolfram.com/10.07.03.0007.01.  But this also
    // follows from https://dlmf.nist.gov/25.12.E4:
    //
    // li[2](z) + li[2](1/z) = -%pi^2/6-log(-z)^2/2
    //
    // with z = 2.
    sub(
      div(power(q_d__pctpi, int(2)), int(4)),
      mul(list3(q_d__pctpi, q_d__pcti, ftake(q_p_log, [int(2)]))),
    )
  } else if eq(arg, q_d__pcti) {
    // li[2](%i) = %i*%catalan - %pi^2/48
    //
    // See http://functions.wolfram.com/10.07.03.0008.01
    sub(
      mul(list2(q_d__pcti, q_d__pctcatalan)),
      mul(list3(q_d__pctpi, q_d__pctpi, div(int(1), int(48)))),
    )
  } else if alike1(arg, neg(q_d__pcti)).truthy() {
    // li[2](-%i) = -%i*%catalan - %pi^2/48
    //
    // See http://functions.wolfram.com/10.07.03.0009.01, but this follows
    // from the mirror symmetry: li[2](conjugate(z)) = conjugate(li[2](z)),
    // which holds when z is not on the negative real line.
    sub(
      mul(list3(int(-1), q_d__pcti, q_d__pctcatalan)),
      mul(list3(q_d__pctpi, q_d__pctpi, div(int(1), int(48)))),
    )
  } else if alike1(arg, sub(int(1), q_d__pcti)).truthy() {
    // li[2](1 - %i) = %pi^2/16 - %i*%catalan - %pi*%i*log(2)/4
    //
    // See http://functions.wolfram.com/10.07.03.0010.01
    sub(
      div(power(q_d__pctpi, int(2)), int(16)),
      add(
        list2(
          mul(list2(q_d__pcti, q_d__pctcatalan)),
          mul(
            list4(q_d__pctpi, q_d__pcti, div(int(1), int(4)), ftake(q_p_log, [int(2)])),
          ),
        ),
      ),
    )
  } else if alike1(arg, add(list2(int(1), q_d__pcti))).truthy() {
    // li[2](1 + %i) = %pi^2/16 + %i*%catalan + %pi*%i*log(2)/4
    //
    // See http://functions.wolfram.com/10.07.03.0011.01, but this also
    // follows from mirror symmetry.
    add(
      list3(
        div(power(q_d__pctpi, int(2)), int(16)),
        mul(list2(q_d__pcti, q_d__pctcatalan)),
        mul(
          list4(q_d__pctpi, q_d__pcti, div(int(1), int(4)), ftake(q_p_log, [int(2)])),
        ),
      ),
    )
  } else {
    Nil
  }
}

///|
fn li3simp(arg : Value) -> Value raise {
  if float_numerical_eval_p(list1(arg)).truthy() ||
    complex_float_numerical_eval_p(list1(arg)).truthy() {
    maxima_to(bf_li3numer(bf_to(d_rectform(d_float(arg)))))
  } else if bigfloat_numerical_eval_p(list1(arg)).truthy() ||
    complex_bigfloat_numerical_eval_p(list1(arg)).truthy() {
    maxima_to(bf_li3numer(bf_to(d_rectform(d_bfloat(arg)))))
  } else if alike1(arg, specfn__lit_rat_half).truthy() {
    add(
      list3(
        mul(list2(specfn__rat(7L, 8L), take(list1(q_p_zeta), [int(3)]))),
        mul(
          list2(
            div(take(list1(q_p_zeta), [int(2)]), int(-2)),
            take(list1(q_p_log), [int(2)]),
          ),
        ),
        mul(
          list2(specfn__rat(1L, 6L), power(take(list1(q_p_log), [int(2)]), int(3))),
        ),
      ),
    )
  } else {
    Nil
  }
}

///|
/// exponent in first term of taylor expansion of $li is one
fn li_ord(subl : Value) -> Value raise {
  ignore(subl)
  ncons(rcone())
}

///|
/// taylor expansion of $li is its definition:
/// x + x^2/2^s + x^3/3^s + ...
fn exp_dolli_fun(pw : Value, subl : Value, l : Value) -> Value raise {
  ignore(l)
  let subl = car(subl) // subl is subscript of li
  let mut e = 0 // e is exponent of current term
  let npw = to_double(lfloat(car(pw))) / to_double(lfloat(cdr(pw))) // exponent of last term needed
  let l = cons(specfn__lit_zero_one, Nil)
  while true {
    e = e + 1
    if e.to_double() > npw {
      return l
    }
    rplacd(
      last(l),
      list1(
        cons(
          cons(int(e), int(1)),
          prep1(power_star(int(e), mul_star(list2(int(-1), subl)))),
        ),
      ),
    )
    |> ignore
  }
  l
}

///|
/// computes first pw terms of asymptotic expansion of $li[s](z)
///
/// pw should be < (1/2)*s or gamma term is undefined
///
/// Wood, D.C. (June 1992). The Computation of Polylogarithms. Technical
/// Report 15-92, University of Kent Computing Laboratory, equation 11.1
fn li_asymptotic_expansion(pw : Value, s : Value, z : Value) -> Value raise {
  let terms = Collector::new()
  let mut k = int(0)
  while num_le(k, pw) {
    let term = if d_integerp(k).truthy() &&
      mgqp(int(0), add_star(list3(s, int(1), mul_star(list2(int(-2), k))))).truthy() {
      int(0) // gamma in denominator below is infinite, this term is 0
    } else {
      mul_star(
        list([
          power_star(int(-1), k),
          sub_star(
            int(1),
            power_star(int(2), sub_star(int(1), mul_star(list2(int(2), k)))),
          ),
          power_star(
            mul_star(list2(int(2), q_d__pctpi)),
            mul_star(list2(int(2), k)),
          ),
          div_star(
            ftake(q_p_bern, [mul_star(list2(int(2), k))]),
            mk(q_mfactorial, [mul_star(list2(int(2), k))]),
          ),
          div_star(
            power_star(
              mk(q_p_log, [mul_star(list2(int(-1), z))]),
              sub_star(s, mul_star(list2(int(2), k))),
            ),
            ftake(q_p_gamma, [
              add_star(list3(s, int(1), mul_star(list2(int(-2), k)))),
            ]),
          ),
        ]),
      )
    }
    terms.add(term)
    k = num_add(k, int(1))
  }
  addn(terms.result(), Nil)
}

///|
/// Numerical evaluation for Chebyschev expansions of the first kind
fn cheby(x : Value, chebarr : Value) -> Value raise {
  let mut bn_plus2 : Value = Flo(0.0)
  let mut bn_plus1 : Value = Flo(0.0)
  let mut i = floor1(aref1(chebarr, 0))
  while !num_lt(i, int(1)) {
    let old = bn_plus1
    bn_plus1 = num_add(
      aref1(chebarr, to_int(i)),
      num_sub(num_mul(num_mul(Flo(2.0), x), bn_plus1), bn_plus2),
    )
    bn_plus2 = old
    i = num_sub(i, int(1))
  }
  num_sub(bn_plus1, num_mul(bn_plus2, x))
}

///|
fn cheby_prime(x : Value, chebarr : Value) -> Value raise {
  num_sub(cheby(x, chebarr), num_mul(aref1(chebarr, 1), Flo(0.5)))
}

///|
/// The local LI2 of LI2NUMER (CL arithmetic).
fn specfn__li2(x : Value) -> Value raise {
  // SBCL compiles (expt x 2), with a constant 2, to (* x x).
  let pi2 = num_mul(Flo(@math.PI), Flo(@math.PI))
  if num_lt(x, int(0)) {
    num_add(
      num_add(
        specfn__li2(num_inv(num_sub(int(1), x))),
        num_mul(
          num_mul(Flo(0.5), llog(num_sub(int(1), x))),
          llog(num_div(num_sub(int(1), x), num_mul(x, x))),
        ),
      ),
      num_neg(num_div(pi2, int(6))),
    )
  } else if num_lt(x, int(1)) {
    Flo(@slatec.dspenc(to_double(x)))
  } else if num_eq(x, int(1)) {
    num_div(pi2, int(6))
  } else {
    // li[2](x) = -li[2](1/x)-log(-x)^2/2-%pi^2/6
    num_neg(
      num_add(
        num_add(
          specfn__li2(num_inv(x)),
          { let l = llog(num_neg(x)); num_div(num_mul(l, l), int(2)) },
        ),
        num_div(pi2, int(6)),
      ),
    )
  }
}

///|
fn li2numer(y : Value) -> Value raise {
  // Spence's function can be used to compute li[2] for 0 <= x <= 1.
  // To compute the rest, we need the following identities:
  //
  // li[2](x) = -li[2](1/x)-log(-x)^2/2-%pi^2/6
  // li[2](x) = li[2](1/(1-x)) + log(1-x)*log((1-x)/x^2)/2 - %pi^2/6
  //
  // The first tells us how to compute li[2] for x > 1.  The result is
  // complex.  For x < 0, the second can be used, and the result is real.
  complexify(specfn__li2(y))
}

///|
fn chebyli2(x : Value) -> Value raise {
  num_mul(
    x,
    cheby_prime(
      num_div(one_plus(num_mul(x, int(4))), int(3)),
      symval(q_ear_li2),
    ),
  )
}

///|
fn chebyli3(x : Value) -> Value raise {
  num_mul(
    x,
    cheby_prime(
      num_div(one_plus(num_mul(int(4), x)), int(3)),
      symval(q_ear_li3),
    ),
  )
}

///|
fn chebys12(x : Value) -> Value raise {
  num_mul(
    num_div(num_mul(x, x), int(4)),
    cheby_prime(
      num_div(one_plus(num_mul(int(4), x)), int(3)),
      symval(q_ear_s12),
    ),
  )
}

// ---------------------------------------------------------------------------
// subtitle polygamma routines

///|
fn pole_err(exp_ : Value) -> Value raise {
  if symval(q_errorsw).truthy() {
    throw_tag(q_errorsw, t)
  } else {
    merr("Pole encountered in: ~M", [exp_])
  }
}

///|
/// Integral of psi function psi[n](x)
fn specfn__psi_integral(n : Value, x : Value) -> Value raise {
  if d_integerp(n).truthy() && num_ge(n, int(0)) {
    if num_eq(n, int(0)) {
      mk(q_p_log_gamma, [x])
    } else {
      list3(
        list1(q_mqapply),
        list2(list2(q_d_psi, q_array), mk(q_mplus, [int(-1), n])),
        x,
      )
    }
  } else {
    Nil
  }
}

///|
/// Simplifier for psi[s](a).
fn simp__pctpsi(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let pretty_name = list([
    list1(q_mqapply),
    list2(list2(q_d_psi, q_array), q_s),
    q_a,
  ])
  sub_arg_count_check(int(1), int(1), form, pretty_name) |> ignore
  let s = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunsubs(form)))
  let a = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunargs(form)))
  let z = integer_representation_p(a)
  if z.truthy() && num_lt(z, int(1)) {
    pole_err(form) |> ignore
  }
  specfn__psisimp1(s, a, s, form)
}

///|
/// Compute the sum(exp(k), k, lo, hi).  EXP must be a function that takes
/// a single arg which is the index of the summation.  If HI < LO,
/// immediately return 0.
fn specfn__msum(exp_ : (Value) -> Value raise, lo : Value, hi : Value) -> Value raise {
  if num_lt(hi, lo) {
    int(0)
  } else {
    let mut sum = int(0)
    let mut k = lo
    while !num_gt(k, hi) {
      sum = add2(sum, exp_(k))
      k = num_add(k, int(1))
    }
    sum
  }
}

///|
/// (m- x) = (mul* -1 x)
fn specfn__mneg(x : Value) -> Value raise {
  mul_star(list2(int(-1), x))
}

///|
/// Evaluate `%pi*diff(cot(%pi*z),z,s)` at z = -a (the `$z` binding of the
/// Lisp code).
fn specfn__pi_dcot(s : Value, a : Value) -> Value raise {
  let dif = mul_star(
    list2(
      q_d__pctpi,
      d_diff(
        list3(mk(q_p_cot, [mul_star(list2(q_d__pctpi, q_d_z))]), q_d_z, s),
      ),
    ),
  )
  let zval = neg(a)
  with_special(q_d_z, zval, () => meval(dif))
}

///|
/// The local PSISIMP1 of the psi simplifier.  `s0` is the subscript seen by
/// GIVE-UP.
fn specfn__psisimp1(s : Value, a : Value, s0 : Value, form : Value) -> Value raise {
  let give_up = (fun_args : Value) => eqtest(
    subfunmakes(q_d_psi, list1(s0), fun_args),
    form,
  )
  // This gets pretty hairy now.
  if integerp(s) && num_ge(s, int(0)) && mnumericalp(a).truthy() {
    let v = with_special(q_d_float2bf, t, () => d_float(
      mfuncall(q_d_bfpsi, list3(s, a, int(18))),
    ))
    if v.truthy() {
      return v
    }
  }
  if integerp(s) && num_ge(s, int(0)) && d_bfloatp(a).truthy() {
    let v = mfuncall(q_d_bfpsi, list3(s, a, symval(q_d_fpprec)))
    if v.truthy() {
      return v
    }
  }
  if !symval(q_d_numer).truthy() &&
    !symval(q_d_float).truthy() &&
    integerp(s) &&
    num_gt(s, int(-1)) {
    let v = specfn__psisimp1_exact(s, a, s0, form)
    if v.truthy() {
      return v
    }
  }
  give_up(list1(a))
}

///|
fn specfn__psisimp1_exact(
  s : Value,
  a : Value,
  s0 : Value,
  form : Value,
) -> Value raise {
  let give_up = (fun_args : Value) => eqtest(
    subfunmakes(q_d_psi, list1(s0), fun_args),
    form,
  )
  let half = symval(q_n1_sl_sl2)
  if integerp(a) {
    // For s >= 1,
    //   psi[s](a) = (-1)^(s+1)*s!*(zeta(1+s) - sum(1/k^(s+1),k,1,a-1)
    //
    // The same formula can be used for s = 0 if we replace zeta(1) with
    // -%gamma.
    //
    // See https://en.wikipedia.org/wiki/Polygamma_function
    //
    // The computation below is
    //
    //   psi[s](a) = (-1)^s*s!*(sum(1/k^(s+1),k,1,a-1) - zeta(1+s))
    if num_gt(a, symval(q_d_maxpsiposint)) {
      return Nil
    }
    return mul(
      list3(
        expt(int(-1), s),
        factorial(s),
        sub_star(
          specfn__msum(k => inv(power(k, one_plus(s))), int(1), num_sub(a, int(1))),
          if zerop(s) {
            q_d__pctgamma
          } else {
            ftake(q_p_zeta, [one_plus(s)])
          },
        ),
      ),
    )
  }
  if !ratnump(a).truthy() || ratgreaterp(a, symval(q_d_maxpsiposint)).truthy() {
    return Nil
  }
  if ratgreaterp(a, int(0)).truthy() {
    if ratgreaterp(a, int(1)).truthy() {
      let int_ = d_entier(a) // reduction to fractional values
      let frac = sub(a, int_)
      // Uses the recurrence relation
      //
      // psi[s](z+m) = psi[s](z) + (-1)^s*s!*sum(1/(z+k)^(s+1),k,0,m-1)
      //
      // where a = z + m, m = int, frac = a - int.
      let p1 = specfn__psisimp1(s, frac, s0, form)
      let p2 = if num_gt(int_, symval(q_d_maxpsiposint)) {
        give_up(list1(frac))
      } else {
        mul(
          list3(
            expt(int(-1), s),
            factorial(s),
            specfn__msum(
              k => power(
                add(list2(sub(a, int_), k)),
                num_sub(num_neg(s), int(1)),
              ),
              int(0),
              num_sub(int_, int(1)),
            ),
          ),
        )
      }
      return add(list2(p1, p2))
    }
    if num_eq(s, int(0)) {
      let p = cadr(a)
      let q = caddr(a)
      // a is a rational of the form p/q.
      if num_gt(p, symval(q_d_maxpsifracnum)) ||
        num_gt(q, symval(q_d_maxpsifracdenom)) ||
        bignump(p) ||
        bignump(q) {
        // Give up if the numerator or denominator is too big.
        return Nil
      }
      // These can be found at
      // https://mathworld.wolfram.com/GausssDigammaTheorem.html
      if num_eq(p, int(1)) {
        let v = if num_eq(q, int(2)) {
          // psi[0](1/2) = -%gamma - log(4)
          add_star(
            list2(
              mul_star(list2(int(-2), specfn__log(2L))),
              specfn__mneg(q_d__pctgamma),
            ),
          )
        } else if num_eq(q, int(3)) {
          // psi[0](1/3) = -3/2*log(3)-%pi/(2*sqrt(3))-%gamma
          add_star(
            list3(
              mul_star(
                list3(
                  specfn__rat(-1L, 2L),
                  power(int(3), specfn__rat(-1L, 2L)),
                  q_d__pctpi,
                ),
              ),
              mul_star(list2(specfn__rat(-3L, 2L), specfn__log(3L))),
              specfn__mneg(q_d__pctgamma),
            ),
          )
        } else if num_eq(q, int(4)) {
          // psi[0](1/4) = -%pi/2-log(8)-%gamma
          add_star(
            list3(
              mul_star(list2(specfn__rat(-1L, 2L), q_d__pctpi)),
              mul_star(list2(int(-3), specfn__log(2L))),
              specfn__mneg(q_d__pctgamma),
            ),
          )
        } else if num_eq(q, int(6)) {
          // psi[0](1/6) = -%gamma -sqrt(3)*%pi/2-2*log(2)-3/2*log(3)
          specfn__mneg(
            add_star(
              list4(
                mul_star(list2(specfn__rat(3L, 2L), specfn__log(3L))),
                mul_star(list2(int(2), specfn__log(2L))),
                mul_star(list3(half, q_d__pctpi, power(int(3), half))),
                q_d__pctgamma,
              ),
            ),
          )
        } else {
          Nil
        }
        if v.truthy() {
          return v
        }
      }
      if num_eq(p, int(2)) && num_eq(q, int(3)) {
        // psi[0](2/3) = (sqrt(3)*%pi-9*log(3))/6-%gamma
        return add_star(
          list3(
            mul_star(list3(half, power(int(3), specfn__rat(-1L, 2L)), q_d__pctpi)),
            mul_star(list2(specfn__rat(-3L, 2L), specfn__log(3L))),
            specfn__mneg(q_d__pctgamma),
          ),
        )
      }
      if num_eq(p, int(3)) && num_eq(q, int(4)) {
        // psi[0](3/4) = %pi/2-log(8)-%gamma
        return add_star(
          list3(
            mul_star(list2(half, q_d__pctpi)),
            mul_star(list2(int(-3), specfn__log(2L))),
            specfn__mneg(q_d__pctgamma),
          ),
        )
      }
      if num_eq(p, int(5)) && num_eq(q, int(6)) {
        // psi[0](5/6) = -%gamma+sqrt(3)*%pi/2-2*log(2)-3/2*log(3)
        return sub_star(
          mul_star(list3(half, q_d__pctpi, power(int(3), half))),
          add_star(
            list3(
              mul_star(list2(specfn__rat(3L, 2L), specfn__log(3L))),
              mul_star(list2(int(2), specfn__log(2L))),
              q_d__pctgamma,
            ),
          ),
        )
      }
      // Gauss's Formula.
      //
      // psi[0](p/q) = -%gamma - log(2*q) - %pi/2*cot(p/q*%pi)
      //   + 2 * sum(cos(2*%pi*p*k/q)*log(sin(%pi*k/q)), k, 1, floor(q/2)-1).
      //
      // However, the formula here is different.  Instead of
      // log(sin(%pi*k/q)), we use log(sin((2*%pi*k/q)/2)) and the halfangle
      // formula to get
      //
      //   log(sqrt(1-cos(2*%pi*k/q))/sqrt(2)) =
      //     1/2*log(1-cos(2*%pi*k/q)) - log(2)/2.
      let f = (k : Value) => mul_star(
        list2(
          mk(q_p_cos, [mul_star(list4(int(2), a, q_d__pctpi, k))]),
          mk(q_p_log, [
            sub(
              int(2),
              mul_star(
                list2(
                  int(2),
                  mk(q_p_cos, [
                    div(mul_star(list3(int(2), q_d__pctpi, k)), q),
                  ]),
                ),
              ),
            ),
          ]),
        ),
      )
      let q2 = num_truncate(q, b=int(2)).0
      return add(
        list3(
          specfn__msum(f, int(1), num_sub(q2, int(1))),
          mul(list2(f(q2), if oddp(q) { int(1) } else { half })),
          neg(
            add_star(
              list3(
                mul_star(
                  list3(
                    q_d__pctpi,
                    half,
                    mk(q_p_cot, [mk_simp(q_mtimes, [a, q_d__pctpi])]),
                  ),
                ),
                mk(q_p_log, [q]),
                q_d__pctgamma,
              ),
            ),
          ),
        ),
      )
    }
    if alike1(a, specfn__lit_rat_half).truthy() {
      // psi[s](1/2) = (-1)^(s+1)*s!*(2^(s+1)-1)*zeta(s+1)
      // See https://dlmf.nist.gov/5.15.E3
      return mul(
        list4(
          expt(int(-1), one_plus(s)),
          factorial(s),
          num_sub(expt(int(2), one_plus(s)), int(1)),
          simplify(ftake(q_p_zeta, [one_plus(s)])),
        ),
      )
    }
    if ratgreaterp(a, specfn__lit_rat_half).truthy() &&
      ratgreaterp(int(1), a).truthy() {
      // psi[s](a) where a > 1/2 and 1 > a.
      //
      // From https://dlmf.nist.gov/5.15.E6:
      //
      //   psi[s](1-z) + (-1)^(s-1)*psi[s](z) = (-1)^s*%pi*diff(cot(%pi*z),z,s)
      //
      // Solve for psi[s](z):
      //
      //   psi[s](z) = -%pi*diff(cot(%pi*z),z,s) - (-1)^(s-1)*psi[s](1-z)
      //             = (-1)^s*%pi*diff(cot(-%pi*z),z,s) + (-1)^s*psi[s](1-z)
      //             = (-1)^s*(psi[s](1-z) + %pi*diff(cot(-%pi*z),z,s))
      let e1 = expt(int(-1), s)
      let p1 = specfn__psisimp1(s, sub_star(int(1), a), s0, form)
      return mul(list2(e1, add(list2(p1, specfn__pi_dcot(s, a)))))
    }
    return Nil
  }
  if ratgreaterp(a, symval(q_d_maxpsinegint)).truthy() {
    // Reflection Formula
    let e1 = expt(int(-1), s)
    let p1 = specfn__psisimp1(s, specfn__mneg(a), s0, form)
    let inner = add(list2(p1, specfn__pi_dcot(s, a)))
    return mul(
      list2(
        e1,
        add(
          list2(
            inner,
            mul(
              list3(
                expt(int(-1), s),
                factorial(s),
                power(neg(a), num_sub(num_neg(s), int(1))),
              ),
            ),
          ),
        ),
      ),
    )
  }
  Nil
}

// ---------------------------------------------------------------------------
// subtitle polygamma tayloring routines

// These routines are specially coded to be as fast as possible given the
// current $TAYLOR; too bad they have to be so ugly.

///|
fn expgam_fun(pw : Value, temp : Value) -> Value raise {
  ignore(temp)
  let temp = get_datum(get_key_var(car(symval(q_var))))
  // (let-pw temp pw ...)
  let d = temp
  push_pw(d, pw) |> ignore
  let r = {
    let a = {
      let d2 = temp
      push_pw(d2, e1_plus(pw)) |> ignore
      let r2 = psexpt_fn(
        getexp_fun(specfn__lit_psi_m1, symval(q_var), e1_plus(pw)),
      )
      pop_pw(d2) |> ignore
      r2
    }
    pstimes(
      a,
      make_ps(symval(q_var), ncons(pw), terms=specfn__lit_expgam_terms),
    )
  }
  pop_pw(d) |> ignore
  r
}

///|
fn expplygam_funs(pw : Value, subl : Value, l : Value) -> Value raise {
  ignore(l)
  let subl = car(subl)
  if !integerp(subl) || num_lt(subl, int(-1)) {
    return tay_err(Str("Unable to expand at a subscript in"))
  }
  let npw = to_double(lfloat(car(pw))) / to_double(lfloat(cdr(pw)))
  let mut sf_last : Value = Nil
  let l = if num_eq(subl, int(-1)) {
    list1(cons(cons(int(1), int(1)), prep1(specfn__lit_neg_gamma)))
  } else if num_eq(subl, int(0)) {
    cons(
      specfn__lit_m1_m1,
      if 0.0 > npw {
        Nil
      } else {
        list1(cons(cons(int(0), int(1)), prep1(specfn__lit_neg_gamma)))
      },
    )
  } else {
    sf_last = factorial(subl)
    list1(
      cons(
        cons(num_neg(one_plus(subl)), int(1)),
        cons(num_mul(expt(int(-1), one_plus(subl)), factorial(subl)), int(1)),
      ),
    )
  }
  let mut e = if num_lt(subl, int(1)) { num_neg(subl) } else { int(-1) }
  let mut sf_sign = if num_lt(subl, int(1)) {
    int(-1)
  } else {
    expt(int(-1), subl)
  }
  while true {
    e = num_add(e, int(1))
    sf_sign = num_neg(sf_sign)
    if to_double(e) > npw {
      return l
    }
    rplacd(
      last(l),
      list1(
        cons(
          cons(e, int(1)),
          rctimes(
            rcplygam(e, sf_sign, subl, sf_last),
            prep1(ftake(q_p_zeta, [num_add(one_plus(subl), e)])),
          ),
        ),
      ),
    )
    |> ignore
  }
  l
}

///|
fn rcplygam(k : Value, sf_sign : Value, subl : Value, sf_last : Value) -> Value raise {
  if num_eq(subl, int(-1)) {
    cons(sf_sign, k)
  } else if num_eq(subl, int(0)) {
    cons(sf_sign, int(1))
  } else {
    // The Lisp code then assigns its own (lexical) SF-LAST parameter; that
    // assignment has no visible effect.
    cons(num_mul(sf_sign, sf_last), int(1))
  }
}

///|
fn plygam_ord(subl : Value) -> Value raise {
  let sub_ = car(subl)
  if equal(sub_, int(-1)) {
    ncons(rcone())
  } else if !integerp(sub_) || num_lt(sub_, int(-1)) {
    tay_err(Str("Unable to expand at a subscript in"))
  } else {
    list1(cons(mul_star(list2(int(-1), m1_plus(sub_))), int(1)))
  }
}

///|
fn plygam_pole(a : Value, c : Value, func : Value) -> Value raise {
  if rcmintegerp(c).truthy() {
    let ps = get_lexp(sub_star(a, rcdisrep(c)), Nil, t)
    rplacd(cddr(ps), cons(cons(cons(int(0), int(1)), c), cdddr(ps))) |> ignore
    if atom(func) {
      gam_const(a, ps, func)
    } else {
      plygam_const(a, ps, func)
    }
  } else {
    prep1(
      simplifya(
        if atom(func) {
          mk(q_p_gamma, [rcdisrep(c)])
        } else {
          list3(list1(q_mqapply), func, rcdisrep(c))
        },
        Nil,
      ),
    )
  }
}

///|
fn gam_const(a : Value, arg : Value, func : Value) -> Value raise {
  ignore(func)
  let mut const_ = ps_lc_star(arg)
  let mut arg_c : Value = Nil
  if !rcintegerp(const_).truthy() {
    return taylor2(diff_expand(mk(q_p_gamma, [a]), symval(q_tlist)))
  }
  const_ = car(const_)
  if pscoefp(arg).truthy() {
    arg_c = get_lexp(
      add(list2(a, num_neg(const_))),
      rcone(),
      signp(q_le, const_),
    )
  }
  if arg_c.truthy() && !psp(arg_c).truthy() {
    return taylor2(simplify(mk(q_p_gamma, [const_])))
  }
  let datum = get_datum(
    get_key_var(gvar(if arg_c.truthy() { arg_c } else { arg })),
  )
  let ord = if arg_c.truthy() {
    le(terms(arg_c))
  } else {
    le(n__term(terms(arg)))
  }
  let func = current_trunc(datum)
  if num_gt(const_, int(0)) {
    let x = {
      push_pw(datum, e_(func, e2=ord)) |> ignore
      let r = expand(add(list2(a, num_neg(const_))), q_p_gamma)
      pop_pw(datum) |> ignore
      r
    }
    let y = {
      push_pw(datum, e_plus(func, ord)) |> ignore
      let r = tsprsum(
        add(list2(a, neg(q_p__pcttaylor_index_pct_pct))),
        list3(q_p__pcttaylor_index_pct_pct, int(1), const_),
        q_p_product,
      )
      pop_pw(datum) |> ignore
      r
    }
    pstimes(x, y)
  } else {
    let x = expand(add(list2(a, num_neg(const_))), q_p_gamma)
    let y = {
      push_pw(datum, e_plus(func, ord)) |> ignore
      let r = psexpt(
        tsprsum(
          add(list2(a, q_p__pcttaylor_index_pct_pct)),
          list3(
            q_p__pcttaylor_index_pct_pct,
            int(0),
            num_neg(one_plus(const_)),
          ),
          q_p_product,
        ),
        rcmone(),
      )
      pop_pw(datum) |> ignore
      r
    }
    pstimes(x, y)
  }
}

///|
fn plygam_const(a : Value, arg : Value, func : Value) -> Value raise {
  let mut const_ = ps_lc_star(arg)
  let sub_ = cadr(func)
  if !integerp(sub_) || num_lt(sub_, int(-1)) {
    return tay_err(Str("Unable to expand at a subscript in"))
  }
  if !rcintegerp(const_).truthy() {
    return taylor2(
      diff_expand(list3(list1(q_mqapply), func, a), symval(q_tlist)),
    )
  }
  const_ = car(const_)
  let x = expand(add(list2(a, num_neg(const_))), func)
  let y = if num_gt(const_, int(0)) {
    pstimes(
      cons(num_mul(expt(int(-1), sub_), factorial(sub_)), int(1)),
      tsprsum(
        mk(q_mexpt, [
          add(list2(a, neg(q_p__pcttaylor_index_pct_pct))),
          num_neg(one_plus(sub_)),
        ]),
        list3(q_p__pcttaylor_index_pct_pct, int(1), const_),
        q_p_sum,
      ),
    )
  } else {
    pstimes(
      cons(num_mul(expt(int(-1), one_plus(sub_)), factorial(sub_)), int(1)),
      tsprsum(
        mk(q_mexpt, [
          add(list2(a, q_p__pcttaylor_index_pct_pct)),
          num_neg(one_plus(sub_)),
        ]),
        list3(
          q_p__pcttaylor_index_pct_pct,
          int(0),
          num_neg(one_plus(const_)),
        ),
        q_p_sum,
      ),
    )
  }
  psplus(x, y)
}

// ---------------------------------------------------------------------------
// Lambert W function
//
// References
//
// Corless, R. M., Gonnet, D. E. G., Jeffrey, D. J., Knuth, D. E. (1996).
// "On the Lambert W function". Advances in Computational Mathematics 5:
// pp 329-359
//
// D. J. Jeffrey, D. E. G. Hare, R. M. Corless
// Unwinding the branches of the Lambert W function
// The Mathematical Scientist, 21, pp 1-7, (1996)
//
// Winitzki, S. Uniform Approximations for Transcendental Functions.
// In Part 1 of Computational Science and its Applications - ICCSA 2003,
// Lecture Notes in Computer Science, Vol. 2667, Springer-Verlag,
// Berlin, 2003, 780-789. DOI 10.1007/3-540-44839-X_82
//
// Darko Veberic,
// Having Fun with Lambert W(x) Function
// arXiv:1003.1628v1, March 2010, http://arxiv.org/abs/1003.1628

///|
fn simp__pctlambert_w(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=int(1),
      pretty_name=mk(q_p_lambert_w, [q_d_x]),
    )
    |> ignore
  }
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  if equal(x, int(0)) {
    int(0)
  } else if equal(x, Flo(0.0)) {
    Flo(0.0)
  } else if zerop1(x).truthy() {
    d_bfloat(int(0)) // bfloat case
  } else if eq(x, q_d__pcte) {
    // W(%e) = 1
    int(1)
  } else if alike1(x, specfn__lit_neg_half_log2).truthy() {
    // W(-log(2)/2) = -log(2)
    specfn__lit_neg_log2
  } else if alike1(x, specfn__lit_neg_inv_e).truthy() {
    // W(-1/e) = -1
    int(-1)
  } else if alike1(x, specfn__lit_neg_half_pi).truthy() {
    // W(-%pi/2) = %i*%pi/2
    specfn__lit_half_i_pi
  } else if complex_float_numerical_eval_p(list1(x)).truthy() {
    // numerical evaluation
    // x may be an integer.  eg "lambert_w(1),numer;"
    if integerp(x) {
      maxima_to(bf_lambert_w_k(int(0), bf_to(d_float(x))))
    } else {
      maxima_to(bf_lambert_w_k(int(0), bf_to(x)))
    }
  } else if complex_bigfloat_numerical_eval_p(list1(x)).truthy() {
    maxima_to(bf_lambert_w_k(int(0), bf_to(x)))
  } else {
    eqtest(mk(q_p_lambert_w, [x]), form)
  }
}

///|
/// An approximation of the k-branch of generalized Lambert W function
///   k integer
///   z real or complex lisp float
/// Used as initial guess for Halley's iteration.
/// When W(z) is real, ensure that guess is real.
fn init_lambert_w_k(k : Value, z : Value) -> Value raise {
  // parameters for k = +/- 1 near branch point z=-1/%e
  let branch_eps : Value = Flo(0.2)
  let branch_point = num_div(int(-1), symval(q_p_e_val)) // branch point z=-1/%e
  if num_eq(k, int(0)) {
    // For principal branch k=0, use expression by Winitzki
    init_lambert_w_0(z)
  } else if num_eq(k, int(1)) &&
    num_lt(imagpart(z), int(0)) &&
    num_lt(num_abs(num_sub(branch_point, z)), branch_eps) {
    // For k=1 branch, near branch point z=-1/%e with im(z) <  0
    bf_lambert_branch_approx(z)
  } else if num_eq(k, int(-1)) &&
    realp(z) &&
    num_gt(z, branch_point) &&
    num_lt(z, int(0)) {
    // For k=-1 branch, z real with -1/%e < z < 0
    // W(z) is real in this range
    init_lambert_w_minus1(z)
  } else if num_eq(k, int(-1)) &&
    num_ge(imagpart(z), int(0)) &&
    num_lt(num_abs(num_sub(branch_point, z)), branch_eps) {
    // For k=-1 branch, near branch point z=-1/%e with im(z) >= 0
    bf_lambert_branch_approx(z)
  } else {
    // Default to asymptotic expansion Corless et al (4.20)
    // W_k(z) = log(z) + 2.pi.i.k - log(log(z)+2.pi.i.k)
    let two_pi_i_k = complex(
      Flo(0.0),
      i=num_mul(num_mul(int(2), Flo(@math.PI)), k),
    )
    num_add(
      num_add(llog(z), two_pi_i_k),
      num_mul(int(-1), llog(num_add(llog(z), two_pi_i_k))),
    )
  }
}

///|
/// Complex value of the principal branch of Lambert's W function in the
/// entire complex plane with relative error less than 1%, given standard
/// branch cuts for sqrt(z) and log(z).
/// Winitzki (2003)
fn init_lambert_w_0(z : Value) -> Value raise {
  let a : Value = Flo(2.344)
  let b : Value = Flo(0.8842)
  let c : Value = Flo(0.9294)
  let d : Value = Flo(0.5106)
  let e : Value = Flo(-1.213)
  // y=sqrt(2*%e*z+2)
  let y = lsqrt(
    num_add(num_mul(num_mul(int(2), symval(q_p_e_val)), z), int(2)),
  )
  // w = (2*log(1+B*y)-log(1+C*log(1+D*y))+E)/(1+1/(2*log(1+B*y)+2*A)
  num_div(
    num_add(
      num_add(
        num_mul(int(2), llog(num_add(int(1), num_mul(b, y)))),
        num_mul(
          int(-1),
          llog(
            num_add(
              int(1),
              num_mul(c, llog(num_add(int(1), num_mul(d, y)))),
            ),
          ),
        ),
      ),
      e,
    ),
    num_add(
      int(1),
      num_div(
        int(1),
        num_add(
          num_mul(int(2), llog(num_add(int(1), num_mul(b, y)))),
          num_mul(int(2), a),
        ),
      ),
    ),
  )
}

///|
/// Approximate k=-1 branch of Lambert's W function over -1/e < z < 0.
/// W(z) is real, so we ensure the starting guess for Halley iteration is
/// also real.
/// Veberic (2010)
fn init_lambert_w_minus1(z : Value) -> Value raise {
  if !realp(z) {
    merr("z not real in init-lambert-w-minus1", [])
  } else if num_lt(z, num_div(int(-1), symval(q_p_e_val))) || plusp(z) {
    merr("z outside range of approximation in init-lambert-w-minus1", [])
  } else if num_lt(z, Flo(-0.3)) {
    // In the region where W(z) is real
    // -1/e < z < C, use power series about branch point -1/e ~ -0.36787
    // C = -0.3 seems a reasonable crossover point
    bf_lambert_branch_approx(z)
  } else {
    // otherwise C <= z < 0, use iteration W(z) ~ ln(-z)-ln(-W(z))
    // nine iterations are sufficient over -0.3 <= z < 0
    let ln_z = llog(num_neg(z))
    let maxiter = 9
    let mut w = ln_z
    for _k in 0..<maxiter {
      w = num_sub(ln_z, llog(num_neg(w)))
    }
    w
  }
}

///|
/// Approximate Lambert W(k,z) for k=1 and k=-1 near branch point z=-1/%e
/// using power series in y=-sqrt(2*%e*z+2)
///   for im(z) < 0,  approximates k=1 branch
///   for im(z) >= 0, approximates k=-1  branch
///
/// Corless et al (1996) (4.22)
/// Veberic (2010)
///
/// z is a real or complex bigfloat:
fn bf_lambert_branch_approx(z : Value) -> Value raise {
  // y=-sqrt(2*%e*z+2)
  let y = bf_neg(
    bf_sqrt(bf_add(bf_mul(bf_mul(int(2), bf_p_e(z)), z), int(2))),
  )
  let b0 = int(-1)
  let b1 = int(1)
  let b2 = num_div(int(-1), int(3))
  let b3 = num_div(int(11), int(72))
  bf_add(b0, bf_mul(y, bf_add(b1, bf_mul(y, bf_add(b2, bf_mul(b3, y))))))
}

///|
/// The bigfloat-package generic INIT-LAMBERT-W-K.
fn specfn__bf_init_lambert_w_k(k : Value, z : Value) -> Value raise {
  if integerp(k) && numberp(z) {
    init_lambert_w_k(k, z)
  } else if integerp(k) && (bf_is_bigfloat(z) || bf_is_complex_bigfloat(z)) {
    bf_bfloat_init_lambert_w_k(k, z)
  } else {
    raise LispError::SimpleError(
      "There is no applicable method for the generic function INIT-LAMBERT-W-K",
    )
  }
}

///|
/// Algorithm based in part on Corless et al (1996).
///
/// It is Halley's iteration applied to w*exp(w).
///
///                               w[j] exp(w[j]) - z
/// w[j+1] = w[j] - -------------------------------------------------
///                                       (w[j]+2)(w[j] exp(w[j]) -z)
///                  exp(w[j])(w[j]+1) -  ---------------------------
///                                               2 w[j] + 2
///
/// The algorithm has cubic convergence.  Once convergence begins, the
/// number of digits correct at step k is roughly 3 times the number which
/// were correct at step k-1.
///
/// Convergence can stall using convergence test abs(w[j+1]-w[j]) < prec,
/// as happens for generalized_lambert_w(-1,z) near branch point z = -1/%e
/// Therefore also stop iterating if abs(w[j]*exp(w[j]) - z) << abs(z)
fn bf_lambert_w_k(k : Value, z : Value, maxiter? : Value = Fix(50L)) -> Value raise {
  let mut w = specfn__bf_init_lambert_w_k(k, z)
  let prec = bf_mul(int(4), bf_epsilon(z))
  let mut i = int(0)
  let mut converged = false
  while num_lt(i, maxiter) {
    let we = bf_mul(w, bf_exp(w))
    if bf_le(
        bf_abs(bf_sub(z, we)),
        bf_mul(bf_mul(int(4), bf_epsilon(z)), bf_abs(z)),
      ) {
      converged = true
      break
    }
    let w1e = bf_mul(bf_1_plus(w), bf_exp(w))
    let delta = bf_div(
      bf_sub(we, z),
      bf_sub(
        w1e,
        bf_div(
          bf_mul(bf_add(w, int(2)), bf_sub(we, z)),
          bf_add(int(2), bf_mul(int(2), w)),
        ),
      ),
    )
    w = bf_sub(w, delta)
    if bf_le(bf_abs(bf_div(delta, w)), prec) {
      converged = true
      break
    }
    i = num_add(i, int(1))
  }
  if !converged {
    merr("lambert-w-k did not converge", []) |> ignore
  }
  // Check iteration converged to correct branch
  bf_check_lambert_w_k(k, w, z) |> ignore
  w
}

///|
/// Approximate generalized_lambert_w(k,z) for bigfloat: z as initial guess
fn bf_bfloat_init_lambert_w_k(k : Value, z : Value) -> Value raise {
  let branch_point : Value = Flo(-0.36787944117144) // branch point -1/%e
  if bf_eq(k, int(-1)) &&
    (bf_zerop(bf_imagpart(z)) || bf_plusp(bf_imagpart(z))) &&
    bf_lt(bf_abs(bf_sub(z, branch_point)), Flo(1.0e-10)) {
    // if k=-1, z very close to -1/%e and imag(z)>=0, use power series
    bf_lambert_branch_approx(z)
  } else if bf_eq(k, int(1)) &&
    bf_minusp(bf_imagpart(z)) &&
    bf_lt(bf_abs(bf_sub(z, branch_point)), Flo(1.0e-10)) {
    // if k=1, z very close to -1/%e and imag(z)<0, use power series
    bf_lambert_branch_approx(z)
  } else if bf_lt(bf_abs(z), Flo(1.0e100)) {
    // Initialize using float value if z is representable as a float
    if bf_complexp(z) {
      bf_bigfloat(
        bf_lambert_w_k(
          k,
          complex(
            bf_float(bf_realpart(z), Flo(1.0)),
            i=bf_float(bf_imagpart(z), Flo(1.0)),
          ),
        ),
      )
    } else {
      bf_bigfloat(bf_lambert_w_k(k, bf_float(z, Flo(1.0))))
    }
  } else {
    // For large z, use Corless et al (4.20)
    //              W_k(z) ~ log(z) + 2.pi.i.k - log(log(z)+2.pi.i.k)
    let log_z = bf_log(z)
    if bf_eq(k, int(0)) {
      bf_sub(log_z, bf_log(log_z))
    } else {
      let i = bf_make_complex_bigfloat(bf_intofp(int(0)), bf_intofp(int(1)))
      let two_pi_i_k = bf_mul(bf_mul(bf_mul(int(2), bf_p_pi(z)), i), k)
      bf_sub(bf_add(log_z, two_pi_i_k), bf_log(bf_add(log_z, two_pi_i_k)))
    }
  }
}

///|
/// Check Lambert W iteration converged to the correct branch
/// W_k(z) + ln W_k(z) = ln z, for k = -1 and z in [-1/e,0)
///                    = ln z + 2 pi i k, otherwise
/// See Jeffrey, Hare, Corless (1996), eq (12)
/// k integer
/// z, w bigfloat: numbers
fn bf_check_lambert_w_k(k : Value, w : Value, z : Value) -> Value raise {
  let tolerance : Value = Flo(1.0e-6)
  let ok = if bf_eq(k, int(-1)) &&
    bf_realp(z) &&
    bf_minusp(z) &&
    bf_ge(z, bf_div(int(-1), bf_p_e(z))) {
    // k=-1 branch with z and w real.
    bf_realp(w) &&
    bf_le(w, int(-1)) &&
    bf_lt(bf_abs(bf_add(bf_add(w, bf_log(w)), bf_neg(bf_log(z)))), tolerance)
  } else {
    // i k =  (W_k(z) + ln W_k(z) - ln(z)) / 2 pi
    let ik = bf_div(
      bf_add(bf_add(w, bf_log(w)), bf_neg(bf_log(z))),
      bf_mul(int(2), bf_p_pi(z)),
    )
    bf_lt(bf_realpart(ik), tolerance) &&
    bf_lt(bf_abs(bf_sub(k, bf_imagpart(ik))), tolerance)
  }
  if ok {
    t
  } else {
    merr("Lambert W iteration converged to wrong branch", [])
  }
}

// ---------------------------------------------------------------------------
// Generalized Lambert W function

///|
/// The ARG must be some kind of number acceptable to BIGFLOAT:TO.  If ARG
/// is numerically equal to an integer, return the integer value.
/// Otherwise, return NIL.
fn specfn__test_for_integer(arg : Value) -> Value raise {
  let new_arg = bf_to(arg)
  let arg_truncate = bf_truncate(new_arg).0
  if bf_eq(arg_truncate, new_arg) {
    arg_truncate
  } else {
    Nil
  }
}

///|
fn simp__pctgeneralized_lambert_w(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 2 {
    wna_err(
      form,
      required_arg_count=int(2),
      pretty_name=mk(q_p_generalized_lambert_w, [q_d_k, q_d_x]),
    )
    |> ignore
  }
  let k = simpcheck(nth(1, form), p__pctsimpflag)
  let x = simpcheck(nth(2, form), p__pctsimpflag)
  let give_up = () => eqtest(mk(q_p_generalized_lambert_w, [k, x]), form)
  if complex_float_numerical_eval_p(list2(k, x)).truthy() {
    // Numerical evaluation for real or complex x
    // x may be an integer.  eg "generalized_lambert_w(0,1),numer;"
    // Also, we can only evaluate this if k is equal to an integer.
    let k_int = specfn__test_for_integer(k)
    if k_int.truthy() {
      if integerp(x) {
        maxima_to(bf_lambert_w_k(k_int, bf_to(d_float(x))))
      } else {
        maxima_to(bf_lambert_w_k(k_int, bf_to(x)))
      }
    } else {
      give_up()
    }
  } else if complex_bigfloat_numerical_eval_p(list2(k, x)).truthy() {
    // Numerical evaluation for real or complex bigfloat x
    let k_int = specfn__test_for_integer(k)
    if k_int.truthy() {
      maxima_to(bf_lambert_w_k(k_int, bf_to(x)))
    } else {
      give_up()
    }
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// Bateman function
//
// References:
//  - https://en.wikipedia.org/wiki/Bateman_function
//  - https://www.researchgate.net/publication/350992070_The_Bateman_Functions_Revisited_After_90_Years_--_A_Survey_of_Old_and_New_Results

///|
fn simp__pctkbateman(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let pretty_name = list([
    list1(q_mqapply),
    list2(list2(q_d_kbateman, q_array), q_v),
    q_z,
  ])
  sub_arg_count_check(int(1), int(1), form, pretty_name) |> ignore
  let v = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunsubs(form)))
  let z = car(mapcar(x => simpcheck(x, p__pctsimpflag), subfunargs(form)))
  let give_up = () => eqtest(
    subfunmakes(q_d_kbateman, list1(v), list1(z)),
    form,
  )
  let vn = integer_representation_p(v)
  if vn.truthy() && num_ge(vn, int(0)) {
    // kbateman[n](z), for integer n >= 0
    let signz = asksign(z)
    if eq(signz, q_d_zero) {
      // kbateman[n](0) = 2/%pi/n*sin(%pi*n/2)
      if zerop(vn) {
        int(0)
      } else {
        mul(
          list2(
            div(int(2), mul(list2(q_d__pctpi, vn))),
            ftake(q_p_sin, [div(mul(list2(q_d__pctpi, vn)), int(2))]),
          ),
        )
      }
    } else if evenp(vn) && eq(signz, q_d_positive) {
      // kbateman[2*n](x) = (-1)^n*x*exp(x)/n!*diff(x^(n-1)*exp(-2*x),x,n)
      // for x >= 0.
      let n = num_div(vn, int(2))
      let zarg = gensym()
      // Handle small n directly and use the formula for larger values.
      if num_eq(n, int(0)) {
        ftake(q_p_exp, [neg(z)])
      } else if num_eq(n, int(1)) {
        mul(list3(int(2), z, ftake(q_p_exp, [neg(z)])))
      } else if num_eq(n, int(2)) {
        mul(list4(int(2), z, sub(z, int(1)), ftake(q_p_exp, [neg(z)])))
      } else {
        d_factor(
          d_substitute(
            z,
            zarg,
            expr=mul(
              list2(
                div(
                  mul(list3(expt(int(-1), n), zarg, ftake(q_p_exp, [zarg]))),
                  ftake(q_p_gamma, [add(list2(int(1), n))]),
                ),
                d_diff(
                  list3(
                    mul(
                      list2(
                        power(zarg, sub(n, int(1))),
                        ftake(q_p_exp, [mul(list2(int(-2), zarg))]),
                      ),
                    ),
                    zarg,
                    n,
                  ),
                ),
              ),
            ),
          ),
        )
      }
    } else {
      give_up()
    }
  } else {
    give_up()
  }
}

// ---------------------------------------------------------------------------
// Bigfloat package: numerical evaluation of polylogarithms

///|
/// The local ZFUN of LI-USING-POWERS-OF-LOG and POLYLOG-LOG-SERIES:
/// Z(j) = zeta(j) for j != 1, Z(1) = -log(-log(z)) + sum(1/k, k, 1, n - 1)
fn specfn__zfun(j : Value, n : Value, x : Value) -> Value raise {
  if bf_eq(j, int(1)) {
    let sum = bf_neg(bf_log(bf_neg(bf_log(x))))
    let mut acc = int(0)
    let mut k = int(1)
    while num_lt(k, n) {
      acc = num_add(acc, bf_inv(k))
      k = num_add(k, int(1))
    }
    bf_add(sum, acc)
  } else {
    bf_to(ftake(q_p_zeta, [maxima_to(bf_float(j, bf_realpart(x)))]))
  }
}

///|
fn bf_li_using_powers_of_log(n : Value, x : Value) -> Value raise {
  // When x is on or near the unit circle the other approaches don't work.
  // Use the expansion in powers of log(z) (from cephes cpolylog)
  //
  //   li[s](z) = sum(Z(s-j)*(log(z))^j/j!, j = 0, inf)
  //
  // where Z(j) = zeta(j) for j != 1.  For j = 1:
  //
  //   Z(1) = -log(-log(z)) + sum(1/k, k, 1, s - 1)
  //
  // This is similar to http://functions.wolfram.com/10.08.06.0024.01, but
  // that identity is clearly undefined if v is a positive integer because
  // zeta(1) is undefined.
  //
  // But Z(-k) = zeta(-k) is 0 if k is even.
  let eps = bf_epsilon(x)
  let logx = bf_log(x)
  let mut sum : Value = int(0)
  let mut k : Value = int(0)
  let mut top : Value = int(1)
  let mut bot : Value = int(1)
  let mut term = bf_mul(bf_div(top, bot), bf_to(specfn__zfun(bf_sub(n, k), n, x)))
  while !(bf_gt(k, int(4)) &&
    oddp(bf_sub(n, k)) &&
    // even terms are all zero
    bf_le(bf_abs(term), bf_mul(bf_abs(sum), eps))) {
    sum = bf_add(sum, term)
    k = bf_1_plus(k)
    top = bf_mul(top, logx)
    bot = bf_mul(bot, k)
    term = bf_mul(bf_div(top, bot), bf_to(specfn__zfun(bf_sub(n, k), n, x)))
  }
  sum
}

///|
fn bf_li3numer(x : Value) -> Value raise {
  // If |x| < series-threshold, the series is used.
  let series_threshold : Value = Flo(0.8)
  if bf_zerop(x) {
    Flo(0.0)
  } else if bf_eq(x, int(1)) {
    ftake(q_p_zeta, [maxima_to(bf_float(int(3), x))])
  } else if bf_eq(x, int(-1)) {
    // li[3](-1) = -(1-2^(1-3))*li[3](1)
    //           = -3/4*zeta(3)
    //
    // From the formula
    //
    //   li[s](-1) = (2^(1-s)-1)*zeta(s)
    //
    // (See http://functions.wolfram.com/10.08.03.0003.01)
    bf_mul(
      num_div(int(-3), int(4)),
      bf_to(ftake(q_p_zeta, [maxima_to(bf_float(int(3), x))])),
    )
  } else if bf_gt(bf_abs(x), int(1)) {
    // For z not in the interval (0, 1) and for integral n, we have the
    // identity:
    //
    // li[n](z) = -log(-z)^n/n! + (-1)^(n-1)*li[n](1/z)
    //    + 2 * sum(li[2*r](-1)/(n-2*r)!*log(-z)^(n-2*r), r, 1, floor(n/2))
    //
    // In particular for n = 3:
    //
    // li[3](z) = li[3](1/z) - log(-z)/6*(log(-z)^2+%pi^2)
    let lg = bf_log(bf_neg(x))
    let dpi = bf_p_pi(x)
    bf_sub(
      bf_li3numer(bf_inv(x)),
      bf_mul(bf_div(lg, int(6)), bf_add(bf_mul(lg, lg), bf_mul(dpi, dpi))),
    )
  } else if bf_gt(bf_abs(x), series_threshold) {
    let result = bf_li_using_powers_of_log(int(3), x)
    // For real x, li-using-power-of-log can return a complex number with a
    // tiny imaginary part.  Get rid of that when x is real.
    if bf_realp(x) {
      bf_realpart(result)
    } else {
      result
    }
  } else {
    // Sum the power series.  threshold determines when the summation has
    // converted.
    let threshold = bf_epsilon(x)
    let p = bf_mul(bf_mul(x, x), x)
    let mut term = bf_div(p, int(27))
    term = bf_add(term, bf_mul(bf_mul(Flo(0.125), x), x))
    term = bf_add(term, x)
    let mut k = int(4)
    let mut p1 = bf_mul(p, x)
    let mut h = bf_div(p1, bf_mul(bf_mul(k, k), k))
    let mut s = h
    while !bf_le(bf_abs(bf_div(h, s)), threshold) {
      k = bf_1_plus(k)
      p1 = bf_mul(p1, x)
      h = bf_div(p1, bf_mul(bf_mul(k, k), k))
      s = bf_add(s, h)
    }
    bf_add(s, term)
  }
}

///|
fn bf_li2numer(z : Value) -> Value raise {
  // The series threshold to above sqrt(1/2) because li[2](%i) needs the
  // value of li[2](1/2-%i/2), and the magnitude of the argument is
  // sqrt(1/2) = 0.707.  If the threshold is below this, we get into an
  // infinite recursion oscillating between the two args.
  let series_threshold : Value = Flo(0.75)
  if bf_zerop(z) {
    int(0)
  } else if bf_eq(z, int(1)) {
    // %pi^2/6.  This follows from the series.
    bf_div(bf_expt(bf_p_pi(z), int(2)), int(6))
  } else if bf_eq(z, int(-1)) {
    // -%pi^2/12.  From the formula
    //
    //   li[s](-1) = (2^(1-s)-1)*zeta(s)
    bf_div(bf_expt(bf_p_pi(z), int(2)), int(-12))
  } else if bf_gt(bf_abs(z), int(1)) {
    // Use
    //   li[2](z) = -li[2](1/z) - 1/2*log(-z)^2 - %pi^2/6,
    //
    // valid for all z not in the intervale (0, 1).
    bf_neg(
      bf_add(
        bf_add(
          bf_li2numer(bf_inv(z)),
          bf_mul(Flo(0.5), bf_expt(bf_log(bf_neg(z)), int(2))),
        ),
        bf_div(bf_expt(bf_p_pi(z), int(2)), int(6)),
      ),
    )
  } else if bf_gt(bf_abs(z), series_threshold) {
    // this converges faster when close to unit circle
    bf_li_using_powers_of_log(int(2), z)
  } else {
    // Series evaluation:
    //
    // li[2](z) = sum(z^k/k^2, k, 1, inf);
    let eps = bf_epsilon(z)
    let mut k = int(0)
    let mut term = z
    let mut sum = z
    while !bf_le(bf_abs(bf_div(term, sum)), eps) {
      k = bf_1_plus(k)
      term = bf_mul(
        term,
        bf_div(bf_mul(bf_mul(z, k), k), bf_expt(bf_1_plus(k), int(2))),
      )
      sum = bf_add(term, sum)
    }
    sum
  }
}

///|
fn bf_polylog_power_series(s : Value, z : Value) -> (Value, Value) raise {
  // Series evaluation:
  //
  // li[s](z) = sum(z^k/k^s, k, 1, inf);
  let eps = bf_epsilon(z)
  let mut k = int(1)
  let mut term = z
  let mut sum = z
  while !bf_le(bf_abs(bf_div(term, sum)), eps) {
    k = bf_1_plus(k)
    term = bf_mul(
      bf_mul(term, z),
      bf_expt(bf_div(bf_sub(k, int(1)), k), s),
    )
    sum = bf_add(term, sum)
  }
  // Return the value and the number of terms used, for debugging and for
  // helping in determining the series threshold.
  (sum, k)
}

///|
fn bf_polylog_log_series(s : Value, z : Value) -> Value raise {
  // When x is on or near the unit circle the other approaches don't work.
  // Use the expansion in powers of log(z) (from cephes cpolylog)
  //
  //   li[s](z) = sum(Z(s-j)*(log(z))^j/j!, j = 0, inf)
  //
  // where Z(j) = zeta(j) for j != 1.  For j = 1:
  //
  //   Z(1) = -log(-log(z)) + sum(1/k, k, 1, s - 1)
  let debug = () => symval(q_ear_debug_li_eval).truthy()
  let eps = bf_epsilon(z)
  let logx = bf_log(z)
  let logx_2 = bf_mul(logx, logx)
  let mut top = logx
  let mut bot : Value = int(1)
  let mut sum = specfn__zfun(s, s, z)
  // Compute sum(Z(s-j)*log(z)^j/j!, j = 1, s)
  let mut k = int(1)
  let mut zf = specfn__zfun(bf_sub(s, k), s, z)
  let mut term = bf_mul(bf_div(top, bot), zf)
  while !bf_gt(k, s) {
    if debug() {
      format(t, "~3d: ~A / ~A * ~A => ~A~%", [k, top, bot, zf, term]) |> ignore
    }
    sum = bf_add(sum, term)
    bot = bf_mul(bot, bf_1_plus(k))
    top = bf_mul(top, logx)
    k = bf_1_plus(k)
    zf = specfn__zfun(bf_sub(s, k), s, z)
    term = bf_mul(bf_div(top, bot), zf)
  }
  if debug() {
    format(t, "s = ~A, sum = ~S top, bot = ~S ~S~%", [s, sum, top, bot])
    |> ignore
  }
  // Compute the sum for j = s+1 and up.  But since zeta(-k) is 0 for k
  // even, we only every other term.
  k = bf_add(s, int(1))
  zf = specfn__zfun(bf_sub(s, k), s, z)
  term = bf_mul(bf_div(top, bot), zf)
  while !bf_le(bf_abs(term), bf_mul(bf_abs(sum), eps)) {
    if debug() {
      format(t, "~3d: ~A / ~A = ~A~%", [k, top, bot, term]) |> ignore
    }
    sum = bf_add(sum, term)
    bot = bf_mul(bf_mul(bot, bf_add(k, int(1))), bf_add(k, int(2)))
    top = bf_mul(top, logx_2)
    k = bf_add(k, int(2))
    zf = specfn__zfun(bf_sub(s, k), s, z)
    term = bf_mul(bf_div(top, bot), zf)
  }
  // Return the result (the Lisp also returns the number of terms used as
  // a second value).
  //
  // Note that if z is real and less than 0, li[s](z) is real.  The series
  // can return a tiny complex value in this case, so we want to clear
  // that out before returning the answer.
  if bf_realp(z) && bf_minusp(z) {
    bf_realpart(sum)
  } else {
    sum
  }
}

///|
fn bf_polylog_inversion_formula(s : Value, z : Value) -> Value raise {
  // For z not in the interval (0, 1) and for integral n, we have the
  // identity:
  //
  // li[n](z) = -log(-z)^n/n! + (-1)^(n-1)*li[n](1/z)
  //    + 2 * sum(li[2*r](-1)/(n-2*r)!*log(-z)^(n-2*r), r, 1, floor(n/2))
  //
  // Or
  //
  // li[n](z) = -log(-z)^n/n! + (-1)^(n-1)*li[n](1/z)
  //    + 2 * sum((li[2*m-2*r](-1)*log(-z)^(2*r+1))/(2*r+1)!,r,0,floor(n/2)-1);
  //
  // where m = floor(n/2).
  let debug = () => symval(q_ear_debug_li_eval).truthy()
  let lgz = bf_log(bf_neg(z))
  let lgz_2 = bf_mul(lgz, lgz)
  let half_s = bf_floor(s, divisor=int(2)).0
  let neg_1 = bf_float(int(-1), bf_realpart(z))
  let mut sum : Value = int(0)
  let even = evenp(s)
  let mut r = int(0)
  let mut top = if oddp(s) { lgz } else { int(1) }
  let mut bot : Value = int(1)
  let mut term = bf_mul(
    bf_li_s_simp(bf_mul(int(2), bf_sub(half_s, r)), neg_1),
    bf_div(top, bot),
  )
  while !bf_ge(r, half_s) {
    sum = bf_add(sum, term)
    if debug() {
      format(t, "r = ~4d:  ~A / ~A, ~A; ~A~%", [r, top, bot, term, sum])
      |> ignore
    }
    r = bf_1_plus(r)
    top = bf_mul(top, lgz_2)
    bot = if even {
      bf_mul(bf_mul(bot, bf_add(bf_add(r, r), int(-1))), bf_add(r, r))
    } else {
      bf_mul(bf_mul(bot, bf_add(r, r)), bf_add(bf_add(r, r), int(1)))
    }
    term = bf_mul(
      bf_li_s_simp(bf_mul(int(2), bf_sub(half_s, r)), neg_1),
      bf_div(top, bot),
    )
  }
  bf_add(
    bf_add(
      bf_add(sum, sum),
      bf_neg(bf_div(bf_expt(lgz, s), take(list1(q_mfactorial), [s]))),
    ),
    bf_mul(bf_expt(int(-1), bf_sub(s, int(1))), bf_li_s_simp(s, bf_inv(z))),
  )
}

///|
fn bf_li_s_simp(s : Value, z : Value) -> Value raise {
  let series_threshold : Value = Flo(0.5)
  let log_series_threshold = int(2)
  if bf_zerop(z) {
    maxima_to(bf_to(Flo(0.0)))
  } else if bf_eq(z, int(1)) {
    ftake(q_p_zeta, [maxima_to(bf_float(s, z))])
  } else if bf_eq(z, int(-1)) {
    bf_neg(
      bf_mul(
        bf_sub(int(1), bf_expt(int(2), bf_sub(int(1), s))),
        bf_to(bf_li_s_simp(s, bf_neg(z))),
      ),
    )
  } else if bf_le(bf_abs(z), series_threshold) {
    bf_polylog_power_series(s, z).0
  } else if bf_le(bf_abs(z), log_series_threshold) {
    bf_polylog_log_series(s, z)
  } else if bf_gt(bf_abs(z), Flo(1.5)) {
    bf_polylog_inversion_formula(s, z)
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Computation of Catalan's constant
//
// catalan = 1/2*sum(a[n], k, 0, inf)
//
//  a[n] = (-8)^k*(3*k+2)/((2*k+1)^3*binomial(2*k,k)^3)
//
// This is the first of the other quickly converging series from
// https://en.wikipedia.org/wiki/Catalan%27s_constant
//
// This is an alternating series, so we can stop when the computed term is
// below our desired accuracy.
//
// The ratio between successive terms is
//
//   a[n+1]/a[n] = -(3*k+5)/(3*k+2)*((k+1)/(2*k+3))^3

///|
fn bf_comp_catalan(prec : Value) -> Value raise {
  let limit = bf_expt(int(2), bf_neg(prec))
  let mut k = int(0)
  let mut a = bf_bigfloat(int(2))
  let mut sum = bf_bigfloat(int(0))
  while !bf_lt(bf_abs(a), limit) {
    let new_a = bf_mul(
      bf_mul(int(-1), a),
      bf_mul(
        bf_div(
          bf_add(bf_mul(int(3), k), int(5)),
          bf_add(bf_mul(int(3), k), int(2)),
        ),
        bf_expt(
          bf_div(bf_add(k, int(1)), bf_add(bf_mul(int(2), k), int(3))),
          int(3),
        ),
      ),
    )
    let new_sum = bf_add(sum, a)
    k = bf_add(k, int(1))
    a = new_a
    sum = new_sum
  }
  maxima_to(bf_div(sum, int(2)))
}

// ---------------------------------------------------------------------------

///|
fn specfn__make_flonum_array(xs : Array[Double]) -> Value raise {
  let a = make_array([xs.length()], elt="flonum")
  for i, x in xs {
    aset1(a, i, Flo(x)) |> ignore
  }
  a
}

///|
fn init_specfn() -> Unit raise {
  // li has mirror symmetry:
  //
  //   li[s](conjugate(z)) = conjugate(li[s](z))
  //
  // for z not on the negative real line.
  putprop(q_p_li, t, q_commutes_with_conjugate) |> ignore
  defvar_init(
    q_ear_li2,
    specfn__make_flonum_array([
      14.0, 1.93506430, 0.166073033, 2.48793229e-2, 4.68636196e-3, 1.0016275e-3,
      2.32002196e-4, 5.68178227e-5, 1.44963006e-5, 3.81632946e-6, 1.02990426e-6,
      2.83575385e-7, 7.9387055e-8, 2.2536705e-8, 6.474338e-9,
    ]),
  )
  defvar_init(
    q_ear_li3,
    specfn__make_flonum_array([
      14.0, 1.95841721, 8.51881315e-2, 8.55985222e-3, 1.21177214e-3, 2.07227685e-4,
      3.99695869e-5, 8.38064066e-6, 1.86848945e-6, 4.36660867e-7, 1.05917334e-7,
      2.6478920e-8, 6.787e-9, 1.776536e-9, 4.73417e-10,
    ]),
  )
  defvar_init(
    q_ear_s12,
    specfn__make_flonum_array([
      17.0, 1.90361778, 0.431311318, 0.100022507, 2.44241560e-2, 6.22512464e-3,
      1.64078831e-3, 4.44079203e-4, 1.22774942e-4, 3.45398128e-5, 9.85869565e-6,
      2.84856995e-6, 8.31708473e-7, 2.45039499e-7, 7.2764962e-8, 2.1758023e-8,
      6.546158e-9, 1.980328e-9,
    ]),
  )
  // Integral of psi function psi[n](x)
  putprop(
    q_d_psi,
    list3(
      list2(q_n, q_x),
      Nil,
      lfunc("psi-integral", args => specfn__psi_integral(arg(args, 0), arg(args, 1))),
    ),
    q_integral,
  )
  |> ignore
  // Derivative of lambert_w
  push_special(q_p_lambert_w, q_ear_defgrad_syms) |> ignore
  setf_get(
    q_p_lambert_w,
    q_grad,
    list2(list1(q_d_x), maxima_lit("%e^-lambert_w(x)/(lambert_w(x)+1)")),
  )
  |> ignore
  // Integral of lambert_w
  // integrate(W(x),x) := x*(W(x)^2-W(x)+1)/W(x)
  putprop(
    q_p_lambert_w,
    lread(
      "((x) ((mtimes) x ((mplus) ((mexpt) ((%lambert_w) x) 2) ((mtimes) -1 ((%lambert_w) x)) 1) ((mexpt) ((%lambert_w) x) -1)))",
    ),
    q_integral,
  )
  |> ignore
  // Derivative of generalized_lambert_w
  push_special(q_p_generalized_lambert_w, q_ear_defgrad_syms) |> ignore
  setf_get(
    q_p_generalized_lambert_w,
    q_grad,
    list3(
      list2(q_d_k, q_d_x),
      // wrt k
      Nil,
      // wrt x
      maxima_lit(
        " %e^-generalized_lambert_w(k,x)/(generalized_lambert_w(k,x)+1)",
      ),
    ),
  )
  |> ignore
  // Integral of generalized_lambert_w
  // integrate(W(k,x),x) := x*(W(k,x)^2-W(k,x)+1)/W(k,x)
  putprop(
    q_p_generalized_lambert_w,
    lread(
      "((k x) nil ((mtimes) x ((mplus) ((mexpt) ((%generalized_lambert_w) k x) 2) ((mtimes) -1 ((%generalized_lambert_w) k x)) 1) ((mexpt) ((%generalized_lambert_w) k x) -1)))",
    ),
    q_integral,
  )
  |> ignore
}
