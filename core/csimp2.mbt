// Port of src/csimp2.lisp: simplifiers for plog, binomial, beta and gamma;
// numerical gamma; zeromatrix/ematrix/coefmatrix/entermatrix; $xthru;
// XRUTOUT (back substitution for linsolve).

///|
/// The argument-count check and argument fetching of DEF-SIMPLIFIER.
fn csimp2__simp_args(
  form : Value,
  noun : Value,
  argnames : Array[Value],
  z : Value,
) -> Array[Value] raise {
  let n = argnames.length()
  if length(cdr(form)) != n {
    wna_err(
      form,
      required_arg_count=int(n),
      pretty_name=cons(list1(noun), list(argnames)),
    )
    |> ignore
  }
  let out = []
  for i in 1..=n {
    out.push(simpcheck(nth(i, form), z))
  }
  out
}

///|
/// The local GIVE-UP of DEF-SIMPLIFIER.
fn csimp2__give_up(noun : Value, args : Array[Value], form : Value) -> Value raise {
  eqtest(cons(list1(noun), list(args)), form)
}

// ---------------------------------------------------------------------------
// Implementation of the plog function

///|
fn simp__pctplog(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let x = csimp2__simp_args(form, q_p_plog, [q_d_x], p__pctsimpflag)[0]
  let give_up = () => csimp2__give_up(q_p_plog, [x], form)
  with_special(q_varlist, Nil, () => {
    if equal(Fix(0L), x) {
      merr("plog: plog(0) is undefined.", []) |> ignore
    } else if among(symval(q_var), x).truthy() {
      // This is used in DEFINT, in particular in the call to KEYHOLE in
      // ZTORAT for an integral like integrate(1/(x^2+x+1),x,0,inf).
      return give_up()
    }
    newvar(x) |> ignore
    let varlist = symval(q_varlist)
    if memq(q_d__pcti, varlist).truthy() &&
      !some(v => atom(v) && !eq(v, q_d__pcti), varlist) {
      let dd = trisplit(x)
      let z = patan(car(dd), cdr(dd))
      if z.truthy() {
        return add2_star(
          ftake(q_p_log, [
            power(
              d_expand(
                add_star(
                  list2(power(car(dd), Fix(2L)), power(cdr(dd), Fix(2L))),
                ),
              ),
              symval(q_n1_sl_sl2),
            ),
          ]),
          mul_star(list2(z, q_d__pcti)),
        )
      }
    } else if free(x, q_d__pcti).truthy() && eq(d_sign(x), q_d_pnz) {
      return give_up()
    } else if equal(d_imagpart(x), Fix(0L)) &&
      {
        let y = d_asksign(x)
        if y.truthy() {
          return if eq(y, q_d_pos) {
            ftake(q_p_log, [x])
          } else if symval(q_plogabs).truthy() && eq(y, q_d_neg) {
            ftake(q_p_log, [mk(q_mtimes, [Fix(-1L), x])])
          } else if eq(y, q_d_neg) {
            add2(symval(q_p_p_pcti), ftake(q_p_log, [mul2(Fix(-1L), x)]))
          } else {
            merr("plog: plog(0) is undefined.", [])
          }
        }
        false
      } {
      ()
    } else {
      let z = div_star(x, q_d__pcti)
      if equal(d_imagpart(z), Fix(0L)) {
        let y = d_asksign(z)
        if y.truthy() {
          if equal(y, q_d_zero) {
            return merr("plog: plog(0) is undefined.", [])
          }
          let yy : Value = if eq(y, q_d_pos) {
            Fix(1L)
          } else if eq(y, q_d_neg) {
            Fix(-1L)
          } else {
            y
          }
          return add2_star(
            ftake(q_p_log, [mul2(yy, z)]),
            muln_([yy, symval(q_n1_sl_sl2), q_d__pcti, q_d__pctpi]),
          )
        }
      }
    }
    give_up()
  })
}

///|
fn patan(r0 : Value, i0 : Value) -> Value raise {
  with_specials([(q_d_numer, symval(q_d_numer)), (q_var, Nil)], () => {
    let i = simplifya(i0, Nil)
    let r = simplifya(r0, Nil)
    if zerop1(r).truthy() {
      if floatp(i) {
        set(q_d_numer, t) |> ignore
      }
      let s = d_asksign(i)
      return if equal(s, q_d_pos) {
        simplify(symval(q_half_pctpi))
      } else if equal(s, q_d_neg) {
        mul2(Fix(-1L), simplify(symval(q_half_pctpi)))
      } else {
        merr("plog: encountered atan(0/0).", [])
      }
    } else if zerop1(i).truthy() {
      if floatp(r) {
        set(q_d_numer, t) |> ignore
      }
      let s = d_asksign(r)
      return if equal(s, q_d_pos) {
        Fix(0L)
      } else if equal(s, q_d_neg) {
        simplify(q_d__pctpi)
      } else {
        merr("plog: encountered atan(0/0).", [])
      }
    } else if among(q_p_cos, r).truthy() && among(q_p_sin, i).truthy() {
      // genvar and varlist, used by the rational function system, are bound
      // in order to prevent the symbol 'xz from leaking out of this
      // function.
      let res = with_specials(
        [(q_var, q_xz), (q_genvar, Nil), (q_varlist, Nil)],
        () => {
          numden(div_star(r, i)) |> ignore
          let nn = symval(q_nn_star)
          let dn = symval(q_dn_star)
          if eq(caar(nn), q_p_cos) && eq(caar(dn), q_p_sin) {
            cadr(nn)
          } else {
            Nil
          }
        },
      )
      if res.truthy() {
        return res
      }
    }
    let sign_to_int = fn(s : Value) -> Value {
      if eq(s, q_d_pos) {
        Fix(1L)
      } else if eq(s, q_d_neg) {
        Fix(-1L)
      } else if eq(s, q_d_zero) {
        Fix(0L)
      } else {
        s
      }
    }
    let a = sign_to_int(d_sign(r))
    let b = sign_to_int(d_sign(i))
    if equal(i, Fix(0L)) {
      return if equal(a, Fix(1L)) { Fix(0L) } else { simplify(q_d__pctpi) }
    } else if equal(r, Fix(0L)) {
      return if equal(b, Fix(1L)) {
        simplify(symval(q_half_pctpi))
      } else {
        mul2(mk_simp(q_rat, [Fix(-1L), Fix(2L)]), simplify(q_d__pctpi))
      }
    }
    let r = simptimes(mk(q_mtimes, [a, b, div_star(i, r)]), Fix(1L), Nil)
    if onep1(r).truthy() {
      archk(a, b, mk(q_mtimes, [mk(q_rat, [Fix(1L), Fix(4L)]), q_d__pctpi]))
    } else if alike1(r, mk(q_mexpt, [Fix(3L), mk(q_rat, [Fix(1L), Fix(2L)])])).truthy() {
      archk(a, b, mk(q_mtimes, [mk(q_rat, [Fix(1L), Fix(3L)]), q_d__pctpi]))
    } else if alike1(r, mk(q_mexpt, [Fix(3L), mk(q_rat, [Fix(-1L), Fix(2L)])])).truthy() {
      archk(a, b, mk(q_mtimes, [mk(q_rat, [Fix(1L), Fix(6L)]), q_d__pctpi]))
    } else {
      Nil
    }
  })
}

// ---------------------------------------------------------------------------
// Implementation of the Binomial coefficient

///|
fn simp__pctbinomial(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let a = csimp2__simp_args(form, q_p_binomial, [q_d_u, q_d_v], p__pctsimpflag)
  let u = a[0]
  let v = a[1]
  let give_up = () => csimp2__give_up(q_p_binomial, [u, v], form)
  if integerp(v) {
    if minusp(v) {
      if integerp(u) && minusp(u) && num_lt(v, u) {
        bincomp(u, num_sub(u, v))
      } else {
        Fix(0L)
      }
    } else if zerop(v) || equal(u, v) {
      Fix(1L)
    } else if integerp(u) && !minusp(u) {
      bincomp(u, num_min(v, num_sub(u, v)))
    } else {
      bincomp(u, v)
    }
  } else {
    let y = sub(u, v)
    if integerp(y) {
      if zerop1(y).truthy() {
        // u and v are equal, simplify not if argument can be negative
        if memq(d_csign(u), list([q_d_pnz, q_d_pn, q_d_neg, q_d_nz])).truthy() {
          give_up()
        } else {
          bincomp(u, y)
        }
      } else {
        bincomp(u, y)
      }
    } else if complex_float_numerical_eval_p(list2(u, v)).truthy() {
      // Numercial evaluation for real and complex floating point numbers.
      with_specials([(q_d_numer, t), (q_d_float, t)], () => d_rectform(
        d_float(
          d_makegamma(list([list1(q_p_binomial), d_float(u), d_float(v)])),
        ),
      ))
    } else if complex_bigfloat_numerical_eval_p(list2(u, v)).truthy() {
      // Numerical evaluation for real and complex bigfloat numbers.
      d_rectform(
        d_bfloat(
          d_makegamma(list([list1(q_p_binomial), d_bfloat(u), d_bfloat(v)])),
        ),
      )
    } else if mplusp(v).truthy() &&
      {
        let y = sub(u, v)
        !mplusp(y).truthy() || length(cdr(y)) < length(cdr(v))
      } {
      // We have binomial(u, v), where v is a sum (or difference), and y =
      // u-v is either no longer a sum or has fewer terms than v.  In this
      // case, simplify to binomial(u, u-v).
      ftake(q_p_binomial, [u, sub(u, v)])
    } else {
      give_up()
    }
  }
}

///|
fn bincomp(u : Value, v : Value) -> Value raise {
  if minusp(v) {
    Fix(0L)
  } else if zerop(v) {
    Fix(1L)
  } else if mnump(u).truthy() {
    binocomp(u, v)
  } else {
    muln(bincomp1(u, v), Nil)
  }
}

///|
fn bincomp1(u : Value, v : Value) -> Value raise {
  if equal(v, Fix(1L)) {
    ncons(u)
  } else {
    cons(
      u,
      cons(mk(q_mexpt, [v, Fix(-1L)]), bincomp1(add2(Fix(-1L), u), one_minus(v))),
    )
  }
}

///|
fn binocomp(u0 : Value, v0 : Value) -> Value raise {
  let mut ans : Value = Fix(1L)
  let mut u = u0
  let mut v = v0
  while !zerop(v) {
    ans = timesk(timesk(u, ans), simplify(mk(q_rat, [Fix(1L), v])))
    u = addk(Fix(-1L), u)
    v = one_minus(v)
  }
  ans
}

// ---------------------------------------------------------------------------
// Implementation of the Beta function

///|
/// (nth-value 1 (truncate x))
fn csimp2__trunc_rem(x : Value) -> Value raise {
  num_truncate(x).1
}

///|
/// (and (mnump v) (eq ($sign (sub ($truncate v) v)) '$zero)
///      (eq ($sign v) '$neg) (eq ($sign (add u v)) '$pos))
fn csimp2__negint_sum_pos(v : Value, u : Value) -> Bool raise {
  mnump(v).truthy() &&
  eq(d_sign(sub(ftake(q_p_truncate, [v]), v)), q_d_zero) &&
  eq(d_sign(v), q_d_neg) &&
  eq(d_sign(add2(u, v)), q_d_pos)
}

///|
/// `(= NIL 0)`: a type error in the Lisp.
fn csimp2__nil_eq_error() -> Bool raise {
  raise LispError::Condition(
    intern("type-error"),
    "The value NIL is not of type NUMBER",
    Nil,
  )
}

///|
fn simp__pctbeta(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let a = csimp2__simp_args(form, q_p_beta, [q_d_u, q_d_v], p__pctsimpflag)
  let mut u = a[0]
  let mut v = a[1]
  let give_up = () => csimp2__give_up(q_p_beta, [a[0], a[1]], form)
  let truncate = fn(x : Value) -> Value raise { ftake(q_p_truncate, [x]) }
  if zerop1(u).truthy() || zerop1(v).truthy() {
    if symval(q_errorsw).truthy() {
      throw_tag(q_errorsw, t)
    } else {
      merr("beta: expected nonzero arguments; found ~M, ~M", [u, v])
    }
  } else if complex_float_numerical_eval_p(list2(u, v)).truthy() {
    // Check for numerical evaluation in float precision.  We use
    // gamma(u)*gamma(v)/gamma(u+v) for numerical evaluation.  Therefore u,
    // v or u+v can not be a negative integer or a floating point
    // representation of a negative integer.
    if (!numberp(u) || plusp(u) || !num_eq(csimp2__trunc_rem(u), Fix(0L))) &&
      (!numberp(v) || plusp(v) || !num_eq(csimp2__trunc_rem(v), Fix(0L))) &&
      (
        !numberp(add2(u, v)) ||
        plusp(add2(v, u)) ||
        // (nth-value 1 ($truncate (add u v))) is NIL: (= NIL 0) signals an
        // error in the Lisp.
        csimp2__nil_eq_error()
      ) {
      d_rectform(
        power(
          d_float(q_d__pcte),
          addn_([
            d_log_gamma(d_float(u)),
            d_log_gamma(d_float(v)),
            mul2(Fix(-1L), d_log_gamma(d_float(add2(u, v)))),
          ]),
        ),
      )
    } else if (
        numberp(u) &&
        plusp(u) &&
        num_eq(csimp2__trunc_rem(u), Fix(0L)) &&
        !csimp2__negint_sum_pos(v, u) &&
        {
          u = num_truncate(u).0
          u.truthy()
        }
      ) ||
      (
        numberp(v) &&
        plusp(v) &&
        num_eq(csimp2__trunc_rem(v), Fix(0L)) &&
        !csimp2__negint_sum_pos(u, v) &&
        {
          v = num_truncate(v).0
          v.truthy()
        }
      ) {
      // One value is representing a negative integer, the other a positive
      // integer and the sum is negative. Expand.
      d_rectform(d_float(beta_expand_integer(u, v)))
    } else {
      give_up()
    }
  } else if complex_bigfloat_numerical_eval_p(list2(u, v)).truthy() {
    // Check for numerical evaluation in bigfloat precision
    with_special(q_d_ratprint, Nil, () => if (
        !mnump(u).truthy() ||
        eq(d_sign(u), q_d_pos) ||
        !eq(d_sign(sub(truncate(u), u)), q_d_zero)
      ) &&
      (
        !mnump(v).truthy() ||
        eq(d_sign(v), q_d_pos) ||
        !eq(d_sign(sub(truncate(v), v)), q_d_zero)
      ) &&
      (
        !mnump(add2(u, v)).truthy() ||
        eq(d_sign(add2(u, v)), q_d_pos) ||
        !eq(d_sign(sub(truncate(add2(u, v)), add2(u, v))), q_d_zero)
      ) {
      d_rectform(
        power(
          d_bfloat(q_d__pcte),
          addn_([
            d_log_gamma(d_bfloat(u)),
            d_log_gamma(d_bfloat(v)),
            mul2(Fix(-1L), d_log_gamma(d_bfloat(add2(u, v)))),
          ]),
        ),
      )
    } else if (
        mnump(u).truthy() &&
        eq(d_sign(u), q_d_pos) &&
        eq(d_sign(sub(truncate(u), u)), q_d_zero) &&
        !csimp2__negint_sum_pos(v, u) &&
        {
          u = truncate(u)
          u.truthy()
        }
      ) ||
      (
        mnump(v).truthy() &&
        eq(d_sign(v), q_d_pos) &&
        eq(d_sign(sub(truncate(v), v)), q_d_zero) &&
        !csimp2__negint_sum_pos(u, v) &&
        {
          v = truncate(v)
          v.truthy()
        }
      ) {
      d_rectform(d_bfloat(beta_expand_integer(u, v)))
    } else {
      give_up()
    })
  } else if (integerp(u) && plusp(u) && !csimp2__negint_sum_pos(v, u)) ||
    (integerp(v) && plusp(v) && !csimp2__negint_sum_pos(u, v)) {
    // Expand for a positive integer. But not if the other argument is a
    // negative integer and the sum of the integers is not negative.
    beta_expand_integer(u, v)
  } else {
    // At this point both integers are negative. This code does not work
    // for negative integers. The factorial function is not defined.
    let mut x = Value::Nil
    if (
        ratnump(u).truthy() &&
        ratnump(v).truthy() &&
        {
          x = addk(u, v)
          integerp(x)
        }
      ) ||
      (
        symval(q_d_beta_args_sum_to_integer).truthy() &&
        {
          x = expand1(add2(u, v), Fix(1L), Fix(1L))
          integerp(x)
        }
      ) {
      let w = if symbolp(v) { v } else { u }
      div_star(
        mul2_star(
          q_d__pctpi,
          list([list1(q_p_binomial), add2(one_minus(x), neg(w)), one_minus(x)]),
        ),
        list2(list1(q_p_sin), mk(q_mtimes, [w, q_d__pctpi])),
      )
    } else if symval(q_d_beta_expand).truthy() &&
      mplusp(u).truthy() &&
      integerp(cadr(u)) {
      // Expand beta(a+n,b) where n is an integer.
      let n = cadr(u)
      let u2 = simplify(cons(list1(q_mplus), cddr(u)))
      beta_expand_add_integer(n, u2, v)
    } else if symval(q_d_beta_expand).truthy() &&
      mplusp(v).truthy() &&
      integerp(cadr(v)) {
      // Expand beta(a,b+n) where n is an integer.
      let n = cadr(v)
      let v2 = simplify(cons(list1(q_mplus), cddr(v)))
      beta_expand_add_integer(n, v2, u)
    } else {
      give_up()
    }
  }
}

///|
/// One of the arguments is a positive integer. Do an expansion.  BUT for a
/// negative integer as second argument the expansion is only possible when
/// the sum of the integers is negative too.  This routine expects that the
/// calling routine has checked this.
fn beta_expand_integer(u : Value, v : Value) -> Value raise {
  let x = add2(u, v)
  power(
    mul2(
      sub(x, Fix(1L)),
      simplify(
        list([
          list1(q_p_binomial),
          sub(x, Fix(2L)),
          sub(if integerp(u) && plusp(u) { u } else { v }, Fix(1L)),
        ]),
      ),
    ),
    Fix(-1L),
  )
}

///|
fn beta_expand_add_integer(n : Value, u : Value, v : Value) -> Value raise {
  if plusp(n) {
    muln_([
      simplify(list([list1(q_d_pochhammer), u, n])),
      power(simplify(list([list1(q_d_pochhammer), add2(u, v), n])), Fix(-1L)),
      ftake_star(q_p_beta, [u, v]),
    ])
  } else {
    muln_([
      simplify(list([list1(q_d_pochhammer), addn_([u, v, n]), num_neg(n)])),
      power(
        simplify(list([list1(q_d_pochhammer), add2(u, n), num_neg(n)])),
        Fix(-1L),
      ),
      ftake_star(q_p_beta, [u, v]),
    ])
  }
}

// ---------------------------------------------------------------------------
// Implementation of the Gamma function

///|
/// |z| <= sqrt(epsilon(z)) for the bigfloat number z = zr + %i*zi (ZI nil
/// for a real z), as BIGFLOAT:<=, BIGFLOAT:ABS, BIGFLOAT:SQRT and
/// BIGFLOAT:EPSILON compute it.
fn csimp2__bf_small_p(zr : Value, zi : Value) -> Bool raise {
  let absz = if zi is Nil {
    fpabs(cdr(zr))
  } else {
    let x = cdr(zr)
    let y = cdr(zi)
    let s = bcons(fpplus(fptimes_star(x, x), fptimes_star(y, y)))
    if minusp(cadr(s)) {
      raise LispError::SimpleError("bigfloat sqrt of a negative number")
    }
    fproot(s, Fix(2L))
  }
  // epsilon is just above 2^(-fpprec).
  let p = float__prec()
  let eps = bcons(
    list([one_plus(ash(Fix(1L), to_int(p) - 1)), num_neg(one_minus(p))]),
  )
  let sq = fproot(eps, Fix(2L))
  zerop(car(fpdifference(absz, sq))) || fplessp(absz, sq).truthy()
}

///|
/// The bigfloat real and imaginary parts of a Maxima complex number, as
/// BIGFLOAT:TO makes them.
fn csimp2__bf_parts(w : Value) -> (Value, Value) raise {
  let re = bigfloatp(d_bfloat(d_realpart(w)))
  let im = bigfloatp(d_bfloat(d_imagpart(w)))
  (re, im)
}

///|
/// TWO-ARG-/ of two COMPLEX-BIGFLOATs, converted back with MAXIMA::TO.
fn csimp2__cbf_div(
  a_re : Value,
  a_im : Value,
  b_re : Value,
  b_im : Value,
) -> Value raise {
  let (re, im) = if fpgreaterp(fpabs(b_re), fpabs(b_im)).truthy() {
    let r = fpquotient(b_im, b_re)
    let dn = fpplus(b_re, fptimes_star(r, b_im))
    (
      bcons(fpquotient(fpplus(a_re, fptimes_star(a_im, r)), dn)),
      bcons(fpquotient(fpdifference(a_im, fptimes_star(a_re, r)), dn)),
    )
  } else {
    let r = fpquotient(b_re, b_im)
    let dn = fpplus(b_im, fptimes_star(r, b_re))
    (
      bcons(fpquotient(fpplus(fptimes_star(a_re, r), a_im), dn)),
      bcons(fpquotient(fpdifference(fptimes_star(a_im, r), a_re), dn)),
    )
  }
  add2(re, mul2(q_d__pcti, im))
}

///|
fn simp__pctgamma(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let j = csimp2__simp_args(form, q_p_gamma, [q_d_j], p__pctsimpflag)[0]
  let give_up = () => csimp2__give_up(q_p_gamma, [j], form)
  if floatp(j) &&
    (zerop(j) || (minusp(j) && zerop(csimp2__trunc_rem(j)))) {
    merr("gamma: gamma(~:M) is undefined.", [j])
  } else if float_numerical_eval_p(list1(j)).truthy() {
    gammafloat(d_float(j))
  } else if d_bfloatp(j).truthy() &&
    (
      zerop1(j).truthy() ||
      (
        eq(d_sign(j), q_d_neg) &&
        zerop1(sub(j, ftake(q_p_truncate, [j]))).truthy()
      )
    ) {
    merr("gamma: gamma(~:M) is undefined.", [j])
  } else if bigfloat_numerical_eval_p(list1(j)).truthy() {
    // Adding 4 digits in the call to bffac. For $fpprec up to about 256 and
    // an argument up to about 500.0 the accuracy of the result is better
    // than 10^(-$fpprec).
    let z = bigfloatp(d_bfloat(j))
    if csimp2__bf_small_p(z, Nil) {
      // For small z, use gamma(z) = gamma(z+1)/z = z!/z
      div(
        mfuncall(
          q_d_bffac,
          list2(d_bfloat(j), num_add(symval(q_d_fpprec), Fix(4L))),
        ),
        d_bfloat(j),
      )
    } else {
      let result = mfuncall(
        q_d_bffac,
        list2(
          m_plus(list2(d_bfloat(j), Fix(-1L))),
          num_add(symval(q_d_fpprec), Fix(4L)),
        ),
      )
      // bigfloatp will round the result to the correct fpprec
      bigfloatp(result)
    }
  } else if complex_float_numerical_eval_p(list1(j)).truthy() {
    complexify(
      gamma_lanczos(
        complex(d_float(d_realpart(j)), i=d_float(d_imagpart(j))),
      ),
    )
  } else if complex_bigfloat_numerical_eval_p(list1(j)).truthy() {
    let (zr, zi) = csimp2__bf_parts(d_bfloat(j))
    if csimp2__bf_small_p(zr, zi) {
      // For small z, use gamma(z) = gamma(z+1)/z = z!/z
      let w = mfuncall(
        q_d_cbffac,
        list2(add2(zr, mul2(q_d__pcti, zi)), num_add(symval(q_d_fpprec), Fix(4L))),
      )
      let (wr, wi) = csimp2__bf_parts(w)
      csimp2__cbf_div(cdr(wr), cdr(wi), cdr(zr), cdr(zi))
    } else {
      // Adding 4 digits in the call to cbffac. See comment above.
      let result = mfuncall(
        q_d_cbffac,
        list2(
          addn_([
            Fix(-1L),
            d_bfloat(d_realpart(j)),
            mul2(q_d__pcti, d_bfloat(d_imagpart(j))),
          ]),
          num_add(symval(q_d_fpprec), Fix(4L)),
        ),
      )
      add2(
        bigfloatp(d_realpart(result)),
        mul2(q_d__pcti, bigfloatp(d_imagpart(result))),
      )
    }
  } else {
    let tz = taylorize(mop(form), cadr(form))
    if tz.truthy() {
      tz
    } else if eq(j, q_d_inf) {
      // Simplify to $inf to be more consistent.
      q_d_inf
    } else if symval(q_d_gamma_expand).truthy() &&
      mplusp(j).truthy() &&
      integerp(cadr(j)) {
      // Expand gamma(z+n) for n an integer.
      let n = cadr(j)
      let z = simplify(cons(list1(q_mplus), cddr(j)))
      if plusp(n) {
        mul2(
          simplify(list([list1(q_d_pochhammer), z, n])),
          simplify(list2(list1(q_p_gamma), z)),
        )
      } else if minusp(n) {
        let n = num_neg(n)
        div(
          mul2(power(Fix(-1L), n), simplify(list2(list1(q_p_gamma), z))),
          // We factor to get the order (z-1)*(z-2)*...  and not
          // (1-z)*(2-z)*...
          d_factor(simplify(list([list1(q_d_pochhammer), sub(Fix(1L), z), n]))),
        )
      } else {
        Nil
      }
    } else if integerp(j) {
      if plusp(j) {
        if num_le(j, symval(q_d_factlim)) {
          // Positive integer less than $factlim. Evaluate.
          simplify(list2(list1(q_mfactorial), one_minus(j)))
        } else {
          // Positive integer greater $factlim. Noun form.
          give_up()
        }
      } else if symval(q_errorsw).truthy() {
        // Negative integer. Throw a Maxima error.
        throw_tag(q_errorsw, t)
      } else {
        merr("gamma: gamma(~:M) is undefined.", [j])
      }
    } else if alike1(j, mk(q_rat, [Fix(1L), Fix(2L)])).truthy() {
      list([list2(q_mexpt, q_simp), q_d__pctpi, j])
    } else if mnump(j).truthy() &&
      ratgreaterp(symval(q_d_gammalim), simplify(list2(list1(q_mabs), j))).truthy() &&
      (ratgreaterp(j, Fix(1L)).truthy() || ratgreaterp(Fix(0L), j).truthy()) {
      // Expand for rational numbers less than $gammalim.
      gammared(j)
    } else {
      give_up()
    }
  }
}

///|
/// A sign function for gamma(x); when x > 0 return pos; when x < 0 or
/// x > 0, return pn; otherwise, return pnz (that is, nothing known).
fn gamma_sign(x : Value) -> Value raise {
  // careful! x = ((%gamma) XXX)
  let sgn = d_csign(second(x))
  set(
    q_sign,
    if eql(sgn, q_d_pos) {
      q_d_pos
    } else if eql(sgn, q_d_neg) || eql(sgn, q_d_pn) {
      q_d_pn
    } else {
      q_d_pnz
    },
  )
}

///|
/// numerical evaluation for 0 < y < 1
fn gamma(y0 : Value) -> Value raise {
  let mut coefs = list([
    Flo(0.035868343),
    Flo(-0.193527817),
    Flo(0.48219939),
    Flo(-0.75670407),
    Flo(0.91820685),
    Flo(-0.89705693),
    Flo(0.98820588),
    Flo(-0.57719165),
  ])
  let y = if atom(y0) { y0 } else { fpcofrat(y0) }
  let mut sum = car(coefs)
  coefs = cdr(coefs)
  while true {
    sum = num_add(num_mul(sum, y), car(coefs))
    coefs = cdr(coefs)
    if coefs is Nil {
      break
    }
  }
  num_add(num_inv(y), sum)
}

///|
/// A is assumed to be '((RAT) M N)
fn gammared(a : Value) -> Value raise {
  if floatp(a) {
    return gammafloat(a)
  }
  // Numerator, denominator, integer part
  let mut m = cadr(a)
  let n = caddr(a)
  let mut q = num_abs(num_truncate(m, b=n).0)
  if minusp(m) {
    q = one_plus(q)
    m = num_add(m, num_mul(n, q))
    return simptimes(
      list([
        list1(q_mtimes),
        mk(q_mexpt, [n, q]),
        ftake_star(q_p_gamma, [mk(q_rat, [m, n])]),
        mk(q_mexpt, [gammac(m, n, q), Fix(-1L)]),
      ]),
      Fix(1L),
      Nil,
    )
  }
  m_star(
    list([
      gammac(m, n, q),
      ftake_star(q_p_gamma, [mk(q_rat, [num_rem(m, n), n])]),
      m_hat(n, num_neg(q)),
    ]),
  )
}

///|
fn gammac(m0 : Value, n : Value, q0 : Value) -> Value raise {
  let mut ans : Value = Fix(1L)
  let mut m = m0
  let mut q = q0
  while !num_lt(q, Fix(1L)) {
    q = one_minus(q)
    m = num_sub(m, n)
    ans = num_mul(m, ans)
  }
  ans
}

///|
let csimp2__lanczos_c : Array[Double] = [
  0.99999999999999709182, 57.156235665862923517, -59.597960355475491248, 14.136097974741747174,
  -0.49191381609762019978, 0.33994649984811888699e-4, 0.46523628927048575665e-4,
  -0.98374475304879564677e-4, 0.15808870322491248884e-3, -0.21026444172410488319e-3,
  0.21743961811521264320e-3, -0.16431810653676389022e-3, 0.84418223983852743293e-4,
  -0.26190838401581408670e-4, 0.36899182659531622704e-5,
]

///|
/// This implementation is based on Lanczos convergent formula for the gamma
/// function for Re(z) > 0.  We can use the reflection formula
///    -z*Gamma(z)*Gamma(-z) = pi/sin(pi*z)
/// to handle the case of Re(z) <= 0.
fn gamma_lanczos(z : Value) -> Value raise {
  let c = csimp2__lanczos_c
  let pi : Value = Flo(@math.PI)
  if minusp(realpart(z)) {
    // Gamma(z) = pi/z/sin(pi*z)/Gamma(-z)
    // If z is a negative integer, Gamma(z) is infinity.  The test must be
    // done by the calling routine.
    num_div(
      pi,
      num_mul(
        num_mul(num_neg(z), lsin(num_mul(pi, z))),
        gamma_lanczos(num_neg(z)),
      ),
    )
  } else if num_le(num_abs(z), Flo((double_float_epsilon).sqrt())) {
    // For |z| small, use Gamma(z) = Gamma(z+1)/z
    num_div(gamma_lanczos(num_add(Fix(1L), z)), z)
  } else {
    let z = num_sub(z, Fix(1L))
    let zh = num_add(z, num_div(Fix(1L), Fix(2L)))
    let zgh = num_add(zh, num_div(Fix(607L), Fix(128L)))
    let mut ss : Value = Flo(0.0)
    let mut pp = c.length() - 1
    while !(pp < 1) {
      ss = num_add(ss, num_div(Flo(c[pp]), num_add(z, int(pp))))
      pp -= 1
    }
    // We check for an overflow. The last positive value in double-float
    // precision for which Maxima can calculate gamma is ~171.6243.
    let result = errset(() => {
      let zp = expt(zgh, num_div(zh, Fix(2L)))
      num_mul(
        num_mul(Flo((2.0 * @math.PI).sqrt()), num_add(ss, Flo(c[0]))),
        num_mul(num_div(zp, lexp(zgh)), zp),
      )
    })
    match result {
      None => merr("gamma: overflow in GAMMA-LANCZOS.", [])
      Some(result) =>
        if float_nan_p(realpart(result)).truthy() ||
          float_inf_p(realpart(result)).truthy() {
          // Result, but beyond extreme values. Overflow.
          merr("gamma: overflow in GAMMA-LANCZOS.", [])
        } else {
          result
        }
    }
  }
}

///|
fn gammafloat(a0 : Value) -> Value raise {
  let a = to_double(a0)
  if a < 0.0 {
    // Reflection formula to make it positive:
    // gamma(x) = %pi/sin(%pi*x)/x/gamma(-x)
    Flo(
      -@math.PI / (a * dsin(@math.PI * a)) /
      to_double(gammafloat(Flo(-a))),
    )
  } else if a <= (double_float_epsilon).sqrt() {
    // Use gamma(x) = gamma(1+x)/x when x is very small
    Flo(to_double(gammafloat(Flo(1.0 + a))) / a)
  } else if a < 10.0 {
    Flo(@slatec.dgamma(a))
  } else {
    let c = (2.0 * @math.PI).sqrt() * dexp(@slatec.d9lgmc(a))
    let v = dpow(a, 0.5 * a - 0.25)
    let result = v * (v / dexp(a)) * c
    if result.is_nan() || result.is_inf() {
      merr("gamma: overflow in GAMMAFLOAT.", [])
    } else {
      Flo(result)
    }
  }
}

// ---------------------------------------------------------------------------
// Matrices

///|
fn d_zeromatrix(m : Value, n : Value) -> Value raise {
  d_ematrix(m, n, Fix(0L), Fix(1L), Fix(1L))
}

///|
fn d_ematrix(m0 : Value, n : Value, var_ : Value, i : Value, j : Value) -> Value raise {
  let mut m = m0
  if equal(m, Fix(0L)) {
    return ncons(list2(q_d_matrix, q_simp))
  } else if equal(n, Fix(0L)) && fixnump(m) && plusp(m) {
    return cons(list2(q_d_matrix, q_simp), list_of_mlists(m))
  } else if !(
      fixnump(m) &&
      fixnump(n) &&
      fixnump(i) &&
      fixnump(j) &&
      plusp(m) &&
      plusp(n) &&
      plusp(i) &&
      plusp(j)
    ) {
    merr("ematrix: arguments must be positive integers; found ~M", [
      list([list2(q_mlist, q_simp), m, n, i, j]),
    ])
    |> ignore
  } else if num_gt(i, m) || num_gt(j, n) {
    merr(
      "ematrix: the entry position [~M, ~M] is outside a ~M by ~M matrix.",
      [i, j, m, n],
    )
    |> ignore
  }
  let mut ans = Value::Nil
  while true {
    let row = if num_eq(m, i) {
      onen(j, n, var_, Fix(0L))
    } else if zerop(m) {
      return cons(list1(q_d_matrix), mxc(ans))
    } else {
      let mut row = Value::Nil
      let mut k = n
      while !zerop(k) {
        row = cons(Fix(0L), row)
        k = one_minus(k)
      }
      row
    }
    ans = cons(row, ans)
    m = one_minus(m)
  }
  Nil
}

///|
fn list_of_mlists(n : Value) -> Value raise {
  let mut l = Value::Nil
  let mut k = n
  while !num_eq(k, Fix(0L)) {
    l = cons(ncons(list2(q_mlist, q_simp)), l)
    k = one_minus(k)
  }
  l
}

///|
fn d_coefmatrix(eql_ : Value, varl : Value) -> Value raise {
  coefmatrix(eql_, varl, Nil)
}

///|
fn d_augcoefmatrix(eql_ : Value, varl : Value) -> Value raise {
  coefmatrix(eql_, varl, t)
}

///|
fn coefmatrix(eql0 : Value, varl0 : Value, ind : Value) -> Value raise {
  if !d_listp(eql0).truthy() {
    improper_arg_err(eql0, q_d_coefmatrix) |> ignore
  }
  if !d_listp(varl0).truthy() {
    improper_arg_err(varl0, q_d_coefmatrix) |> ignore
  }
  for v in cdr(varl0).iter() {
    if !atom(v) && memq(caar(v), list2(q_mplus, q_mtimes)).truthy() {
      merr(
        "coefmatrix: variables cannot be '+' or '*' expressions; found ~M",
        [v],
      )
      |> ignore
    }
  }
  let mut eql = nreverse(mapcar(e => meqhk(e), cdr(eql0)))
  let varl = reverse(cdr(varl0))
  let mut ans = Value::Nil
  while eql.truthy() {
    let a = car(eql)
    eql = cdr(eql)
    let mut row = Value::Nil
    if ind.truthy() {
      row = cons(const1(a, varl), row)
    }
    let mut b = varl
    while true {
      let elem = ratcoef(a, car(b))
      row = cons(
        if symval(q_d_ratmx).truthy() {
          elem
        } else {
          ratdisrep(elem)
        },
        row,
      )
      b = cdr(b)
      if b is Nil {
        break
      }
    }
    ans = cons(row, ans)
  }
  cons(list1(q_d_matrix), mxc(ans))
}

///|
fn const1(e0 : Value, varl : Value) -> Value raise {
  let mut e = e0
  for v in varl.iter() {
    e = maxima_substitute(Fix(0L), v, e)
  }
  e
}

///|
fn d_entermatrix(rows : Value, columns : Value) -> Value raise {
  if !fixnump(rows) || !fixnump(columns) {
    merr("entermatrix: arguments must be integers; found ~M, ~M", [
      rows, columns,
    ])
    |> ignore
  }
  let mut row : Value = Fix(0L)
  let mut column : Value = Fix(0L)
  let mut vector = Value::Nil
  let mut matrix = Value::Nil
  let mut sym_ = Value::Nil
  let mut symvector = Value::Nil
  let prompt_for = fn(row : Value, column : Value) -> Value raise {
    format(Nil, "Row ~a Column ~a: ", [row, column])
  }
  // States: 0 quest, 1 oloop, 2 iloop
  let mut state = if !num_eq(rows, columns) {
    sym_ = Nil
    1
  } else {
    0
  }
  while true {
    match state {
      0 => {
        format(
          t,
          "~%Is the matrix  1. Diagonal  2. Symmetric  3. Antisymmetric  4. General~%",
          [],
        )
        |> ignore
        sym_ = retrieve(Str("Answer 1, 2, 3 or 4 : "), Nil)
        if member(sym_, list([Fix(1L), Fix(2L), Fix(3L), Fix(4L)])).truthy() {
          state = 1
        }
      }
      1 => {
        row = one_plus(row)
        if num_gt(row, rows) {
          format(t, "~%Matrix entered.~%", []) |> ignore
          return cons(list1(q_d_matrix), mxc(matrix))
        }
        if equal(sym_, Fix(1L)) {
          column = row
          let prompt = prompt_for(row, column)
          matrix = nconc(
            matrix,
            ncons(onen(row, columns, meval(retrieve(prompt, Nil)), Fix(0L))),
          )
          // stay in oloop
        } else if equal(sym_, Fix(2L)) {
          column = one_minus(row)
          if !equal(row, Fix(1L)) {
            symvector = cons(nthcdr(to_int(column), vector), symvector)
            vector = nreverse(mapcar(x => car(x), symvector))
            symvector = mapcar(x => cdr(x), symvector)
          }
          state = 2
        } else if equal(sym_, Fix(3L)) {
          column = row
          if equal(row, Fix(1L)) {
            vector = ncons(Fix(0L))
          } else {
            symvector = cons(
              mapcar(x => neg(x), nthcdr(to_int(one_minus(column)), vector)),
              symvector,
            )
            vector = nreconc(mapcar(x => car(x), symvector), ncons(Fix(0L)))
            symvector = mapcar(x => cdr(x), symvector)
          }
          state = 2
        } else {
          column = Fix(0L)
          vector = Nil
          state = 2
        }
      }
      _ => {
        column = one_plus(column)
        if num_gt(column, columns) {
          matrix = nconc(matrix, ncons(vector))
          state = 1
        } else {
          let prompt = prompt_for(row, column)
          vector = nconc(vector, ncons(meval(retrieve(prompt, Nil))))
        }
      }
    }
  }
  Nil
}

// ---------------------------------------------------------------------------
// $xthru

///|
fn d_xthru(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if mtimesp(e).truthy() {
    muln(mapcar(x => d_xthru(x), cdr(e)), Nil)
  } else if mplusp(e).truthy() {
    simplify(comdenom(mapcar(x => d_xthru(x), cdr(e)), t))
  } else if mexptp(e).truthy() {
    power(d_xthru(cadr(e)), caddr(e))
  } else if mbagp(e).truthy() {
    cons(car(e), mapcar(x => d_xthru(x), cdr(e)))
  } else {
    e
  }
}

///|
fn comdenom(l0 : Value, ind : Value) -> Value raise {
  let mut l = l0
  prodnumden(car(l)) |> ignore
  let mut n = m_starl(symval(q_sn_star))
  set(q_sn_star, Nil) |> ignore
  let mut d = m_starl(symval(q_sd_star))
  set(q_sd_star, Nil) |> ignore
  while true {
    l = cdr(l)
    if l is Nil {
      return if ind.truthy() {
        div_star(
          if symval(q_rsn_star).truthy() {
            d_ratsimp(n, Nil)
          } else {
            n
          },
          d,
        )
      } else {
        list2(n, d)
      }
    }
    prodnumden(car(l)) |> ignore
    let nd = comdenom1(n, d, m_starl(symval(q_sn_star)), m_starl(symval(q_sd_star)))
    n = car(nd)
    d = cadr(nd)
  }
  Nil
}

///|
fn prodnumden(e : Value) -> Value raise {
  if atom(e) {
    prodnd(list1(e))
  } else if eq(caar(e), q_mtimes) {
    prodnd(cdr(e))
  } else {
    prodnd(list1(e))
  }
}

///|
fn prodnd(l0 : Value) -> Value raise {
  let l = reverse(l0)
  set(q_sn_star, Nil) |> ignore
  set(q_sd_star, Nil) |> ignore
  for e in l.iter() {
    if atom(e) {
      push_special(e, q_sn_star) |> ignore
    } else if ratnump(e).truthy() {
      if !equal(Fix(1L), cadr(e)) {
        push_special(cadr(e), q_sn_star) |> ignore
      }
      push_special(caddr(e), q_sd_star) |> ignore
    } else if eq(caar(e), q_mexpt) && mnegp(caddr(e)).truthy() {
      push_special(power(cadr(e), timesk(Fix(-1L), caddr(e))), q_sd_star)
      |> ignore
    } else {
      push_special(e, q_sn_star) |> ignore
    }
  }
  Nil
}

///|
fn comdenom1(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  prodnumden(div_star(b, d)) |> ignore
  let b1 = m_starl(symval(q_sn_star))
  set(q_sn_star, Nil) |> ignore
  let c1 = m_starl(symval(q_sd_star))
  set(q_sd_star, Nil) |> ignore
  list2(add2(m_star(list2(a, c1)), m_star(list2(c, b1))), mul2(d, b1))
}

// ---------------------------------------------------------------------------
// XRUTOUT

///|
fn csimp2__aref(ax : Value, i : Value, j : Value) -> Value raise {
  aref(ax, [to_int(i), to_int(j)])
}

///|
fn csimp2__aset(ax : Value, i : Value, j : Value, v : Value) -> Unit raise {
  aset(ax, [to_int(i), to_int(j)], v) |> ignore
}

///|
fn xrutout(
  ax0 : Value,
  n : Value,
  m : Value,
  varl : Value,
  ind : Value,
) -> Value raise {
  let lp = if symval(q_d_backsubst).truthy() {
    symval(q_d_linsolve_params)
  } else {
    Nil
  }
  // AX is special.
  with_specials([(q_ax, ax0), (q_d_linsolve_params, lp)], () => {
    set(q_ax, get_array_pointer(symval(q_ax))) |> ignore
    let ax = symval(q_ax)
    let mut tim : Value = Fix(0L)
    if symval(q_d_linsolve_params).truthy() {
      set(q_d__pctrnum_list, list1(list1(q_mlist))) |> ignore
    }
    let m_1 = one_minus(m)
    let imin = num_min(m_1, n)
    let mut ix = num_max(imin, int(length(varl)))
    let mut zz = Value::Nil
    // loop
    while true {
      if zerop(ix) {
        if ind.truthy() {
          break
        } else {
          return cons(list1(q_mlist), zz)
        }
      }
      let mut goto_saval = true
      if num_gt(ix, imin) || equal(car(csimp2__aref(ax, ix, ix)), Fix(0L)) {
        csimp2__aset(
          ax,
          Fix(0L),
          ix,
          rform(
            if symval(q_d_linsolve_params).truthy() {
              make_param()
            } else {
              ith(varl, ix)
            },
          ),
        )
        goto_saval = symval(q_d_linsolve_params).truthy()
      } else {
        let mut ans = csimp2__aref(ax, ix, m)
        csimp2__aset(ax, ix, m, Nil)
        let mut j = one_plus(ix)
        while !num_gt(j, m_1) {
          ans = ratdif(
            ans,
            rattimes(csimp2__aref(ax, ix, j), csimp2__aref(ax, Fix(0L), j), t),
          )
          csimp2__aset(ax, ix, j, Nil)
          j = one_plus(j)
        }
        csimp2__aset(
          ax,
          Fix(0L),
          ix,
          ratquotient(ans, csimp2__aref(ax, ix, ix)),
        )
        csimp2__aset(ax, ix, ix, Nil)
      }
      if goto_saval {
        // saval
        zz = cons(
          if symval(q_n_starmosesflag).truthy() {
            csimp2__aref(ax, Fix(0L), ix)
          } else {
            list([
              list1(
                if symval(q_d_globalsolve).truthy() {
                  q_msetq
                } else {
                  q_mequal
                },
              ),
              ith(varl, ix),
              simplify(rdis(csimp2__aref(ax, Fix(0L), ix))),
            ])
          },
          zz,
        )
        if !symval(q_d_backsubst).truthy() {
          csimp2__aset(ax, Fix(0L), ix, rform(ith(varl, ix)))
        }
        if symval(q_d_globalsolve).truthy() {
          meval(car(zz)) |> ignore
        }
      }
      // next
      ix = one_minus(ix)
    }
    // out
    if symval(q_d_dispflag).truthy() {
      mtell(list1(Str("Solution:~%"))) |> ignore
    }
    let sol = list1(list1(q_mlist))
    let mut chk = checklabel(symval(q_d_linechar)).truthy()
    for zzz0 in zz.iter() {
      if chk {
        chk = false
      } else {
        set(q_d_linenum, one_plus(symval(q_d_linenum))) |> ignore
      }
      with_special(q_d_nolabels, Nil, () => makelabel(symval(q_d_linechar)))
      |> ignore
      let label = symval(q_ear_linelabel)
      set(label, zzz0) |> ignore
      let zzz = list([list1(q_mlabel), label, zzz0])
      nconc(sol, ncons(symval(q_ear_linelabel))) |> ignore
      if symval(q_d_dispflag).truthy() {
        tim = int64((cpu_time() * 1000000.0).to_int64())
        mtell_open(Str("~%~M"), list1(zzz)) |> ignore
        timeorg(tim) |> ignore
      } else {
        putprop(symval(q_ear_linelabel), t, q_nodisp) |> ignore
      }
    }
    sol
  })
}

///|
fn init_csimp2() -> Unit raise {
  // Binomial has Mirror symmetry
  putprop(q_p_binomial, t, q_commutes_with_conjugate) |> ignore
  // gradient of binomial
  putprop(
    q_p_binomial,
    lread(
      "((a b) ((mtimes) -1 ((%binomial) a b) ((mplus) ((mtimes) -1 ((mqapply) (($psi array) 0) ((mplus) 1 a))) ((mqapply) (($psi array) 0) ((mplus) 1 a ((mtimes) -1 b))))) ((mtimes) -1 ((%binomial) a b) ((mplus) ((mtimes) -1 ((mqapply) (($psi array) 0) ((mplus) 1 a ((mtimes) -1 b)))) ((mqapply) (($psi array) 0) ((mplus) 1 b)))))",
    ),
    q_grad,
  )
  |> ignore
  // The Beta function has mirror symmetry
  putprop(q_p_beta, t, q_commutes_with_conjugate) |> ignore
  // Derivative of beta function
  push_special(q_p_beta, q_ear_defgrad_syms) |> ignore
  putprop(
    q_p_beta,
    list([
      list2(q_d_a, q_d_b),
      // derivative wrt a
      maxima_lit("-(beta(a,b)*(psi[0](b+a)-psi[0](a)))"),
      // derivative wrt b
      maxima_lit("-(beta(a,b)*(psi[0](b+a)-psi[0](b)))"),
    ]),
    q_grad,
  )
  |> ignore
  putprop(q_p_gamma, q_gamma_sign, q_sign_function) |> ignore
}
