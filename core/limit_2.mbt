// Port of src/limit.lisp, part 2: LIMIT2, factorial/gamma handling,
// SIMPLIMSUBST, NUMDEN*, RATLIM, BEHAVIOR and l'Hospital's rule.

///|
fn limit2(n : Value, dn : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let mut n = hyperex(n)
  let mut dn = hyperex(dn)
  let mut d1 = limit(dn, var_, val, Nil)
  let mut n1 = limit(n, var_, val, Nil)
  let mut lim_sign : Value = Nil
  let mut cinf = false
  if n1 is Nil || d1 is Nil {
    return Nil
  } else {
    n1 = sratsimp(n1)
    d1 = sratsimp(d1)
  }
  if involve(n, list1(q_mfactorial)).truthy() ||
    involve(dn, list1(q_mfactorial)).truthy() {
    let ans = limfact2(n, dn, var_, val)
    if ans.truthy() {
      return ans
    }
  }
  if zerop2(n1).truthy() && zerop2(d1).truthy() {
    let gcp = gcpower(n, dn)
    if !equal(gcp, Fix(1L)) {
      return colexpt(n, dn, gcp)
    } else if real_epsilonp(limit__val()).truthy() &&
      !free(n, q_p_log).truthy() &&
      !free(dn, q_p_log).truthy() {
      return liminv(div_star(n, dn))
    } else {
      n1 = try_lhospital_quit(n, dn, Nil)
      if n1.truthy() {
        return n1
      }
    }
  } else if eq(n1, q_d_ind) && eq(d1, q_d_ind) {
    // when dn # 0, we have ind/ind = ind, otherwise ind/ind = und
    return if eq(t, mnqp(dn, Fix(0L))) { q_d_ind } else { q_d_und }
  } else if zerop2(n1).truthy() && !limit__memq(d1, [q_d_ind, q_d_und]) {
    return Fix(0L)
  } else if zerop2(d1).truthy() {
    n1 = ridofab(n1)
    return simplimtimes(list([n1, simplimexpt(dn, Fix(-1L), d1, Fix(-1L))]))
  }
  n1 = ridofab(n1)
  d1 = ridofab(d1)
  if eq(d1, q_d_und) ||
    (eq(n1, q_d_und) && !real_infinityp(d1).truthy()) {
    return q_d_und
  } else if eq(d1, q_d_ind) {
    // At this point we have n1/$ind. Look if n1 is one of the infinities or
    // zero.
    if infinityp(n1).truthy() && eq(d_sign(dn), q_d_pos) {
      return n1
    } else if infinityp(n1).truthy() && eq(d_sign(dn), q_d_neg) {
      return simpinf(mul2_star(Fix(-1L), n1))
    } else if zerop1(n1).truthy() &&
      (eq(d_sign(dn), q_d_pos) || eq(d_sign(dn), q_d_neg)) {
      return Fix(0L)
    } else {
      return q_d_und
    }
  } else if eq(n1, q_d_ind) {
    return if infinityp(d1).truthy() {
      Fix(0L)
    } else if equal(d1, Fix(0L)) {
      q_d_und
    } else {
      q_d_ind
    }
  } else if real_infinityp(d1).truthy() &&
    limit__memq(n1, [q_d_inf, q_d_und, q_d_minf]) {
    if !atom(dn) && !atom(n) {
      let gcp = gcpower(n, dn)
      if !equal(gcp, Fix(1L)) {
        return colexpt(n, dn, gcp)
      } else if eq(q_d_inf, limit__val()) &&
        (
          involve(
            dn,
            list([q_mfactorial, q_p_gamma, q_p_expintegral_ei]),
          ).truthy() ||
          involve(n, list([q_mfactorial, q_p_gamma, q_p_expintegral_ei])).truthy()
        ) {
        return limfact(n, dn)
      }
    }
    if eq(n1, d1) {
      lim_sign = Fix(1L)
    } else {
      lim_sign = Fix(-1L)
    }
  } else if infinityp(d1).truthy() && infinityp(n1).truthy() {
    // One of the two is infinity, which has no sign.
    lim_sign = if eq(d1, q_d_minf) || eq(n1, q_d_minf) {
      Fix(-1L)
    } else {
      Fix(1L)
    }
    cinf = true
  } else {
    return simplimtimes(list([n1, power_star(d1, Fix(-1L))]))
  }
  // cp
  n = d_expand(n)
  dn = d_expand(dn)
  if mplusp(n).truthy() {
    let new_n = addn(maxi(cdr(n)), Nil)
    if !alike1(new_n, n).truthy() {
      return limit(div_star(new_n, dn), limit__var(), limit__val(), q_think)
    }
    n1 = new_n
  } else {
    n1 = n
  }
  if mplusp(dn).truthy() {
    let new_dn = addn(maxi(cdr(dn)), Nil)
    if !alike1(new_dn, dn).truthy() {
      return limit(div_star(n, new_dn), limit__var(), limit__val(), q_think)
    }
    d1 = new_dn
  } else {
    d1 = dn
  }
  let sheur_ans = sheur0(n1, d1)
  if cinf && limit__memq(sheur_ans, [q_d_inf, q_d_zeroa]) {
    // Growth rates give only the modulus of a complex quotient.
    return if eq(sheur_ans, q_d_inf) { q_d_infinity } else { Fix(0L) }
  } else if limit__memq(sheur_ans, [q_d_inf, q_d_zeroa]) ||
    free(sheur_ans, limit__var()).truthy() {
    return simplimtimes(list([lim_sign, sheur_ans]))
  } else if alike1(sheur_ans, dn).truthy() && !mplusp(n).truthy() {
    ()
  } else {
    n1 = if expfactorp(n1, d1).truthy() {
      expfactor(n1, d1, limit__var())
    } else {
      Nil
    }
    if limit__memq(n1, [q_d_inf, q_d_zeroa]) {
      return n1
    }
    n1 = if expfactorp(n, dn).truthy() {
      expfactor(n, dn, limit__var())
    } else {
      Nil
    }
    if n1.truthy() {
      return n1
    } else if alike1(sheur_ans, dn).truthy() && !mplusp(n).truthy() {
      ()
    } else if !alike1(sheur_ans, div_star(n, dn)).truthy() {
      return simplimit(
        div_star(
          d_expand(div_star(n, sheur_ans)),
          d_expand(div_star(dn, sheur_ans)),
        ),
        limit__var(),
        limit__val(),
      )
    }
  }
  if !(
      eq(limit__val(), q_d_inf) &&
      expp(n).truthy() &&
      expp(dn).truthy()
    ) {
    n1 = try_lhospital_quit(n, dn, Nil)
    if n1.truthy() && !amongl(list([q_d_und, q_d_ind]), n1).truthy() {
      return n1
    }
  }
  throw_tag(q_limit, t)
}

///|
/// Test whether both n and dn have form product of poly^poly. Both n and dn
/// must be free of extended real numbers (see bug #4222).
fn expfactorp(n : Value, dn : Value) -> Value raise {
  let mut llist = append(
    if mtimesp(n).truthy() { cdr(n) } else { ncons(n) },
    if mtimesp(dn).truthy() { cdr(dn) } else { ncons(dn) },
  )
  let mut exp_q = t // IS EVERY ELEMENT SO FAR A POLY^POLY?
  while !(llist is Nil || exp_q is Nil) {
    let factor = car(llist)
    exp_q = if amongl(
        list([
          q_d_minf, q_d_zerob, q_d_zeroa, q_d_ind, q_d_und, q_d_inf, q_d_infinity,
        ]),
        factor,
      ).truthy() {
      Nil
    } else {
      let p = polyinx(factor, limit__var(), Nil)
      if p.truthy() {
        p
      } else if mexptp(factor).truthy() &&
        polyinx(cadr(factor), limit__var(), Nil).truthy() {
        polyinx(caddr(factor), limit__var(), Nil)
      } else {
        Nil
      }
    }
    llist = cdr(llist)
  }
  exp_q
}

///|
/// Attempts to evaluate limit by grouping terms with similar exponents.
fn expfactor(n : Value, dn : Value, var_ : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  // exppoly unrats expon and rtns deg of expons
  let new_exp = exppoly(n)
  let n = car(new_exp)
  let mut highest_deg = cdr(new_exp)
  if n is Nil {
    // nil means expon is not a rat func.
    return Nil
  }
  let new_exp = exppoly(dn)
  let dn = car(new_exp)
  highest_deg = num_max(highest_deg, cdr(new_exp))
  if dn is Nil || num_eq(highest_deg, Fix(0L)) {
    // prevent infinite recursion
    return Nil
  }
  let mut answer : Value = Fix(1L)
  let mut degree = highest_deg
  let mut numerator = n
  let mut denominator = dn
  let mut numfactors : Value = Nil
  let mut denfactors : Value = Nil
  while !num_eq(degree, Fix(-1L)) {
    let newnumer_factor = get_newexp_ampfactors(numerator, degree, var_)
    numerator = car(newnumer_factor)
    numfactors = cdr(newnumer_factor)
    let newdenom_factor = get_newexp_ampfactors(denominator, degree, var_)
    denominator = car(newdenom_factor)
    denfactors = cdr(newdenom_factor)
    answer = simplimit(
      mk(q_mexpt, [
        mul2_star(answer, div_star(numfactors, denfactors)),
        if num_gt(degree, Fix(0L)) {
          var_
        } else {
          Fix(1L)
        },
      ]),
      var_,
      limit__val(),
    )
    if member_equal(answer, list([q_d_ind, q_d_und])).truthy() {
      // cannot handle limit(exp(x*%i)*x, x, inf);
      return Nil
    } else if member_equal(answer, list([q_d_inf, q_d_minf])).truthy() {
      // 0, zeroa, zerob are passed through to next iteration
      return simplimtimes(list([div_star(numerator, denominator), answer]))
    }
    degree = one_minus(degree)
  }
  mul2_star(
    answer,
    limit(div_star(numerator, denominator), var_, limit__val(), q_think),
  )
}

///|
/// RETURNS EXPRESSION WITH UNRATTED EXPONENTS
fn exppoly(exp_ : Value) -> Value raise {
  let mut highest_deg : Value = Fix(0L)
  let mut new_exp : Value = Fix(1L)
  let b = bind(q_exp, if mtimesp(exp_).truthy() { cdr(exp_) } else { ncons(exp_) })
  defer unbind(b)
  while limit__exp().truthy() {
    let factor = car(limit__exp())
    let f = if !mexptp(factor).truthy() ||
      !ratp(caddr(factor), limit__var()).truthy() {
      factor
    } else {
      highest_deg = num_max(highest_deg, ratdegree(caddr(factor)))
      power_star(cadr(factor), unrat(caddr(factor)))
    }
    new_exp = mul2_star(f, new_exp)
    set(q_exp, cdr(limit__exp())) |> ignore
  }
  cons(new_exp, highest_deg)
}

///|
/// RETURNS UNRATTED EXPRESSION
fn unrat(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  let (n, d) = numden_star(exp_)
  let tem = d_divide(n, d, Nil)
  add2_star(cadr(tem), div_star(caddr(tem), d))
}

///|
/// RETURNS (CONS NEWEXP FACTORS) SUCH THAT NEWEXP*FACTORS^(VAR^DEGREE) IS
/// EQUAL TO EXP.
fn get_newexp_ampfactors(
  exp_ : Value,
  degree : Value,
  var_ : Value,
) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_)])
  defer unbind_all(bs)
  let mut terms = if mtimesp(exp_).truthy() { cdr(exp_) } else { ncons(exp_) }
  let mut factors : Value = Fix(1L)
  let mut newexp : Value = Fix(1L)
  while terms.truthy() {
    let factor = car(terms)
    if !mexptp(factor).truthy() {
      if num_eq(degree, Fix(0L)) {
        factors = mul2_star(factor, factors)
      } else {
        newexp = mul2_star(factor, newexp)
      }
    } else if num_eq(degree, Fix(-1L)) ||
      num_eq(ratdegree(caddr(factor)), degree) {
      factors = mul2_star(
        power_star(cadr(factor), leading_coef(caddr(factor))),
        factors,
      )
      newexp = mul2_star(
        power_star(
          cadr(factor),
          sub_star(
            caddr(factor),
            mul2_star(leading_coef(caddr(factor)), power_star(var_, degree)),
          ),
        ),
        newexp,
      )
    } else {
      newexp = mul2_star(factor, newexp)
    }
    terms = cdr(terms)
  }
  cons(newexp, factors)
}

///|
fn leading_coef(rat : Value) -> Value raise {
  ratlim(div_star(rat, power_star(limit__var(), ratdegree(rat))))
}

///|
fn ratdegree(rat : Value) -> Value raise {
  let (n, d) = numden_star(rat)
  num_sub(deg(n), deg(d))
}

///|
fn limfact2(n : Value, d : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let n1 = reflect0(n, var_, val)
  let d1 = reflect0(d, var_, val)
  if alike1(n, n1).truthy() && alike1(d, d1).truthy() {
    Nil
  } else {
    limit(div_star(n1, d1), var_, val, q_think)
  }
}

///|
/// takes expression and returns operator at front with all flags removed
/// except array flag. array flag must match for alike1 to consider two things
/// to be the same.
///   ((MTIMES SIMP) ... ) => (MTIMES)
///   ((PSI SIMP ARRAY) 0) => (PSI ARRAY)
fn operator_with_array_flag(exp_ : Value) -> Value raise {
  if member(q_array, car(exp_)).truthy() {
    list2(caar(exp_), q_array)
  } else {
    list1(caar(exp_))
  }
}

///|
fn reflect0(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  if atom(exp_) {
    exp_
  } else if eq(caar(exp_), q_mfactorial) &&
    {
      let argval = limit(cadr(exp_), var_, val, q_think)
      eq(argval, q_d_minf) ||
      (numberp(argval) && num_gt(Fix(0L), argval))
    } {
    reflect(cadr(exp_))
  } else {
    cons(
      operator_with_array_flag(exp_),
      mapcar(term => reflect0(term, var_, val), cdr(exp_)),
    )
  }
}

///|
fn reflect(arg : Value) -> Value raise {
  muln_star([
    Fix(-1L),
    q_d__pctpi,
    power_star(
      list2(ncons(q_mfactorial), add2_star(Fix(-1L), mul2_star(Fix(-1L), arg))),
      Fix(-1L),
    ),
    power_star(list2(ncons(q_p_sin), mul2_star(q_d__pctpi, arg)), Fix(-1L)),
  ])
}

///|
fn limfact(n : Value, d : Value) -> Value raise {
  let ans = toplevel__dollimit(
    list([div(stirling0(n), stirling0(d)), limit__var(), limit__val()]),
  )
  if successful_limit_result_p(ans).truthy() {
    ans
  } else {
    Nil
  }
}

///|
/// substitute asymptotic approximations for gamma, factorial,
/// polylogarithm, and expintegral_ei
fn stirling0(e : Value) -> Value raise {
  if atom(e) {
    return e
  }
  let e = cons(car(e), mapcar(x => stirling0(x), cdr(e)))
  let op = caar(e)
  if eq(op, q_p_gamma) {
    let ans = limit(cadr(e), limit__var(), limit__val(), q_think)
    if limit__memq(ans, [q_d_inf, q_d_minf, q_d_infinity]) {
      stirling(cadr(e))
    } else if eq(ans, q_d_zeroa) {
      add2(div(Fix(1L), cadr(e)), mul2(Fix(-1L), q_d__pctgamma))
    } else if integerp(ans) && num_lt(ans, Fix(0L)) {
      div(
        if oddp(ans) {
          Fix(-1L)
        } else {
          Fix(1L)
        },
        mul2(ftake(q_mfactorial, [mul2(Fix(-1L), ans)]), sub(cadr(e), ans)),
      )
    } else {
      ftake(q_p_gamma, [cadr(e)])
    }
  } else if eq(op, q_mfactorial) {
    let mut n = limit(cadr(e), limit__var(), limit__val(), q_think)
    if eq(n, q_d_inf) {
      stirling(add2(Fix(1L), cadr(e)))
    } else if integerp(n) && num_lt(n, Fix(0L)) {
      n = mul2(Fix(-1L), n)
      div(
        if oddp(n) {
          Fix(1L)
        } else {
          Fix(-1L)
        },
        mul2(ftake(q_mfactorial, [sub(n, Fix(1L))]), add2(cadr(e), n)),
      )
    } else {
      e
    }
  } else if eq(op, q_mqapply) &&
    eq(subfunname(e), q_d_li) &&
    {
      let arglim = limit(car(subfunargs(e)), limit__var(), limit__val(), q_think)
      eq(arglim, q_d_inf) || eq(arglim, q_d_minf)
    } &&
    integerp(car(subfunsubs(e))) {
    // polylogarithm
    li_asymptotic_expansion(
      sub_star(car(subfunsubs(e)), Fix(1L)),
      car(subfunsubs(e)),
      car(subfunargs(e)),
    )
  } else if eq(op, q_p_expintegral_ei) {
    let arglim = limit(cadr(e), limit__var(), limit__val(), q_think)
    if eq(arglim, q_d_inf) {
      ei_asymptotic_expansion(symval(q_d_lhospitallim), cadr(e))
    } else if zerop2(arglim).truthy() {
      ei_powerseries(symval(q_d_lhospitallim), cadr(e))
    } else {
      e
    }
  } else if eq(op, q_p_gamma_u_incomplete) {
    gamma_incomplete_asymptotic(
      e,
      limit__var(),
      limit__val(),
      symval(q_d_lhospitallim),
    )
  } else {
    e
  }
}

///|
/// See http://dlmf.nist.gov/8.11.i
fn gamma_incomplete_asymptotic(
  e : Value,
  x : Value,
  pt : Value,
  n : Value,
) -> Value raise {
  let aaa = second(e)
  let z = third(e)
  let xxx = limit(z, x, pt, q_think)
  if (eq(q_d_inf, xxx) || eq(q_d_minf, xxx)) && freeof(x, aaa).truthy() {
    // Case 1: Asymptotic expansion when z -> +/- inf and aaa is free of x.
    // For the series, see http://dlmf.nist.gov/8.11.i
    let mut f : Value = Fix(1L)
    let mut s : Value = Fix(0L)
    let cnt = to_int(n)
    for k in 0..<cnt {
      s = add2(s, f)
      f = mul2(f, div(addn_([aaa, Fix(-1L), Fix(-k.to_int64())]), z))
    }
    // return z^(a-1)*exp(-z)*s
    muln_([
      ftake(q_mexpt, [z, sub(aaa, Fix(1L))]),
      ftake(q_mexpt, [q_d__pcte, mul2(Fix(-1L), z)]),
      s,
    ])
  } else if zerop2(xxx).truthy() && integerp(aaa) && num_ge(Fix(0L), aaa) {
    // Case 2: Asymptotic expansion when z -> 0, aaa integer, and aaa <= 0.
    // For the series, see http://dlmf.nist.gov/8.4.E15
    let mut s : Value = Fix(0L)
    fn fn_(k : Value) -> Value raise {
      if eql(add2(k, aaa), Fix(0L)) {
        Fix(0L)
      } else {
        div(power(neg(z), k), mul2(ftake(q_mfactorial, [k]), add2(k, aaa)))
      }
    }

    let cnt = to_int(n)
    for k in 0..<cnt {
      s = add2(s, fn_(Fix(k.to_int64())))
    }
    sub(
      mul2(
        div(
          ftake(q_mexpt, [Fix(-1L), neg(aaa)]),
          ftake(q_mfactorial, [neg(aaa)]),
        ),
        sub(
          simplifya(
            subfunmake(q_d_psi, list1(Fix(0L)), list1(add2(neg(aaa), Fix(1L)))),
            Nil,
          ),
          ftake(q_p_log, [z]),
        ),
      ),
      mul2(ftake(q_mexpt, [z, aaa]), s),
    )
  } else {
    // Case 3: fall back
    ftake(q_p_gamma_u_incomplete, [aaa, z])
  }
}

///|
/// Return sqrt(2*%pi/x)*(x/%e)^x, the Stirling approximation of gamma(x).
/// The argument x can be any valid expression.
fn stirling(x : Value) -> Value raise {
  mul2(
    power(div(mul2(Fix(2L), q_d__pctpi), x), symval(q_n1_sl_sl2)),
    power(div(x, q_d__pcte), x),
  )
}

///|
/// The macro IGNORE-RAT-ERR: the value of `f`, or NIL after a throw to
/// RAT-ERR.
fn limit__ignore_rat_err(f : () -> Value raise) -> Value raise {
  let mut result : Value = Nil
  let mut error_p = true
  catch_tag(q_rat_err, () => {
    result = f()
    error_p = false
    Nil
  })
  |> ignore
  if error_p {
    Nil
  } else {
    result
  }
}

///|
/// Shared body of NO-ERR-SUB and NO-ERR-SUB-VAR.
fn limit__no_err(f : () -> Value raise) -> Value raise {
  let bs = bind_all([
    (q_errorsw, t),
    (q_n_starzexptsimp_q, t),
    (q_errcatch, t),
    // Don't print any error messages
    (q_d_errormsg, Nil),
  ])
  defer unbind_all(bs)
  let ans = catch_tag(q_errorsw, () => limit__ignore_rat_err(f)) catch {
    e => if is_maxima_error(e) { Nil } else { raise e }
  }
  if ans is Nil {
    // Ratfun package returns NIL for failure.
    t
  } else {
    ans
  }
}

///|
fn no_err_sub(v : Value, e : Value) -> Value raise {
  limit__no_err(() => sratsimp(subin(v, e)))
}

///|
/// Like NO-ERR-SUB but dependency on VAR is explicit. Use this instead when
/// possible.
fn no_err_sub_var(v : Value, e : Value, var1 : Value) -> Value raise {
  limit__no_err(() => sratsimp(subin_var(v, e, var1)))
}

///|
fn simplim_pctmabs(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if eq(lim, q_d_zeroa) || eql(lim, Fix(0L)) || eq(lim, q_d_ind) {
    lim
  } else if eq(lim, q_d_zerob) {
    q_d_zeroa
  } else if eq(lim, q_d_und) {
    q_d_und
  } else if eq(lim, q_d_minf) || eq(lim, q_d_inf) || eq(lim, q_d_infinity) {
    q_d_inf
  } else {
    ftake(q_mabs, [lim])
  }
}

///|
fn extended_real_p(e : Value) -> Value raise {
  member(
    e,
    list([q_d_minf, q_d_zerob, q_d_zeroa, q_d_ind, q_d_und, q_d_inf, q_d_infinity]),
  )
}

///|
/// Evaluate the limit of e as var (special) approaches v using direct
/// substitution. This function is the last of the chain of methods tried by
/// limit, so it doesn't call higher level functions such as simplimit or
/// limit. It special cases sums, products, and powers, and declines direct
/// substitution on expressions whose main operator has a simplim%function.
/// Locally setting $numer and $%enumer to nil keeps some limits, for example
/// limit(sin(x)/x,x,0), from returning 1.0 when numer is true.
fn simplimsubst(v : Value, e : Value) -> Value raise {
  let bs = bind_all([(q_d_numer, Nil), (q_d__pctenumer, Nil)])
  defer unbind_all(bs)
  if d_numberp(e).truthy() {
    // When e is a number, return it.
    e
  } else if d_mapatom(e).truthy() {
    // When e is a mapatom, substitute v for var and return.
    d_substitute(v, limit__var(), expr=e)
  } else if mexptp(e).truthy() && !extended_real_p(v).truthy() {
    // Special case mexpt expressions. Decline direct substitution for
    // extended reals, for 0^negative, and when x is on the negative real
    // axis and n isn't an integer.
    let x = simplimsubst(v, second(e))
    let n = simplimsubst(v, third(e))
    if x.truthy() &&
      n.truthy() &&
      !(zerop2(x).truthy() && eq(t, mgqp(Fix(0L), n))) &&
      (off_negative_real_axisp(x).truthy() || integerp(n)) {
      ftake(q_mexpt, [x, n])
    } else {
      Nil
    }
  } else if (mplusp(e).truthy() || mtimesp(e).truthy()) &&
    !extended_real_p(v).truthy() {
    // Special case product and sum expressions.
    let ee = mapcar(q => simplimsubst(v, q), cdr(e))
    if some(q => q is Nil, ee) {
      Nil
    } else {
      simplifya(cons(list1(caar(e)), ee), t)
    }
  } else if (mexptp(e).truthy() || mplusp(e).truthy() || mtimesp(e).truthy()) &&
    extended_real_p(v).truthy() {
    // Decline direct substitution for sums, products, and powers for the
    // extended real case.
    Nil
  } else if consp(e) && consp(car(e)) && eq(q_p_log, caar(e)) {
    // Special case log expressions.
    let w = simplimsubst(v, cadr(e))
    if w.truthy() && off_negative_real_axisp(w).truthy() {
      ftake(q_p_log, [w])
    } else {
      Nil
    }
  } else if consp(e) &&
    consp(car(e)) &&
    (eq(caar(e), q_p_cos) || eq(caar(e), q_p_sin)) {
    // Special case %cos and %sin expressions. The lenient-realp check
    // declines direct substitution for complex arguments.
    let op = caar(e)
    let e = simplimsubst(v, second(e))
    if e.truthy() && lenient_realp(e).truthy() && !extended_real_p(e).truthy() {
      ftake(op, [e])
    } else {
      Nil
    }
  } else if consp(e) && consp(car(e)) && get(caar(e), q_simplim_pctfunction).truthy() {
    // Don't use direct substitution on expressions whose main operator has a
    // simplim%function.
    Nil
  } else {
    // The function no-err-sub returns true when there is an error
    let mut ans = no_err_sub(ridofab(v), e)
    if !eq(t, ans) {
      if limit__memq(v, [q_d_zeroa, q_d_zerob]) && zerop2(ans).truthy() {
        ans = behavior(e, limit__var(), v)
        if eql(ans, Fix(1L)) {
          q_d_zeroa
        } else if eql(ans, Fix(-1L)) {
          q_d_zerob
        } else {
          Nil // behavior can't find direction
        }
      } else {
        ans
      }
    } else {
      // direct substitution fails, so return nil.
      Nil
    }
  }
}

///|
/// returns (values numerator denominator)
fn numden_star(e : Value) -> (Value, Value) raise {
  let e = factor(simplify(e))
  let bs = bind_all([(q_numer, Nil), (q_denom, Nil)])
  defer unbind_all(bs)
  if atom(e) {
    set(q_numer, cons(e, symval(q_numer))) |> ignore
  } else if mtimesp(e).truthy() {
    for f in cdr(e).iter() {
      forq(f) |> ignore
    }
  } else {
    forq(e) |> ignore
  }
  let numer = symval(q_numer)
  if numer is Nil {
    set(q_numer, Fix(1L)) |> ignore
  } else if cdr(numer) is Nil {
    set(q_numer, car(numer)) |> ignore
  } else {
    set(q_numer, muln(numer, Nil)) |> ignore
  }
  let denom = symval(q_denom)
  if denom is Nil {
    set(q_denom, Fix(1L)) |> ignore
  } else if cdr(denom) is Nil {
    set(q_denom, car(denom)) |> ignore
  } else {
    set(q_denom, muln(denom, Nil)) |> ignore
  }
  let n = factor(symval(q_numer))
  let d = factor(symval(q_denom))
  (n, d)
}

///|
/// FACTOR OR QUOTIENT. Setq's the special vars numer and denom from numden*
fn forq(e : Value) -> Value raise {
  if mexptp(e).truthy() &&
    !freeof(limit__var(), e).truthy() &&
    pos_neg_p(caddr(e)) is Nil {
    set(
      q_denom,
      cons(power_star(cadr(e), mul2_star(Fix(-1L), caddr(e))), symval(q_denom)),
    )
  } else {
    set(q_numer, cons(e, symval(q_numer)))
  }
}

///|
/// Predicate to tell whether an expression is pos,zero or neg as var -> val.
/// returns T if pos,zero. () if negative or don't know.
fn pos_neg_p(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  let ans = limit(exp_, limit__var(), limit__val(), q_think)
  if !limit__memq(ans, [q_d_und, q_d_ind, q_d_infinity]) &&
    equal(d_imagpart(ans), Fix(0L)) {
    let sign = getsignl(ans)
    if equal(sign, Fix(1L)) || equal(sign, Fix(0L)) {
      t
    } else {
      Nil
    }
  } else {
    q_unknown
  }
}

///|
fn expp(e : Value) -> Value raise {
  if radicalp(e, limit__var()).truthy() {
    Nil
  } else if limit__memq(caar(e), [
      q_p_log, q_p_sin, q_p_cos, q_p_tan, q_p_sinh, q_p_cosh, q_p_tanh, q_mfactorial,
      q_p_asin, q_p_acos, q_p_atan, q_p_asinh, q_p_acosh, q_p_atanh,
    ]) {
    Nil
  } else if simplexp(e).truthy() {
    t
  } else {
    for x in cdr(e).iter() {
      if expp(x).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
fn simplexp(e : Value) -> Value raise {
  if mexptp(e).truthy() &&
    radicalp(cadr(e), limit__var()).truthy() &&
    among(limit__var(), caddr(e)).truthy() {
    radicalp(caddr(e), limit__var())
  } else {
    Nil
  }
}

///|
fn gcpower(a : Value, b : Value) -> Value raise {
  d_gcd(getexp(a), getexp(b), Nil)
}

///|
fn getexp(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  if mexptp(exp_).truthy() &&
    free(caddr(exp_), limit__var()).truthy() &&
    eq(ask_integer(caddr(exp_), q_d_integer), q_d_yes) {
    caddr(exp_)
  } else if mtimesp(exp_).truthy() {
    getexplist(cdr(exp_))
  } else {
    Fix(1L)
  }
}

///|
fn getexplist(list_ : Value) -> Value raise {
  if cdr(list_) is Nil {
    getexp(car(list_))
  } else {
    d_gcd(getexp(car(list_)), getexplist(cdr(list_)), Nil)
  }
}

///|
/// limroot is deprecated and no longer available.
fn limroot(args : Value) -> Value raise {
  ignore(args)
  merr("limroot is deprecated and no longer available.", [])
}

///|
/// Return T iff e is semantically free of extended-real numbers.
fn freeof_extended_real(e : Value) -> Value raise {
  d_freeof(
    list([q_d_minf, q_d_zerob, q_d_zeroa, q_d_ind, q_d_und, q_d_inf, q_d_infinity, e]),
  )
}

///|
/// colexpt returns limit(n/dn, var, val). Assumptions:
///   (a) n  has the form a^P
///   (b) dn has the form b^Q
///   (c) gcp is a positive integer
/// It uses the identity
///     limit(a^P / b^Q, x, pt) = limit(a^(P/gcp) / b^(Q/gcp), x, pt)^gcp.
/// When the assumptions are unmet, or when Maxima is unsuccessful, colexpt
/// throws to 'limit. To avoid returning expressions such as ind^2, the code
/// checks that the result is either an extended real or does not involve
/// one.
fn colexpt(n : Value, dn : Value, gcp : Value) -> Value raise {
  if mexptp(n).truthy() &&
    mexptp(dn).truthy() &&
    integerp(gcp) &&
    num_gt(gcp, Fix(0L)) {
    let a = second(n)
    let p = div(third(n), gcp)
    let b = second(dn)
    let q = div(third(dn), gcp)
    let lim = limit(
      div(ftake(q_mexpt, [a, p]), ftake(q_mexpt, [b, q])),
      limit__var(),
      limit__val(),
      q_think,
    )
    let lim_hatgcp = if successful_limit_result_p(lim).truthy() {
      infsimp(ftake(q_mexpt, [lim, gcp]))
    } else {
      Nil
    }
    if lim_hatgcp.truthy() &&
      (
        extended_real_p(lim_hatgcp).truthy() ||
        freeof_extended_real(lim_hatgcp).truthy()
      ) {
      lim_hatgcp
    } else {
      throw_tag(q_limit, Nil)
    }
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
/// Assuming `substitute(pt, x, e)` vanishes, attempt to determine if the
/// zero is `zerob` or `zeroa`. If determination is possible, return `zeroa`
/// or `zerob`; otherwise, return 0.
fn zero_fixup(e : Value, x : Value, pt : Value) -> Value raise {
  let e = d_totaldisrep(d_taylor(e, list([x, pt, Fix(1L)])))
  let dir = behavior(e, x, pt)
  if eql(dir, Fix(-1L)) {
    q_d_zerob
  } else if eql(dir, Fix(1L)) {
    q_d_zeroa
  } else {
    Fix(0L)
  }
}

///|
/// When `e` is an explicit polynomial in `x` and `pt` is either `zerob`,
/// `zeroa` or 0, return limit(e,x,pt); otherwise, return nil. When the limit
/// vanishes, attempt to determine if the limit is `zerob` or `zeroa`.
fn limit_of_polynomial(e : Value, x : Value, pt : Value) -> Value raise {
  if (eq(pt, q_d_zeroa) || eq(pt, q_d_zerob) || eql(pt, Fix(0L))) &&
    d_polynomialp(
      e,
      ftake(q_mlist, [x]),
      coeffp=lfunc("limit-of-polynomial-coeffp", a => freeof(x, arg(a, 0))),
    ).truthy() {
    let ans = maxima_substitute(Fix(0L), x, e)
    if eql(Fix(0L), ans) {
      zero_fixup(e, x, pt)
    } else {
      ans
    }
  } else {
    Nil
  }
}

///|
fn ratlim(e : Value) -> Value raise {
  let mut e = sratsimp(d_trigreduce(e))
  let val = limit__val()
  let var_ = limit__var()
  if limit__memq(val, [q_d_inf, q_d_infinity]) {
    e = maxima_substitute(power(q_x, Fix(-1L)), var_, e)
  } else if eq(val, q_d_minf) {
    e = maxima_substitute(
      mul2_star(Fix(-1L), power(q_x, Fix(-1L))),
      var_,
      e,
    )
  } else if eq(val, q_d_zerob) {
    e = maxima_substitute(mul2_star(Fix(-1L), q_x), var_, e)
  } else if eq(val, q_d_zeroa) {
    e = maxima_substitute(q_x, var_, e)
  } else {
    e = maxima_substitute(add2(q_x, val), var_, e)
  }
  e = with_special(q_d_ratfac, Nil, () => d_rat(sratsimp(e), list1(q_x)))
  let h = car(e)
  let mut n = cadr(e)
  let d = cddr(e)
  let g = genfind(h, q_x)
  let nd = lodeg(n, g)
  let dd = lodeg(d, g)
  let mut sgn : Value = Nil
  e = subst(
    limit__var(),
    q_x,
    sratsimp(
      div_star(
        d_ratdisrep(cons(h, cons(locoef(n, g), Fix(1L)))),
        d_ratdisrep(cons(h, cons(locoef(d, g), Fix(1L)))),
      ),
    ),
  )
  let val = limit__val()
  if e.truthy() && num_gt(nd, dd) {
    if !limit__memq(val, [q_d_zerob, q_d_zeroa, q_d_inf, q_d_minf]) {
      Fix(0L)
    } else if !equal(d_imagpart(e), Fix(0L)) {
      Fix(0L)
    } else {
      e = getsignl(d_realpart(e))
      if e is Nil {
        Fix(0L)
      } else if equal(e, Fix(1L)) {
        q_d_zeroa
      } else if equal(e, Fix(-1L)) {
        q_d_zerob
      } else {
        Fix(0L)
      }
    }
  } else if equal(nd, dd) {
    e
  } else if !limit__memq(val, [
      q_d_zerob, q_d_zeroa, q_d_infinity, q_d_inf, q_d_minf,
    ]) {
    throw_tag(q_limit, t)
  } else if eq(val, q_d_infinity) {
    q_d_infinity
  } else if !equal(
      Fix(0L),
      d_imagpart(
        sratsimp(
          div(
            d_ratdisrep(
              cons(
                h,
                cons(
                  droptop(n, g, dd),
                  droptop(d, g, num_sub(num_mul(Fix(2L), dd), nd)),
                ),
              ),
            ),
            e,
          ),
        ),
      ),
    ) {
    // E is only the ratio of the leading coefficients, so a lower-order
    // imaginary term never reaches it. Ask the part of the whole function
    // that survives the limit whether it is real.
    q_d_infinity
  } else {
    sgn = getsignl(e)
    if sgn is Nil {
      // No sign for E. A coefficient that cannot vanish still leaves an
      // infinite magnitude, and that is INFINITY.
      if freeof_extended_real(e).truthy() && eq(t, mnqp(e, Fix(0L))) {
        q_d_infinity
      } else {
        throw_tag(q_limit, t)
      }
    } else if equal(sgn, Fix(1L)) {
      q_d_inf
    } else if equal(sgn, Fix(-1L)) {
      q_d_minf
    } else {
      // The leading coefficient is zero, so that term is not there at all.
      // Drop it, and start over on what is left.
      n = droplo(n, g)
      if n.truthy() {
        ratlim(d_ratdisrep(cons(h, cons(n, d))))
      } else {
        Fix(0L)
      }
    }
  }
}

///|
fn lodeg(n : Value, x : Value) -> Value raise {
  if atom(n) || !eq(car(n), x) {
    Fix(0L)
  } else {
    lowdeg(cdr(n))
  }
}

///|
fn locoef(n : Value, x : Value) -> Value raise {
  if atom(n) || !eq(car(n), x) {
    n
  } else {
    car(last(n))
  }
}

///|
/// N is a polynomial in X, stored as (x exp coef exp coef ...) in descending
/// powers, so its lowest-degree term is the last pair. Return N without that
/// term, or NIL when it was the only one.
fn droplo(n : Value, x : Value) -> Value raise {
  if atom(n) || !eq(car(n), x) || cdddr(n) is Nil {
    Nil
  } else {
    butlast(n, n=2)
  }
}

///|
/// N is a polynomial in X in descending powers. Return N without the terms
/// of degree greater than K.
fn droptop(n : Value, x : Value, k : Value) -> Value raise {
  if atom(n) || !eq(car(n), x) {
    n
  } else {
    let mut l = cdr(n)
    while !(l is Nil || !num_gt(car(l), k)) {
      l = cddr(l)
    }
    if l.truthy() {
      cons(car(n), l)
    } else {
      Fix(0L)
    }
  }
}

///|
/// This function tries to determine the increasing/decreasing behavior of an
/// expression exp with respect to some variable var. val determines the
/// mode:
/// - $zeroa: From "positive zero" towards the right
/// - $zerob: From "negative zero" towards the left
/// - $inf:   From "positive infinity" towards the left
/// - $minf:  From "negative infinity" towards the right
/// Return values are -1 (decreasing), +1 (increasing) or 0 (don't know).
fn behavior(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  // $inf/$minf is handled by substituting 1/var for var and setting val to
  // $zeroa/$zerob.
  if real_infinityp(limit__val()).truthy() {
    set(
      q_val,
      if eq(limit__val(), q_d_inf) {
        q_d_zeroa
      } else if eq(limit__val(), q_d_minf) {
        q_d_zerob
      } else {
        Nil
      },
    )
    |> ignore
    set(q_exp, sratsimp(subin(power_star(limit__var(), Fix(-1L)), limit__exp())))
    |> ignore
  }
  let exp_ = limit__exp()
  let var_ = limit__var()
  let val = limit__val()
  if !limit__memq(val, [q_d_zeroa, q_d_zerob, q_d_inf, q_d_minf]) {
    return Fix(0L)
  } else if freeof(var_, exp_).truthy() {
    // Shortcut for constants.
    return Fix(0L)
  } else if eq(exp_, var_) {
    // Shortcut for the variable itself.
    return if limit__memq(val, [q_d_zeroa, q_d_minf]) {
      Fix(1L)
    } else {
      Fix(-1L)
    }
  } else if num_eq(
      symval(q_ear_behavior_count_now),
      symval(q_n_plusbehavior_count_plus),
    ) {
    // This limits the recursion depth of the function. Before giving up,
    // always try behavior-by-diff, which doesn't recurse.
    return behavior_by_diff(exp_, var_, val)
  }
  let bs2 = bind_all([
    (q_ear_behavior_count_now, one_plus(symval(q_ear_behavior_count_now))),
    (q_sign, Nil),
  ])
  defer unbind_all(bs2)
  let mut pair : Value = Nil
  let mut ans : Value = Nil
  // Pull out constant factors with known signs from a product:
  // behavior(c * f(x)) = signum(c) * behavior(f(x))
  if mtimesp(exp_).truthy() &&
    {
      pair = partition(exp_, var_, Fix(1L))
      !equal(car(pair), Fix(1L))
    } {
    set(q_sign, getsignl(car(pair))) |> ignore
    return if !fixnump(symval(q_sign)) {
      Fix(0L)
    } else {
      let s = symval(q_sign)
      mul2(s, behavior(cdr(pair), var_, val))
    }
  }
  // Pull out constant terms from a sum:
  // behavior(c + f(x)) = behavior(f(x))
  if mplusp(exp_).truthy() &&
    {
      pair = partition(exp_, var_, Fix(0L))
      !equal(car(pair), Fix(0L))
    } {
    return behavior(cdr(pair), var_, val)
  }
  // Handle f(x)^c for the case f(0) = 0 and c > 0 (probably other cases
  // could be handled, too)
  if mexptp(exp_).truthy() &&
    free(caddr(exp_), var_).truthy() &&
    eq0(no_err_sub(Fix(0L), exp_)) &&
    equal(getsignl(caddr(exp_)), Fix(1L)) &&
    {
      ans = behavior_expt(cadr(exp_), caddr(exp_))
      !equal(Fix(0L), ans)
    } {
    return ans
  }
  // Handle 1 / f(x): behavior(1 / f(x)) = -behavior(f(x))
  let r = {
    let (num, denom) = with_specials(
      [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
      () => num_denom_split(exp_),
    )
    with_special(q_denom, denom, () => if equal(num, Fix(1L)) {
      ans = num_neg(behavior(symval(q_denom), var_, val))
      ans
    } else {
      Nil
    })
  }
  if r.truthy() {
    return ans
  }
  // Handle c^f(x) for c > 1: behavior(c^f(x)) = behavior(f(x))
  if mexptp(exp_).truthy() &&
    free(cadr(exp_), var_).truthy() &&
    equal(Fix(1L), getsignl(sub_star(cadr(exp_), Fix(1L)))) &&
    {
      ans = behavior(caddr(exp_), var_, val)
      !equal(Fix(0L), ans)
    } {
    return ans
  }
  // Handle c^f(x) for 0 < c < 1: behavior(c^f(x)) = -behavior(f(x))
  if mexptp(exp_).truthy() &&
    free(cadr(exp_), var_).truthy() &&
    equal(Fix(1L), getsignl(cadr(exp_))) &&
    equal(Fix(-1L), getsignl(sub_star(cadr(exp_), Fix(1L)))) &&
    {
      ans = behavior(caddr(exp_), var_, val)
      !equal(Fix(0L), ans)
    } {
    return num_neg(ans)
  }
  // atan, erf, sinh and tanh are monotonically increasing, so their behavior
  // is equal to the behavior of their arguments.
  if limit__memq(caar(exp_), [q_p_atan, q_p_erf, q_p_sinh, q_p_tanh]) {
    return behavior(cadr(exp_), var_, val)
  }
  // Similarly, acot is monotonically decreasing left and right of x = 0.
  if eq(caar(exp_), q_p_acot) {
    return num_neg(behavior(cadr(exp_), var_, val))
  }
  // Handle log(f(x)) for f(0) = 0: If behavior(f(x)) = 1, then
  // behavior(log(f(x))) = 1
  if mlogp(exp_).truthy() &&
    eq0(no_err_sub(Fix(0L), cadr(exp_))) &&
    equal(Fix(1L), behavior(cadr(exp_), var_, val)) {
    return Fix(1L)
  }
  // Try to determine the behavior by taking the derivative.
  ans = behavior_by_diff(exp_, var_, val)
  if !equal(Fix(0L), ans) {
    return ans
  }
  // If exp is a sum and all terms have the same behavior, return that.
  if mplusp(exp_).truthy() &&
    {
      ans = behavior_all_same(exp_, var_, val)
      !equal(Fix(0L), ans)
    } {
    return ans
  }
  Fix(0L)
}

///|
fn behavior_all_same(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let exps = cdr(exp_)
  let first_behavior = behavior(first(exps), var_, val)
  if equal(first_behavior, Fix(0L)) ||
    !every(e => equal(behavior(e, var_, val), first_behavior), rest(exps)) {
    Fix(0L)
  } else {
    first_behavior
  }
}

///|
fn behavior_expt(bas : Value, expo : Value) -> Value raise {
  let behavior = behavior(bas, limit__var(), limit__val())
  if num_eq(behavior, Fix(1L)) {
    Fix(1L)
  } else if num_eq(behavior, Fix(0L)) {
    Fix(0L)
  } else if eq(ask_integer(expo, q_d_integer), q_d_yes) {
    if eq(ask_integer(expo, q_d_even), q_d_yes) {
      Fix(1L)
    } else {
      behavior
    }
  } else if ratnump(expo).truthy() {
    if evenp(cadr(expo)) {
      Fix(1L)
    } else if oddp(caddr(expo)) {
      behavior
    } else {
      Fix(0L)
    }
  } else {
    Fix(0L)
  }
}

///|
fn behavior_by_diff(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let mut ct = 0
  set(q_exp, sratsimp(sdiff(limit__exp(), limit__var()))) |> ignore
  let mut n = false
  // This do wins by a return.
  while ct <= 1 {
    // This loop used to run up to 5 times, but the size of some expressions
    // would blow up.
    let mut ans = no_err_sub(Fix(0L), limit__exp())
    if eq(ans, t) {
      return Fix(0L)
    } else if eq0(ans) {
      // Do it again.
      ()
    } else {
      ans = getsignl(ans)
      if n {
        return if ans.truthy() { ans } else { Fix(0L) }
      } else if equal(ans, Fix(1L)) {
        return if eq(limit__val(), q_d_zeroa) { Fix(1L) } else { Fix(-1L) }
      } else if equal(ans, Fix(-1L)) {
        return if eq(limit__val(), q_d_zeroa) { Fix(-1L) } else { Fix(1L) }
      } else {
        return Fix(0L)
      }
    }
    ct = ct + 1
    set(q_exp, sratsimp(sdiff(limit__exp(), limit__var()))) |> ignore
    n = !n
  }
  Fix(0L)
}

///|
fn try_lhospital(n : Value, d : Value, ind : Value) -> Value raise {
  // Make one catch for the whole bunch of lhospital trials.
  let ans = lhospital_catch(n, d, ind)
  if ans is Nil {
    Nil
  } else if !free_infp(ans).truthy() {
    simpinf(ans)
  } else if !free_epsilonp(ans).truthy() {
    simpab(ans)
  } else {
    ans
  }
}

///|
fn try_lhospital_quit(n : Value, d : Value, ind : Value) -> Value raise {
  let ans = {
    let a = lhospital_catch(n, d, ind)
    if a.truthy() {
      a
    } else {
      lhospital_catch(power_star(d, Fix(-1L)), power_star(n, Fix(-1L)), ind)
    }
  }
  if ans is Nil {
    throw_tag(q_limit, t)
  } else if !free_infp(ans).truthy() {
    simpinf(ans)
  } else if !free_epsilonp(ans).truthy() {
    simpab(ans)
  } else {
    ans
  }
}

///|
/// If this succeeds then raise LHCOUNT.
fn lhospital_catch(n : Value, d : Value, ind : Value) -> Value raise {
  if num_gt(Fix(0L), symval(q_lhcount)) {
    set(q_lhcount, symval(q_d_lhospitallim)) |> ignore
    throw_tag(q_lhospital, Nil)
  } else if equal(symval(q_lhcount), symval(q_d_lhospitallim)) {
    with_special(q_lhcount, add2_star(symval(q_lhcount), Fix(-1L)), () => catch_tag(
      q_lhospital,
      () => lhospital(n, d, ind),
    ))
  } else {
    set(q_lhcount, add2_star(symval(q_lhcount), Fix(-1L))) |> ignore
    let r = lhospital(n, d, ind)
    set(q_lhcount, add2_star(symval(q_lhcount), Fix(1L))) |> ignore
    r
  }
}

///|
fn lhospital(n : Value, d : Value, ind : Value) -> Value raise {
  let mut n = n
  let mut d = d
  if mtimesp(n).truthy() {
    n = muln(
      mapcar(term => lhsimp(term, limit__var(), limit__val()), cdr(n)),
      Nil,
    )
  }
  if mtimesp(d).truthy() {
    d = muln(
      mapcar(term => lhsimp(term, limit__var(), limit__val()), cdr(d)),
      Nil,
    )
  }
  let (n0, d0) = lhop_numden(n, d)
  n = n0
  d = d0
  set(q_lhp_q, if ind is Nil { cons(n, d) } else { Nil }) |> ignore
  let (nconst, n1) = var_or_const(n)
  n = n1
  let (dconst, d1) = var_or_const(d)
  d = d1
  // replace factorial and %gamma with approximations
  n = stirling0(n)
  d = stirling0(d)
  // take derivatives for l'hospital
  n = sdiff(n, limit__var())
  d = sdiff(d, limit__var())
  if !free(n, q_p_derivative).truthy() || !free(d, q_p_derivative).truthy() {
    throw_tag(q_lhospital, Nil) |> ignore
  }
  // see #895 limit x->inf sin(100/x)*x very slow
  with_special(q_d_trigexpandtimes, Nil, () => {
    n = expand_trigs(tansc(n), limit__var())
    d = expand_trigs(tansc(d), limit__var())
    (Nil : Value)
  })
  |> ignore
  let (const0, n2, d2) = remove_singularities(n, d)
  n = n2
  d = d2
  let const_ = mul2_star(const0, div_star(nconst, dconst))
  simpinf({
    let ans = if ind.truthy() {
      limit2(n, d, limit__var(), limit__val())
    } else {
      limit_numden(n, d, limit__val())
    }
    // When the limit function returns, it's possible that it will return NIL
    // (gave up without finding a limit). It's also possible that it will
    // return something containing UND. We treat that as a failure too.
    if ans.truthy() && freeof(q_d_und, ans).truthy() {
      sratsimp(mul2_star(const_, ans))
    } else {
      Nil
    }
  })
}

///|
/// Try to compute the limit of a quotient NUM/DEN, trying to massage the
/// input into a convenient form for LIMIT on the way.
fn limit_numden(n : Value, d : Value, val : Value) -> Value raise {
  let b = bind(q_val, val)
  defer unbind(b)
  let expr = if !mplusp(n).truthy() {
    // For general arguments, use sratsimp to simplify the quotient as much as
    // we can, then $multthru, which splits it up into a sum.
    d_multthru(sratsimp(div_star(n, d)))
  } else {
    // If we've already got a sum in the numerator, it seems to be better not
    // to recombine it.
    addn(mapcar(x => sratsimp(div_star(x, d)), cdr(n)), Nil)
  }
  limit(expr, limit__var(), val, q_think)
}

///|
/// Heuristics for picking the right way to express a LHOSPITAL problem.
fn lhop_numden(num : Value, denom : Value) -> (Value, Value) raise {
  let b = bind(q_denom, denom)
  defer unbind(b)
  let mut num = num
  // (psetq num (m^ denom -1) denom (m^ num -1))
  fn swap(num : Value) -> Value raise {
    let new_num = power_star(symval(q_denom), Fix(-1L))
    let new_denom = power_star(num, Fix(-1L))
    set(q_denom, new_denom) |> ignore
    new_num
  }

  let var_ = limit__var()
  let done = {
    let log_num = involve(num, list1(q_p_log))
    if log_num is Nil {
      false
    } else {
      if lessthan(
          num_of_logs(factor(sratsimp(sdiff(power_star(num, Fix(-1L)), var_)))),
          num_of_logs(factor(sratsimp(sdiff(num, var_)))),
        ).truthy() {
        num = swap(num)
      }
      true
    }
  }
  if !done {
    let done2 = {
      let denom = symval(q_denom)
      let log_denom = involve(denom, list1(q_p_log))
      if log_denom is Nil {
        false
      } else {
        if lessthan(
            num_of_logs(sratsimp(sdiff(power_star(denom, Fix(-1L)), var_))),
            num_of_logs(sratsimp(sdiff(denom, var_))),
          ).truthy() {
          // (psetq denom (m^ num -1) num (m^ denom -1))
          num = swap(num)
        }
        true
      }
    }
    if !done2 {
      let exp_num = p_einvolve(num)
      let done3 = if exp_num.truthy() {
        if !p_e_right_placep(exp_num).truthy() {
          num = swap(num)
        }
        true
      } else {
        false
      }
      if !done3 {
        let exp_den = p_einvolve(symval(q_denom))
        let done4 = if exp_den.truthy() {
          if !p_e_right_placep(exp_den).truthy() {
            num = swap(num)
          }
          true
        } else {
          false
        }
        if !done4 {
          let scnum = involve(num, list1(q_p_sin))
          let done5 = if scnum.truthy() {
            if !trig_right_placep(q_p_sin, scnum).truthy() {
              num = swap(num)
            }
            true
          } else {
            false
          }
          if !done5 {
            let scden = involve(symval(q_denom), list1(q_p_sin))
            let done6 = if scden.truthy() {
              if !trig_right_placep(q_p_sin, scden).truthy() {
                num = swap(num)
              }
              true
            } else {
              false
            }
            if !done6 {
              // If the numerator contains an inverse trig and the denominator
              // or reciprocal of denominator is polynomial, leave everything
              // as is. This is not perfect.
              let scnum2 = involve(num, list([q_p_asin, q_p_acos, q_p_atan]))
              let denom = symval(q_denom)
              let done7 = scnum2.truthy() &&
                (
                  polyinx(denom, var_, Nil).truthy() ||
                  polyinx(power_star(denom, Fix(-1L)), var_, Nil).truthy()
                )
              if !done7 {
                if !(oscip(num).truthy() || oscip(symval(q_denom)).truthy()) {
                  if frac(num).truthy() {
                    num = swap(num)
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  (num, symval(q_denom))
}

///|
/// i don't know what to do here for some cases, may have to be refined.
fn num_of_logs(exp_ : Value) -> Value raise {
  if mapatom(exp_).truthy() {
    Fix(0L)
  } else if equal(caar(exp_), q_p_log) {
    add2_star(Fix(1L), num_of_log_l(cdr(exp_)))
  } else if mexptp(exp_).truthy() && mnump(caddr(exp_)).truthy() {
    mul2_star(simplify(mk(q_mabs, [caddr(exp_)])), num_of_logs(cadr(exp_)))
  } else {
    num_of_log_l(cdr(exp_))
  }
}

///|
fn num_of_log_l(llist : Value) -> Value raise {
  let mut ans : Value = Fix(0L)
  for x in llist.iter() {
    ans = add2_star(ans, num_of_logs(x))
  }
  ans
}

///|
fn p_e_right_placep(p_e_arg : Value) -> Value raise {
  let p_e_arg_diff = sdiff(p_e_arg, limit__var())
  let f = free(p_e_arg_diff, limit__var())
  if f.truthy() {
    // simple cases
    return f
  }
  let denom = symval(q_denom)
  if (mexptp(denom).truthy() && equal(cadr(denom), Fix(-1L))) ||
    polyinx(power_star(denom, Fix(-1L)), limit__var(), Nil).truthy() {
    return Nil
  }
  let diff_lim = ridofab(limit(p_e_arg_diff, limit__var(), limit__val(), q_think))
  let exp_lim = ridofab(
    limit(power_star(q_d__pcte, p_e_arg), limit__var(), limit__val(), q_think),
  )
  if equal(diff_lim, exp_lim) {
    t
  } else if mnump(diff_lim).truthy() && mnump(exp_lim).truthy() {
    t
  } else if mnump(diff_lim).truthy() && infinityp(exp_lim).truthy() {
    // This is meant to make maxima handle bug 1469411 correctly.
    // Undoubtedly, this needs work.
    t
  } else {
    Nil
  }
}

///|
fn trig_right_placep(trig_type : Value, arg : Value) -> Value raise {
  let arglim = ridofab(limit(arg, limit__var(), limit__val(), q_think))
  let triglim = ridofab(
    limit(mk(trig_type, [arg]), limit__var(), limit__val(), q_think),
  )
  if equal(arglim, Fix(0L)) && equal(triglim, Fix(0L)) {
    t
  } else if infinityp(arglim).truthy() && infinityp(triglim).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Remove the first element EQUAL to X from L (CL `delete :count 1 :test
/// #'equal`).
fn limit__delete_first_equal(x : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  let mut found = false
  while p is Cons(_) {
    if !found && equal(car(p), x) {
      found = true
    } else {
      c.add(car(p))
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// Takes a numerator and a denominator. If they tries all combinations of
/// products to try and make a simpler set of subproblems for LHOSPITAL.
fn remove_singularities(
  numer : Value,
  denom : Value,
) -> (Value, Value, Value) raise {
  let bs = bind_all([(q_numer, numer), (q_denom, denom)])
  defer unbind_all(bs)
  if numer is Nil ||
    denom is Nil ||
    atom(numer) ||
    atom(denom) ||
    !mtimesp(numer).truthy() ||
    !mtimesp(denom).truthy() {
    // Leave this here for a while.
    return (Fix(1L), numer, denom)
  }
  let mut const_ : Value = Fix(1L)
  let (num_consts, num_vars0) = var_or_const(numer)
  let (denom_consts, denom_vars0) = var_or_const(denom)
  let num_vars = if !mtimesp(num_vars0).truthy() {
    list1(num_vars0)
  } else {
    cdr(num_vars0)
  }
  let denom_vars = if !mtimesp(denom_vars0).truthy() {
    list1(denom_vars0)
  } else {
    cdr(denom_vars0)
  }
  let mut nl = num_vars
  let mut num_list = copy_list(num_vars)
  let mut den_list = denom_vars
  let mut den_list_temp = copy_list(denom_vars)
  while nl.truthy() {
    let mut dl = den_list
    while dl.truthy() {
      if p_einvolve(car(nl)).truthy() || p_einvolve(car(dl)).truthy() {
        ()
      } else {
        let lim = catch_tag(q_limit, () => simpinf(
          simpab(
            limit(
              div_star(car(nl), car(dl)),
              limit__var(),
              limit__val(),
              q_think,
            ),
          ),
        ))
        if eq(lim, t) ||
          lim is Nil ||
          equal(ridofab(lim), Fix(0L)) ||
          infinityp(lim).truthy() ||
          !free(lim, q_d_inf).truthy() ||
          !free(lim, q_d_minf).truthy() ||
          !free(lim, q_d_infinity).truthy() ||
          !free(lim, q_d_ind).truthy() ||
          !free(lim, q_d_und).truthy() {
          ()
        } else {
          const_ = mul2_star(lim, const_)
          num_list = limit__delete_first_equal(car(nl), num_list)
          den_list_temp = limit__delete_first_equal(car(dl), den_list_temp)
          break
        }
      }
      dl = cdr(dl)
    }
    nl = cdr(nl)
    den_list = den_list_temp
  }
  (
    mul2_star(const_, div_star(num_consts, denom_consts)),
    muln(num_list, Nil),
    muln(den_list_temp, Nil),
  )
}

///|
/// separate terms that contain var from constant terms
/// returns (const-terms . var-terms)
fn var_or_const(expr : Value) -> (Value, Value) raise {
  let expr = d_factor(expr)
  let var_ = limit__var()
  if atom(expr) {
    if eq(expr, var_) {
      (Fix(1L), expr)
    } else {
      (expr, Fix(1L))
    }
  } else if free(expr, var_).truthy() {
    (expr, Fix(1L))
  } else if mtimesp(expr).truthy() {
    let mut const_ : Value = Fix(1L)
    let mut varl : Value = Fix(1L)
    for f in cdr(expr).iter() {
      if free(f, var_).truthy() {
        const_ = mul2_star(f, const_)
      } else {
        varl = mul2_star(f, varl)
      }
    }
    (const_, varl)
  } else {
    (Fix(1L), expr)
  }
}

///|
/// if term goes to non-zero constant, replace with constant
fn lhsimp(term : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  if d_mapatom(term).truthy() {
    term
  } else {
    let term_value = ridofab(limit(term, var_, val, q_think))
    if !limit__memq(term_value, [
        q_d_inf, q_d_minf, q_d_und, q_d_ind, q_d_infinity,
      ]) &&
      eq(t, mnqp(term_value, Fix(0L))) {
      term_value
    } else {
      term
    }
  }
}

///|
/// Attempts to evaluate limit(bas^expo, var val) using the l'Hospital rule
/// applied to log(bas)/(1/expo). When `ans` is an extended real, the call to
/// the one argument limit function simplifies the result (but it misses the
/// case limit(exp(ind)) = ind).
fn bylog(expo : Value, bas : Value) -> Value raise {
  let ans = try_lhospital_quit(
    ftake(q_p_log, [bas]),
    div(Fix(1L), expo),
    Nil,
  )
  if ans.truthy() {
    d_radcan(d_limit(list1(ftake(q_mexpt, [q_d__pcte, ans]))))
  } else {
    Nil
  }
}

///|
/// Return
///  (a) pos-real-inside if 0 < x < 1
///  (b) inside if |e| < 1
///  (c) one if e = 1
///  (d) zero if e = 0
///  (e) on if |e| = 1
///  (f) pos-real-outside if real(e) > 1 & imag(e)=0
///  (g) outside if |e| > 1
///  (h) nil if all other tests fail
fn inside_outside_unit_circle(e : Value) -> Value raise {
  let e = risplit(e)
  let re = car(e)
  let im = cdr(e)
  let x = add2(mul2(re, re), mul2(im, im))
  if eq(t, meqp(Fix(0L), re)) && eq(t, meqp(Fix(0L), im)) {
    q_zero
  } else if eq(t, meqp(im, Fix(0L))) && eq(t, meqp(re, Fix(1L))) {
    q_one
  } else if eql(im, Fix(0L)) &&
    eq(t, mgrp(re, Fix(0L))) &&
    eq(t, mgrp(Fix(1L), re)) {
    q_pos_real_inside
  } else if eq(t, mgrp(Fix(1L), x)) {
    q_inside
  } else if eq(t, meqp(Fix(1L), x)) {
    q_on
  } else if eq(t, meqp(im, Fix(0L))) && eq(t, mgrp(re, Fix(1L))) {
    q_pos_real_outside
  } else if eq(t, mgrp(x, Fix(1L))) {
    q_outside
  } else {
    Nil
  }
}
