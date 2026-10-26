// Port of src/simp.lisp, part 2: log, sqrt, quotient, abs, SIMPTIMES and
// TMS, limit/integrate/derivative nouns, signum and EXPTRL.

///|
let simp__q_bf_abs : Value = sym("bigfloat::abs")

///|
let simp__q_bf_signum : Value = sym("bigfloat::signum")

///|
/// `(member x '($complex $imaginary))`
fn simp__complex_sign_p(s : Value) -> Bool {
  eq(s, q_d_complex) || eq(s, q_d_imaginary)
}

///|
/// Simplification of the Log function (def-simplifier log (y)).
fn simp__pctlog(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(form, required_arg_count=Fix(1L), pretty_name=list2(list1(q_p_log), q_d_y))
    |> ignore
  }
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_log), list1(y)), form)
  if onep1(y).truthy() {
    return addk(Fix(-1L), y)
  }
  if zerop1(y).truthy() {
    return if symval(q_radcanp).truthy() {
      list2(list2(q_p_log, q_simp), Fix(0L))
    } else if !symval(q_errorsw).truthy() {
      merr("log: encountered log(0).", [])
    } else {
      throw_tag(q_errorsw, t)
    }
  }
  // Check evaluation in floating point precision.
  let r = flonum_eval(mop(form), y)
  if r.truthy() {
    return r
  }
  // Check evaluation in bigfloat precision.
  if !member(q_simp, cdar(form)).truthy() {
    let r = big_float_eval(mop(form), y)
    if r.truthy() {
      return r
    }
  }
  if eq(y, q_d__pcte) {
    return Fix(1L)
  }
  let logexpand = symval(q_d_logexpand)
  let all_or_super = eq(logexpand, q_d_all) || eq(logexpand, q_d_super)
  if mexptp(y).truthy() {
    if (logexpand.truthy() && eq(symval(q_d_domain), q_d_real)) ||
      all_or_super ||
      (
        eq(d_csign(cadr(y)), q_d_pos) &&
        !simp__complex_sign_p(d_csign(caddr(y)))
      ) {
      // Simplify log(x^a) -> a*log(x), where x > 0 and a is real
      return mul2(caddr(y), take(list1(q_p_log), [cadr(y)]))
    } else if (
        ratnump(caddr(y)).truthy() &&
        (eql(Fix(1L), cadr(caddr(y))) || eql(Fix(-1L), cadr(caddr(y))))
      ) ||
      maxima_integerp(inv(caddr(y))).truthy() {
      // Simplify log(z^(1/n)) -> log(z)/n, where n is an integer
      return mul2(caddr(y), take(list1(q_p_log), [cadr(y)]))
    } else if eq(cadr(y), q_d__pcte) &&
      (
        !simp__complex_sign_p(d_csign(caddr(y))) ||
        !simp__complex_sign_p(d_csign(mul2(q_d__pcti, caddr(y))))
      ) {
      // Simplify log(exp(x)) and log(exp(%i*x)), where x is a real
      return caddr(y)
    } else {
      return give_up()
    }
  }
  if ratnump(y).truthy() {
    // Simplify log(n/d)
    return if eql(cadr(y), Fix(1L)) {
      mul2(Fix(-1L), take(list1(q_p_log), [caddr(y)]))
    } else if eq(logexpand, q_d_super) {
      sub(take(list1(q_p_log), [cadr(y)]), take(list1(q_p_log), [caddr(y)]))
    } else {
      give_up()
    }
  }
  if all_or_super && mtimesp(y).truthy() {
    let mut b : Value = Nil
    for f in cdr(y).iter() {
      b = cons(take(list1(q_p_log), [f]), b)
    }
    return addn(b, t)
  }
  if all_or_super &&
    y is Cons(_) &&
    (eq(caar(y), q_p_product) || eq(caar(y), q_d_product)) {
    let new_op = if eq(get_first_char(caar(y)), Char('%')) {
      q_p_sum
    } else {
      q_d_sum
    }
    return simplifya(
      cons(list1(new_op), cons(list2(list1(q_p_log), cadr(y)), cddr(y))),
      Nil,
    )
  }
  if symval(q_d_lognegint).truthy() &&
    maxima_integerp(y).truthy() &&
    eq(d_sign(y), q_d_neg) {
    return add2(mul2(q_d__pcti, q_d__pctpi), take(list1(q_p_log), [neg(y)]))
  }
  let r = taylorize(mop(form), second(form))
  if r.truthy() {
    return r
  }
  give_up()
}

///|
/// SIMPLN1 computes LOG(W), where W is an MEXPT expression.
/// It's called by ORDMEXPT in cases where (TAKE '(%LOG) ...) could result
/// in infinite recursion.
fn simpln1(w : Value) -> Value raise {
  let simped = lbool(member(q_simp, cdar(w)).truthy())
  // Don't lie to SIMPLIFYA (2nd arg)!
  simplifya(
    list3(list1(q_mtimes), caddr(w), simplifya(list2(list1(q_p_log), cadr(w)), simped)),
    simped,
  )
}

///|
/// Implementation of the Square root function
fn simp_sqrt(x : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(x) |> ignore
  let arg = if z.truthy() { cadr(x) } else { simplifya(cadr(x), Nil) }
  simplifya(list3(list1(q_mexpt), arg, mk_simp(q_rat, [Fix(1L), Fix(2L)])), t)
}

///|
/// Simplification of the "/" operator.
fn simpquot(x : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  twoargcheck(x) |> ignore
  let num = if z.truthy() { cadr(x) } else { simplifya(cadr(x), Nil) }
  let den = if z.truthy() { caddr(x) } else { simplifya(caddr(x), Nil) }
  if integerp(num) && integerp(den) && !zerop(den) {
    n_starred(num, den)
  } else if numberp(num) && numberp(den) && !zerop(den) {
    num_div(num, den)
  } else if floatp(num) && floatp(den) {
    num_div(num, den)
  } else if d_bfloatp(num).truthy() &&
    d_bfloatp(den).truthy() &&
    !zerop(cadr(den)) {
    // Call BIGFLOATP to ensure that arguments have same precision.
    // Otherwise FPQUOTIENT could return a spurious value.
    bcons(fpquotient(cdr(bigfloatp(num)), cdr(bigfloatp(den))))
  } else {
    let inv_den = simplifya(list3(list1(q_mexpt), den, Fix(-1L)), t)
    if equal(num, Fix(1L)) {
      inv_den
    } else {
      simplifya(list3(list1(q_mtimes), num, inv_den), t)
    }
  }
}

///|
fn simp__take_abs(u : Value) -> Value raise {
  take(list1(q_mabs), [u])
}

///|
/// Implementation of the abs function.
fn simpabs(e : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(e) |> ignore
  let x = simpcheck(second(e), z)
  if complex_number_p(
      x,
      ntypep=lfunc("simpabs-lambda", args => {
        let s = arg(args, 0)
        lbool(floatp(s) || d_bfloatp(s).truthy())
      }),
    ).truthy() {
    return funcall(q_to, [funcall(simp__q_bf_abs, [bf_to(x)])])
  }
  if complex_number_p(x, ntypep=q_mnump).truthy() {
    return ftake(q_p_cabs, [x])
  }
  // nounform for arrays...
  if arrayp(x) || d_member(x, symval(q_d_arrays)).truthy() {
    return list2(list2(q_mabs, q_simp), x)
  }
  // taylor polynomials
  let r = taylorize(q_mabs, x)
  if r.truthy() {
    return r
  }
  // values for extended real arguments:
  if eq(x, q_d_inf) || eq(x, q_d_infinity) || eq(x, q_d_minf) {
    return q_d_inf
  }
  if eq(x, q_d_ind) || eq(x, q_d_und) {
    return x
  }
  // abs(abs(expr)) --> abs(expr). Since x is simplified, it's OK to return x.
  if is_op(x, q_mabs) {
    return x
  }
  // abs(conjugate(expr)) = abs(expr).
  if is_op(x, q_d_conjugate) {
    return simp__take_abs(cadr(x))
  }
  let sgn = d_csign(x)
  if eq(sgn, q_d_neg) || eq(sgn, q_d_nz) {
    mul2(Fix(-1L), x)
  } else if eq(q_d_zero, sgn) {
    mul2(Fix(0L), x)
  } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
    x
  } else if eq(sgn, q_d_complex) && d_constantp(x).truthy() {
    // for complex constant expressions, use $cabs
    ftake(q_p_cabs, [x])
  } else if eq(sgn, q_d_complex) &&
    mexptp(x).truthy() &&
    eq(q_d_pos, d_csign(second(x))) {
    // abs(pos^complex) --> pos^(realpart(complex)).
    power(second(x), d_realpart(third(x)))
  } else if mexptp(x).truthy() && eq(q_d_neg, d_csign(second(x))) {
    // for abs(neg^z), use cabs.
    ftake(q_p_cabs, [x])
  } else if eq(q_d_pn, sgn) && is_op(x, q_p_signum) {
    // abs(signum(x)) = 1 for signum(x) real and non-zero.
    Fix(1L)
  } else if eq(q_d_pn, sgn) &&
    mexptp(x).truthy() &&
    is_op(cadr(x), q_p_signum) &&
    d_featurep(caddr(x), q_d_integer).truthy() {
    // abs(signum(x)^int) = 1 for signum(x)^int real and non-zero
    Fix(1L)
  } else if mtimesp(x).truthy() {
    // multiplicative property: abs(x*y) = abs(x) * abs(y).
    muln(mapcar(u => simp__take_abs(u), margs(x)), t)
  } else if mexptp(x).truthy() && d_featurep(caddr(x), q_d_integer).truthy() {
    // abs(x^n) = abs(x)^n for integer n.
    power(simp__take_abs(cadr(x)), caddr(x))
  } else if great(neg(x), x).truthy() {
    // Reflection rule: abs(-x) --> abs(x)
    simp__take_abs(neg(x))
  } else {
    // nounform return
    eqtest(list2(list1(q_mabs), x), e)
  }
}

///|
fn abs_integral(x : Value) -> Value raise {
  muln_([div(Fix(1L), Fix(2L)), x, simp__take_abs(x)])
}

///|
/// Some simple optimizations of x * y.
fn testt(x : Value) -> Value raise {
  if mnump(x).truthy() {
    x
  } else if cddr(x) is Nil {
    // We have something like ((mtimes) foo).  This is the same as foo.
    cadr(x)
  } else if eql(Fix(1L), cadr(x)) {
    // We have 1*foo.  Which is the same as foo.  This should not
    // be applied to 1.0 or 1b0!
    if cdddr(x) is Nil {
      caddr(x)
    } else {
      rplacd(x, cddr(x))
    }
  } else {
    testtneg(x)
  }
}

///|
/// This basically converts -(a+b) to -a-b.
fn testtneg(x : Value) -> Value raise {
  if equal(cadr(x), Fix(-1L)) &&
    cdddr(x) is Nil &&
    mplusp(caddr(x)).truthy() &&
    symval(q_d_negdistrib).truthy() {
    // If x is exactly of the form -1*(sum), and $negdistrib is
    // true, we distribute the -1 across the sum.
    addn(mapcar(z => mul2(Fix(-1L), z), cdr(caddr(x))), t)
  } else {
    x
  }
}

///|
/// Simplification of the "-" operator
fn simpmin(x : Value, vestigial : Value, z : Value) -> Value raise {
  ignore(vestigial)
  if cdr(x) is Nil {
    Fix(0L)
  } else if cddr(x) is Nil {
    mul2(Fix(-1L), if z.truthy() { cadr(x) } else { simplifya(cadr(x), Nil) })
  } else {
    // ((mminus) a b ...) -> ((mplus) a ((mtimes) -1 b) ...)
    sub(if z.truthy() { cadr(x) } else { simplifya(cadr(x), Nil) }, addn(cddr(x), z))
  }
}

///|
/// `(member x '(-1 -1.0))`
fn simp__minus_one_p(x : Value) -> Bool {
  eql(x, Fix(-1L)) || eql(x, Flo(-1.0))
}

///|
fn simptimes(x : Value, w : Value, z : Value) -> Value raise {
  // W must be 1
  if cdr(x) is Nil {
    return Fix(1L)
  }
  let check = x
  let mut x = x
  let mut w = w
  let mut res : Value = Nil
  let mut eqnflag : Value = Nil
  let mut matrixflag : Value = Nil
  let mut sumflag : Value = Nil
  while true {
    // start
    x = cdr(x)
    if zerop1(res).truthy() {
      // A zero factor was found. But we still need to simplify any remaining
      // factors to catch errors like division by zero or log(0).
      // Also apply (big)float contagion so that 0 * 0.0 becomes 0.0 and
      // 0 * 0b0 becomes 0b0.
      if x.truthy() {
        let mut float_found = floatp(res)
        let mut bigfloat_found = d_bfloatp(res).truthy()
        for f in x.iter() {
          let f = if z.truthy() { f } else { simplifya(f, Nil) }
          if floatp(f) {
            float_found = true
          } else if d_bfloatp(f).truthy() {
            bigfloat_found = true
          }
        }
        if bigfloat_found {
          res = symval(q_ear_bigfloatzero)
        } else if float_found {
          res = Flo(0.0)
        }
      }
      if symval(q_d_mx0simp).truthy() {
        if matrixflag.truthy() && mxorlistp1(matrixflag).truthy() {
          return constmx(res, matrixflag)
        } else if eqnflag.truthy() {
          return list3(
            list2(q_mequal, q_simp),
            mul2(res, cadr(eqnflag)),
            mul2(res, caddr(eqnflag)),
          )
        } else {
          for u in x.iter() {
            if mxorlistp(u).truthy() {
              res = constmx(res, u)
              break
            } else if mexptp(u).truthy() &&
              mxorlistp1(cadr(u)).truthy() &&
              d_numberp(caddr(u)).truthy() {
              res = constmx(res, cadr(u))
              break
            } else if mequalp(u).truthy() {
              res = list3(
                list2(q_mequal, q_simp),
                mul2(res, cadr(u)),
                mul2(res, caddr(u)),
              )
              break
            }
          }
        }
      }
      return res
    }
    if x is Nil {
      break
    }
    w = if z.truthy() { car(x) } else { simplifya(car(x), Nil) }
    let mut mult_it = true
    while true {
      // st1
      if atom(w) {
        ()
      } else if eq(caar(w), q_mrat) {
        if eqnflag.truthy() ||
          matrixflag.truthy() ||
          (sumflag.truthy() && !member(q_trunc, cdar(w)).truthy()) ||
          spsimpcases(cdr(x), w).truthy() {
          w = ratdisrep(w)
          continue
        } else {
          // Bind VARLIST and GENVAR so kernels from this
          // conversion don't accumulate in the global table.
          // The MRAT returned carries its own copies.
          let w1 = w
          let x1 = x
          let res1 = res
          return with_specials(
            [(q_varlist, symval(q_varlist)), (q_genvar, symval(q_genvar))],
            () => ratf(
              cons(
                list1(q_mtimes),
                nconc(mapcar(a => simplify(a), cons(w1, cdr(x1))), cdr(res1)),
              ),
            ),
          )
        }
      } else if eq(caar(w), q_mequal) {
        eqnflag = if !eqnflag.truthy() {
          w
        } else {
          list3(
            car(eqnflag),
            mul2(cadr(eqnflag), cadr(w)),
            mul2(caddr(eqnflag), caddr(w)),
          )
        }
        mult_it = false
      } else if eq(caar(w), q_mlist) || eq(caar(w), q_d_matrix) {
        matrixflag = if !matrixflag.truthy() {
          w
        } else if (
            symval(q_d_doallmxops).truthy() ||
            symval(q_d_domxmxops).truthy() ||
            symval(q_d_domxtimes).truthy()
          ) &&
          (!eq(caar(w), q_mlist) || symval(q_d_listarith).truthy()) &&
          !eq(symval(q_ear_inv), q_d_detout) {
          stimex(matrixflag, w)
        } else {
          res = tms(w, Fix(1L), res)
          matrixflag
        }
        mult_it = false
      } else if eq(caar(w), q_p_sum) && symval(q_d_sumexpand).truthy() {
        sumflag = sumtimes(sumflag, w)
        mult_it = false
      }
      break
    }
    if mult_it {
      res = tms(w, Fix(1L), res)
    }
  }
  // end
  if mtimesp(res).truthy() {
    res = testt(res)
  }
  if sumflag.truthy() {
    res = if res is Nil || equal(res, Fix(1L)) {
      sumflag
    } else if !mtimesp(res).truthy() {
      list3(list1(q_mtimes), res, sumflag)
    } else {
      nconc(res, list1(sumflag))
    }
  }
  if atom(res) ||
    !(eq(caar(res), q_mexpt) || eq(caar(res), q_mtimes)) ||
    (zerop(symval(q_d_expop)) && zerop(symval(q_d_expon))) ||
    symval(q_ear_expandflag).truthy() {
    ()
  } else if eq(caar(res), q_mtimes) {
    res = expandtimes(res)
  } else if mplusp(cadr(res)).truthy() &&
    fixnump(caddr(res)) &&
    !(
      num_gt(caddr(res), symval(q_d_expop)) ||
      num_gt(num_neg(caddr(res)), symval(q_d_expon))
    ) {
    res = expandexpt(cadr(res), caddr(res))
  }
  if matrixflag.truthy() {
    res = if res is Nil {
      matrixflag
    } else if (
        d_listp(matrixflag).truthy() ||
        symval(q_d_doallmxops).truthy() ||
        (symval(q_d_doscmxops).truthy() && !simp__minus_one_p(res)) ||
        // RES should only be -1 here (not = 1)
        (symval(q_d_domxmxops).truthy() && simp__minus_one_p(res))
      ) &&
      (!d_listp(matrixflag).truthy() || symval(q_d_listarith).truthy()) {
      mxtimesc(res, matrixflag)
    } else {
      testt(tms(matrixflag, Fix(1L), tms(res, Fix(1L), Nil)))
    }
  }
  if res.truthy() {
    res = eqtest(res, check)
  }
  if eqnflag.truthy() {
    if res is Nil {
      res = Fix(1L)
    }
    list3(car(eqnflag), mul2(cadr(eqnflag), res), mul2(caddr(eqnflag), res))
  } else {
    res
  }
}

///|
fn spsimpcases(l : Value, e : Value) -> Value raise {
  for u in l.iter() {
    if mbagp(u).truthy() ||
      (
        !atom(u) && eq(caar(u), q_p_sum) && !member(q_trunc, cdar(e)).truthy()
      ) {
      return t
    }
  }
  Nil
}

///|
fn mxtimesc(sc : Value, mx : Value) -> Value raise {
  let mut sign : Value = Nil
  if mtimesp(sc).truthy() &&
    simp__minus_one_p(cadr(sc)) &&
    symval(q_d_doscmxops).truthy() &&
    !(
      symval(q_d_doallmxops).truthy() ||
      symval(q_d_domxmxops).truthy() ||
      symval(q_d_domxtimes).truthy()
    ) {
    sign = cadr(sc)
    rplaca(cdr(sc), Nil) |> ignore
  }
  let out = {
    let mut scp_star = if mtimesp(sc).truthy() {
      partition_ns(cdr(sc))
    } else if !scalar_or_constant_p(sc, symval(q_d_assumescalar)).truthy() {
      Nil
    } else {
      sc
    }
    if scp_star is Nil {
      list3(list2(q_mtimes, q_simp), sc, mx)
    } else if !atom(scp_star) && car(scp_star) is Nil {
      append(list1(list1(q_mtimes)), append(cadr(scp_star), list1(mx)))
    } else if atom(scp_star) ||
      (
        cdr(scp_star) is Nil &&
        !(cdr(sc) is Nil) &&
        {
          scp_star = cons(list1(q_mtimes), car(scp_star))
          true
        }
      ) ||
      !mtimesp(sc).truthy() {
      simplifya(outermap1(list([q_mtimes, scp_star, mx])), Nil)
    } else {
      append(
        list1(list1(q_mtimes)),
        append(
          list1(
            simplifya(
              outermap1(list([q_mtimes, cons(list1(q_mtimes), car(scp_star)), mx])),
              t,
            ),
          ),
          cadr(scp_star),
        ),
      )
    }
  }
  if sign.truthy() {
    if mtimesp(out).truthy() {
      rplacd(out, cons(sign, cdr(out)))
    } else {
      list3(list1(q_mtimes), sign, out)
    }
  } else if mtimesp(out).truthy() {
    testt(out)
  } else {
    out
  }
}

///|
fn stimex(x : Value, y : Value) -> Value raise {
  with_specials(
    [(q_d_doscmxops, t), (q_d_domxmxops, t), (q_d_listarith, t)],
    () => simplify(fmapl1(q_mtimes, list2(x, y))),
  )
}

///|
/// TMS takes a simplified expression FACTOR and a cumulative
/// PRODUCT as arguments and modifies the cumulative product so
/// that the expression is now one of its factors.  The
/// exception to this occurs when a tellsimp rule is triggered.
/// The second argument is the POWER to which the expression is
/// to be raised within the product.
fn tms(factor : Value, power : Value, product : Value) -> Value raise {
  let b = bind(q_ear_rulesw, Nil)
  defer unbind(b)
  let mut product = product
  let mut z : Value = Nil
  if mplusp(product).truthy() {
    product = list2(list2(q_mtimes, q_simp), product)
  }
  if zerop1(factor).truthy() {
    return if mnegp(power).truthy() {
      if symval(q_errorsw).truthy() {
        throw_tag(q_errorsw, t)
      } else {
        merr("Division by 0", [])
      }
    } else if mtimesp(product).truthy() {
      // Factor is a zero, but use ZERORES for (big)float contagion.
      zerores(factor, cadr(product))
    } else {
      factor
    }
  }
  if product is Nil {
    if mtimesp(factor).truthy() && equal(power, Fix(1L)) {
      return cons(
        list1(q_mtimes),
        append(
          if mnump(cadr(factor)).truthy() {
            Nil
          } else {
            list1(Fix(1L))
          },
          copy_list(cdr(factor)),
        ),
      )
    }
    product = list2(list1(q_mtimes), Fix(1L))
  }
  if mtimesp(factor).truthy() {
    let mut factor_list = cdr(factor)
    while !(factor_list is Nil || zerop1(product).truthy()) {
      z = timesin(car(factor_list), cdr(product), power)
      if symval(q_ear_rulesw).truthy() {
        set(q_ear_rulesw, Nil) |> ignore
        product = tms_format_product(z)
      }
      factor_list = cdr(factor_list)
    }
    product
  } else {
    z = timesin(factor, cdr(product), power)
    if symval(q_ear_rulesw).truthy() {
      tms_format_product(z)
    } else {
      product
    }
  }
}

///|
fn tms_format_product(x : Value) -> Value raise {
  if zerop1(x).truthy() {
    x
  } else if mnump(x).truthy() {
    list2(list1(q_mtimes), x)
  } else if !mtimesp(x).truthy() {
    list3(list1(q_mtimes), Fix(1L), x)
  } else if !mnump(cadr(x)).truthy() {
    cons(list1(q_mtimes), cons(Fix(1L), cdr(x)))
  } else {
    x
  }
}

///|
/// Multiply FACTOR into the product of the list RES, as TMS does, and
/// return the new list of factors.
fn tms_factors(factor : Value, res : Value) -> Value raise {
  let product = tms(factor, Fix(1L), cons(list1(q_mtimes), res))
  if mtimesp(product).truthy() {
    cdr(product)
  } else {
    list1(product)
  }
}

///|
fn plsk(x : Value, y : Value) -> Value raise {
  if symval(q_d_ratsimpexpons).truthy() {
    sratsimp(list3(list1(q_mplus), x, y))
  } else if mnump(x).truthy() && mnump(y).truthy() {
    addk(x, y)
  } else {
    add2(x, y)
  }
}

///|
fn mult(x : Value, y : Value) -> Value raise {
  if mnump(x).truthy() && mnump(y).truthy() {
    timesk(x, y)
  } else {
    mul2(x, y)
  }
}

///|
fn simp_limit(x : Value, vestigial : Value, z : Value) -> Value raise {
  ignore(vestigial)
  let l1 = length(x)
  if !(l1 == 2 || l1 == 4 || l1 == 5) {
    merr("limit: wrong number of arguments.", []) |> ignore
  }
  let y = simpmap(cdr(x), z)
  if l1 == 5 && !(eq(cadddr(y), q_d_plus) || eq(cadddr(y), q_d_minus)) {
    merr("limit: direction must be either 'plus' or 'minus': ~M", [cadddr(y)])
  } else if mnump(cadr(y)).truthy() {
    merr("limit: variable must not be a number; found: ~M", [cadr(y)])
  } else if equal(car(y), Fix(1L)) {
    Fix(1L)
  } else {
    eqtest(cons(list1(q_p_limit), y), x)
  }
}

///|
fn simpinteg(x : Value, vestigial : Value, z : Value) -> Value raise {
  ignore(vestigial)
  let mut z = z
  let l1 = length(x)
  if !(l1 == 3 || l1 == 5) {
    merr("integrate: wrong number of arguments.", []) |> ignore
  }
  let y = simpmap(cdr(x), z)
  if mnump(cadr(y)).truthy() {
    return merr("integrate: variable must not be a number; found: ~M", [cadr(y)])
  }
  if l1 == 5 && alike1(caddr(y), cadddr(y)).truthy() {
    return Fix(0L)
  }
  if l1 == 5 &&
    {
      z = sub(cadddr(y), caddr(y))
      free(z, q_d__pcti).truthy()
    } &&
    eq(d_sign(z), q_d_neg) {
    return neg(
      simplifya(
        list([list1(q_p_integrate), car(y), cadr(y), cadddr(y), caddr(y)]),
        t,
      ),
    )
  }
  if equal(car(y), Fix(1L)) {
    if l1 == 3 {
      cadr(y)
    } else if among(q_d_inf, z).truthy() || among(q_d_minf, z).truthy() {
      infsimp(z)
    } else {
      z
    }
  } else {
    eqtest(cons(list1(q_p_integrate), y), x)
  }
}

///|
fn simpbigfloat(x : Value, vestigial : Value, simp_flag : Value) -> Value raise {
  ignore(vestigial)
  ignore(simp_flag)
  bigfloatm_star(x)
}

///|
/// Implementation of the Exp function.
fn simp_exp(x : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(x) |> ignore
  let arg = if z.truthy() { cadr(x) } else { simplifya(cadr(x), Nil) }
  simplifya(list3(list1(q_mexpt), q_d__pcte, arg), t)
}

///|
fn simplambda(x : Value, vestigial : Value, simp_flag : Value) -> Value raise {
  ignore(vestigial)
  ignore(simp_flag)
  // Check for malformed lambda expressions.
  // We verify that we have a valid list of parameters and a non-empty body.
  let params = cadr(x)
  if !d_listp(params).truthy() {
    merr("lambda: first argument must be a list; found: ~M", [params]) |> ignore
  }
  let mut params = cdr(params)
  let mut seen_params : Value = Nil
  while !(params is Nil) {
    if mdeflistp(params).truthy() {
      params = cdar(params)
    }
    let mut p = car(params)
    if !(
        mdefparam(p).truthy() ||
        (op_equalp(p, q_mquote).truthy() && mdefparam(cadr(p)).truthy())
      ) {
      merr(
        "lambda: parameter must be a symbol and must not be a system constant; found: ~M",
        [p],
      )
      |> ignore
    }
    p = mparam(p)
    if memq(p, seen_params).truthy() {
      merr("lambda: ~M occurs more than once in the parameter list", [p])
      |> ignore
    }
    seen_params = cons(p, seen_params)
    params = cdr(params)
  }
  if cddr(x) is Nil {
    merr("lambda: no body present", []) |> ignore
  }
  cons(list2(q_lambda, q_simp), cdr(x))
}

///|
fn simpmdef(x : Value, vestigial : Value, simp_flag : Value) -> Value raise {
  ignore(vestigial)
  ignore(simp_flag)
  twoargcheck(x) |> ignore
  cons(list2(q_mdefine, q_simp), cdr(x))
}

///|
fn simpmap(e : Value, z : Value) -> Value raise {
  mapcar(u => simpcheck(u, z), e)
}

///|
fn infsimp(e : Value) -> Value raise {
  let x = d_expand(e, expop=Fix(1L), expon=Fix(1L))
  if !free(x, q_d_ind).truthy() ||
    !free(x, q_d_und).truthy() ||
    !free(x, q_d_zeroa).truthy() ||
    !free(x, q_d_zerob).truthy() ||
    !free(x, q_d_infinity).truthy() ||
    mbagp(x).truthy() {
    infsimp2(x, e)
  } else if free(x, q_d_inf).truthy() && free(x, q_d_minf).truthy() {
    x
  } else {
    infsimp1(x, e)
  }
}

///|
fn infsimp1(x : Value, e : Value) -> Value raise {
  let minf_coef = coeff(x, q_d_minf, Fix(1L))
  let inf_coef = coeff(x, q_d_inf, Fix(1L))
  if (equal(minf_coef, Fix(0L)) && equal(inf_coef, Fix(0L))) ||
    (!free(minf_coef, q_d_inf).truthy() && !free(inf_coef, q_d_minf).truthy()) ||
    {
      let new_exp = sub(
        add2(mul2(minf_coef, q_d_minf), mul2(inf_coef, q_d_inf)),
        x,
      )
      !free(new_exp, q_d_inf).truthy() || !free(new_exp, q_d_minf).truthy()
    } {
    infsimp2(x, e)
  } else {
    let sign_minf_coef = d_asksign(minf_coef)
    let sign_inf_coef = d_asksign(inf_coef)
    let i_zero = eq(sign_inf_coef, q_d_zero)
    let i_pos = eq(sign_inf_coef, q_d_pos)
    let i_neg = eq(sign_inf_coef, q_d_neg)
    let m_zero = eq(sign_minf_coef, q_d_zero)
    let m_pos = eq(sign_minf_coef, q_d_pos)
    let m_neg = eq(sign_minf_coef, q_d_neg)
    if (i_zero && m_neg) || (i_pos && m_zero) || (i_pos && m_neg) {
      q_d_inf
    } else if (i_zero && m_pos) || (i_neg && m_zero) || (i_neg && m_pos) {
      q_d_minf
    } else if (i_pos && m_pos) || (i_neg && m_neg) {
      q_d_und
    } else {
      Nil
    }
  }
}

///|
fn infsimp2(x : Value, e : Value) -> Value raise {
  let x = d_limit(list1(x))
  if isinop(x, q_p_limit).truthy() {
    e
  } else {
    x
  }
}

///|
fn simpderiv(x : Value, y : Value, z : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut z = z
  let mut flag = false
  if length(x) % 2 != 0 {
    if !(cdr(x) is Nil) && cdddr(x) is Nil {
      x = append(x, list1(Fix(1L)))
    } else {
      wna_err(q_p_derivative) |> ignore
    }
  }
  let w = cons(list1(q_p_derivative), simpmap(cdr(x), z))
  y = cadr(w)
  let mut u = cddr(w)
  while !(u is Nil) {
    if mnump(car(u)).truthy() {
      merr("diff: variable must not be a number; found: ~M", [car(u)]) |> ignore
    }
    u = cddr(u)
  }
  if zerop1(y).truthy() ||
    (
      (mnump(y).truthy() || (atom(y) && constant(y).truthy())) &&
      (
        cddr(w) is Nil ||
        (
          !alike1(y, caddr(w)).truthy() &&
          {
            let mut found = false
            let mut u = cddr(w)
            while !(u is Nil) {
              if numberp(cadr(u)) && !zerop(cadr(u)) {
                found = true
                break
              }
              u = cddr(u)
            }
            found
          }
        )
      )
    ) {
    return Fix(0L)
  } else if !atom(y) &&
    eq(caar(y), q_p_derivative) &&
    symval(q_derivsimp).truthy() {
    rplacd(w, append(cdr(y), cddr(w))) |> ignore
  }
  if cddr(w) is Nil {
    return if symval(q_derivflag) is Nil {
      list2(list2(q_p_del, q_simp), y)
    } else {
      deriv(cdr(w))
    }
  }
  u = cdr(w)
  // ztest
  while !(u is Nil) {
    if zerop1(caddr(u)).truthy() {
      rplacd(u, cdddr(u)) |> ignore
    } else {
      u = cddr(u)
    }
  }
  // next
  if cddr(w) is Nil {
    return y
  } else if cddddr(w) is Nil &&
    onep(cadddr(w)).truthy() &&
    alike1(cadr(w), caddr(w)).truthy() {
    return Fix(1L)
  }
  while true {
    // again
    z = cddr(w)
    // sort
    while true {
      if cddr(z) is Nil {
        break
      } else if alike1(car(z), caddr(z)).truthy() {
        rplaca(cdddr(z), add2(cadr(z), cadddr(z))) |> ignore
        rplacd(z, cdddr(z)) |> ignore
      } else if great(car(z), caddr(z)).truthy() {
        let u1 = car(z)
        let u2 = cadr(z)
        let v1 = caddr(z)
        let v2 = cadddr(z)
        flag = true
        rplaca(z, v1) |> ignore
        rplacd(z, cons(v2, cons(u1, cons(u2, cddddr(z))))) |> ignore
      }
      z = cddr(z)
      if z is Nil {
        break
      }
    }
    // loop
    if !flag {
      return if symval(q_derivflag) is Nil {
        eqtest(w, x)
      } else {
        deriv(cdr(w))
      }
    }
    flag = false
  }
  Nil
}

///|
fn signum1(x : Value) -> Value raise {
  if mnump(x).truthy() {
    let x = num1(x)
    if plusp(x) {
      Fix(1L)
    } else if minusp(x) {
      Fix(-1L)
    } else {
      Fix(0L)
    }
  } else if atom(x) {
    Fix(1L)
  } else if mplusp(x).truthy() {
    if symval(q_ear_expandp).truthy() {
      Fix(1L)
    } else {
      signum1(car(last(x)))
    }
  } else if mtimesp(x).truthy() {
    if mplusp(cadr(x)).truthy() {
      Fix(1L)
    } else {
      signum1(cadr(x))
    }
  } else {
    Fix(1L)
  }
}

///|
fn simp__take_signum(s : Value) -> Value raise {
  take(list1(q_p_signum), [s])
}

///|
/// def-simplifier signum (x)
fn simp__pctsignum(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(q_p_signum), q_d_x),
    )
    |> ignore
  }
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  if complex_number_p(x, ntypep=q_mnump).truthy() {
    return if complex_number_p(x, ntypep=q_d_ratnump).truthy() {
      // nonfloat complex
      if zerop1(x).truthy() {
        Fix(0L)
      } else {
        d_rectform(div(x, ftake(q_p_cabs, [x])))
      }
    } else {
      funcall(q_to, [funcall(simp__q_bf_signum, [bf_to(x)])])
    }
  }
  // idempotent: signum(signum(z)) = signum(z).
  if x is Cons({ car: Cons(_), .. }) && eq(q_p_signum, mop(x)) {
    return x
  }
  // Let's catch errors from $csign. Doing so allows signum(ind) to return a
  // signum nounform, for example.
  let sgn = with_specials(
    [(q_d_errormsg, Nil), (q_errcatch, t), (q_errset, Nil)],
    () => match errset(() => d_csign(x)) {
      Some(v) => v
      None => Nil
    },
  )
  if eq(sgn, q_d_neg) {
    Fix(-1L)
  } else if eq(sgn, q_d_zero) {
    Fix(0L)
  } else if eq(sgn, q_d_pos) {
    Fix(1L)
  } else if mtimesp(x).truthy() {
    // multiplicative: signum(ab) = signum(a) * signum(b).
    muln(mapcar(s => simp__take_signum(s), margs(x)), t)
  } else if great(neg(x), x).truthy() {
    // Reflection rule: signum(-x) --> -signum(x).
    neg(simp__take_signum(neg(x)))
  } else if mexptp(x).truthy() &&
    apparently_real_to_judge_by__dolcsign_p(caddr(x)).truthy() {
    // signum(z^real) = signum(z)^real
    power(ftake(q_p_signum, [cadr(x)]), caddr(x))
  } else {
    // nounform return
    eqtest(cons(list1(q_p_signum), list1(x)), form)
  }
}

///|
/// `(equal r2 (float (floor r2)))` for a float R2
fn simp__float_integral_p(r2 : Value) -> Bool raise {
  equal(r2, lfloat(floor1(r2)))
}

///|
fn exptrl(r1 : Value, r2 : Value) -> Value raise {
  if equal(r2, Fix(1L)) {
    return r1
  }
  if equal(r2, Flo(1.0)) {
    return if mnump(r1).truthy() {
      addk(Flo(0.0), r1)
    } else {
      // Do not simplify the type of the number away.
      list3(list2(q_mexpt, q_simp), r1, Flo(1.0))
    }
  }
  if equal(r2, symval(q_ear_bigfloatone)) {
    return if mnump(r1).truthy() {
      d_bfloat(r1)
    } else {
      // Do not simplify the type of the number away.
      list3(list2(q_mexpt, q_simp), r1, symval(q_ear_bigfloatone))
    }
  }
  if zerop1(r1).truthy() {
    return if zerop1(r2).truthy() || mnegp(r2).truthy() {
      if !symval(q_errorsw).truthy() {
        merr("expt: undefined: ~M", [list3(list1(q_mexpt), r1, r2)])
      } else {
        throw_tag(q_errorsw, t)
      }
    } else {
      zerores(r1, r2)
    }
  }
  if zerop1(r2).truthy() || onep1(r1).truthy() {
    return if d_bfloatp(r1).truthy() || d_bfloatp(r2).truthy() {
      symval(q_ear_bigfloatone)
    } else if floatp(r1) || floatp(r2) {
      Flo(1.0)
    } else {
      Fix(1L)
    }
  }
  if d_bfloatp(r1).truthy() || d_bfloatp(r2).truthy() {
    return d_bfloat(mk(q_mexpt, [r1, r2]))
  }
  if numberp(r1) && integerp(r2) {
    return exptb(r1, r2)
  }
  if numberp(r1) && floatp(r2) && simp__float_integral_p(r2) {
    return exptb(lfloat(r1), floor1(r2))
  }
  if ratnump(r1).truthy() && floatp(r2) && simp__float_integral_p(r2) {
    return exptb(fpcofrat(r1), floor1(r2))
  }
  if symval(q_d_numer).truthy() ||
    (
      floatp(r2) &&
      (plusp(num1(r1)) || symval(q_d_numer_pbranch).truthy())
    ) {
    let mut r1 = addk(Flo(0.0), r1)
    let mut r2 = r2
    if minusp(r1) {
      if symval(q_d_numer_pbranch).truthy() ||
        eq(symval(q_d_domain), q_d_complex) {
        // for R1<0:
        // R1^R2 = (-R1)^R2*cos(pi*R2) + i*(-R1)^R2*sin(pi*R2)
        r2 = addk(Flo(0.0), r2)
        let y = exptrl(num_neg(r1), r2)
        r2 = num_mul(mget(q_d__pctpi, q_d_numer), r2)
        return add2(
          num_mul(y, lcos(r2)),
          list3(list2(q_mtimes, q_simp), num_mul(y, lsin(r2)), q_d__pcti),
        )
      } else {
        let y = with_specials(
          [(q_d_numer, Nil), (q_d_float, Nil), (q_d_keepfloat, Nil), (q_d_ratprint, Nil)],
          () => power(Fix(-1L), r2),
        )
        return mul2(y, exptrl(num_neg(r1), r2))
      }
    }
    r2 = addk(Flo(0.0), r2)
    if equal(r2, lfloat(floor1(r2))) {
      return exptb(r1, floor1(r2))
    }
    let y = num_mul(Flo(2.0), r2)
    if equal(y, lfloat(floor1(y))) && !equal(r1, symval(q_p_e_val)) {
      return exptb(lsqrt(r1), floor1(y))
    }
    return lexp(num_mul(r2, llog(r1)))
  }
  if floatp(r2) {
    return list3(list2(q_mexpt, q_simp), r1, r2)
  }
  if integerp(r2) {
    return if minusp(r2) {
      exptrl(
        if equal(num_abs(cadr(r1)), Fix(1L)) {
          num_mul(cadr(r1), caddr(r1))
        } else if minusp(cadr(r1)) {
          // We set the simp flag at this place. This
          // changes nothing for an exponent r2 # -1.
          list3(list2(q_rat, q_simp), num_neg(caddr(r1)), num_neg(cadr(r1)))
        } else {
          list3(list2(q_rat, q_simp), caddr(r1), cadr(r1))
        },
        num_neg(r2),
      )
    } else {
      list3(list2(q_rat, q_simp), exptb(cadr(r1), r2), exptb(caddr(r1), r2))
    }
  }
  if floatp(r1) && alike1(r2, mk(q_rat, [Fix(1L), Fix(2L)])).truthy() {
    return if minusp(r1) {
      list3(list2(q_mtimes, q_simp), lsqrt(num_neg(r1)), q_d__pcti)
    } else {
      lsqrt(r1)
    }
  }
  if floatp(r1) && alike1(r2, mk(q_rat, [Fix(-1L), Fix(2L)])).truthy() {
    return if minusp(r1) {
      list3(
        list2(q_mtimes, q_simp),
        num_div(Flo(-1.0), lsqrt(num_neg(r1))),
        q_d__pcti,
      )
    } else {
      num_div(Fix(1L), lsqrt(r1))
    }
  }
  if floatp(r1) {
    return if plusp(r1) {
      exptrl(r1, fpcofrat(r2))
    } else {
      // (-4.5)^(1/4) -> (4.5)^(1/4) * (-1)^(1/4)
      mul2(exptrl(Fix(-1L), r2), exptrl(num_neg(r1), r2))
    }
  }
  if symval(q_ear_exptrlsw).truthy() {
    return list3(list2(q_mexpt, q_simp), r1, r2)
  }
  with_special(q_ear_exptrlsw, t, () => {
    let a = exptrl(r1, num_truncate(cadr(r2), b=caddr(r2)).0)
    let y = with_specials([(q_d_keepfloat, Nil), (q_d_ratprint, Nil)], () => simpnrt(
      r1,
      caddr(r2),
    ))
    let z = num_rem(cadr(r2), caddr(r2))
    let b = if mexptp(y).truthy() {
      list3(car(y), cadr(y), mul2(caddr(y), z))
    } else {
      power(y, z)
    }
    simptimes(list3(list1(q_mtimes), a, b), Fix(1L), t)
  })
}
