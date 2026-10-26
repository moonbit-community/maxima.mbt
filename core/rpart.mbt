// Port of src/rpart.lisp: complex variable utilities.
//
// Macsyma functions: $realpart $imagpart $rectform $polarform $cabs $carg
// Utility functions: trisplit risplit absarg cabs

///|
/// The argument-count check and argument fetching of DEF-SIMPLIFIER.
fn rpart__simp_arg(
  form : Value,
  noun : Value,
  argname : Value,
  z : Value,
) -> Value raise {
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(noun), argname),
    )
    |> ignore
  }
  simpcheck(nth(1, form), z)
}

///|
/// WITH-DEFAULT-QUOTIENT-DISPFLAGS around NUM-DENOM-SPLIT.
fn rpart__num_denom_split(e : Value) -> (Value, Value) raise {
  with_specials(
    [
      (q_d_exptdispflag, t),
      (q_d_pfeformat, Nil),
      (q_d__pctedispflag, Nil),
    ],
    () => num_denom_split(e),
  )
}

///|
/// `(let ((sign-imag-errp nil)) (catch 'sign-imag-err ($sign x)))`
fn rpart__sign_catch(x : Value) -> Value raise {
  with_special(q_sign_imag_errp, Nil, () => catch_tag(q_sign_imag_err, () => d_sign(
    x,
  )))
}

///|
/// T if a real base raised to POW is the real root: With domain : real, the
/// simplifier and SIGN take the real root for a rational POW with an odd
/// denominator, as in (-8)^(1/3) = -2. SIGN-MEXPT does so for a symbolic
/// POW too, as 1/(2*n+1) for an integer n, if its numerator is an integer.
fn odd_root_exponent_p(pow : Value) -> Value raise {
  let dom = {
    let d = symval(q_ear_risplit_domain)
    if d.truthy() {
      d
    } else {
      symval(q_d_domain)
    }
  }
  if eq(dom, q_d_complex) {
    return Nil
  }
  if ratnump(pow).truthy() {
    lbool(oddp(caddr(pow)))
  } else if mnump(pow).truthy() {
    Nil
  } else {
    let (num, denom) = rpart__num_denom_split(pow)
    if !eql(denom, Fix(1L)) && eq(evod(denom), q_d_odd) {
      let v = evod(num)
      if v.truthy() {
        v
      } else {
        maxima_integerp(num)
      }
    } else {
      Nil
    }
  }
}

///|
/// rectangular form for a signum expression
fn risplit_signum(x : Value) -> Value raise {
  // signum(a+%i b), where a and b are real
  let z = risplit(cadr(x))
  let a = car(z)
  let b = cdr(z)
  if eq(t, meqp(b, Fix(0L))) {
    // signum(a) -> signum(a) + 0 %i
    cons(take(list1(q_p_signum), [a]), Fix(0L))
  } else if eq(t, mnqp(a, Fix(0L))) || eq(t, mnqp(b, Fix(0L))) {
    // signum(a + %i b) --> a/sqrt(a^2+b^2) + %i b/sqrt(a^2+b^2)
    let r = take(list1(q_p_sqrt), [
      add2(power(a, Fix(2L)), power(b, Fix(2L))),
    ])
    cons(div(a, r), div(b, r))
  } else {
    // nothing known
    cons(take(list1(q_p_realpart), [x]), take(list1(q_p_imagpart), [x]))
  }
}

///|
/// Realpart gives the real part of an expr.
fn d_realpart(xx : Value) -> Value raise {
  car(trisplit(xx))
}

///|
fn simp__pctrealpart(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = rpart__simp_arg(form, q_p_realpart, q_d_z, p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_realpart), list1(z)), form)
  if mnump(z).truthy() {
    z
  } else {
    let sgn = d_csign(z)
    if eq(sgn, q_d_imaginary) {
      Fix(0L)
    } else if eq(sgn, q_d_complex) {
      let z_expanded = d_expand(z)
      if complex_number_p(z_expanded, ntypep=q_bigfloat_or_number_p).truthy() {
        d_realpart(z_expanded)
      } else {
        give_up()
      }
    } else {
      give_up()
    }
  }
}

///|
/// Imagpart gives the imaginary part of an expr.
fn d_imagpart(xx : Value) -> Value raise {
  cdr(trisplit(xx))
}

///|
fn simp__pctimagpart(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = rpart__simp_arg(form, q_p_imagpart, q_d_z, p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_imagpart), list1(z)), form)
  if mnump(z).truthy() {
    Fix(0L)
  } else {
    let sgn = d_csign(z)
    if eq(sgn, q_d_imaginary) {
      muln_([Fix(-1L), q_d__pcti, z])
    } else if eq(sgn, q_d_complex) {
      let z_expanded = d_expand(z)
      if complex_number_p(z_expanded, ntypep=q_bigfloat_or_number_p).truthy() {
        d_imagpart(z_expanded)
      } else {
        give_up()
      }
    } else {
      give_up()
    }
  }
}

///|
/// Rectform gives a result of the form a+b*%i.
fn d_rectform(xx : Value) -> Value raise {
  let ris = trisplit(xx)
  add2(car(ris), mul2(cdr(ris), q_d__pcti))
}

///|
/// Return real and imaginary part of E as a list.  Equivalent to
/// [realpart(x), imagpart(x)], but more efficient.
fn d_real_imag_part(e : Value) -> Value raise {
  let ri = trisplit(e)
  list([list2(q_mlist, q_simp), car(ri), cdr(ri)])
}

///|
/// Polarform gives a result of the form a*%e^(%i*b).
fn d_polarform(xx : Value) -> Value raise {
  if mbagp(xx).truthy() {
    cons(car(xx), mapcar(x => d_polarform(x), cdr(xx)))
  } else {
    let aas = absarg(xx)
    with_special(q_d__pctemode, Nil, () => mul2(
      car(aas),
      powers(q_d__pcte, mul2(q_d__pcti, cdr(aas))),
    ))
  }
}

///|
/// Cabs gives the complex absolute value.  Nota bene: an expression may be
/// syntactically real without being real (e.g. sqrt(x), x<0).  Thus Cabs
/// must lead an independent existence from Abs.  This is the internal
/// cabs, used by other Macsyma programs.
fn cabs(xx : Value) -> Value raise {
  car(absarg(xx, absflag=t))
}

///|
fn simp__pctcabs(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = rpart__simp_arg(form, q_p_cabs, q_d_z, p__pctsimpflag)
  if is_op(z, q_mabs) {
    // cabs(abs(x)) = cabs(x)
    ftake(q_p_cabs, [cadr(z)])
  } else {
    let sgn = d_csign(z)
    if eq(sgn, q_d_complex) || eq(sgn, q_d_imaginary) {
      cabs(z)
    } else if eq(sgn, q_d_zero) {
      Fix(0L)
    } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) {
      z
    } else if eq(sgn, q_d_neg) {
      mul2(Fix(-1L), z)
    } else {
      cabs(z)
    }
  }
}

///|
fn rpart__carg(xx : Value) -> Value raise {
  if mbagp(xx).truthy() {
    cons(car(xx), mapcar(x => rpart__carg(x), cdr(xx)))
  } else {
    cdr(absarg(xx))
  }
}

///|
/// Carg gives the complex argument.
fn simp__pctcarg(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  let z = rpart__simp_arg(form, q_p_carg, q_d_z, p__pctsimpflag)
  if eq(z, q_d__pcti) {
    div(q_d__pctpi, Fix(2L))
  } else {
    let sgn = d_csign(z)
    if eq(sgn, q_d_complex) || eq(sgn, q_d_imaginary) {
      rpart__carg(z)
    } else if eq(sgn, q_d_pos) || eq(sgn, q_d_pz) || eq(sgn, q_d_zero) {
      Fix(0L)
    } else if eq(sgn, q_d_neg) {
      q_d__pctpi
    } else if eq(sgn, q_d_pnz) {
      rpart__carg(z)
    } else {
      eqtest(cons(list1(q_p_carg), list1(z)), form)
    }
  }
}

///|
/// Some objects can only appear at the top level of a legal simplified
/// expression: CRE forms and equations in particular.  Top level of
/// risplit.
fn trisplit(el : Value) -> Value raise {
  if atom(el) {
    risplit(el)
  } else if specrepp(el).truthy() {
    trisplit(specdisrep(el))
  } else if eq(caar(el), q_mequal) {
    dot_sp_ri(cdr(el), list2(q_mequal, q_simp))
  } else {
    risplit(el)
  }
}

// Auxiliaries: Macsyma equivalents to (mapcar 'trisplit ...).  The lists are
// Macsyma lists, and the results must be separated: ((a . b) (c . d))
// becomes something like ([a,c].[b,d]).

///|
fn dsrl(el : Value) -> Value raise {
  dot_sp_ri(cdr(el), list2(q_mlist, q_simp))
}

///|
fn dot_sp_ri(el : Value, ind : Value) -> Value raise {
  dot__ri(mapcar(x => trisplit(x), el), ind)
}

///|
/// Dot--ri does the ((a.b)(c.d))->([a,c].[b,d]) transformation with
/// minimal Cons'ing.
fn dot__ri(el : Value, ind : Value) -> Value raise {
  let mut i = el
  let mut k = Value::Nil
  while i.truthy() {
    let cdari = cdar(i)
    k = rplacd(car(i), k)
    rplaca(i, cdari) |> ignore
    i = cdr(i)
  }
  cons(cons(ind, nreverse(k)), cons(ind, el))
}

///|
fn risplit_mplus(l : Value) -> Value raise {
  let mut rpart = Value::Nil
  let mut ipart = Value::Nil
  for m in cdr(l).iter() {
    let sp = risplit(m)
    if !eq0(car(sp)) {
      rpart = cons(car(sp), rpart)
    }
    if !eq0(cdr(sp)) {
      ipart = cons(cdr(sp), ipart)
    }
  }
  cons(addn(rpart, t), addn(ipart, t))
}

///|
fn risplit_times(l : Value) -> Value raise {
  let mut purerl = Value::Nil
  let mut compl = Value::Nil
  for f in cdr(l).iter() {
    let sp = risplit(f)
    if eq0(cdr(sp)) {
      purerl = rplacd(sp, purerl)
    } else if atom(car(sp)) || atom(cdr(sp)) {
      compl = cons(sp, compl)
    } else if eq(caaar(sp), q_mtimes) &&
      // Try risplit z/w and notice denominator.  If this check were not
      // made, the real and imaginary parts would not each be over a common
      // denominator.
      eq(caadr(sp), q_mtimes) &&
      {
        let mut nr = nreverse(cdar(sp))
        let mut ni = nreverse(cddr(sp))
        if equal(car(nr), car(ni)) {
          purerl = cons(car(nr), purerl)
          compl = cons(
            cons(muln(nreverse(cdr(nr)), t), muln(nreverse(cdr(ni)), t)),
            compl,
          )
          true
        } else {
          nr = nreverse(nr)
          ni = nreverse(ni)
          ignore(nr)
          ignore(ni)
          false
        }
      } {
      ()
    } else {
      compl = cons(sp, compl)
    }
  }
  if compl is Nil {
    cons(muln(purerl, t), Fix(0L))
  } else {
    let mut rpart : Value = Fix(1L)
    let mut ipart : Value = Fix(0L)
    for m in compl.iter() {
      let r = sub(mul2(rpart, car(m)), mul2(ipart, cdr(m)))
      let i = add2(mul2(ipart, car(m)), mul2(rpart, cdr(m)))
      rpart = r
      ipart = i
    }
    cons(
      if eq0(rpart) {
        Fix(0L)
      } else {
        muln(cons(rpart, purerl), t)
      },
      if eq0(ipart) {
        Fix(0L)
      } else {
        muln(cons(ipart, purerl), t)
      },
    )
  }
}

///|
/// Split L = ((mexpt) BASE POW) into real and imaginary parts.
fn risplit_expt(l : Value) -> Value raise {
  let base = cadr(l)
  let pow = caddr(l)
  // Disable 'simplifications' like sqrt(-x) -> %i*sqrt(x)
  with_special(q_d_radexpand, Nil, () => {
    let sp = risplit(base)
    if fixnump(pow) {
      risplit_expt_fixnum_pow(sp, pow)
    } else if eq0(cdr(sp)) && odd_root_exponent_p(pow).truthy() {
      // The real root of a real BASE, see ODD-ROOT-EXPONENT-P. Take it of
      // the real part of BASE, as BASE itself can contain %i, and simplify
      // it in the domain outside of RISPLIT.
      let dom = {
        let d = symval(q_ear_risplit_domain)
        if d.truthy() {
          d
        } else {
          symval(q_d_domain)
        }
      }
      cons(with_special(q_d_domain, dom, () => power(car(sp), pow)), Fix(0L))
    } else if ratnump(pow).truthy() &&
      fixnump(cadr(pow)) &&
      !num_lt(cadr(pow), num_neg(symval(q_d_maxnegex))) &&
      !num_gt(cadr(pow), symval(q_d_maxposex)) &&
      (num_eq(caddr(pow), Fix(2L)) || eq0(cdr(sp))) {
      if eq0(cdr(sp)) {
        risplit_expt_real_hatrat(base, pow)
      } else {
        risplit_expt_sqrt_pow(base, sp, pow)
      }
    } else if (floatp(pow) || d_bfloatp(pow).truthy()) &&
      spcomplexnump(sp).truthy() {
      risplit_expt_inexact_pow(sp, pow)
    } else if floatp(base) && floatp(pow) {
      risplit(with_special(q_d_numer, t, () => exptrl(base, pow)))
    } else {
      let ab = risplit(pow)
      let rt = absarg1(base)
      risplit_expt_general_form(car(rt), cdr(rt), car(ab), cdr(ab))
    }
  })
}

///|
/// Split BASE^POWER into real and imaginary parts. POWER is assumed to be a
/// fixnum. SP is (RISPLIT BASE)
fn risplit_expt_fixnum_pow(sp : Value, power_ : Value) -> Value raise {
  // We use the squared absolute value of BASE several times below; it is
  // calculated when it's needed (a maximum of once) to avoid floating point
  // under/overflows.
  let real = car(sp)
  let imag = cdr(sp)
  if minusp(power_) && zerop1(real).truthy() && zerop1(imag).truthy() {
    // Signal the simplifier's error for 0 to a negative power.
    cons(power(real, power_), Fix(0L))
  } else if num_eq(power_, Fix(-1L)) {
    // Handle the case of 1/(x+%i*y) carefully.  This is needed if x and y
    // are (Lisp) numbers to prevent spurious underflows/overflows. See bug
    // 1908.
    if (numberp(real) || ratnump(real).truthy()) &&
      (numberp(imag) || ratnump(imag).truthy()) {
      sprecip(sp)
    } else {
      let abs2 = spabs(sp)
      cons(div(real, abs2), mul2(Fix(-1L), div(imag, abs2)))
    }
  } else if num_gt(num_abs(power_), symval(q_d_maxposex)) &&
    !spinexactp(sp).truthy() {
    if eq0(imag) {
      cons(powers(real, power_), Fix(0L))
    } else {
      let abs_hatn = powers(spabs(sp), n_starred(power_, Fix(2L)))
      let natan = mul2(power_, genatan(imag, real))
      cons(
        mul2(abs_hatn, take(list1(q_p_cos), [natan])),
        mul2(abs_hatn, take(list1(q_p_sin), [natan])),
      )
    }
  } else if plusp(power_) {
    spintexpt(sp, power_)
  } else {
    let abbas = powers(spabs(sp), num_neg(power_))
    let basspli = spintexpt(sp, num_neg(power_))
    cons(div(car(basspli), abbas), neg(div(cdr(basspli), abbas)))
  }
}

///|
/// Return the "general form" for RISPLIT applied to
/// (r*exp(%i*theta))^(alpha+%i*beta), whose rectform is
///   pre * cos(post) + %i * pre * sin(post)
/// where pre  = exp(-theta*beta) * r^alpha
/// and   post = beta*log(r) + alpha*theta
fn risplit_expt_general_form(
  r : Value,
  theta : Value,
  alpha : Value,
  beta : Value,
) -> Value raise {
  let pre = mul2(
    powers(q_d__pcte, muln_([Fix(-1L), theta, beta])),
    powers(r, alpha),
  )
  let post = add2(
    mul2(beta, take(list1(q_p_log), [r])),
    mul2(alpha, theta),
  )
  cons(
    mul2(pre, take(list1(q_p_cos), [post])),
    mul2(pre, take(list1(q_p_sin), [post])),
  )
}

///|
/// Split BASE^POW into real and imaginary parts. SP is (RISPLIT BASE) and
/// is assumed to be a complex number, POW is assumed to be a float or a
/// bigfloat.
fn risplit_expt_inexact_pow(sp0 : Value, pow : Value) -> Value raise {
  let sp = if d_bfloatp(car(sp0)).truthy() ||
    d_bfloatp(cdr(sp0)).truthy() ||
    d_bfloatp(pow).truthy() {
    cons(d_bfloat(car(sp0)), d_bfloat(cdr(sp0)))
  } else {
    cons(d_float(car(sp0)), d_float(cdr(sp0)))
  }
  let n = integer_representation_p(pow)
  if n.truthy() {
    // BASE^POW is the integer power BASE^N, whose argument is N times the
    // argument of BASE.  Multiplying that out spends the leading digits of
    // the product on a multiple of 2*%pi, so raise BASE to the N instead.
    risplit_expt_fixnum_pow(sp, n)
  } else {
    let rt = absarg1(add2(car(sp), mul2(q_d__pcti, cdr(sp))))
    risplit_expt_general_form(car(rt), cdr(rt), pow, Fix(0L))
  }
}

///|
/// Split BASE^POWER into real and imaginary parts. We assume that BASE is
/// real and that POWER is a rational number.
fn risplit_expt_real_hatrat(base : Value, power_ : Value) -> Value raise {
  let s = if mnegp(base).truthy() {
    q_d_neg
  } else if symval(q_implicit_real).truthy() {
    q_d_pos
  } else {
    // BASE is real, but can contain %i, as %i*erf(%i) does.  Use $sign not
    // asksign.
    rpart__sign_catch(base)
  }
  if eq(s, q_d_neg) {
    risplit_expt_general_form(neg(base), q_d__pctpi, power_, Fix(0L))
  } else if eq(s, q_d_zero) {
    cons(power(Fix(0L), power_), Fix(0L))
  } else if eq(s, q_d_pos) {
    cons(power(base, power_), Fix(0L))
  } else {
    let rt = absarg1(base)
    risplit_expt_general_form(car(rt), cdr(rt), power_, Fix(0L))
  }
}

///|
/// Split BASE^POWER into real and imaginary parts. SP is (RISPLIT BASE). We
/// assume that POWER is a rational number. Moreover, we assume that the
/// denominator of POWER is 2.
fn risplit_expt_sqrt_pow(base : Value, sp : Value, power_ : Value) -> Value raise {
  // n = abs(2*power) is a non-negative integer
  let real = car(sp)
  let imag = cdr(sp)
  let half = symval(q_n1_sl_sl2)
  let abs2 = spabs(sp)
  let abs = power(abs2, half)
  let n = num_abs(cadr(power_))
  let pos_q = num_gt(cadr(power_), Fix(-1L))
  // IMAG is real, but can contain %i, as %i*(1-erfc(%i)) for erfc(%i)
  // does.
  let imag_sign = rpart__sign_catch(imag)
  if eq(imag_sign, q_d_neg) || eq(imag_sign, q_d_pos) {
    // Here, we use the half-angle formulas for cos and sin:
    //   sqrt(real+%i*imag) = (sqrt(abs+real) + %i*sqrt(abs-real))/sqrt(2)
    // but possibly with signs on the square roots. This function always
    // chooses the square root with the non-negative real part.
    divcarcdr(
      spintexpt(
        cons(
          power(add2(abs, real), half),
          porm(
            lbool(eq(imag_sign, q_d_pos) == pos_q),
            power(sub(abs, real), half),
          ),
        ),
        n,
      ),
      if pos_q {
        power(Fix(2L), div(n, Fix(2L)))
      } else {
        power(mul2(Fix(2L), abs2), div(n, Fix(2L)))
      },
    )
  } else {
    let ab = risplit(power_)
    let rt = absarg1(base)
    risplit_expt_general_form(car(rt), cdr(rt), car(ab), cdr(ab))
  }
}

///|
fn risplit_noun(l : Value) -> Value raise {
  cons(
    simplify(list2(list1(q_p_realpart), l)),
    simplify(list2(list1(q_p_imagpart), l)),
  )
}

///|
fn absarg1(arg0 : Value) -> Value raise {
  with_special(q_d_keepfloat, t, () => {
    let mut arg = arg0
    let mut arg1 = arg0
    if (
        free(arg, q_d__pcti).truthy() ||
        {
          arg1 = sratsimp(arg)
          free(arg1, q_d__pcti).truthy()
        }
      ) &&
      !eq(csign(arg1), t) {
      arg = arg1
      if symval(q_implicit_real).truthy() {
        cons(arg, Fix(0L))
      } else {
        let fact = assume(list([list1(q_d_notequal), arg, Fix(0L)]))
        let r = absarg(arg) catch {
          e => {
            forget(fact) |> ignore
            raise e
          }
        }
        forget(fact) |> ignore
        r
      }
    } else {
      absarg(arg)
    }
  })
}

///|
let rpart__trig_table : Value = try! lread(
  "((%sin %cosh %cos . %sinh) (%cos %cosh %sin . %sinh) (%sinh %cos %cosh . %sin) (%cosh %cos %sinh . %sin))",
)

///|
/// Main function: takes an expression and returns the dotted pair
/// (<Real part> . <imaginary part>).
fn risplit(l : Value) -> Value raise {
  let dom = {
    let d = symval(q_ear_risplit_domain)
    if d.truthy() {
      d
    } else {
      symval(q_d_domain)
    }
  }
  with_specials(
    [
      (q_ear_risplit_domain, dom),
      (q_d_domain, q_d_complex),
      (q_d_m1pbranch, t),
      (q_d_logarc, Nil),
    ],
    () => rpart__risplit1(l),
  )
}

///|
fn rpart__risplit1(l : Value) -> Value raise {
  if atom(l) {
    // Symbols are assumed to represent real values, unless they have been
    // declared to be complex. If they have been declared to be both real
    // and complex, they are taken to be real.
    return if eq(l, q_d__pcti) {
      cons(Fix(0L), Fix(1L))
    } else if eq(l, q_d_infinity) {
      cons(q_d_und, q_d_und)
    } else if decl_complexp(l).truthy() && !decl_realp(l).truthy() {
      risplit_noun(l)
    } else {
      cons(l, Fix(0L))
    }
  }
  let op = caar(l)
  if eq(op, q_rat) {
    return cons(l, Fix(0L))
  }
  if eq(op, q_mplus) {
    return risplit_mplus(l)
  }
  if eq(op, q_mtimes) {
    return risplit_times(l)
  }
  if eq(op, q_mexpt) {
    return risplit_expt(l)
  }
  if eq(op, q_p_log) {
    let aa = absarg1(cadr(l))
    return rplaca(aa, take(list1(q_p_log), [car(aa)]))
  }
  if eq(op, q_bigfloat) {
    // All numbers are real.
    return cons(l, Fix(0L))
  }
  if memq(op, list([q_p_integrate, q_p_derivative, q_p_laplace, q_p_sum])).truthy() &&
    freel(cddr(l), q_d__pcti).truthy() {
    let ris = risplit(cadr(l))
    return cons(
      simplify(cons(ncons(op), cons(car(ris), cddr(l)))),
      simplify(cons(ncons(op), cons(cdr(ris), cddr(l)))),
    )
  }
  if eq(op, q_d_conjugate) {
    return cons(
      simplify(list2(list1(q_p_realpart), cadr(l))),
      mul2(Fix(-1L), simplify(list2(list1(q_p_imagpart), cadr(l)))),
    )
  }
  // This clause handles the very similar trigonometric and hyperbolic
  // functions.  It is driven by the table RPART__TRIG_TABLE.
  let ass = assq(op, rpart__trig_table)
  if ass.truthy() {
    let ri = risplit(cadr(l))
    return if eq0(cdr(ri)) {
      // Pure real case.
      cons(take(list1(car(ass)), [car(ri)]), Fix(0L))
    } else {
      let re = mul2(
        take(list1(car(ass)), [car(ri)]),
        take(list1(cadr(ass)), [cdr(ri)]),
      )
      let negp = eq(op, q_p_cos)
      let im0 = mul2(
        take(list1(caddr(ass)), [car(ri)]),
        take(list1(cdddr(ass)), [cdr(ri)]),
      )
      cons(re, if negp { neg(im0) } else { im0 })
    }
  }
  if eq(op, q_p_tan) || eq(op, q_p_tanh) {
    // The similar tan and tanh cases.
    let sp = risplit(cadr(l))
    return if eq0(cdr(sp)) {
      cons(l, Fix(0L))
    } else {
      let n2rl = mul2(car(sp), Fix(2L))
      let n2im = mul2(cdr(sp), Fix(2L))
      let denom = inv(
        if eq(op, q_p_tan) {
          add2(
            take(list1(q_p_cosh), [n2im]),
            take(list1(q_p_cos), [n2rl]),
          )
        } else {
          add2(
            take(list1(q_p_cos), [n2im]),
            take(list1(q_p_cosh), [n2rl]),
          )
        },
      )
      if eq(op, q_p_tan) {
        cons(
          mul2(take(list1(q_p_sin), [n2rl]), denom),
          mul2(take(list1(q_p_sinh), [n2im]), denom),
        )
      } else {
        cons(
          mul2(take(list1(q_p_sinh), [n2rl]), denom),
          mul2(take(list1(q_p_sin), [n2im]), denom),
        )
      }
    }
  }
  if memq(
      op,
      list([q_p_atan, q_p_csc, q_p_sec, q_p_cot, q_p_csch, q_p_sech, q_p_coth]),
    ).truthy() &&
    eq0(cdr(risplit(cadr(l)))) {
    return cons(l, Fix(0L))
  }
  if eq(op, q_p_cot) || eq(op, q_p_coth) {
    // Split cot(z) and coth(z) directly. Splitting 1/tan(z) and 1/tanh(z)
    // divides by zero where cot(z) or coth(z) is zero.
    let sp = risplit(cadr(l))
    let n2rl = mul2(car(sp), Fix(2L))
    let n2im = mul2(cdr(sp), Fix(2L))
    let denom = if eq(op, q_p_cot) {
      sub(take(list1(q_p_cosh), [n2im]), take(list1(q_p_cos), [n2rl]))
    } else {
      sub(take(list1(q_p_cosh), [n2rl]), take(list1(q_p_cos), [n2im]))
    }
    return if eq(op, q_p_cot) {
      cons(
        div(take(list1(q_p_sin), [n2rl]), denom),
        neg(div(take(list1(q_p_sinh), [n2im]), denom)),
      )
    } else {
      cons(
        div(take(list1(q_p_sinh), [n2rl]), denom),
        neg(div(take(list1(q_p_sin), [n2im]), denom)),
      )
    }
  }
  if eq(op, q_p_atan2) &&
    // SRATSIMP, since the real parts that the conjugate formulas below give
    // can leave an imaginary part like %i*(a-b)/2+%i*(b-a)/2, which is 0,
    // but not literally 0.
    zerop1(
      sratsimp(
        cdr(
          risplit(
            if zerop1(caddr(l)).truthy() {
              cadr(l)
            } else {
              div(cadr(l), caddr(l))
            },
          ),
        ),
      ),
    ).truthy() {
    // Case atan2(y,x) and y/x a real expression, or x = 0 and y real.
    return cons(l, Fix(0L))
  }
  // acoth(0) = -%i*%pi/2, but the simplifier doesn't do this.  It does
  // handle acoth(0.0) and acoth(0b0), so just handle 0 here.
  if eq(op, q_p_acoth) && eql(Fix(0L), cadr(l)) {
    return cons(Fix(0L), div(q_d__pctpi, Fix(-2L)))
  }
  if arcp(op).truthy() || eq(op, q_p_atan2) {
    let mut ans = risplit(
      logarc(
        op,
        // atan2 has 2 args, unlike all the other inverse trig functions.
        if eq(op, q_p_atan2) {
          rest(l)
        } else {
          cadr(l)
        },
      ),
    )
    if eq(op, q_p_atan2) {
      ans = cons(sratsimp(car(ans)), sratsimp(cdr(ans)))
    }
    return if free(l, q_d__pcti).truthy() && eq0(cdr(ans)) {
      cons(l, Fix(0L))
    } else {
      ans
    }
  }
  if eq(op, q_p_plog) {
    return risplit(cons(list1(q_p_log), cdr(l)))
  }
  // Look for a risplit-function on the property list to handle the
  // realpart and imagpart for this function.
  let f = safe_get(mop(l), q_risplit_function)
  if f.truthy() {
    return funcall(f, [l])
  }
  // All the above are guaranteed pure real.  The handling of lists and
  // matrices below has to be thought through.
  if eq(op, q_mlist) {
    return dsrl(l)
  }
  if eq(op, q_d_matrix) {
    return dot__ri(mapcar(x => dsrl(x), cdr(l)), list2(q_d_matrix, q_simp))
  }
  // The Coversinemyfoot clause covers functions which can be converted to
  // functions known by risplit, such as the more useless trigonometrics.
  let foot = coversinemyfoot(l)
  if foot.truthy() {
    let r = risplit(foot)
    if r.truthy() {
      return r
    }
  }
  {
    let op2 = if mqapplyp(l).truthy() { subfunname(l) } else { op }
    if safe_get(op2, q_real_valued).truthy() || decl_realp(op2).truthy() {
      // Simplification for a real-valued function, a subscripted one under
      // its name, as csign takes it.
      return cons(l, Fix(0L))
    }
  }
  if safe_get(mop(l), q_commutes_with_conjugate).truthy() ||
    safe_get(mop(l), q_conjugate_function).truthy() {
    // An operator that $conjugate may be able to simplify.  If $conjugate
    // simplifies l to something not involving '$conjugate, use
    // Re(z) = (conjugate(z) + z) / 2, Im(z) = %i * (conjugate(z) - z) / 2.
    let conjugate = ftake(q_d_conjugate, [l])
    if freeof(q_d_conjugate, conjugate).truthy() {
      return cons(
        mul2(div(Fix(1L), Fix(2L)), add2(conjugate, l)),
        muln_([div(Fix(1L), Fix(2L)), q_d__pcti, sub(conjugate, l)]),
      )
    }
  }
  // A MAJOR ASSUMPTION: All random functions are pure real, regardless of
  // argument.  This is evidently assumed by some of the integration
  // functions.
  if symval(q_rp_polylogp).truthy() &&
    mqapplyp(l).truthy() &&
    eq(subfunname(l), q_d_li) {
    return cons(l, Fix(0L))
  }
  {
    let op3 = if eq(op, q_mqapply) { caaadr(l) } else { op }
    if decl_complexp(op3).truthy() {
      return risplit_noun(l)
    }
  }
  if eq(op, q_p_product) && !free(cadr(l), q_d__pcti).truthy() {
    return risplit_noun(l)
  }
  if d_subvarp(l).truthy() {
    // return a real answer for subscripted variable
    return cons(l, Fix(0L))
  }
  cons(mk_simp(q_p_realpart, [l]), mk_simp(q_p_imagpart, [l]))
}

///|
fn coversinemyfoot(l : Value) -> Value raise {
  if memq(
      caar(l),
      list([q_p_csc, q_p_sec, q_p_cot, q_p_csch, q_p_sech, q_p_coth]),
    ) is Nil {
    Nil
  } else {
    let recip = get(caar(l), q_recip)
    if recip is Nil {
      Nil
    } else {
      div(Fix(1L), cons(list1(recip), cdr(l)))
    }
  }
}

///|
fn powers(c : Value, d : Value) -> Value raise {
  if eq1(d) {
    c
  } else if equal(d, Fix(0L)) {
    // equal to preclude 0^(pdl 0)->0:
    Fix(1L)
  } else if eq0(c) {
    Fix(0L)
  } else if eq1(c) {
    Fix(1L)
  } else {
    power(c, d)
  }
}

///|
/// SP is a cons of the real part and imaginary part of a complex number.
/// SPABS computes the sum of squares of the real and imaginary parts.
fn spabs(sp : Value) -> Value raise {
  add2(powers(car(sp), Fix(2L)), powers(cdr(sp), Fix(2L)))
}

///|
/// BIGFLOAT:TO of a Lisp number or a Maxima rational.
fn rpart__to_cl(x : Value) -> Value raise {
  if ratnump(x).truthy() {
    num_div(cadr(x), caddr(x))
  } else {
    x
  }
}

///|
/// MAXIMA::TO of a CL real.
fn rpart__to_maxima(x : Value) -> Value raise {
  match x {
    Ratio(_, _) => mk_simp(q_rat, [numerator(x), denominator(x)])
    _ => x
  }
}

///|
/// Compute 1/(x+%i*y) when both x and y are Lisp numbers or Maxima
/// rationals.  Return a cons of the real and imaginary part of the result.
/// We count on the underlying Lisp to be able to compute (/ (complex x y))
/// accurately and without unnecessary overflow or underflow.
fn sprecip(sp : Value) -> Value raise {
  let x = rpart__to_cl(car(sp))
  let y = rpart__to_cl(cdr(sp))
  let q = num_inv(complex(x, i=y))
  cons(rpart__to_maxima(realpart(q)), rpart__to_maxima(imagpart(q)))
}

///|
fn divcarcdr(a : Value, b : Value) -> Value raise {
  cons(div(car(a), b), div(cdr(a), b))
}

///|
/// Is SP, a (<real part> . <imaginary part>) pair, a complex number?
fn spcomplexnump(sp : Value) -> Value raise {
  lbool(
    mnump(car(sp)).truthy() &&
    mnump(cdr(sp)).truthy() &&
    !zerop1(cdr(sp)).truthy(),
  )
}

///|
/// Is SP a complex number with a float or a bigfloat part?
fn spinexactp(sp : Value) -> Value raise {
  lbool(
    spcomplexnump(sp).truthy() &&
    (
      floatp(car(sp)) ||
      floatp(cdr(sp)) ||
      d_bfloatp(car(sp)).truthy() ||
      d_bfloatp(cdr(sp)).truthy()
    ),
  )
}

///|
/// Multiply SP1 and SP2, both (<real part> . <imaginary part>) pairs
fn spmult(sp1 : Value, sp2 : Value) -> Value raise {
  cons(
    sub(mul2(car(sp1), car(sp2)), mul2(cdr(sp1), cdr(sp2))),
    add2(mul2(car(sp1), cdr(sp2)), mul2(cdr(sp1), car(sp2))),
  )
}

///|
/// Compute base^N, where base is (<real part> . <imaginary part>), and N
/// is a positive integer
fn spintexpt(base : Value, n : Value) -> Value raise {
  if spinexactp(base).truthy() && plusp(n) {
    // The binomial expansion in EXPANINTEXPT is exact as long as BASE is,
    // but its terms are larger than their sum by a factor of about
    // binomial(n, n/2), so for an inexact BASE the cancellation eats every
    // significant digit. Use exponentiation by squaring instead.
    let mut acc = base
    let mut i = integer_length(n) - 2
    while !(i < 0) {
      acc = spmult(acc, acc)
      if logbitp(i, n) {
        acc = spmult(acc, base)
      }
      i -= 1
    }
    acc
  } else {
    expanintexpt(base, n)
  }
}

///|
/// Expand bas^n, where bas is (<real part> . <imaginary part>)
fn expanintexpt(bas : Value, n : Value) -> Value raise {
  if num_eq(n, Fix(1L)) {
    return bas
  }
  let rp = car(bas)
  let ip = cdr(bas)
  let mut c : Value = Fix(1L)
  let mut ex = n
  let mut i : Value = Fix(1L)
  let mut rori = true
  let mut negp = symval(q_negp_star)
  let mut rpt = Value::Nil
  let mut ipt = Value::Nil
  while !minusp(ex) {
    let pred = car(negp)
    let v0 = muln_([c, powers(rp, ex), powers(ip, one_minus(i))])
    let temp = cons(
      if pred.truthy() {
        neg(v0)
      } else {
        v0
      },
      if rori {
        rpt
      } else {
        ipt
      },
    )
    if rori {
      rpt = temp
    } else {
      ipt = temp
    }
    // parallel stepping
    let c2 = float__quot(num_mul(c, ex), i)
    c = c2
    ex = one_minus(ex)
    i = one_plus(i)
    rori = !rori
    negp = cdr(negp)
  }
  cons(addn(rpt, t), addn(ipt, t))
}

///|
/// Subtract out multiples of 2*%pi with a minimum of consing.  Attempts to
/// reduce to interval (-pi,pi].
fn n2pistrip(exp_ : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if eq(caar(exp_), q_mtimes) {
    if mnump(cadr(exp_)).truthy() &&
      eq(caddr(exp_), q_d__pctpi) &&
      cdddr(exp_) is Nil {
      let c = cadr(exp_)
      if integerp(c) {
        // 5*%pi
        mul2(num_mod(c, Fix(2L)), q_d__pctpi)
      } else if floatp(c) {
        // 1.5*%pi
        mul2(one_minus(num_mod(one_plus(c), Fix(2L))), q_d__pctpi)
      } else if listp(c) && eq(caar(c), q_rat) {
        // Neither 0 nor 1 appears as a coef.  5/2*%pi
        let num = cadr(c)
        let den = caddr(c)
        mul2(
          cons(
            list2(q_rat, q_simp),
            cons(
              num_sub(num_mod(num_add(num, den), num_mul(Fix(2L), den)), den),
              cddr(c),
            ),
          ),
          q_d__pctpi,
        )
      } else {
        exp_
      }
    } else {
      exp_
    }
  } else if eq(caar(exp_), q_mplus) {
    let res = n2pirec(cdr(exp_))
    if eq(res, cdr(exp_)) {
      exp_
    } else {
      addn(res, t)
    }
  } else {
    exp_
  }
}

///|
/// Takes a list of exprs
fn n2pirec(fm : Value) -> Value raise {
  if cdr(fm) is Nil {
    // If monad, just return.
    let n2pf = n2pistrip(car(fm))
    if eq(n2pf, car(fm)) {
      fm
    } else if eq0(n2pf) {
      Nil
    } else {
      list1(n2pf)
    }
  } else {
    let n2pfma = n2pistrip(car(fm))
    let n2pfmd = n2pirec(cdr(fm))
    if n2pfmd is Nil || eq0(n2pfmd) {
      list1(n2pfma)
    } else if eq(n2pfmd, cdr(fm)) && eq(n2pfma, car(fm)) {
      fm
    } else {
      cons(n2pfma, n2pfmd)
    }
  }
}

///|
/// Rectify into polar form; Arguments similar to risplit
fn argnum(n : Value) -> Value raise {
  if minusp(n) {
    simplify(q_d__pctpi)
  } else {
    Fix(0L)
  }
}

///|
/// (defmacro half () ''((rat simp) 1 2))  ;1/2
fn half() -> Value raise {
  mk_simp(q_rat, [Fix(1L), Fix(2L)])
}

///|
/// Return the argument of a product in (-%pi, %pi], given ARGS, the
/// arguments of its factors. Multiples of %pi and the arguments atan2(0, u)
/// of real factors u combine into c*%pi + s*atan2(0, u1*u2*...), with
/// -1 < c <= 1, s = 1 for c <= 0 and s = -1 otherwise, which is in range and
/// keeps the atan2(0, u) of a single real factor as it is. With other
/// arguments, the sum is reduced modulo 2*%pi unless $SIGN shows that it is
/// in range, but not in the Risch integrator (IMPLICIT-REAL), whose TRIGIN1
/// needs it continuous.
fn absarg_product_arg(args : Value) -> Value raise {
  let mut c : Value = Fix(0L)
  let mut reals = Value::Nil
  let mut others = Value::Nil
  for arg in args.iter() {
    if eq(arg, q_d__pctpi) {
      c = add2(c, Fix(1L))
    } else if !atom(arg) &&
      eq(caar(arg), q_mtimes) &&
      mnump(cadr(arg)).truthy() &&
      eq(caddr(arg), q_d__pctpi) &&
      cdddr(arg) is Nil {
      c = add2(c, cadr(arg))
    } else if !atom(arg) &&
      eq(caar(arg), q_p_atan2) &&
      zerop1(cadr(arg)).truthy() {
      reals = cons(caddr(arg), reals)
    } else if !zerop1(arg).truthy() {
      others = cons(arg, others)
    }
  }
  let implicit_real = symval(q_implicit_real).truthy()
  let mut arg = n2pistrip(mul2(c, q_d__pctpi))
  if reals.truthy() {
    let u = muln(reals, t)
    arg = if eq(d_sign(arg), q_d_pos) {
      sub(arg, ftake(q_p_atan2, [Fix(0L), u]))
    } else {
      add2(arg, ftake(q_p_atan2, [Fix(0L), u]))
    }
  }
  let sum = if others.truthy() &&
    cdr(others) is Nil &&
    zerop1(arg).truthy() &&
    !implicit_real {
    // The argument of the only factor that is not real, as ABSARG gave it.
    // 2PISTRIP would take atan(3)-%pi to atan(3)+%pi.
    car(others)
  } else {
    n2pistrip(addn(cons(arg, others), t))
  }
  if implicit_real ||
    others is Nil ||
    (cdr(others) is Nil && zerop1(arg).truthy()) ||
    (
      memq(d_sign(sub(sum, q_d__pctpi)), list([q_d_neg, q_d_nz, q_d_zero])).truthy() &&
      eq(d_sign(add2(sum, q_d__pctpi)), q_d_pos)
    ) {
    sum
  } else {
    reduce_angle_mod_2pi(sum)
  }
}

///|
/// absarg returns pair (abs . arg); if absflag is true, arg result is not
/// guaranteed to be correct.
///
/// The function of Absflag is to communicate that only the absolute value
/// part of the result is wanted.  This allows Absarg to avoid asking
/// questions irrelevant to the absolute value.
fn absarg(l : Value, absflag? : Value = Nil) -> Value raise {
  if atom(l) {
    if eq(l, q_d__pcti) {
      cons(
        Fix(1L),
        simplify(mk(q_mtimes, [mk_simp(q_rat, [Fix(1L), Fix(2L)]), q_d__pctpi])),
      )
    } else if numberp(l) {
      cons(num_abs(l), argnum(l))
    } else if eq(l, q_d__pcte) || eq(l, q_d__pctpi) {
      cons(l, Fix(0L))
    } else if eq(l, q_d_infinity) {
      cons(q_d_inf, q_d_ind)
    } else if decl_complexp(l).truthy() {
      // noun form with mabs
      cons(mk_simp(q_mabs, [l]), mk_simp(q_p_carg, [l]))
    } else if absflag.truthy() {
      cons(take(list1(q_mabs), [l]), Fix(0L))
    } else {
      // At this point l is representing a real value. Try to determine the
      // sign and return a general form when the sign is unknown.
      let gs = if eq(symval(q_rischp), l) { q_d_pos } else { d_sign(l) }
      if eq(gs, q_d_pos) || eq(gs, q_d_pz) {
        cons(l, Fix(0L))
      } else if eq(gs, q_d_zero) {
        cons(Fix(0L), Fix(0L))
      } else if eq(gs, q_d_neg) {
        cons(neg(l), simplify(q_d__pctpi))
      } else {
        cons(take(list1(q_mabs), [l]), genatan(Fix(0L), l))
      }
    }
  } else if eq(q_d_zero, rpart__sign_catch(l)) {
    if some_bfloatp(l).truthy() {
      // contagious
      cons(symval(q_ear_bigfloatzero), symval(q_ear_bigfloatzero))
    } else if some_floatp(l).truthy() {
      cons(Flo(0.0), Flo(0.0))
    } else {
      cons(Fix(0L), Fix(0L))
    }
  } else if eq(caar(l), q_rat) || eq(caar(l), q_bigfloat) {
    cons(list([car(l), num_abs(cadr(l)), caddr(l)]), argnum(cadr(l)))
  } else if eq(caar(l), q_mtimes) {
    let mut n = cdr(l)
    let mut abars = Value::Nil
    let mut argl = Value::Nil
    let mut absl = Value::Nil
    while true {
      if n is Nil {
        return cons(muln(absl, t), absarg_product_arg(argl))
      }
      abars = absarg(car(n), absflag~)
      n = cdr(n)
      argl = cons(cdr(abars), argl)
      absl = rplacd(abars, absl)
    }
    Nil
  } else if eq(caar(l), q_mexpt) {
    // An expression z^a
    // (abs(z) . arg(z))
    let aa = absarg(cadr(l), absflag=Nil)
    // (realpart(a) . imagpart(a))
    let sp = risplit(caddr(l))
    with_special(q_d_radexpand, Nil, () => if (
        integerp(caddr(l)) || odd_root_exponent_p(caddr(l)).truthy()
      ) &&
      eq0(cdr(risplit(cadr(l)))) {
      // An integer power or real root of a real z, see
      // ODD-ROOT-EXPONENT-P. Its argument is that of z for an odd
      // numerator, 0 for an even one, and that of the real z^a itself for
      // an integer numerator of unknown parity.
      let p = power(car(aa), caddr(l))
      let parity = evod(rpart__num_denom_split(caddr(l)).0)
      cons(
        p,
        if eq(parity, q_d_odd) {
          cdr(aa)
        } else if eq(parity, q_d_even) {
          Fix(0L)
        } else {
          ftake(q_p_atan2, [Fix(0L), l])
        },
      )
    } else if zerop1(cdr(sp)).truthy() &&
      eq(d_sign(sub(Fix(1L), take(list1(q_mabs), [car(sp)]))), q_d_pos) {
      // Special case: a is real and abs(a) < 1.  This simplifies e.g.
      // carg(sqrt(z)) -> carg(z)/2
      cons(
        mul2(
          power(car(aa), car(sp)),
          power(q_d__pcte, neg(mul2(cdr(aa), cdr(sp)))),
        ),
        mul2(caddr(l), cdr(aa)),
      )
    } else {
      // General case for z and a
      let arg = add2(
        mul2(cdr(sp), take(list1(q_p_log), [car(aa)])),
        mul2(cdr(aa), car(sp)),
      )
      cons(
        mul2(
          power(car(aa), car(sp)),
          power(q_d__pcte, neg(mul2(cdr(aa), cdr(sp)))),
        ),
        if symval(q_generate_atan2).truthy() {
          take(list1(q_p_atan2), [
            take(list1(q_p_sin), [arg]),
            take(list1(q_p_cos), [arg]),
          ])
        } else {
          take(list1(q_p_atan), [take(list1(q_p_tan), [arg])])
        },
      )
    })
  } else if (eq(caar(l), q_p_tan) || eq(caar(l), q_p_tanh)) &&
    !eq0(cdr(risplit(cadr(l)))) {
    let sp = risplit(cadr(l))
    let mut n2frst = mul2(cdr(sp), Fix(2L))
    let mut n2scnd = mul2(car(sp), Fix(2L))
    if eq(caar(l), q_p_tanh) {
      let tmp = n2frst
      n2frst = n2scnd
      n2scnd = tmp
    }
    let a = {
      let cosh = take(list1(q_p_cosh), [n2frst])
      let cos = take(list1(q_p_cos), [n2scnd])
      root(div(add2(cosh, neg(cos)), add2(cosh, cos)), Fix(2L))
    }
    // RISPLIT's denominator for tan and tanh is never negative, so the
    // argument is that of the numerator.
    let b = if eq(caar(l), q_p_tan) {
      genatan(take(list1(q_p_sinh), [n2frst]), take(list1(q_p_sin), [n2scnd]))
    } else {
      genatan(take(list1(q_p_sin), [n2scnd]), take(list1(q_p_sinh), [n2frst]))
    }
    cons(a, b)
  } else if specrepp(l).truthy() {
    absarg(specdisrep(l), absflag~)
  } else {
    let foot = coversinemyfoot(l)
    if foot.truthy() && !eq0(cdr(risplit(cadr(l)))) {
      let r = absarg(foot, absflag~)
      if r.truthy() {
        return r
      }
    }
    let ris = trisplit(l)
    // Arguments must be in this order so that the side-effect of the
    // Atan2, that is, determining the Asksign of the argument, can happen
    // before Take Mabs does its Sign.
    let arg : Value = if absflag.truthy() {
      Fix(0L)
    } else {
      genatan(cdr(ris), car(ris))
    }
    let abs = if equal(car(ris), Fix(0L)) {
      absarg_mabs(cdr(ris))
    } else if equal(cdr(ris), Fix(0L)) {
      absarg_mabs(car(ris))
    } else {
      hypotenuse(car(ris), cdr(ris))
    }
    cons(abs, arg)
  }
}

///|
/// Dispatch the CL abs function to return |re + %i im|. The inputs re and
/// im should be floating point numbers.
fn hypotenuse_numerical(re : Value, im : Value) -> Value raise {
  if zerop(im) {
    num_abs(re)
  } else if zerop(re) {
    num_abs(im)
  } else {
    num_abs(complex(re, i=im))
  }
}

///|
fn hypotenuse(re : Value, im : Value) -> Value raise {
  // ok to use when no worries about floating point over/underflow.  For
  // mixed binary64 and symbolic cases, computing re^2 or im^2 can cause a
  // floating point overflow. When an error happens, we'll punt to an abs
  // nounform.
  let hypotenuse_default = fn(re : Value, im : Value) -> Value raise {
    let re = d_expand(re, expop=Fix(1L), expon=Fix(0L))
    let im = d_expand(im, expop=Fix(1L), expon=Fix(0L))
    match
      errset(() => ftake(q_mexpt, [
        add2(mul2(re, re), mul2(im, im)),
        symval(q_n1_sl_sl2),
      ])) {
      Some(v) if v.truthy() => v
      _ => ftake(q_mabs, [add2(re, mul2(q_d__pcti, im))])
    }
  }
  if d_bfloatp(re).truthy() || d_bfloatp(im).truthy() {
    // at least one bigfloat
    hypotenuse_default(d_bfloat(re), d_bfloat(im))
  } else if (floatp(re) && mnump(im).truthy()) ||
    (mnump(re).truthy() && floatp(im)) {
    // at least one float part
    hypotenuse_numerical(d_float(re), d_float(im))
  } else {
    // fall back
    hypotenuse_default(re, im)
  }
}

///|
fn genatan(num : Value, den : Value) -> Value raise {
  let arg = take(list1(q_p_atan2), [num, den])
  if symval(q_generate_atan2).truthy() ||
    zerop1(den).truthy() ||
    free(arg, q_p_atan2).truthy() {
    arg
  } else {
    take(list1(q_p_atan), [div(num, den)])
  }
}

///|
fn absarg_mabs(l : Value) -> Value raise {
  if eq(csign(l), t) {
    if memq(caar(l), list2(q_mabs, q_p_cabs)).truthy() {
      l
    } else {
      // mabs and not %cabs as noun form
      mk_simp(q_mabs, [l])
    }
  } else if {
      let s = d_csign(l)
      eq(s, q_d_complex) || eq(s, q_d_imaginary)
    } {
    // Do not try to simplify a complex expression at this point, this would
    // cause an endless loop. Return a noun form.
    mk_simp(q_mabs, [l])
  } else {
    take(list1(q_mabs), [l])
  }
}

///|
fn init_rpart() -> Unit raise {
  putprop(q_p_signum, q_risplit_signum, q_risplit_function) |> ignore
  // defmfun (... :properties ((evfun t)))
  putprop(q_d_rectform, t, q_evfun) |> ignore
  putprop(q_d_polarform, t, q_evfun) |> ignore
  // (defvar negp* (let ((l (list nil nil t t))) (nconc l l)))
  let l = list([Nil, Nil, t, t])
  nconc(l, l) |> ignore
  set(q_negp_star, l) |> ignore
}
