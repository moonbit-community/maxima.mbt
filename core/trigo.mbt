// Port of src/trigo.lisp: simplifiers for the hyperbolic functions and the
// inverse trigonometric and hyperbolic functions, and trigexpand.

///|
/// The value of the hyperbolic function FUN (%SINH, ..., %COTH) at the
/// inverse hyperbolic function INVFUN (%ASINH, ..., %ACOTH) of X, as an
/// algebraic expression, or NIL when INVFUN is not one. csch, sech and coth
/// are 1/sinh, 1/cosh and 1/tanh, and acsch(x), asech(x) and acoth(x) are
/// asinh(1/x), acosh(1/x) and atanh(1/x). The forms follow from the
/// logarithmic forms of asinh, acosh and atanh by algebra alone, with no
/// choice of branch. acoth(0) is left alone.
fn hyperbolic_of_inverse(fun : Value, invfun : Value, x : Value) -> Value raise {
  let base_invfun = if eq(invfun, q_p_acsch) {
    q_p_asinh
  } else if eq(invfun, q_p_asech) {
    q_p_acosh
  } else if eq(invfun, q_p_acoth) {
    q_p_atanh
  } else {
    invfun
  }
  let base_fun = if eq(fun, q_p_csch) {
    q_p_sinh
  } else if eq(fun, q_p_sech) {
    q_p_cosh
  } else if eq(fun, q_p_coth) {
    q_p_tanh
  } else {
    fun
  }
  let mut x = x
  let mut val : Value = Nil
  if !(eq(invfun, q_p_acoth) && zerop1(x).truthy()) {
    if !eq(base_invfun, invfun) {
      x = div(Fix(1L), x)
    }
    val = if eq(base_invfun, q_p_asinh) {
      // asinh(x) = log(x+r) with r = sqrt(x^2+1), and (x+r)*(r-x) = 1, so
      // exp(-asinh(x)) = r-x.
      if eq(base_fun, q_p_sinh) {
        x
      } else if eq(base_fun, q_p_cosh) {
        sqrt1_plusx_hat2(x)
      } else if eq(base_fun, q_p_tanh) {
        div(x, sqrt1_plusx_hat2(x))
      } else {
        Nil
      }
    } else if eq(base_invfun, q_p_acosh) {
      // acosh(x) = log(x+s) with s = sqrt(x-1)*sqrt(x+1), and
      // (x+s)*(x-s) = 1, so exp(-acosh(x)) = x-s.
      let s = mul2(
        power(sub(x, Fix(1L)), symval(q_n1_sl_sl2)),
        power(add2(x, Fix(1L)), symval(q_n1_sl_sl2)),
      )
      if eq(base_fun, q_p_sinh) {
        s
      } else if eq(base_fun, q_p_cosh) {
        x
      } else if eq(base_fun, q_p_tanh) {
        div(s, x)
      } else {
        Nil
      }
    } else if eq(base_invfun, q_p_atanh) {
      // atanh(x) = (log(1+x)-log(1-x))/2, so
      // exp(atanh(x)) = sqrt(1+x)/sqrt(1-x).
      let s = mul2(
        power(sub(Fix(1L), x), symval(q_n1_sl_sl2)),
        power(add2(Fix(1L), x), symval(q_n1_sl_sl2)),
      )
      if eq(base_fun, q_p_sinh) {
        div(x, s)
      } else if eq(base_fun, q_p_cosh) {
        div(Fix(1L), s)
      } else if eq(base_fun, q_p_tanh) {
        x
      } else {
        Nil
      }
    } else {
      Nil
    }
  }
  if val.truthy() {
    if eq(base_fun, fun) {
      val
    } else {
      div(Fix(1L), val)
    }
  } else {
    Nil
  }
}

///|
/// The first three clauses shared by these simplifiers: float evaluation,
/// bigfloat evaluation (only for forms not yet marked simp when
/// `check_simp`), and Taylor series. Nil when none applies.
fn trigo__numeric(form : Value, y : Value, check_simp : Bool) -> Value raise {
  let v = flonum_eval(mop(form), y)
  if v.truthy() {
    return v
  }
  if !check_simp || !trigi__simp_flag_set(form) {
    let v = big_float_eval(mop(form), y)
    if v.truthy() {
      return v
    }
  }
  taylorize(mop(form), second(form))
}

///|
/// `(mfuncall '$mod a b)`
fn trigo__mod(a : Value, b : Value) -> Value raise {
  mfuncall(q_d_mod, list2(a, b))
}

///|
/// The trigexpand/exponentialize/halfangles/reflection tail shared by the
/// hyperbolic simplifiers, ending in give-up.
fn trigo__hyper_tail(form : Value, op : Value, y : Value) -> Value raise {
  if symval(q_d_trigexpand).truthy() {
    let v = trigexpand(op, y)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d_exponentialize).truthy() {
    return exponentialize(op, y)
  }
  if symval(q_d_halfangles).truthy() {
    let v = halfangle(op, y)
    if v.truthy() {
      return v
    }
  }
  let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
  if v.truthy() {
    return v
  }
  trigi__give_up(op, [y], form)
}

///|
fn simp__pctsinh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_sinh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, false)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    return Fix(0L)
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_sin, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = hyperbolic_of_inverse(q_p_sinh, caar(y), cadr(y))
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_sinh, y)
}

///|
fn simp__pctcosh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_cosh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    return Fix(1L)
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return ftake_star(q_p_cos, [coeff(y, q_d__pcti, Fix(1L))])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = hyperbolic_of_inverse(q_p_cosh, caar(y), cadr(y))
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_cosh, y)
}

///|
fn simp__pcttanh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_tanh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    return Fix(0L)
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_tan, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = hyperbolic_of_inverse(q_p_tanh, caar(y), cadr(y))
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_tanh, y)
}

///|
fn simp__pctcoth(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_coth)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    let v = domain_error(y, q_coth)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_cot, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = if eq(q_p_acoth, caar(y)) {
      cadr(y)
    } else {
      hyperbolic_of_inverse(q_p_coth, caar(y), cadr(y))
    }
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_coth, y)
}

///|
fn simp__pctcsch(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_csch)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    let v = domain_error(y, q_csch)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_csc, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = if eq(q_p_acsch, caar(y)) {
      cadr(y)
    } else {
      hyperbolic_of_inverse(q_p_csch, caar(y), cadr(y))
    }
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_csch, y)
}

///|
fn simp__pctsech(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_sech)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    return Fix(1L)
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return ftake_star(q_p_sec, [coeff(y, q_d__pcti, Fix(1L))])
  }
  if symval(q_d_triginverses).truthy() && !atom(y) {
    let v = if eq(q_p_asech, caar(y)) {
      cadr(y)
    } else {
      hyperbolic_of_inverse(q_p_sech, caar(y), cadr(y))
    }
    if v.truthy() {
      return v
    }
  }
  trigo__hyper_tail(form, q_p_sech, y)
}

///|
/// The `$logarc`, reflection and give-up tail of the inverse function
/// simplifiers.
fn trigo__arc_tail(
  form : Value,
  op : Value,
  y : Value,
  reflect : Bool,
) -> Value raise {
  if symval(q_d_logarc).truthy() {
    return logarc(op, y)
  }
  if reflect {
    let v = apply_reflection_simp(mop(form), y, b=symval(q_d_trigsign))
    if v.truthy() {
      return v
    }
  }
  trigi__give_up(op, [y], form)
}

///|
/// `(and (eq $triginverses '$all) (not (atom y)) (if (eq f (caar y)) (cadr y)))`
fn trigo__inverses_all(y : Value, f : Value) -> Value {
  if eq(symval(q_d_triginverses), q_d_all) && !atom(y) && eq(f, caar(y)) {
    cadr(y)
  } else {
    Nil
  }
}

///|
/// The range check of the `$triginverses = true` clauses: csign(a) is in
/// ($nz $neg) and csign(b) is in ($pz $pos).
fn trigo__in_range(a : Value, b : Value) -> Bool raise {
  memq(csign(a), list2(q_d_nz, q_d_neg)).truthy() &&
  memq(csign(b), list2(q_d_pz, q_d_pos)).truthy()
}

///|
fn simp__pctasin(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_asin)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  let half = symval(q_n1_sl_sl2)
  let mhalf = symval(q_n_1_sl_sl2)
  let pi2 = symval(q_p_pi_sl_sl2)
  if symval(q_d__pctpiargs).truthy() {
    // Recognize some special values
    let v : Value = if zerop1(y).truthy() {
      Fix(0L)
    } else if equal(Fix(1L), y) {
      div(q_d__pctpi, Fix(2L))
    } else if equal(Fix(-1L), y) {
      div(q_d__pctpi, Fix(-2L))
    } else if alike1(y, half).truthy() {
      div(q_d__pctpi, Fix(6L))
    } else if alike1(y, mhalf).truthy() {
      div(q_d__pctpi, Fix(-6L))
    } else if alike1(y, power_star(Fix(2L), mhalf)).truthy() {
      // 1/sqrt(2)
      div(q_d__pctpi, Fix(4L))
    } else if alike1(y, div(power_star(Fix(3L), half), Fix(2L))).truthy() {
      // sqrt(3)/2
      div(q_d__pctpi, Fix(3L))
    } else if alike1(y, div(power_star(Fix(3L), half), Fix(-2L))).truthy() {
      // -sqrt(3)/2
      div(q_d__pctpi, Fix(-3L))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_asinh, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  if !atom(y) && memq(caar(y), list2(q_p_cos, q_p_sin)).truthy() {
    if d_constantp(cadr(y)).truthy() {
      let two_pi = mul2_star(Fix(2L), q_d__pctpi)
      let y_val = trigo__mod(
        if eq(caar(y), q_p_sin) {
          cadr(y)
        } else {
          sub_star(pi2, cadr(y))
        },
        two_pi,
      )
      let v : Value = if eq(mlsp(y_val, pi2), t) {
        y_val
      } else if eq(mlsp(y_val, mul2_star(Fix(3L), pi2)), t) {
        sub_star(q_d__pctpi, y_val)
      } else if eq(mlsp(y_val, mul2_star(Fix(2L), q_d__pctpi)), t) {
        sub_star(y_val, mul2_star(Fix(2L), q_d__pctpi))
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
  }
  if eq(symval(q_d_triginverses), t) && !atom(y) && eq(caar(y), q_p_sin) {
    if trigo__in_range(sub_star(cadr(y), pi2), add2_star(cadr(y), pi2)) {
      let v = cadr(y)
      if v.truthy() {
        return v
      }
    }
  }
  let v = trigo__inverses_all(y, q_p_sin)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_asin, y, true)
}

///|
fn simp__pctacos(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acos)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  let half = symval(q_n1_sl_sl2)
  let mhalf = symval(q_n_1_sl_sl2)
  let pi2 = symval(q_p_pi_sl_sl2)
  if symval(q_d__pctpiargs).truthy() {
    // Recognize some special values
    let v : Value = if zerop1(y).truthy() {
      div(q_d__pctpi, Fix(2L))
    } else if equal(Fix(1L), y) {
      Fix(0L)
    } else if equal(Fix(-1L), y) {
      q_d__pctpi
    } else if alike1(y, half).truthy() {
      div(q_d__pctpi, Fix(3L))
    } else if alike1(y, mhalf).truthy() {
      mul2(q_d__pctpi, div(Fix(2L), Fix(3L)))
    } else if alike1(y, power_star(Fix(2L), mhalf)).truthy() {
      // 1/sqrt(2)
      div(q_d__pctpi, Fix(4L))
    } else if alike1(y, div(power_star(Fix(3L), half), Fix(2L))).truthy() {
      // sqrt(3)/2
      div(q_d__pctpi, Fix(6L))
    } else if alike1(y, div(power_star(Fix(3L), half), Fix(-2L))).truthy() {
      // -sqrt(3)/2
      mul2(q_d__pctpi, div(Fix(5L), Fix(6L)))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if !atom(y) && memq(caar(y), list2(q_p_cos, q_p_sin)).truthy() {
    if d_constantp(cadr(y)).truthy() {
      let y_val = trigo__mod(
        if eq(caar(y), q_p_cos) {
          cadr(y)
        } else {
          sub_star(pi2, cadr(y))
        },
        mul2_star(Fix(2L), q_d__pctpi),
      )
      let v : Value = if eq(mlsp(y_val, q_d__pctpi), t) {
        y_val
      } else if eq(mlsp(y_val, mul2_star(Fix(2L), q_d__pctpi)), t) {
        sub_star(mul2_star(Fix(2L), q_d__pctpi), y_val)
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
  }
  let v = trigo__inverses_all(y, q_p_cos)
  if v.truthy() {
    return v
  }
  if eq(symval(q_d_triginverses), t) && !atom(y) && eq(caar(y), q_p_cos) {
    if trigo__in_range(sub_star(cadr(y), q_d__pctpi), cadr(y)) {
      let v = cadr(y)
      if v.truthy() {
        return v
      }
    }
  }
  trigo__arc_tail(form, q_p_acos, y, true)
}

///|
fn simp__pctacot(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acot)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  let pi2 = symval(q_p_pi_sl_sl2)
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      div(q_d__pctpi, Fix(2L))
    } else if equal(Fix(1L), y) {
      div(q_d__pctpi, Fix(4L))
    } else if equal(Fix(-1L), y) {
      div(q_d__pctpi, Fix(-4L))
    } else if alike1(y, trigi__invsqrt3()).truthy() {
      // 1/sqrt(3)
      div(q_d__pctpi, Fix(3L))
    } else if alike1(y, trigi__sqrt3()).truthy() {
      // sqrt(3)
      div(q_d__pctpi, Fix(6L))
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
      ftake_star(q_p_acoth, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if !atom(y) && memq(caar(y), list2(q_p_cot, q_p_tan)).truthy() {
    if d_constantp(cadr(y)).truthy() {
      let y_val = trigo__mod(
        if eq(caar(y), q_p_cot) {
          cadr(y)
        } else {
          sub_star(pi2, cadr(y))
        },
        q_d__pctpi,
      )
      let v : Value = if eq(mlsp(y_val, pi2), t) {
        y_val
      } else if eq(mlsp(y_val, q_d__pctpi), t) {
        sub_star(y_val, q_d__pctpi)
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
  }
  let v = trigo__inverses_all(y, q_p_cot)
  if v.truthy() {
    return v
  }
  if eq(symval(q_d_triginverses), t) && !atom(y) && eq(caar(y), q_p_cot) {
    if trigo__in_range(sub_star(cadr(y), pi2), add2_star(cadr(y), pi2)) {
      let v = cadr(y)
      if v.truthy() {
        return v
      }
    }
  }
  trigo__arc_tail(form, q_p_acot, y, true)
}

///|
fn trigo__two_invsqrt3() -> Value {
  mk(q_mtimes, [Fix(2L), trigi__invsqrt3()])
}

///|
fn simp__pctacsc(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acsc)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  let pi2 = symval(q_p_pi_sl_sl2)
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      domain_error(y, q_acsc)
    } else if equal(Fix(1L), y) {
      div(q_d__pctpi, Fix(2L))
    } else if equal(Fix(-1L), y) {
      div(q_d__pctpi, Fix(-2L))
    } else if equal(y, Fix(2L)) {
      div(q_d__pctpi, Fix(6L))
    } else if alike1(y, trigi__sqrt2()).truthy() {
      // sqrt(2)
      div(q_d__pctpi, Fix(4L))
    } else if alike1(y, trigo__two_invsqrt3()).truthy() {
      // 2*sqrt(3)/3
      div(q_d__pctpi, Fix(3L))
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
      ftake_star(q_p_acsch, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  if !atom(y) && eq(q_p_csc, caar(y)) {
    if d_constantp(cadr(y)).truthy() {
      let y_val = trigo__mod(cadr(y), mul2_star(Fix(2L), q_d__pctpi))
      let v : Value = if eq(mlsp(y_val, pi2), t) {
        y_val
      } else if eq(mlsp(y_val, mul2_star(Fix(3L), pi2)), t) {
        sub_star(q_d__pctpi, y_val)
      } else if eq(mlsp(y_val, mul2_star(Fix(2L), q_d__pctpi)), t) {
        sub_star(y_val, mul2_star(Fix(2L), q_d__pctpi))
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
  }
  let v = trigo__inverses_all(y, q_p_csc)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_acsc, y, true)
}

///|
fn simp__pctasec(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_asec)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      domain_error(y, q_asec)
    } else if equal(Fix(1L), y) {
      Fix(0L)
    } else if equal(Fix(-1L), y) {
      q_d__pctpi
    } else if equal(Fix(2L), y) {
      div(q_d__pctpi, Fix(3L))
    } else if alike1(y, trigi__sqrt2()).truthy() {
      // sqrt(2)
      div(q_d__pctpi, Fix(4L))
    } else if alike1(y, trigo__two_invsqrt3()).truthy() {
      // 2/sqrt(3)
      div(q_d__pctpi, Fix(6L))
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if !atom(y) && eq(q_p_sec, caar(y)) {
    if d_constantp(cadr(y)).truthy() {
      let y_val = trigo__mod(cadr(y), mul2_star(Fix(2L), q_d__pctpi))
      let v : Value = if eq(mlsp(y_val, q_d__pctpi), t) {
        y_val
      } else if eq(mlsp(y_val, mul2_star(Fix(2L), q_d__pctpi)), t) {
        sub_star(mul2_star(Fix(2L), q_d__pctpi), y_val)
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
  }
  let v = trigo__inverses_all(y, q_p_sec)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_asec, y, true)
}

///|
fn simp__pctasinh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_asinh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() && y.truthy() {
    return y
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_asin, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  let v = trigo__inverses_all(y, q_p_sinh)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_asinh, y, true)
}

///|
fn simp__pctacosh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acosh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && equal(y, Fix(1L)) {
    return Fix(0L)
  }
  let v = trigo__inverses_all(y, q_p_cosh)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_acosh, y, false)
}

///|
fn simp__pctatanh(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_atanh)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if zerop1(y).truthy() {
      Fix(0L)
    } else if equal(y, Fix(1L)) || equal(y, Fix(-1L)) {
      domain_error(y, q_atanh)
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return mul2(q_d__pcti, ftake_star(q_p_atan, [coeff(y, q_d__pcti, Fix(1L))]))
  }
  let v = trigo__inverses_all(y, q_p_tanh)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_atanh, y, true)
}

///|
fn simp__pctacoth(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acoth)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && (equal(y, Fix(1L)) || equal(y, Fix(-1L))) {
    let v = domain_error(y, q_acoth)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_acot, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  let v = trigo__inverses_all(y, q_p_coth)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_acoth, y, true)
}

///|
fn simp__pctacsch(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_acsch)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() && zerop1(y).truthy() {
    let v = domain_error(y, q_acsch)
    if v.truthy() {
      return v
    }
  }
  if symval(q_d__pctiargs).truthy() && multiplep(y, q_d__pcti).truthy() {
    return muln_([
      Fix(-1L),
      q_d__pcti,
      ftake_star(q_p_acsc, [coeff(y, q_d__pcti, Fix(1L))]),
    ])
  }
  let v = trigo__inverses_all(y, q_p_csch)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_acsch, y, true)
}

///|
fn simp__pctasech(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  trigi__check1(form, q_p_asech)
  let y = simpcheck(nth(1, form), p__pctsimpflag)
  let v = trigo__numeric(form, y, true)
  if v.truthy() {
    return v
  }
  if symval(q_d__pctpiargs).truthy() {
    let v : Value = if equal(y, Fix(1L)) {
      Fix(0L)
    } else if zerop1(y).truthy() {
      domain_error(y, q_asech)
    } else {
      Nil
    }
    if v.truthy() {
      return v
    }
  }
  let v = trigo__inverses_all(y, q_p_sech)
  if v.truthy() {
    return v
  }
  trigo__arc_tail(form, q_p_asech, y, true)
}

///|
fn d_trigexpand(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if specrepp(e).truthy() {
    d_trigexpand(specdisrep(e))
  } else {
    let v = trigexpand(caar(e), cadr(e))
    if v.truthy() {
      v
    } else {
      recur_apply(lfunc("$trigexpand", args => d_trigexpand(arg(args, 0))), e)
    }
  }
}

///|
fn trigexpand(op : Value, arg : Value) -> Value raise {
  if atom(arg) {
    Nil
  } else if symval(q_d_trigexpandplus).truthy() && eq(q_mplus, caar(arg)) {
    let l = cdr(arg)
    let m1 : Value = Fix(-1L)
    let p1 : Value = Fix(1L)
    if eq(q_p_sin, op) {
      sin_slcos_plus(l, Fix(1L), q_p_sin, q_p_cos, m1)
    } else if eq(q_p_cos, op) {
      sin_slcos_plus(l, Fix(0L), q_p_sin, q_p_cos, m1)
    } else if eq(q_p_tan, op) {
      tan_plus(l, q_p_tan, m1)
    } else if eq(q_p_cot, op) {
      cot_plus(l, q_p_cot, m1)
    } else if eq(q_p_csc, op) {
      csc_slsec_plus(l, Fix(1L), q_p_csc, q_p_sec, m1)
    } else if eq(q_p_sec, op) {
      csc_slsec_plus(l, Fix(0L), q_p_csc, q_p_sec, m1)
    } else if eq(q_p_sinh, op) {
      sin_slcos_plus(l, Fix(1L), q_p_sinh, q_p_cosh, p1)
    } else if eq(q_p_cosh, op) {
      sin_slcos_plus(l, Fix(0L), q_p_sinh, q_p_cosh, p1)
    } else if eq(q_p_tanh, op) {
      tan_plus(l, q_p_tanh, p1)
    } else if eq(q_p_coth, op) {
      cot_plus(l, q_p_coth, p1)
    } else if eq(q_p_csch, op) {
      csc_slsec_plus(l, Fix(1L), q_p_csch, q_p_sech, p1)
    } else if eq(q_p_sech, op) {
      csc_slsec_plus(l, Fix(0L), q_p_csch, q_p_sech, p1)
    } else {
      Nil
    }
  } else if symval(q_d_trigexpandtimes).truthy() &&
    eq(q_mtimes, caar(arg)) &&
    fixnump(cadr(arg)) {
    let l = cddr(arg)
    let n = cadr(arg)
    let m1 : Value = Fix(-1L)
    let p1 : Value = Fix(1L)
    if eq(q_p_sin, op) {
      sin_slcos_times(l, Fix(1L), n, q_p_sin, q_p_cos, m1)
    } else if eq(q_p_cos, op) {
      sin_slcos_times(l, Fix(0L), n, q_p_sin, q_p_cos, m1)
    } else if eq(q_p_tan, op) {
      tan_times(l, n, q_p_tan, m1)
    } else if eq(q_p_cot, op) {
      cot_times(l, n, q_p_cot, m1)
    } else if eq(q_p_csc, op) {
      csc_slsec_times(l, Fix(1L), n, q_p_csc, q_p_sec, m1)
    } else if eq(q_p_sec, op) {
      csc_slsec_times(l, Fix(0L), n, q_p_csc, q_p_sec, m1)
    } else if eq(q_p_sinh, op) {
      sin_slcos_times(l, Fix(1L), n, q_p_sinh, q_p_cosh, p1)
    } else if eq(q_p_cosh, op) {
      sin_slcos_times(l, Fix(0L), n, q_p_sinh, q_p_cosh, p1)
    } else if eq(q_p_tanh, op) {
      tan_times(l, n, q_p_tanh, p1)
    } else if eq(q_p_coth, op) {
      cot_times(l, n, q_p_coth, p1)
    } else if eq(q_p_csch, op) {
      csc_slsec_times(l, Fix(1L), n, q_p_csch, q_p_sech, p1)
    } else if eq(q_p_sech, op) {
      csc_slsec_times(l, Fix(0L), n, q_p_csch, q_p_sech, p1)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn sin_slcos_plus(
  l : Value,
  n : Value,
  f1 : Value,
  f2 : Value,
  flag : Value,
) -> Value raise {
  let len = length(l)
  let mut i = to_int(n)
  let mut sign : Value = Fix(1L)
  let mut result : Value = Nil
  while i <= len {
    result = mpc(
      if minusp(sign) {
        list2(Fix(-1L), list1(q_mtimes))
      } else {
        list1(list1(q_mtimes))
      },
      l,
      result,
      f1,
      f2,
      int(len),
      int(i),
    )
    i = 2 + i
    sign = num_mul(flag, sign)
  }
  simplify(cons(list1(q_mplus), result))
}

///|
fn tan_plus(l : Value, f : Value, flag : Value) -> Value raise {
  let len = length(l)
  let mut i = 1
  let mut sign : Value = Fix(1L)
  let mut num : Value = Nil
  let mut den = list1(Fix(1L))
  while i <= len {
    num = mpc1(list2(sign, list1(q_mtimes)), l, num, f, int(len), int(i))
    den = if len == i {
      den
    } else {
      mpc1(
        list2(num_mul(flag, sign), list1(q_mtimes)),
        l,
        den,
        f,
        int(len),
        int(i + 1),
      )
    }
    i = 2 + i
    sign = num_mul(flag, sign)
  }
  div_star(cons(list1(q_mplus), num), cons(list1(q_mplus), den))
}

///|
fn cot_plus(l : Value, f : Value, flag : Value) -> Value raise {
  let len = length(l)
  let mut i = len
  let mut sign : Value = Fix(1L)
  let mut num : Value = Nil
  let mut den : Value = Nil
  while i >= 0 {
    num = mpc1(list2(sign, list1(q_mtimes)), l, num, f, int(len), int(i))
    den = if 0 == i {
      den
    } else {
      mpc1(list2(sign, list1(q_mtimes)), l, den, f, int(len), int(i - 1))
    }
    i = i - 2
    sign = num_mul(flag, sign)
  }
  div_star(cons(list1(q_mplus), num), cons(list1(q_mplus), den))
}

///|
fn csc_slsec_plus(
  l : Value,
  n : Value,
  f1 : Value,
  f2 : Value,
  flag : Value,
) -> Value raise {
  let mut ll = l
  let mut result : Value = Nil
  while ll is Cons(_) {
    let a = ftake_star(f1, [car(ll)])
    let b = ftake_star(f2, [car(ll)])
    result = cons(a, cons(b, result))
    ll = cdr(ll)
  }
  let numer = cons(list1(q_mtimes), result)
  div_star(numer, sin_slcos_plus(l, n, f2, f1, flag))
}

///|
fn sin_slcos_times(
  l : Value,
  m : Value,
  n : Value,
  f1 : Value,
  f2 : Value,
  flag : Value,
) -> Value raise {
  // Assume m,n < 2^17, but Binom may become big
  // Flag is 1 or -1
  let f1 = ftake_star(f1, [cons(list1(q_mtimes), l)])
  let f2 = ftake_star(f2, [cons(list1(q_mtimes), l)])
  let mut i = m
  let end = num_abs(n)
  let mut result : Value = Nil
  let mut binom : Value = if num_eq(Fix(0L), m) { Fix(1L) } else { num_abs(n) }
  while !num_gt(i, end) {
    result = cons(
      muln_([binom, power(f1, i), power(f2, num_sub(end, i))]),
      result,
    )
    let new_binom = num_truncate(
      num_prod([flag, num_sub(num_sub(end, i), Fix(1L)), num_sub(end, i), binom]),
      b=num_mul(num_add(Fix(2L), i), one_plus(i)),
    ).0
    i = num_add(Fix(2L), i)
    binom = new_binom
  }
  result = simplify(cons(list1(q_mplus), result))
  if num_eq(Fix(1L), m) && minusp(n) {
    neg(result)
  } else {
    result
  }
}

///|
fn tan_times(l : Value, n : Value, f : Value, flag : Value) -> Value raise {
  let f = ftake_star(f, [cons(list1(q_mtimes), l)])
  let mut i : Value = Fix(1L)
  let end = num_abs(n)
  let mut num : Value = Nil
  let mut den = list1(Fix(1L))
  let mut binom = num_abs(n)
  while !num_gt(i, end) {
    num = cons(mul2(binom, power(f, i)), num)
    den = if num_eq(end, i) {
      den
    } else {
      binom = num_truncate(
        num_prod([flag, num_sub(end, i), binom]),
        b=one_plus(i),
      ).0
      cons(mul2(binom, power(f, one_plus(i))), den)
    }
    let new_binom = num_truncate(
      num_mul(num_sub(num_sub(end, i), Fix(1L)), binom),
      b=num_add(Fix(2L), i),
    ).0
    i = num_add(Fix(2L), i)
    binom = new_binom
  }
  num = div_star(cons(list1(q_mplus), num), cons(list1(q_mplus), den))
  if minusp(n) {
    neg(num)
  } else {
    num
  }
}

///|
fn cot_times(l : Value, n : Value, f : Value, flag : Value) -> Value raise {
  let f = ftake_star(f, [cons(list1(q_mtimes), l)])
  let mut i = num_abs(n)
  let end = num_abs(n)
  let mut num : Value = Nil
  let mut den : Value = Nil
  let mut binom : Value = Fix(1L)
  while !minusp(i) {
    num = cons(mul2(binom, power(f, i)), num)
    den = if num_eq(Fix(0L), i) {
      den
    } else {
      binom = num_truncate(
        num_mul(i, binom),
        b=num_add(num_sub(end, i), Fix(1L)),
      ).0
      cons(mul2(binom, power(f, one_minus(i))), den)
    }
    let new_binom = num_truncate(
      num_prod([flag, one_minus(i), binom]),
      b=num_add(num_sub(end, i), Fix(2L)),
    ).0
    i = num_sub(i, Fix(2L))
    binom = new_binom
  }
  num = div_star(cons(list1(q_mplus), num), cons(list1(q_mplus), den))
  if minusp(n) {
    neg(num)
  } else {
    num
  }
}

///|
fn csc_slsec_times(
  l : Value,
  m : Value,
  n : Value,
  f1 : Value,
  f2 : Value,
  flag : Value,
) -> Value raise {
  div_star(
    mul2(
      power(ftake_star(f1, [cons(list1(q_mtimes), l)]), num_abs(n)),
      power(ftake_star(f2, [cons(list1(q_mtimes), l)]), num_abs(n)),
    ),
    sin_slcos_times(l, m, n, f2, f1, flag),
  )
}

///|
fn mpc(
  dl : Value,
  ul : Value,
  result : Value,
  f1 : Value,
  f2 : Value,
  di : Value,
  ui : Value,
) -> Value raise {
  if num_eq(Fix(0L), ui) {
    cons(revappend(dl, mapcar(l => ftake_star(f2, [l]), ul)), result)
  } else if num_eq(di, ui) {
    cons(revappend(dl, mapcar(l => ftake_star(f1, [l]), ul)), result)
  } else {
    let a = cons(ftake_star(f1, [car(ul)]), dl)
    let inner = mpc(
      cons(ftake_star(f2, [car(ul)]), dl),
      cdr(ul),
      result,
      f1,
      f2,
      one_minus(di),
      ui,
    )
    mpc(a, cdr(ul), inner, f1, f2, one_minus(di), one_minus(ui))
  }
}

///|
fn mpc1(
  dl : Value,
  ul : Value,
  result : Value,
  f : Value,
  di : Value,
  ui : Value,
) -> Value raise {
  if num_eq(Fix(0L), ui) {
    cons(reverse(dl), result)
  } else if num_eq(di, ui) {
    cons(revappend(dl, mapcar(l => ftake_star(f, [l]), ul)), result)
  } else {
    let a = cons(ftake_star(f, [car(ul)]), dl)
    let inner = mpc1(dl, cdr(ul), result, f, one_minus(di), ui)
    mpc1(a, cdr(ul), inner, f, one_minus(di), one_minus(ui))
  }
}

///|
fn init_trigo() -> Unit raise {
  // (defmfun ($trigexpand :properties ((evfun t))) ...)
  putprop(q_d_trigexpand, t, q_evfun) |> ignore
}
