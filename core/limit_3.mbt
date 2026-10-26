// Port of src/limit.lisp, part 3: SIMPLIMEXPT, SIMPLIMIT, SIMPLIMTIMES,
// SIMPLIMPLUS, growth-order heuristics (CPA, ISTRENGTH, ...), radicals, and
// the SIMPLIM%FUNCTION handlers of individual operators.

///|
/// A subset U of the complex numbers is *bounded away from zero* if |U| has a
/// positive lower bound. We determine if a set U is bounded away from zero
/// by showing that |U| > tiny-positive.
fn bounded_away_from_zero(e : Value, tiny_positive? : Value = Nil) -> Value raise {
  // Default tiny-positive to 1/*large-positive-number*.
  let tiny_positive = if tiny_positive.truthy() {
    tiny_positive
  } else {
    div(Fix(1L), symval(q_ear_large_positive_number))
  }
  let z = risplit(e)
  let re = car(z)
  let im = cdr(z)
  let r2 = add2(mul2(re, re), mul2(im, im)) // r2 = |e|^2
  // We want r2 > tiny-positive
  lbool(eq(t, mgrp(r2, tiny_positive)))
}

///|
fn limit_ind_to_power(bas : Value, expo : Value, el : Value) -> Value raise {
  ignore(expo) // for now don't need expo, but include if its ever needed.
  if eq(el, q_d_ind) {
    // Case 1: ind^ind: when bas is bounded away from zero, return ind, else
    // und.
    if bounded_away_from_zero(bas).truthy() {
      q_d_ind
    } else {
      q_d_und
    }
  } else if zerop2(el).truthy() {
    // Case 2: Limit of exponent is 0.
    if eq(t, mnqp(bas, Fix(0L))) {
      // (nonvanishing ind)^0 = 1
      Fix(1L)
    } else {
      // (possibly vanishing ind)^0 = und
      q_d_und
    }
  } else if limit__memq(el, [q_d_minf, q_d_inf, q_d_infinity]) {
    // Case 3: Exponent is either inf, minf, or infinity
    let mag = inside_outside_unit_circle(bas)
    let b_nz = eq(t, mnqp(bas, Fix(0L))) // is the base nonzero?
    if eq(el, q_d_inf) && eq(mag, q_pos_real_inside) {
      // (0 < x < 1)^inf = $zeroa
      q_d_zeroa
    } else if eq(el, q_d_minf) && eq(mag, q_pos_real_inside) {
      // (0 < x < 1)^minf = $inf
      q_d_inf
    } else if b_nz && eq(el, q_d_inf) && eq(mag, q_inside) {
      // (0 < |x| < 1)^inf = 0
      Fix(0L)
    } else if b_nz && eq(el, q_d_minf) && eq(mag, q_inside) {
      // (0 < |x| < 1)^minf = infinity
      q_d_infinity
    } else if eq(mag, q_one) {
      // (+/- 1)^inf or (+/- 1)^minf -- throw to limit
      throw_tag(q_limit, Nil)
    } else if eq(mag, q_on) {
      // on unit circle, but not (+/-1)^{minf, inf,infinity} = ind
      q_d_ind
    } else if eq(mag, q_pos_real_outside) {
      // (x > 1)^inf = inf & (x > 1)^minf = zeroa
      if eq(el, q_d_inf) {
        q_d_inf
      } else {
        q_d_zeroa
      }
    } else if eq(mag, q_outside) {
      if eq(el, q_d_minf) {
        Fix(0L) // (|x|>1)^minf = 0
      } else if eq(el, q_d_inf) {
        q_d_infinity // (|x|>1)^inf = infinity
      } else {
        throw_tag(q_limit, Nil) // (|x| > 1)^infinity = throw to limit
      }
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if eq(t, mnqp(bas, Fix(0L))) {
    // Case 4: (nonvanising ind)^finite = ind
    q_d_ind
  } else if eq(t, mgrp(el, Fix(0L))) {
    // Case 5: Exponent is finite and positive (el > 0)
    q_d_ind
  } else if eq(t, mgrp(Fix(0L), el)) {
    // Case 6: Exponent is finite and negative (el < 0). Safe only if base is
    // bounded away from zero
    if bounded_away_from_zero(bas).truthy() {
      q_d_ind
    } else {
      q_d_und
    }
  } else {
    // Default fallback
    q_d_und
  }
}

///|
fn simplimexpt(bas : Value, expo : Value, bl : Value, el : Value) -> Value raise {
  let mut bas = bas
  let mut el = el
  if eq(bl, q_d_und) || eq(el, q_d_und) {
    q_d_und
  } else if eq(bl, q_d_ind) {
    // Handle ind^XXX, from now on it is safe to assume that bl =/= $ind
    limit_ind_to_power(bas, expo, el)
  } else if zerop2(bl).truthy() {
    if eq(el, q_d_inf) {
      if eq(bl, q_d_zeroa) {
        bl
      } else {
        Fix(0L)
      }
    } else if eq(el, q_d_minf) {
      if eq(bl, q_d_zeroa) {
        q_d_inf
      } else {
        q_d_infinity
      }
    } else if eq(el, q_d_ind) {
      q_d_ind
    } else if eq(el, q_d_infinity) {
      q_d_und
    } else if zerop2(el).truthy() {
      bylog(expo, bas)
    } else if equal(getsignl(el), Fix(-1L)) {
      if eq(bl, q_d_zeroa) {
        q_d_inf
      } else if eq(bl, q_d_zerob) {
        if even1(el).truthy() {
          q_d_inf
        } else if eq(ask_integer(el, q_d_integer), q_d_yes) {
          if eq(ask_integer(el, q_d_even), q_d_yes) {
            q_d_inf
          } else {
            q_d_minf // Gotta be ODD.
          }
        } else {
          Nil
        }
      } else if mtimesp(bas).truthy() &&
        some(
          f => eq(limit(f, limit__var(), limit__val(), q_think), q_d_ind) &&
            mnump(ftake(q_mabs, [f])).truthy() &&
            limit__memq(d_csign(f), [q_d_complex, q_d_imaginary]),
          cdr(bas),
        ) {
        // A zero with no direction: The modulus of BAS^EXPO still diverges.
        // When a factor of BAS has constant modulus and an ind limit and is
        // not shown real, the phase of BAS rotates, and the power is
        // infinity.
        q_d_infinity
      } else {
        bas = behavior(bas, limit__var(), limit__val())
        if equal(bas, Fix(1L)) {
          q_d_inf
        } else if equal(bas, Fix(-1L)) {
          q_d_minf
        } else {
          throw_tag(q_limit, t)
        }
      }
    } else if mnump(el).truthy() && limit__memq(bl, [q_d_zeroa, q_d_zerob]) {
      if even1(el).truthy() {
        q_d_zeroa
      } else if eq(bl, q_d_zerob) && ratnump(el).truthy() && evenp(caddr(el)) {
        Fix(0L)
      } else {
        bl
      }
    } else if equal(getsignl(el), Fix(1L)) {
      if eq(bl, q_d_zeroa) {
        bl
      } else {
        Fix(0L)
      }
    } else if equal(getsignl(el), Fix(0L)) {
      Fix(1L)
    } else {
      throw_tag(q_limit, t)
    }
  } else if eq(bl, q_d_infinity) {
    if zerop2(el).truthy() {
      bylog(expo, bas)
    } else if eq(el, q_d_minf) {
      Fix(0L)
    } else if eq(el, q_d_inf) {
      q_d_infinity
    } else if limit__memq(el, [q_d_infinity, q_d_ind]) {
      q_d_und
    } else {
      el = getsignl(el)
      if equal(el, Fix(1L)) {
        q_d_infinity
      } else if equal(el, Fix(0L)) {
        Fix(1L)
      } else if equal(el, Fix(-1L)) {
        Fix(0L)
      } else {
        throw_tag(q_limit, t)
      }
    }
  } else if eq(bl, q_d_inf) {
    if eq(el, q_d_inf) {
      q_d_inf
    } else if equal(el, q_d_minf) {
      Fix(0L)
    } else if zerop2(el).truthy() {
      bylog(expo, bas)
    } else if limit__memq(el, [q_d_infinity, q_d_ind]) {
      q_d_und
    } else if eql(Fix(0L), getsignl(el)) {
      Fix(1L)
    } else if ratgreaterp(Fix(0L), el).truthy() {
      q_d_zeroa
    } else if ratgreaterp(el, Fix(0L)).truthy() {
      q_d_inf
    } else {
      throw_tag(q_limit, t)
    }
  } else if eq(bl, q_d_minf) {
    if zerop2(el).truthy() {
      bylog(expo, bas)
    } else if eq(el, q_d_inf) {
      q_d_und
    } else if equal(el, q_d_minf) {
      Fix(0L)
    } else if mnump(el).truthy() {
      // Why not generalize this. We can ask about the number. -Jim 2/23/81
      if mnegp(el).truthy() {
        if even1(el).truthy() {
          q_d_zeroa
        } else if eq(ask_integer(el, q_d_integer), q_d_yes) {
          if eq(ask_integer(el, q_d_even), q_d_yes) {
            q_d_zeroa
          } else {
            q_d_zerob
          }
        } else {
          Fix(0L)
        }
      } else if even1(el).truthy() {
        q_d_inf
      } else if eq(ask_integer(el, q_d_integer), q_d_yes) {
        if eq(ask_integer(el, q_d_even), q_d_yes) {
          q_d_inf
        } else {
          q_d_minf
        }
      } else {
        q_d_infinity
      }
    } else if symval(q_loginprod_q).truthy() {
      throw_tag(q_lip_q, q_lip_bang)
    } else {
      q_d_und
    }
  } else if equal(simplify(ratdisrep(ridofab(bl))), Fix(1L)) {
    if infinityp(el).truthy() {
      bylog(expo, bas)
    } else {
      Fix(1L)
    }
  } else if equal(ridofab(bl), Fix(-1L)) && infinityp(el).truthy() {
    q_d_ind // LB
  } else if eq(el, q_d_inf) {
    if abeq1(bl).truthy() {
      if equal(getsignl(bl), Fix(1L)) {
        Fix(1L)
      } else {
        q_d_ind
      }
    } else if abless1(bl).truthy() {
      if equal(getsignl(bl), Fix(1L)) {
        q_d_zeroa
      } else {
        Fix(0L)
      }
    } else if equal(getsignl(add2_star(Fix(-1L), bl)), Fix(1L)) {
      q_d_inf
    } else if equal(getsignl(add2_star(Fix(-1L), mk(q_mabs, [bl]))), Fix(1L)) {
      q_d_infinity
    } else {
      throw_tag(q_limit, t)
    }
  } else if eq(el, q_d_minf) {
    if abeq1(bl).truthy() {
      if equal(getsignl(bl), Fix(1L)) {
        Fix(1L)
      } else {
        q_d_ind
      }
    } else if equal(getsignl(add2_star(Fix(-1L), mk(q_mabs, [bl]))), Fix(1L)) {
      if equal(getsignl(bl), Fix(1L)) {
        q_d_zeroa
      } else {
        Fix(0L)
      }
    } else if !abless1(bl).truthy() {
      throw_tag(q_limit, t)
    } else if ratgreaterp(Fix(0L), bl).truthy() {
      q_d_infinity
    } else {
      q_d_inf
    }
  } else if eq(el, q_d_infinity) {
    if equal(limit__val(), q_d_infinity) {
      // Not enough info to do anything.
      q_d_und
    } else {
      // Which way the power goes is decided by the real part of the
      // exponent. The real part of a one-sided limit has to be taken from the
      // same side.
      let real_el = limit(car(trisplit(expo)), limit__var(), limit__val(), Nil)
      if eq(real_el, q_d_minf) {
        Fix(0L)
      } else if eq(real_el, q_d_inf) {
        q_d_infinity
      } else if eq(real_el, q_d_infinity) {
        throw_tag(q_limit, t) // don't really know real component
      } else {
        q_d_ind
      }
    }
  } else if eq(el, q_d_ind) {
    q_d_ind
  } else if zerop2(el).truthy() {
    Fix(1L)
  } else if eql(el, Fix(-1L)) {
    // direct substitution for el = -1
    ftake(q_mexpt, [bl, el])
  } else if off_negative_real_axisp(bl).truthy() {
    // When bl is off the negative real axis, use direct substitution
    ftake(q_mexpt, [bl, el])
  } else {
    // We're looking at (neg + {zerob, 0 zeroa} %i)^el. We need to do a
    // rectform on bas and decide if the imaginary part is zerob, 0, or
    // zeroa.
    with_special(q_ear_preserve_direction, t, () => {
      bas = risplit(bas)
      let x = car(bas)
      let y = cdr(bas)
      let xlim = limit(x, limit__var(), limit__val(), q_think)
      let ylim = limit(y, limit__var(), limit__val(), q_think)
      if eql(Fix(0L), y) {
        ftake(q_mexpt, [bl, el])
      } else if eq(ylim, q_d_zeroa) {
        mul2(
          ftake(q_mexpt, [mul2(Fix(-1L), xlim), el]),
          ftake(q_mexpt, [q_d__pcte, muln_([q_d__pcti, q_d__pctpi, el])]),
        )
      } else if eq(ylim, q_d_zerob) {
        mul2(
          ftake(q_mexpt, [mul2(Fix(-1L), xlim), el]),
          ftake(q_mexpt, [
            q_d__pcte,
            muln_([Fix(-1L), q_d__pcti, q_d__pctpi, el]),
          ]),
        )
      } else {
        throw_tag(q_limit, Nil)
      }
    })
  }
}

///|
fn even1(x : Value) -> Value raise {
  if numberp(x) {
    lbool(integerp(x) && evenp(x))
  } else if mnump(x).truthy() && evenp(cadr(x)) {
    t
  } else {
    Nil
  }
}

///|
/// is absolute value less than one?
fn abless1(bl : Value) -> Value raise {
  let bl = nmr(bl)
  if mnump(bl).truthy() {
    if ratgreaterp(Fix(1L), bl).truthy() {
      ratgreaterp(bl, Fix(-1L))
    } else {
      Nil
    }
  } else {
    lbool(equal(getsignl(add2_star(Fix(-1L), mk(q_mabs, [bl]))), Fix(-1L)))
  }
}

///|
/// is absolute value equal to one?
fn abeq1(bl : Value) -> Value raise {
  let bl = nmr(bl)
  if mnump(bl).truthy() {
    lbool(equal(Fix(1L), bl) || equal(bl, Fix(-1L)))
  } else {
    lbool(equal(getsignl(add2_star(Fix(-1L), mk(q_mabs, [bl]))), Fix(0L)))
  }
}

///|
fn simplimit(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([
    (q_exp, exp_),
    (q_var, var_),
    (q_val, val),
    (q_ear_preserve_direction, t),
  ])
  defer unbind_all(bs)
  let exp_ = limit__exp()
  if eq(var_, exp_) {
    return val
  }
  if !freeof(q_d_und, exp_).truthy() {
    return if eq(exp_, q_d_und) { q_d_und } else { throw_tag(q_limit, Nil) }
  }
  // SIMPINF maps zeroa and zerob to 0, so it would drop the side of a
  // product like 2*zeroa. SIMPLIMTIMES keeps it.
  if mtimesp(exp_).truthy() &&
    freeof(var_, exp_).truthy() &&
    amongl(list([q_d_zeroa, q_d_zerob]), exp_).truthy() &&
    !amongl(list([q_d_inf, q_d_minf, q_d_infinity, q_d_ind]), exp_).truthy() {
    return simplimtimes(cdr(exp_))
  }
  // When exp is freeof var, optionally apply simplify followed by simpinf.
  // Yes, the call to simplify is needed: sometimes exp has the form XXX^1.
  if freeof(var_, exp_).truthy() {
    return if atom(exp_) || mnump(exp_).truthy() {
      exp_
    } else {
      let r = simpinf(simplify(exp_))
      // SIMPINF could not absorb an ordinary factor into the infinity it
      // multiplies - inf*log(a) and the like. That is a failure, not a limit
      // value. A numeric coefficient is fine.
      if mtimesp(r).truthy() &&
        !every(f => freeof_extended_real(f).truthy(), cdr(r)) &&
        some(
          f => freeof_extended_real(f).truthy() && !mnump(f).truthy(),
          cdr(r),
        ) {
        throw_tag(q_limit, t)
      } else {
        r
      }
    }
  }
  // Lookup and dispatch a simplim%function from the property list
  let op = safe_get(mop(exp_), q_simplim_pctfunction)
  if op.truthy() {
    return funcall(op, [exp_, var_, val])
  }
  // And do the same for subscripted:
  if consp(exp_) && consp(car(exp_)) && eq(caar(exp_), q_mqapply) {
    let op = safe_get(subfunname(exp_), q_simplim_pctfunction)
    if op.truthy() {
      return funcall(op, [exp_, var_, val])
    }
  }
  let opr = caar(exp_)
  if mplusp(exp_).truthy() {
    // Without the call to rootscontract,
    //   limit(((-4)*x^2-10*x+24)/((4*x+8)^(1/3)+2),x,-4)
    // returns zero (should be 66).
    with_special(q_d_rootsconmode, Nil, () => d_rootscontract(simplimplus(exp_)))
  } else if mtimesp(exp_).truthy() {
    simplimtimes(cdr(exp_))
  } else if mexptp(exp_).truthy() {
    simplimexpt(
      cadr(exp_),
      caddr(exp_),
      limit(cadr(exp_), var_, val, q_think),
      limit(caddr(exp_), var_, val, q_think),
    )
  } else if eq(opr, q_p_sin) || eq(opr, q_p_cos) {
    simplimsc(exp_, opr, limit(cadr(exp_), var_, val, q_think))
  } else if eq(opr, q_p_sinh) || eq(opr, q_p_cosh) {
    simplimsch(opr, limit(cadr(exp_), var_, val, q_think))
  } else if eq(opr, q_p_erf) || eq(opr, q_p_tanh) {
    simplim_pcterf__pcttanh(opr, cadr(exp_))
  } else if eq(opr, q_p_inverse_jacobi_ns) {
    simplim_pctinverse_jacobi_ns(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_p_inverse_jacobi_nc) {
    simplim_pctinverse_jacobi_nc(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_p_inverse_jacobi_sc) {
    simplim_pctinverse_jacobi_sc(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_p_inverse_jacobi_cs) {
    simplim_pctinverse_jacobi_cs(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_p_inverse_jacobi_dc) {
    simplim_pctinverse_jacobi_dc(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_p_inverse_jacobi_ds) {
    simplim_pctinverse_jacobi_ds(
      limit(cadr(exp_), var_, val, q_think),
      third(exp_),
    )
  } else if eq(opr, q_mqapply) && eq(subfunname(exp_), q_d_psi) {
    simplim_dolpsi(subfunsubs(exp_), subfunargs(exp_), val)
  } else if eq(opr, var_) &&
    member(q_array, car(exp_)).truthy() &&
    every(sub_exp => free(sub_exp, var_).truthy(), cdr(exp_)) {
    exp_ // LIMIT(B[I],B,INF); -> B[I]
  } else if symval(q_d_limsubst).truthy() {
    // When limsubst is true, limit(f(n+1)/f(n),n,inf) = 1. The user
    // documentation warns against setting limsubst to true.
    simplify(
      cons(
        operator_with_array_flag(exp_),
        mapcar(a => limit(a, var_, val, q_think), cdr(exp_)),
      ),
    )
  } else {
    throw_tag(q_limit, t)
  }
}

///|
fn liminv(e : Value) -> Value raise {
  let e = resimplify(
    subst(div_star(Fix(1L), limit__var()), limit__var(), e),
  )
  let new_val = if eq(limit__val(), q_d_zeroa) {
    q_d_inf
  } else if eq(limit__val(), q_d_zerob) {
    q_d_minf
  } else {
    Nil
  }
  if new_val.truthy() {
    with_special(q_ear_preserve_direction, t, () => toplevel__dollimit(
      list([e, limit__var(), new_val]),
    ))
  } else {
    throw_tag(q_limit, t)
  }
}

///|
fn simplimtimes(exp_ : Value) -> Value raise {
  let b0 = bind(q_exp, exp_)
  defer unbind(b0)
  // The following test
  // handles         (-1)^x * 2^x => (-2)^x => $infinity
  // wants to avoid  (-1)^x * 2^x => $ind * $inf => $und
  let try_ = if expfactorp(cons(list1(q_mtimes), exp_), Fix(1L)).truthy() {
    expfactor(cons(list1(q_mtimes), exp_), Fix(1L), limit__var())
  } else {
    Nil
  }
  if try_.truthy() {
    return try_
  }
  let mut prod : Value = Fix(1L)
  let mut num : Value = Fix(1L)
  let b1 = bind(q_denom, Fix(1L))
  defer unbind(b1)
  let mut zf : Value = Nil
  let mut ind_flag = false
  let mut inf_type : Value = Nil
  let mut constant_zero = false
  let mut constant_infty = false
  let mut ind_prod : Value = Fix(1L)
  for term in exp_.iter() {
    let y = with_special(q_loginprod_q, involve(term, list1(q_p_log)), () => catch_tag(
      q_lip_q,
      () => limit(term, limit__var(), limit__val(), q_think),
    ))
    if y is Nil {
      // Limit failed
      return throw_tag(q_limit, t)
    } else if eq(y, q_lip_bang) {
      // limit failed due to log in product
      return liminv(cons(list2(q_mtimes, q_simp), exp_))
    } else if zerop2(y).truthy() {
      // If the limit is infinitesimal or zero
      num = mul2_star(num, term)
      constant_zero = constant_zero || !among(limit__var(), term).truthy()
      if eq(y, q_d_zeroa) {
        if zf is Nil {
          zf = Fix(1L)
        }
      } else if eq(y, q_d_zerob) {
        zf = num_mul(Fix(-1L), if zf.truthy() { zf } else { Fix(1L) })
      } else {
        // A zero without a side leaves the product without one.
        zf = Fix(0L)
      }
    } else if !limit__memq(y, [q_d_inf, q_d_minf, q_d_infinity, q_d_ind, q_d_und]) {
      // If the limit is not some form of infinity or undefined/indeterminate.
      prod = mul2_star(prod, y)
    } else if eq(y, q_d_und) {
      return q_d_und
    } else if eq(y, q_d_ind) {
      ind_flag = true
      ind_prod = mul2_star(ind_prod, term)
    } else {
      // Some form of infinity
      set(q_denom, mul2_star(symval(q_denom), term)) |> ignore
      constant_infty = constant_infty || !among(limit__var(), term).truthy()
      if !eq(inf_type, q_d_infinity) {
        if eq(y, q_d_infinity) {
          inf_type = q_d_infinity
        } else if inf_type is Nil {
          inf_type = y
        } else if eq(y, inf_type) {
          // minf * minf or inf * inf
          inf_type = q_d_inf
        } else {
          // minf * inf
          inf_type = q_d_minf
        }
      }
    }
  }
  let denom = symval(q_denom)
  if constant_zero && constant_infty {
    // If there are zeros and infinities among the terms that are free of
    // VAR, then we have an expression like "inf * zeroa * f(x)" or similar.
    // That gives an undefined result.
    q_d_und
  } else if eql(num, Fix(1L)) && eql(denom, Fix(1L)) {
    // If num=denom=1, we didn't find any explicit infinities or zeros, so we
    // either return the simplified product or ind
    if ind_flag {
      q_d_ind
    } else {
      prod
    }
  } else if equal(denom, Fix(1L)) {
    // If denom=1 (and so num != 1), we have some form of zero
    if zf is Nil {
      Fix(0L)
    } else {
      let mut sign = getsignl(prod)
      // A factor with an ind limit is bounded but has no limit. It keeps the
      // direction of the zero only when its sign is known, otherwise the sign
      // of the product alternates, and only the zero survives.
      if ind_flag && fixnump(sign) {
        let k = if freeof_extended_real(ind_prod).truthy() {
          d_csign(ind_prod)
        } else {
          Nil
        }
        sign = if eq(k, q_d_pos) {
          sign
        } else if eq(k, q_d_neg) {
          num_neg(sign)
        } else {
          Nil
        }
      }
      if !sign.truthy() || eq(sign, q_complex) {
        Fix(0L)
      } else {
        let p = num_mul(zf, sign)
        if eql(p, Fix(0L)) {
          Fix(0L)
        } else if eql(p, Fix(1L)) {
          q_d_zeroa
        } else if eql(p, Fix(-1L)) {
          q_d_zerob
        } else {
          raise LispError::SimpleError(
            "fell through ECASE expression: \{p} is not one of (0 1 -1)",
          )
        }
      }
    }
  } else if equal(num, Fix(1L)) {
    // If num=1 (and so denom != 1), we have some form of infinity
    let sign = d_csign(prod)
    if ind_flag {
      // A non-real indeterminate factor of constant modulus leaves the
      // modulus of the product infinite and only its phase unknown. A real
      // one instead alternates in sign, which is undefined.
      if mnump(ftake(q_mabs, [ind_prod])).truthy() &&
        limit__memq(d_csign(ind_prod), [q_d_complex, q_d_imaginary]) {
        q_d_infinity
      } else {
        q_d_und
      }
    } else if eq(sign, q_d_pos) {
      inf_type
    } else if eq(sign, q_d_neg) {
      if eq(inf_type, q_d_inf) {
        q_d_minf
      } else if eq(inf_type, q_d_minf) {
        q_d_inf
      } else {
        q_d_infinity
      }
    } else if limit__memq(sign, [q_d_complex, q_d_imaginary]) {
      // $CSIGN answers '$COMPLEX whenever it cannot show PROD is real. So
      // settle realness from the imaginary part, and read the sign verdict
      // only for whether PROD can vanish: '$PNZ, '$PZ and '$NZ all admit
      // zero, and there the limit may be 0 rather than an infinity at all.
      if limit__memq(csign(prod), [q_d_pnz, q_d_pz, q_d_nz]) &&
        !eq(t, mnqp(Fix(0L), d_imagpart(prod))) {
        throw_tag(q_limit, t)
      } else {
        q_d_infinity
      }
    } else {
      // sign is '$zero, $pnz, $pz, etc
      throw_tag(q_limit, t)
    }
  } else {
    // Both zeros and infinities. All bets off if there are some infinities
    // or some zeros, but it needn't be undefined (see above)
    if constant_zero || constant_infty {
      throw_tag(q_limit, t) |> ignore
    }
    let ans = limit2(
      num,
      power_star(denom, Fix(-1L)),
      limit__var(),
      limit__val(),
    )
    if ans.truthy() {
      simplimtimes(list([prod, ans, ind_prod]))
    } else {
      throw_tag(q_limit, t)
    }
  }
}

///|
/// At one time when simplimplus1 failed to find a limit, this function
/// applied ratsimp and tried again. This scheme didn't fix any testsuite bugs
/// and it slowed the code, so it was removed.
fn simplimplus(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  if memalike(exp_, symval(q_simplimplus_problems)).truthy() {
    return throw_tag(q_limit, t)
  }
  set(q_simplimplus_problems, cons(exp_, symval(q_simplimplus_problems)))
  |> ignore
  defer {
    set(q_simplimplus_problems, cdr(symval(q_simplimplus_problems))) |> ignore
  }
  let ans = catch_tag(q_limit, () => simplimplus1(exp_))
  if ans is Nil || eq(ans, t) || among(q_p_limit, ans).truthy() {
    throw_tag(q_limit, t)
  } else {
    resimp_extra_simp(ans)
  }
}

///|
fn simplimplus1(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  let mut sum : Value = Nil
  let mut y : Value = Nil
  let mut infl : Value = Nil
  let mut infinityl : Value = Nil
  let mut minfl : Value = Nil
  let mut indl : Value = Nil
  let mut undl : Value = Nil
  let mut zerobl : Value = Nil
  let mut zeroal : Value = Nil
  let mut ans : Value = Nil
  let mut r : Value = Nil
  let mut undir = false
  for term in cdr(exp_).iter() {
    let f = limit(term, limit__var(), limit__val(), q_think)
    if f is Nil {
      throw_tag(q_limit, t) |> ignore
    } else if eq(f, q_d_und) {
      undl = cons(term, undl)
    } else if eq(f, q_d_zerob) {
      zerobl = cons(term, zerobl)
    } else if eq(f, q_d_zeroa) {
      zeroal = cons(term, zeroal)
    } else if eq(f, q_d_ind) {
      indl = cons(term, indl)
    } else if eq(f, q_d_inf) {
      infl = cons(term, infl)
    } else if eq(f, q_d_minf) {
      minfl = cons(term, minfl)
    } else if eq(f, q_d_infinity) {
      infinityl = cons(term, infinityl)
    } else {
      sum = cons(f, sum)
      // This term tends to its limit from an unknown side.
      if !freeof(limit__var(), term).truthy() &&
        free(f, q_d_zeroa).truthy() &&
        free(f, q_d_zerob).truthy() {
        undir = true
      }
    }
  }
  // When there are two or more infinity terms, we dispatch gruntz1 on the
  // rectangular form of their sum. When gruntz1 is able to find the limit, we
  // modify the lists infinityl, minfl, ... accordingly.
  if infinityl.truthy() &&
    cdr(infinityl).truthy() &&
    !among(q_d_li, cons(list1(q_mlist), infinityl)).truthy() {
    let infinityl_sum = fapply(q_mplus, infinityl)
    let b2 = bind(q_d_radexpand, Nil)
    defer unbind(b2)
    ans = risplit(infinityl_sum)
    let mut re = car(ans)
    let mut im = cdr(ans)
    re = catch_tag(q_taylor_catch, () => with_special(
      q_silent_taylor_flag,
      t,
      () => gruntz1(re, limit__var(), limit__val(), Nil),
    ))
    im = catch_tag(q_taylor_catch, () => with_special(
      q_silent_taylor_flag,
      t,
      () => gruntz1(im, limit__var(), limit__val(), Nil),
    ))
    r = if re is Nil || im is Nil {
      Nil
    } else if infinityp(im).truthy() {
      q_d_infinity
    } else if infinityp(re).truthy() {
      re
    } else {
      add2(re, mul2(q_d__pcti, im))
    }
    if eq(r, q_d_infinity) {
      list1(fapply(q_mplus, infinityl)) |> ignore
    } else if r is Nil {
      throw_tag(q_limit, t) |> ignore
    } else {
      infinityl = Nil
      if eq(r, q_d_zerob) {
        zerobl = cons(infinityl_sum, zerobl)
      } else if eq(r, q_d_zeroa) {
        zeroal = cons(infinityl_sum, zeroal)
      } else if eq(r, q_d_ind) {
        indl = cons(infinityl_sum, indl)
      } else if eq(r, q_d_und) {
        undl = cons(infinityl_sum, undl)
      } else if eq(r, q_d_minf) {
        minfl = cons(infinityl_sum, minfl)
      } else if eq(r, q_d_inf) {
        infl = cons(infinityl_sum, infl)
      } else {
        sum = cons(r, sum)
        undir = true
      }
    }
  }
  // An infinity term next to inf or minf terms: the larger side decides, and
  // when neither does, the terms are re-summed below like inf and minf
  // terms. Give up with und terms around as well, and when an infinity term
  // carries PRIN-INF, DEFINT's stand-in for a large real number.
  if infinityl.truthy() && (minfl.truthy() || infl.truthy()) {
    if undl.truthy() || !free(fapply(q_mplus, infinityl), q_prin_inf).truthy() {
      throw_tag(q_limit, t) |> ignore
    } else {
      let d = simplimplus_dominance(
        infinityl,
        append(infl, minfl),
        q_d_infinity,
      )
      if d.truthy() {
        return simplimplus_with_finite(d, fapply(q_mplus, sum))
      }
    }
  }
  // Blend the zerob, zeroa, and sum terms. When there are both zerob and
  // zeroa terms, ignore them. When *preserve-direction* is true and there are
  // zerob terms, push zerob into the sum terms. And do the same for zeroa.
  if symval(q_ear_preserve_direction).truthy() &&
    zerobl.truthy() &&
    zeroal is Nil {
    sum = cons(q_d_zerob, sum)
  }
  if symval(q_ear_preserve_direction).truthy() &&
    zeroal.truthy() &&
    zerobl is Nil {
    sum = cons(q_d_zeroa, sum)
  }
  // When indl has two or more members, we attempt to condense the ind terms
  // into a single term, using factor (needed for cases such as
  // limit(cos(1/x)*sin(x)-sin(x),x,inf)).
  if indl.truthy() && cdr(indl).truthy() {
    ans = d_factor(fapply(q_mplus, indl))
    r = if mplusp(ans).truthy() {
      Nil
    } else {
      limit(ans, limit__var(), limit__val(), q_think)
    }
    if eq(r, q_d_zerob) {
      zerobl = cons(ans, zerobl)
      indl = Nil
    } else if eq(r, q_d_zeroa) {
      zeroal = cons(ans, zeroal)
      indl = Nil
    } else if eq(r, q_d_ind) {
      indl = list1(ans)
    } else if eq(r, q_d_und) {
      indl = Nil
      undl = cons(ans, undl)
    } else if eq(r, q_d_minf) || eq(r, q_d_inf) || eq(r, q_d_infinity) {
      throw_tag(q_limit, t) |> ignore
    } else if r.truthy() {
      // A finite limit, 0 included, condenses the ind terms.
      sum = cons(r, sum)
      indl = Nil
      undir = true
    }
  }
  // Add the members of the list sum.
  sum = fapply(q_mplus, sum)
  if undl.truthy() {
    // When there are inf or minf terms, the limit might not be und: the
    // infinities may dominate the und terms, as in
    // limit(x^2+x*sin(x),x,inf); SIMPLIMPLUS-DOMINANCE decides. Without them
    // the limit is und.
    if infl.truthy() || minfl.truthy() {
      return simplimplus_with_finite(
        simplimplus_dominance(undl, append(infl, minfl), q_d_und),
        sum,
      )
    } else {
      return q_d_und
    }
  } else if !(infl.truthy() || minfl.truthy() || indl.truthy() || infinityl.truthy()) {
    // The side of a vanishing sum is unknown when a term tends to its limit
    // from an unknown side.
    return if undir && zerop1(ridofab(sum)).truthy() {
      Fix(0L)
    } else if atom(sum) {
      sum
    } else if !free(sum, q_d_zeroa).truthy() || !free(sum, q_d_zerob).truthy() {
      simpab(sum)
    } else {
      sum
    }
  } else if infinityl is Nil {
    if infl.truthy() {
      if minfl is Nil {
        return simplimplus_with_finite(q_d_inf, sum)
      }
      // (go oon)
    } else if minfl.truthy() {
      return simplimplus_with_finite(q_d_minf, sum)
    } else if indl.truthy() {
      return q_d_ind
    }
  } else {
    infl = append(infl, infinityl)
  }
  // oon
  y = addn(append(minfl, infl), Nil)
  y = sratsimp(hyperex(y))
  if alike1(exp_, y).truthy() {
    if !infinityp(limit__val()).truthy() {
      infl = cnv(infl, limit__val()) // THIS IS HORRIBLE!!!!
      minfl = cnv(minfl, limit__val())
    }
    let infl1 = infl
    let minfl1 = minfl
    y = with_special(q_val, q_d_inf, () => if every(
        j => radicalp(j, limit__var()).truthy(),
        append(infl1, minfl1),
      ) {
      rheur(infl1, minfl1)
    } else {
      sheur(infl1, minfl1)
    })
  } else {
    y = limit(y, limit__var(), limit__val(), q_think)
  }
  if y is Nil || eq(y, t) {
    Nil
  } else if infinityp(y).truthy() {
    simplimplus_with_finite(y, sum)
  } else if indl.truthy() {
    q_d_ind
  } else {
    add2_star(sum, y)
  }
}

///|
/// The limit of TERM/I, or NIL. LIMIT cannot always place an und numerator
/// over an infinite denominator - SIMPLIMTIMES on the factors of the ratio
/// can.
fn simplimplus_term_ratio(term : Value, i : Value) -> Value raise {
  let r = div(term, i)
  let l = limit_catch(r, limit__var(), limit__val())
  if l.truthy() {
    l
  } else if mtimesp(r).truthy() {
    let y = catch_tag(q_limit, () => simplimtimes(cdr(r)))
    if eq(y, t) {
      Nil
    } else {
      y
    }
  } else {
    Nil
  }
}

///|
/// The limit of a sum of TERMS, whose limits are all und or all infinity,
/// and INFL, whose limits are inf or minf. The infinities decide the limit
/// when they dominate every term. When a term outgrows them, the limit is
/// ANSWER. When the ratios r of the terms to the infinities are bounded, the
/// sum is I*(1+r), and the sign of 1+r decides.
fn simplimplus_dominance(
  terms : Value,
  infl : Value,
  answer : Value,
) -> Value raise {
  let i = fapply(q_mplus, infl)
  let ilim = limit_catch(i, limit__var(), limit__val())
  if ilim is Nil {
    throw_tag(q_limit, t)
  } else if !infinityp(ilim).truthy() {
    // A bounded sum of the infinities leaves the terms to decide.
    if eq(ilim, q_d_und) {
      q_d_und
    } else {
      answer
    }
  } else {
    let ratios = mapcar(term => simplimplus_term_ratio(term, i), terms)
    if member(Nil, ratios).truthy() {
      throw_tag(q_limit, t)
    } else if every(x => zerop2(x).truthy(), ratios) {
      // The infinities dominate. An infinity term still keeps the sum from
      // being real, and inf and minf are real.
      if eq(answer, q_d_infinity) {
        q_d_infinity
      } else {
        ilim
      }
    } else if some(x => infinityp(x).truthy(), ratios) {
      answer
    } else if member(q_d_und, ratios).truthy() {
      q_d_und
    } else if !limit__memq(ilim, [q_d_inf, q_d_minf]) {
      // infinity has no direction to dominate with.
      q_d_und
    } else {
      // ind ratios stand for the expressions, the others for their values.
      let sgn = d_csign(
        add2(
          Fix(1L),
          fapply(
            q_mplus,
            mapcar2(
              (term, r) => if eq(r, q_d_ind) { div(term, i) } else { r },
              terms,
              ratios,
            ),
          ),
        ),
      )
      if eq(sgn, q_d_pos) {
        ilim
      } else if eq(sgn, q_d_neg) {
        if eq(ilim, q_d_inf) {
          q_d_minf
        } else {
          q_d_inf
        }
      } else if eq(sgn, q_d_zero) && eq(answer, q_d_infinity) {
        // 1+r is 0: the leading terms cancel, so nothing here decides.
        Nil
      } else {
        throw_tag(q_limit, t)
      }
    }
  }
}

///|
/// ANS, the inf or minf SIMPLIMPLUS1 found for the infinite terms of a sum,
/// unless the finite terms SUM keep the sum off the real line.
fn simplimplus_with_finite(ans : Value, sum : Value) -> Value raise {
  if limit__memq(ans, [q_d_inf, q_d_minf]) &&
    limit__memq(d_csign(sum), [q_d_imaginary, q_d_complex]) {
    q_d_infinity
  } else {
    ans
  }
}

///|
/// Limit n/d, using heuristics on the order of growth.
fn sheur0(n : Value, d : Value) -> Value raise {
  let orig_n = n
  if free(n, limit__var()).truthy() && free(d, limit__var()).truthy() {
    div_star(n, d)
  } else {
    let n = cpa(n, d, Nil)
    if equal(n, Fix(1L)) {
      if oscip(orig_n).truthy() {
        q_d_und
      } else {
        q_d_inf
      }
    } else if equal(n, Fix(-1L)) {
      q_d_zeroa
    } else if equal(n, Fix(0L)) {
      div_star(orig_n, d)
    } else {
      Nil
    }
  }
}

///|
/// L1 is a list of INF's and L2 is a list of MINF's. Added together it is
/// indeterminate.
fn sheur(l1 : Value, l2 : Value) -> Value raise {
  let term = sheur1(l1, l2)
  if equal(term, q_d_inf) {
    q_d_inf
  } else if equal(term, q_d_minf) {
    q_d_minf
  } else {
    let new_num = addn(
      mapcar(num_term => div_star(num_term, car(l1)), append(l1, l2)),
      Nil,
    )
    limit2(
      new_num,
      div_star(Fix(1L), car(l1)),
      limit__var(),
      limit__val(),
    )
  }
}

///|
fn frac(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  if atom(exp_) {
    Nil
  } else {
    set(q_exp, nformat(exp_)) |> ignore
    let e = limit__exp()
    if eq(caar(e), q_mquotient) && among(limit__var(), caddr(e)).truthy() {
      t
    } else {
      Nil
    }
  }
}

///|
fn zerop2(z : Value) -> Value raise {
  lbool(eq0(ridofab(z)))
}

///|
fn raise_(a : Value) -> Value raise {
  add2_star(a, q_d_zeroa)
}

///|
fn lower(a : Value) -> Value raise {
  add2_star(a, q_d_zerob)
}

///|
fn sincoshk(exp1 : Value, l : Value, sc : Value) -> Value raise {
  if equal(l, Fix(1L)) {
    lower(l)
  } else if equal(l, Fix(-1L)) {
    raise_(l)
  } else if among(sc, l).truthy() {
    l
  } else if limit__memq(limit__val(), [q_d_zeroa, q_d_zerob]) {
    spangside(exp1, l)
  } else {
    l
  }
}

///|
fn spangside(e : Value, l : Value) -> Value raise {
  let e = behavior(e, limit__var(), limit__val())
  if equal(e, Fix(1L)) {
    raise_(l)
  } else if equal(e, Fix(-1L)) {
    lower(l)
  } else {
    l
  }
}

///|
/// get rid of zeroa and zerob
fn ridofab(e : Value) -> Value raise {
  let mut e = e
  if among(q_d_zeroa, e).truthy() {
    e = maxima_substitute(Fix(0L), q_d_zeroa, e)
  }
  if among(q_d_zerob, e).truthy() {
    e = maxima_substitute(Fix(0L), q_d_zerob, e)
  }
  e
}

///|
/// simple radical: returns true if exp is a polynomial raised to a numeric
/// power
fn simplerd(exp_ : Value) -> Value raise {
  if mexptp(exp_).truthy() && mnump(caddr(exp_)).truthy() {
    // exponent must be a number - no variables
    polyp(cadr(exp_))
  } else {
    Nil
  }
}

///|
fn branch1(exp_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_val, val)])
  defer unbind_all(bs)
  if polyp(exp_).truthy() {
    Nil
  } else if simplerd(exp_).truthy() {
    zerop2(subin(val, cadr(exp_)))
  } else {
    let mut v = cdr(exp_)
    while v is Cons(_) {
      if branch1(car(v), val).truthy() {
        return v
      }
      v = cdr(v)
    }
    Nil
  }
}

///|
fn branch(exp_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_val, val)])
  defer unbind_all(bs)
  if polyp(exp_).truthy() {
    Nil
  } else if simplerd(exp_).truthy() || mtimesp(exp_).truthy() {
    branch1(exp_, val)
  } else if mplusp(exp_).truthy() {
    lbool(every(j => branch(j, val).truthy(), cdr(exp_)))
  } else {
    Nil
  }
}

///|
fn ser0(e : Value, n : Value, d : Value, val : Value) -> Value raise {
  let b = bind(q_val, val)
  defer unbind(b)
  if branch(n, val).truthy() && branch(d, val).truthy() {
    set(q_nn_star, Nil) |> ignore
    let mut n = ser1(n)
    let mut d = ser1(d)
    // NN* gets set by POFX, called by SER1, to get a list of exponents.
    set(q_nn_star, ratmin(symval(q_nn_star))) |> ignore
    n = sratsimp(power_star(n, power_star(limit__var(), symval(q_nn_star))))
    d = sratsimp(power_star(d, power_star(limit__var(), symval(q_nn_star))))
    if limit__memq(limit__val(), [q_d_zeroa, q_d_zerob]) {
      ()
    } else {
      set(q_val, Fix(0L)) |> ignore
    }
    radlim(e, n, d)
  } else {
    try_lhospital_quit(n, d, Nil)
  }
}

///|
fn rheur(l1 : Value, l2 : Value) -> Value raise {
  let m1 = mapcar(x => asymredu(x), l1)
  let m2 = mapcar(x => asymredu(x), l2)
  let ans = addn(append(m1, m2), Nil)
  if rptrouble(addn(append(l1, l2), Nil)).truthy() {
    limit(
      simplify(rdsget(addn(append(l1, l2), Nil))),
      limit__var(),
      limit__val(),
      Nil,
    )
  } else if mplusp(ans).truthy() {
    sheur(m1, m2)
  } else {
    limit(ans, limit__var(), limit__val(), t)
  }
}

///|
fn rptrouble(rp : Value) -> Value raise {
  lbool(!equal(rddeg(rp, Nil), rddeg(asymredu(rp), Nil)))
}

///|
fn radicalp(exp_ : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_)])
  defer unbind_all(bs)
  let p = polyinx(exp_, var_, Nil)
  if p.truthy() {
    p
  } else if mexptp(exp_).truthy() {
    if equal(caddr(exp_), Fix(-1L)) {
      radicalp(cadr(exp_), var_)
    } else {
      simplerd(exp_)
    }
  } else if eq(caar(exp_), q_mplus) || eq(caar(exp_), q_mtimes) {
    lbool(every(j => radicalp(j, var_).truthy(), cdr(exp_)))
  } else {
    Nil
  }
}

///|
fn involve(e : Value, nn_star : Value) -> Value raise {
  let b = bind(q_nn_star, nn_star)
  defer unbind(b)
  if atom(e) {
    Nil
  } else if mnump(e).truthy() {
    Nil
  } else if memq(caar(e), nn_star).truthy() &&
    among(limit__var(), cdr(e)).truthy() {
    cadr(e)
  } else {
    some_value(j => involve(j, nn_star), cdr(e))
  }
}

///|
/// Just like INVOLVE, except the dependency on VAR is explicit (second arg
/// here). Use this instead.
fn involve_var(e : Value, var1 : Value, nn_star : Value) -> Value raise {
  let b = bind(q_nn_star, nn_star)
  defer unbind(b)
  if atom(e) {
    Nil
  } else if mnump(e).truthy() {
    Nil
  } else if memq(caar(e), nn_star).truthy() && among(var1, cdr(e)).truthy() {
    cadr(e)
  } else {
    some_value(j => involve_var(j, var1, nn_star), cdr(e))
  }
}

///|
/// Why not implement this as (NOT (INVOLVE EXP NN*))?
fn notinvolve(exp_ : Value, nn_star : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_nn_star, nn_star)])
  defer unbind_all(bs)
  if atom(exp_) {
    t
  } else if mnump(exp_).truthy() {
    t
  } else if memq(caar(exp_), nn_star).truthy() {
    lbool(!among(limit__var(), cdr(exp_)).truthy())
  } else if every(j => notinvolve(j, nn_star).truthy(), cdr(exp_)) {
    t
  } else {
    Nil
  }
}

///|
/// Just like NOTINVOLVE, except the dependency on VAR is explicit (second
/// arg here). Use this instead.
fn notinvolve_var(exp_ : Value, var1 : Value, nn_star : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_nn_star, nn_star)])
  defer unbind_all(bs)
  if atom(exp_) {
    t
  } else if mnump(exp_).truthy() {
    t
  } else if memq(caar(exp_), nn_star).truthy() {
    lbool(!among(var1, cdr(exp_)).truthy())
  } else if every(j => notinvolve_var(j, var1, nn_star).truthy(), cdr(exp_)) {
    t
  } else {
    Nil
  }
}

///|
fn sheur1(l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = mapcar(x => stirling0(x), l1)
  let mut l2 = mapcar(x => stirling0(x), l2)
  l1 = addn(maxi(l1), Nil)
  l2 = addn(maxi(l2), Nil)
  let ans = cpa(l1, l2, t)
  if eq0(ans) {
    add2_star(l1, l2)
  } else if equal(ans, Fix(1L)) {
    q_d_inf
  } else {
    q_d_minf
  }
}

///|
fn zero_lim(cpa_list : Value) -> Value raise {
  for x in cpa_list.iter() {
    if eq(car(x), q_gen) &&
      zerop2(limit(cadr(x), limit__var(), limit__val(), q_think)).truthy() {
      return t
    }
  }
  Nil
}

///|
/// Compare order of growth for R1 and R2. The result is 0, -1, +1 depending
/// on the relative order of growth. 0 is returned if R1 and R2 have the same
/// growth; -1 if R1 grows much more slowly than R2; +1 if R1 grows much more
/// quickly than R2.
fn cpa(r1 : Value, r2 : Value, flag : Value) -> Value raise {
  let mut t1 = r1
  let mut t2 = r2
  let var_ = limit__var()
  let val = limit__val()
  if alike1(t1, t2).truthy() {
    Fix(0L)
  } else if free(t1, var_).truthy() {
    if free(t2, var_).truthy() {
      Fix(0L)
    } else {
      let lim_ans = limit1(t2, var_, val)
      if !limit__memq(lim_ans, [q_d_inf, q_d_minf, q_d_und, q_d_ind]) {
        Fix(0L)
      } else {
        Fix(-1L)
      }
    }
  } else if free(t2, var_).truthy() {
    let lim_ans = limit1(t1, var_, val)
    if !limit__memq(lim_ans, [q_d_inf, q_d_minf, q_d_und, q_d_ind]) {
      Fix(0L)
    } else {
      Fix(1L)
    }
  } else {
    // Make T1 and T2 be a list of terms that are multiplied together.
    t1 = if mtimesp(t1).truthy() { cdr(t1) } else { list1(t1) }
    t2 = if mtimesp(t2).truthy() { cdr(t2) } else { list1(t2) }
    // Find the strengths of each term of T1 and T2
    t1 = mapcar(x => istrength(x), t1)
    t2 = mapcar(x => istrength(x), t2)
    // Compute the max of the strengths of the terms.
    let mut ans = ismax(t1)
    let mut d = ismax(t2)
    if ans is Nil || d is Nil {
      // ismax couldn't find highest term; give up
      Fix(0L)
    } else {
      if eq(car(ans), q_var) {
        ans = add_up_deg(t1)
      }
      if eq(car(d), q_var) {
        d = add_up_deg(t2)
      }
      // Can't just just compare dominating terms if there are
      // indeterm-inates present; e.g. X-X^2*LOG(1+1/X). So check for this.
      if zero_lim(t1).truthy() || zero_lim(t2).truthy() {
        cpa_indeterm(ans, d, t1, t2, flag)
      } else if isgreaterp(ans, d).truthy() {
        Fix(1L)
      } else if isgreaterp(d, ans).truthy() {
        Fix(-1L)
      } else {
        Fix(0L)
      }
    }
  }
}

///|
fn cpa_indeterm(
  ans : Value,
  d : Value,
  t1 : Value,
  t2 : Value,
  flag : Value,
) -> Value raise {
  let mut ans = ans
  let mut d = d
  if !eq(car(ans), q_var) {
    ans = gather(ans, t1)
    d = gather(d, t2)
  }
  let b = bind(q_n_starindicator, if eq(car(ans), q_exp) { flag } else { Nil })
  defer unbind(b)
  let test_ = cpa1(ans, d)
  if zerop1(test_).truthy() &&
    (
      equal(d_radcan(div_star(cadr(ans), cadr(d))), Fix(1L)) ||
      (
        polyp(cadr(ans)).truthy() &&
        polyp(cadr(d)).truthy() &&
        equal(
          limit(
            div_star(cadr(ans), cadr(d)),
            limit__var(),
            limit__val(),
            q_think,
          ),
          Fix(1L),
        )
      )
    ) {
    let new_term1 = div_star(t1, cadr(ans))
    let new_term2 = div_star(t2, cadr(d))
    cpa(new_term1, new_term2, flag)
  } else {
    Fix(0L)
  }
}

///|
fn add_up_deg(strengthl : Value) -> Value raise {
  let mut poxl : Value = Nil
  let mut degl : Value = Nil
  for st in strengthl.iter() {
    if eq(car(st), q_var) {
      poxl = cons(cadr(st), poxl)
      degl = cons(caddr(st), degl)
    }
  }
  list([q_var, muln(poxl, Nil), addn(degl, Nil)])
}

///|
fn cpa1(p1 : Value, p2 : Value) -> Value raise {
  if eq(car(p1), q_gen) {
    return Fix(0L)
  }
  let flag = car(p1)
  let mut p1 = cadr(p1)
  let mut p2 = cadr(p2)
  let var_ = limit__var()
  if eq(flag, q_var) {
    let mut s1 = istrength(p1)
    let s2 = istrength(p2)
    if isgreaterp(s1, s2).truthy() {
      Fix(1L)
    } else if isgreaterp(s2, s1).truthy() {
      Fix(-1L)
    } else if symval(q_n_starindicator).truthy() {
      set(q_n_starindicator, Nil) |> ignore
      if poly_q(p1, var_).truthy() && poly_q(p2, var_).truthy() {
        p1 = sub_star(p1, p2)
        if zerop1(p1).truthy() {
          Fix(0L)
        } else {
          getsignl(hot_coef(p1))
        }
      } else {
        s1 = rheur(list1(p1), list1(mul2(Fix(-1L), p2)))
        if zerop2(s1).truthy() {
          Fix(0L)
        } else if ratgreaterp(s1, Fix(0L)).truthy() {
          Fix(1L)
        } else {
          Fix(-1L)
        }
      }
    } else {
      Fix(0L)
    }
  } else if eq(flag, q_exp) {
    p1 = caddr(p1)
    p2 = caddr(p2)
    if poly_q(p1, var_).truthy() && poly_q(p2, var_).truthy() {
      p1 = sub_star(p1, p2)
      if zerop1(p1).truthy() || !among(var_, p1).truthy() {
        Fix(0L)
      } else {
        getsignl(hot_coef(p1))
      }
    } else if radicalp(p1, var_).truthy() && radicalp(p2, var_).truthy() {
      let s1 = rheur(list1(p1), list1(mul2(Fix(-1L), p2)))
      if eq(s1, q_d_inf) {
        Fix(1L)
      } else if eq(s1, q_d_minf) {
        Fix(-1L)
      } else if mnump(s1).truthy() {
        if ratgreaterp(s1, Fix(0L)).truthy() {
          Fix(1L)
        } else if ratgreaterp(Fix(0L), s1).truthy() {
          Fix(-1L)
        } else {
          Fix(0L)
        }
      } else {
        Fix(0L)
      }
    } else {
      cpa(p1, p2, t)
    }
  } else if eq(flag, q_log) {
    let p1 = try_lhospital(asymredu(p1), asymredu(p2), Nil)
    if zerop2(p1).truthy() {
      Fix(-1L)
    } else if real_infinityp(p1).truthy() {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else {
    Nil
  }
}

///|
/// EXPRESSIONS TO ISGREATERP ARE OF THE FOLLOWING FORMS
///   ("VAR" POLY DEG)
///   ("EXP" %E^EXP)
///   ("LOG" LOG(EXP))
///   ("FACT" <A FACTORIAL EXPRESSION>)
///   ("GEN" <ANY OTHER TYPE OF EXPRESSION>)
fn isgreaterp(a : Value, b : Value) -> Value raise {
  let ta = car(a)
  let tb = car(b)
  if eq(ta, q_gen) || eq(tb, q_gen) {
    Nil
  } else if eq(ta, tb) && eq(ta, q_var) {
    ratgreaterp(caddr(a), caddr(b))
  } else if eq(ta, tb) && eq(ta, q_exp) {
    // Both are exponential order of infinity. Check the exponents to
    // determine which exponent is bigger.
    lbool(
      eq(
        limit(
          sub_star(mk(q_p_log, [second(a)]), mk(q_p_log, [second(b)])),
          limit__var(),
          limit__val(),
          q_think,
        ),
        q_d_inf,
      ),
    )
  } else {
    memq(
      ta,
      cdr(memq(tb, list([q_num, q_log, q_var, q_exp, q_fact, q_gen]))),
    )
  }
}

///|
/// Preprocess the list of products. Separate the terms that exponentials and
/// those that don't. Actually multiply the exponential terms together to form
/// a single term. Pass this and the rest to ismax-core to find the max.
fn ismax(l : Value) -> Value raise {
  let mut exp_terms : Value = Nil
  let mut non_exp_terms : Value = Nil
  for term in l.iter() {
    if eq(q_exp, car(term)) {
      exp_terms = cons(term, exp_terms)
    } else {
      non_exp_terms = cons(term, non_exp_terms)
    }
  }
  // Multiply the exp-terms together
  if exp_terms.truthy() {
    let mut product : Value = Fix(1L)
    for term in exp_terms.iter() {
      product = simplify(mul2(product, second(term)))
    }
    let product = list2(q_exp, d_logcontract(product))
    ismax_core(cons(product, non_exp_terms))
  } else {
    ismax_core(l)
  }
}

///|
fn ismax_core(l : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if atom(l) {
    Nil
  } else if length(l) == 1 {
    // If there is only 1 thing give it back.
    car(l)
  } else if every(x => !eq(car(x), q_gen), l) {
    let mut l1 = cdr(l)
    let mut temp_ans = car(l)
    let mut ans : Value = Nil
    while l1.truthy() {
      if isgreaterp(temp_ans, car(l1)).truthy() {
        ans = temp_ans
      } else if isgreaterp(car(l1), temp_ans).truthy() {
        temp_ans = car(l1)
        ans = temp_ans
      } else {
        ans = Nil
      }
      l1 = cdr(l1)
    }
    ans
  } else {
    Nil
  }
}

///|
/// RETURNS LIST OF HIGH TERMS
fn maxi(all : Value) -> Value raise {
  if atom(all) {
    return Nil
  }
  let mut l = cdr(all)
  let mut hi_term = car(all)
  let mut total : Value = Fix(1L) // running total constant factor of hi-term
  let mut hi_terms = ncons(car(all))
  while l.truthy() {
    let compare = limit(
      div_star(car(l), hi_term),
      limit__var(),
      limit__val(),
      q_think,
    )
    if infinityp(compare).truthy() ||
      (
        eq(compare, q_d_und) &&
        zerop2(
          limit(div_star(hi_term, car(l)), limit__var(), limit__val(), q_think),
        ).truthy()
      ) {
      total = Fix(1L) // have found new high term
      hi_term = car(l)
      hi_terms = ncons(hi_term)
    } else if zerop2(compare).truthy() {
      ()
    } else {
      // COMPARE IS IND, FINITE-VALUED, or und in both directions: add to list
      // of high terms
      total = add2_star(total, compare)
      hi_terms = append(hi_terms, ncons(car(l)))
    }
    l = cdr(l)
  }
  if zerop2(total).truthy() {
    // if high-order terms cancel each other, keep everything
    all
  } else {
    hi_terms
  }
}

///|
fn ratmax(l : Value) -> Value raise {
  if atom(l) {
    return Nil
  }
  let mut l = l
  let mut ans = car(l)
  while true {
    l = cdr(l)
    if l is Nil {
      return ans
    } else if ratgreaterp(ans, car(l)).truthy() {
      continue
    } else {
      ans = car(l)
    }
  }
  ans
}

///|
fn ratmin(l : Value) -> Value raise {
  if atom(l) {
    return Nil
  }
  let mut l = l
  let mut ans = car(l)
  while true {
    l = cdr(l)
    if l is Nil {
      return ans
    } else if ratgreaterp(car(l), ans).truthy() {
      continue
    } else {
      ans = car(l)
    }
  }
  ans
}

///|
fn pofx(e : Value) -> Value raise {
  let var_ = limit__var()
  if atom(e) {
    if eq(e, var_) {
      set(q_nn_star, cons(Fix(1L), symval(q_nn_star)))
    } else {
      Nil
    }
  } else if mnump(e).truthy() || !among(var_, e).truthy() {
    Nil
  } else if mexptp(e).truthy() && eq(cadr(e), var_) {
    set(q_nn_star, cons(caddr(e), symval(q_nn_star)))
  } else if simplerd(e).truthy() {
    Nil
  } else {
    let args = cdr(e)
    for x in args.iter() {
      pofx(x) |> ignore
    }
    args
  }
}

///|
fn ser1(e : Value) -> Value raise {
  let mut e = e
  if limit__memq(limit__val(), [q_d_zeroa, q_d_zerob]) {
    ()
  } else {
    e = subin(add2_star(limit__var(), limit__val()), e)
  }
  e = rdfact(e)
  if pofx(e).truthy() {
    e
  } else {
    Nil
  }
}

///|
fn gather(ind : Value, l : Value) -> Value raise {
  let ind = car(ind)
  let mut ans : Value = Nil
  let mut l = l
  while l.truthy() {
    if equal(caar(l), ind) {
      ans = cons(cadar(l), ans)
    }
    l = cdr(l)
  }
  list2(ind, muln(ans, Nil))
}

///|
/// returns rough class-of-growth of term
fn istrength(term : Value) -> Value raise {
  let var_ = limit__var()
  let val = limit__val()
  if mnump(term).truthy() {
    list2(q_num, term)
  } else if atom(term) {
    if eq(term, var_) {
      list([q_var, var_, Fix(1L)])
    } else {
      list2(q_num, term)
    }
  } else if !among(var_, term).truthy() {
    list2(q_num, term)
  } else if mplusp(term).truthy() {
    let temp = ismax_core(mapcar(x => istrength(x), cdr(term)))
    if temp.truthy() {
      temp
    } else {
      list2(q_gen, term)
    }
  } else if mtimesp(term).truthy() {
    let temp = mapcar(x => istrength(x), cdr(term))
    let temp1 = ismax(temp)
    if temp1 is Nil {
      list2(q_gen, term)
    } else if eq(car(temp1), q_log) {
      list2(q_log, temp)
    } else if eq(car(temp1), q_var) {
      add_up_deg(temp)
    } else {
      list2(q_gen, temp)
    }
  } else if mexptp(term).truthy() &&
    real_infinityp(limit(term, var_, val, t)).truthy() {
    let logterm = logred(term)
    if among(var_, caddr(term)).truthy() &&
      limit__memq(car(istrength(logterm)), [q_var, q_exp, q_fact]) &&
      real_infinityp(limit(logterm, var_, val, t)).truthy() {
      list2(q_exp, power_star(q_d__pcte, logterm))
    } else if !among(var_, caddr(term)).truthy() {
      let temp = istrength(cadr(term))
      if !alike1(temp, term).truthy() {
        rplaca(cdr(temp), term) |> ignore
        if eq(car(temp), q_var) {
          rplaca(cddr(temp), mul2_star(caddr(temp), caddr(term))) |> ignore
        }
        temp
      } else {
        list2(q_gen, term)
      }
    } else {
      list2(q_gen, term)
    }
  } else if eq(caar(term), q_p_log) &&
    real_infinityp(limit(term, var_, val, t)).truthy() {
    let stren = istrength(cadr(term))
    if limit__memq(car(stren), [q_log, q_var]) {
      list2(q_log, term)
    } else if eq(car(stren), q_exp) && eq(caar(second(stren)), q_mexpt) {
      istrength(logred(second(stren)))
    } else {
      list2(q_gen, term)
    }
  } else if eq(caar(term), q_mfactorial) {
    list2(q_fact, term)
  } else {
    let temp = hyperex(term)
    if !alike1(term, temp).truthy() {
      let r = istrength(temp)
      if r.truthy() {
        return r
      }
    }
    list2(q_gen, term)
  }
}

///|
/// log reduce - returns log of s1. When s1 is not of the form a^b, this code
/// doesn't return log(s1).
fn logred(s1 : Value) -> Value raise {
  if eq(cadr(s1), q_d__pcte) && caddr(s1).truthy() {
    caddr(s1)
  } else {
    mul2_star(caddr(s1), mk(q_p_log, [cadr(s1)]))
  }
}

///|
fn asymredu(rd : Value) -> Value raise {
  let var_ = limit__var()
  if atom(rd) {
    return rd
  } else if mnump(rd).truthy() {
    return rd
  } else if !among(var_, rd).truthy() {
    return rd
  }
  let p = polyinx(rd, var_, t)
  if p.truthy() {
    p
  } else if simplerd(rd).truthy() {
    if eq(cadr(rd), var_) {
      rd
    } else {
      mabs_subst(
        factor(d_expand(power_star(polyinx(cadr(rd), var_, t), caddr(rd)))),
        var_,
        limit__val(),
      )
    }
  } else {
    simplify(cons(list1(caar(rd)), mapcar(x => asymredu(x), cdr(rd))))
  }
}

///|
fn rdfact(rd : Value) -> Value raise {
  let var_ = limit__var()
  if atom(rd) {
    rd
  } else if mnump(rd).truthy() {
    rd
  } else if !among(var_, rd).truthy() {
    rd
  } else if polyp(rd).truthy() {
    factor(rd)
  } else if simplerd(rd).truthy() {
    if eq(cadr(rd), var_) {
      rd
    } else {
      let dn_star_star = caddr(rd)
      let nn_star_star = factor(cadr(rd))
      if mtimesp(nn_star_star).truthy() {
        muln(mapcar(j => power_star(j, dn_star_star), cdr(nn_star_star)), Nil)
      } else {
        rd
      }
    }
  } else {
    simplify(cons(ncons(caar(rd)), mapcar(x => rdfact(x), cdr(rd))))
  }
}

///|
fn cnv(expl : Value, val : Value) -> Value raise {
  let b = bind(q_val, val)
  defer unbind(b)
  mapcar(
    e => {
      let var_ = limit__var()
      maxima_substitute(
        if eq(val, q_d_zerob) {
          mul2_star(Fix(-1L), power_star(var_, Fix(-1L)))
        } else if eq(val, q_d_zeroa) {
          power_star(var_, Fix(-1L))
        } else if eq(val, q_d_minf) {
          mul2_star(Fix(-1L), var_)
        } else {
          power_star(add2_star(var_, mul2_star(Fix(-1L), val)), Fix(-1L))
        },
        var_,
        e,
      )
    },
    expl,
  )
}

///|
/// We could replace pwtaylor with a call to (tlimit-taylor exp var l terms).
fn pwtaylor(exp_ : Value, var_ : Value, l : Value, terms : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_)])
  defer unbind_all(bs)
  let mut terms = terms
  let mut mc = false
  let mut ans : Value = Nil
  if eq0(terms) {
    return Nil
  } else if eq0(l) {
    mc = true
  }
  let mut c = 0
  let mut first = true // (go tag1)
  while true {
    if !first {
      // loop
      c = c + 1
      if c > 10 || equal(Fix(c.to_int64()), terms) {
        return addn(ans, Nil)
      } else {
        set(q_exp, sdiff(limit__exp(), var_)) |> ignore
      }
    }
    first = false
    // tag1
    let coef = d_radcan(subin(l, limit__exp()))
    if eq0(coef) {
      terms = one_plus(terms)
      continue
    }
    ans = append(
      ans,
      list1(
        muln_star([
          coef,
          power_star(mk(q_mfactorial, [Fix(c.to_int64())]), Fix(-1L)),
          power_star(
            if mc {
              var_
            } else {
              add2(mul2(Fix(-1L), l), var_)
            },
            Fix(c.to_int64()),
          ),
        ]),
      ),
    )
  }
  Nil
}

///|
fn rdsget(e : Value) -> Value raise {
  if polyp(e).truthy() {
    e
  } else if simplerd(e).truthy() {
    rdtay(e)
  } else {
    cons(list1(caar(e)), mapcar(x => rdsget(x), cdr(e)))
  }
}

///|
fn rdtay(rd : Value) -> Value raise {
  if symval(q_limit_using_taylor).truthy() {
    d_ratdisrep(d_taylor(rd, list([limit__var(), limit__val(), Fix(1L)])))
  } else {
    lrdtay(rd)
  }
}

///|
fn lrdtay(rd : Value) -> Value raise {
  let bs = bind_all([(q_varlist, Nil), (q_d_ratfac, Nil)])
  defer unbind_all(bs)
  let var_ = limit__var()
  set(q_varlist, ncons(var_)) |> ignore
  let p = ratnumerator(cdr(ratrep_star(cadr(rd))))
  if length(p) < 3 {
    return rd
  }
  let e = caddr(rd)
  let mut d = pdegr(p)
  let c = power_star(var_, mul2_star(d, e))
  d = d_ratsimp(
    varinvert(
      mul2_star(pdis(p), power_star(var_, mul2_star(Fix(-1L), d))),
      var_,
    ),
    Nil,
  )
  d = pwtaylor(power_star(d, e), var_, Fix(0L), Fix(3L))
  mul2_star(c, varinvert(d, var_))
}

///|
fn varinvert(e : Value, var_ : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  subin(power(var_, Fix(-1L)), e)
}

///|
fn deg(p : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(limit__var())), (q_d_ratfac, Nil)])
  defer unbind_all(bs)
  newvar(p) |> ignore
  pdegr(cadr(ratrep_star(p)))
}

///|
/// Like DEG, but dependency on VAR is explicit. Use this instead when
/// possible.
fn deg_var(p : Value, var1 : Value) -> Value raise {
  let bs = bind_all([(q_varlist, list1(var1)), (q_d_ratfac, Nil)])
  defer unbind_all(bs)
  newvar(p) |> ignore
  let pf = cadr(ratrep_star(p))
  if atom(pf) || !eq(caadr(ratf(var1)), car(pf)) {
    Fix(0L)
  } else if symval(q_low_star).truthy() {
    cadr(reverse(pf))
  } else {
    cadr(pf)
  }
}

///|
fn rat_no_ratfac(e : Value) -> Value raise {
  with_special(q_d_ratfac, Nil, () => {
    newvar(e) |> ignore
    ratrep_star(e)
  })
}

///|
/// LOW* is a lexical parameter here (it is not proclaimed special when
/// limit.lisp is compiled); PDEGR reads the global LOW*.
fn rddeg(rd : Value, low_star : Value) -> Value raise {
  let var_ = limit__var()
  if mnump(rd).truthy() || !among(var_, rd).truthy() {
    Fix(0L)
  } else if polyp(rd).truthy() {
    deg(rd)
  } else if simplerd(rd).truthy() {
    mul2_star(deg(cadr(rd)), caddr(rd))
  } else if mtimesp(rd).truthy() {
    addn(mapcar(j => rddeg(j, low_star), cdr(rd)), Nil)
  } else if mplusp(rd).truthy() {
    let rd = andmapcar(
      lfunc("rddeg-lambda", a => rddeg(arg(a, 0), low_star)),
      cdr(rd),
    )
    if rd.truthy() {
      if low_star.truthy() {
        ratmin(rd)
      } else {
        ratmax(rd)
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn pdegr(pf : Value) -> Value raise {
  if atom(pf) || !eq(caadr(ratf(limit__var())), car(pf)) {
    Fix(0L)
  } else if symval(q_low_star).truthy() {
    cadr(reverse(pf))
  } else {
    cadr(pf)
  }
}

///|
/// There is some confusion here. We need to be aware of Branch cuts etc....
/// when doing this section of code. It is not very carefully done so there
/// are bugs still lurking. Another misfortune is that LIMIT or its inferiors
/// sometimes decides to change the limit VAL in midstream.
fn asy(n : Value, d : Value) -> Value raise {
  let var_ = limit__var()
  let num_power = rddeg(n, Nil)
  let den_power = rddeg(d, Nil)
  let coef = div_star(
    d_ratcoef(d_expand(n), var_, n=num_power),
    d_ratcoef(d_expand(d), var_, n=den_power),
  )
  let coef_sign = getsignl(coef)
  let power = div_star(num_power, den_power)
  if eq(ask_integer(power, q_d_integer), q_d_integer) {
    ask_integer(power, q_d_even) |> ignore // Can be extended from here.
  }
  let val = limit__val()
  if eq(val, q_d_minf) ||
    eq(val, q_d_zerob) ||
    eq(val, q_d_zeroa) ||
    equal(val, Fix(0L)) {
    // Can be extended to cover some these.
    Nil
  } else if ratgreaterp(den_power, num_power).truthy() {
    if equal(coef_sign, Fix(1L)) {
      q_d_zeroa
    } else if equal(coef_sign, Fix(-1L)) {
      q_d_zerob
    } else if equal(coef_sign, Fix(0L)) {
      Fix(0L)
    } else {
      Fix(0L)
    }
  } else if ratgreaterp(num_power, den_power).truthy() {
    if equal(coef_sign, Fix(1L)) {
      q_d_inf
    } else if equal(coef_sign, Fix(-1L)) {
      q_d_minf
    } else if equal(coef_sign, Fix(0L)) {
      Nil // should never be zero
    } else if coef_sign is Nil {
      q_d_infinity
    } else {
      Nil
    }
  } else {
    coef
  }
}

///|
fn radlim(e : Value, n : Value, d : Value) -> Value raise {
  let mut n = n
  let mut d = d
  if eq(limit__val(), q_d_infinity) {
    return throw_tag(q_limit, Nil)
  } else if eq(limit__val(), q_d_minf) {
    let nl = mul2_star(limit__var(), Fix(-1L))
    n = subin(nl, n)
    d = subin(nl, d)
    // This is the Culprit. Doesn't tell the DATABASE.
    set(q_val, q_d_inf) |> ignore
  }
  if eq(limit__val(), q_d_inf) {
    let nl = asymredu(n)
    let dl = asymredu(d)
    if rptrouble(n).truthy() || rptrouble(d).truthy() {
      return limit(
        mul2_star(rdsget(n), power_star(rdsget(d), Fix(-1L))),
        limit__var(),
        limit__val(),
        t,
      )
    } else {
      return asy(nl, dl)
    }
  }
  let nl = limit(n, limit__var(), limit__val(), t)
  let dl = limit(d, limit__var(), limit__val(), t)
  if zerop2(nl).truthy() && zerop2(dl).truthy() {
    if polyp(n).truthy() || polyp(d).truthy() {
      try_lhospital_quit(n, d, t)
    } else {
      ser0(e, n, d, limit__val())
    }
  } else {
    d_radcan(ratrad(div_star(n, d), n, d, nl, dl))
  }
}

///|
fn ratrad(e : Value, n : Value, d : Value, nl : Value, dl : Value) -> Value raise {
  let mut n1 : Value = Nil
  let mut d1 : Value = Nil
  if equal(nl, Fix(0L)) {
    return Fix(0L)
  } else if zerop2(dl).truthy() {
    n1 = nl
    if equal(dl, Fix(0L)) {
      d1 = q_d_infinity // No direction Info.
    } else if eq(dl, q_d_zeroa) {
      d1 = q_d_inf
    } else {
      let d = behavior(d, limit__var(), limit__val())
      if equal(d, Fix(1L)) {
        d1 = q_d_inf
      } else if equal(d, Fix(-1L)) {
        d1 = q_d_minf
      } else {
        return throw_tag(q_limit, Nil)
      }
    }
  } else if zerop2(nl).truthy() {
    d1 = dl
    let n = behavior(n, limit__var(), limit__val())
    if equal(n, Fix(1L)) {
      n1 = q_d_zeroa
    } else if equal(n, Fix(-1L)) {
      n1 = q_d_zerob
    } else {
      n1 = Fix(0L)
    }
  } else {
    return d_radcan(ridofab(subin(limit__val(), e)))
  }
  simplimtimes(list([n1, d1]))
}

///|
/// When E can be shown to be non-real, return '$COMPLEX or '$IMAGINARY,
/// otherwise return NIL.
fn non_real_sign(e : Value) -> Value raise {
  let z = risplit(e)
  if eq(t, mnqp(cdr(z), Fix(0L))) {
    if eq(t, meqp(car(z), Fix(0L))) {
      q_d_imaginary
    } else {
      q_d_complex
    }
  } else {
    Nil
  }
}

///|
/// When `*getsignl-asksign-ok*` is true, call `asksign`, otherwise call
/// `csign`. A provably non-real sign is returned without asking.
fn maybe_asksign(e : Value) -> Value raise {
  let s = non_real_sign(e)
  if s.truthy() {
    s
  } else if symval(q_ear_getsignl_asksign_ok).truthy() {
    d_asksign(e)
  } else {
    d_csign(e)
  }
}

///|
/// When `*getsignl-asksign-ok*` is true, call `asksign`, otherwise call
/// `sign`. A provably non-real sign is returned without asking.
/// *COMPLEXSIGN* is bound to NIL, because an outer $CSIGN that re-entered
/// LIMIT leaves it true and puts $SIGN in complex mode.
fn maybe_asksign_real(e : Value) -> Value raise {
  with_special(q_ear_complexsign, Nil, () => {
    let s = non_real_sign(e)
    if s.truthy() {
      s
    } else if symval(q_ear_getsignl_asksign_ok).truthy() {
      d_asksign(e)
    } else {
      // LIMITP gives SIGN-PREP's normalization, but for a PRIN-INF
      // expression, SIGN-PREP answers about the limit, not the value.
      let lp = if symval(q_limitp).truthy() {
        free(e, q_prin_inf)
      } else {
        Nil
      }
      with_special(q_limitp, lp, () => d_sign(e))
    }
  })
}

///|
/// Limit(log(XXX), var, 0, val), where val is either zerob (limit from
/// below) or zeroa (limit from above).
fn simplimln(expr : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let mut arglim = with_special(q_ear_preserve_direction, t, () => limit(
    cadr(expr),
    var_,
    val,
    q_think,
  ))
  let mut dir : Value = Nil
  // When arglim is 0, try using behavior to determine if the limit is zerob
  // or zeroa.
  if eql(arglim, Fix(0L)) {
    dir = behavior(expr, var_, val)
    if eql(dir, Fix(-1L)) {
      arglim = q_d_zerob
    } else if eql(dir, Fix(1L)) {
      arglim = q_d_zeroa
    }
  }
  if eq(arglim, q_d_inf) {
    q_d_inf // log(inf) = inf
  } else if limit__memq(arglim, [q_d_minf, q_d_infinity, q_d_zerob]) {
    // log(minf,infinity,zerob) = infinity
    q_d_infinity
  } else if eq(arglim, q_d_zeroa) {
    q_d_minf // log(zeroa) = minf
  } else if eql(arglim, Fix(0L)) {
    // Special case of arglim = 0
    q_d_infinity
  } else if eq(arglim, q_d_ind) {
    // If expr doesn't vanish, log(ind) = ind; otherwise log(ind) = und.
    if eq(t, mnqp(cadr(expr), Fix(0L))) {
      q_d_ind
    } else {
      q_d_und
    }
  } else if eq(arglim, q_d_und) {
    // This case should be caught by simplimit, but in case simplimln is
    // called from outside simplimit, we'll leave this case here for now
    throw_tag(q_limit, Nil)
  } else if eql(ridofab(arglim), Fix(1L)) {
    // log(1^(-)) = zerob, log(1^(+)) = zeroa & log(1)=0. It can happen that
    // arglim is 1 + zeroa, for example. For such cases, we'll apply
    // maybe-asksign; when that doesn't yield a sign, we'll use dispatch
    // behavior.
    let sgn = maybe_asksign(sub(arglim, Fix(1L)))
    if eq(sgn, q_d_neg) {
      q_d_zerob
    } else if eq(sgn, q_d_pos) {
      q_d_zeroa
    } else {
      dir = behavior(cadr(expr), var_, val)
      if eql(dir, Fix(-1L)) {
        q_d_zerob
      } else if eql(dir, Fix(1L)) {
        q_d_zeroa
      } else {
        Fix(0L)
      }
    }
  } else {
    let z = trisplit(arglim)
    let xx = car(z)
    let yy = cdr(z)
    let mut sgn : Value = Nil
    // When yy vanishes, find the sign of xx. But when the sign isn't
    // definitive, use asksign.
    if eql(Fix(0L), yy) {
      sgn = maybe_asksign_real(xx)
      if !limit__memq(sgn, [q_d_pos, q_d_neg, q_d_zero]) {
        // Probably it would be better to (THROW 'LIMIT T) here, but then
        // some cases don't reach the second pass where we would ask, because
        // Gruntz answers, and it does so incorrectly. So we just ask
        // forcefully.
        sgn = with_special(q_ear_getsignl_asksign_ok, t, () => maybe_asksign_real(
          xx,
        ))
      }
    }
    if eql(Fix(0L), yy) && eq(sgn, q_d_neg) {
      // arglim on the negative real axis: examine the imaginary part of
      // 'expr' to see if it vanishes, or if it approaches zero from above or
      // below.
      let yy = cdr(trisplit(cadr(expr)))
      dir = if eq(t, meqp(yy, Fix(0L))) {
        Fix(1L)
      } else {
        behavior(yy, var_, val)
      }
      if eql(dir, Fix(0L)) {
        throw_tag(q_limit, t)
      } else {
        add2(
          ftake(q_p_log, [mul2(Fix(-1L), arglim)]),
          muln_([dir, q_d__pcti, q_d__pctpi]),
        )
      }
    } else if eql(Fix(0L), yy) && eq(sgn, q_d_zero) {
      q_d_infinity
    } else {
      ftake(q_p_log, [arglim])
    }
  }
}

///|
fn simplim_pctlimit(e : Value, x : Value, pt : Value) -> Value raise {
  ignore(e)
  ignore(x)
  ignore(pt)
  throw_tag(q_limit, t)
}

///|
fn simplim_pctunit_step(e : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let lim = limit(cadr(e), var_, val, q_think)
  if eq(lim, q_d_und) {
    q_d_und
  } else if eq(lim, q_d_ind) {
    q_d_ind
  } else if eq(lim, q_d_zerob) {
    Fix(0L)
  } else if eq(lim, q_d_zeroa) {
    Fix(1L)
  } else if !lenient_realp(lim).truthy() {
    throw_tag(q_limit, Nil) // catches infinity too
  } else if eq(t, mgrp(Fix(0L), lim)) {
    // catches minf & inf cases
    Fix(0L)
  } else if eq(t, mgrp(lim, Fix(0L))) {
    Fix(1L)
  } else {
    q_d_ind
  }
}

///|
fn simplim_pctconjugate(e : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let lim = limit(cadr(e), var_, val, q_think)
  if off_negative_real_axisp(lim).truthy() {
    ftake(q_d_conjugate, [lim])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
fn simplim_pctimagpart(e : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let lim = limit(cadr(e), var_, val, q_think)
  if eq(lim, q_d_und) {
    q_d_und
  } else if eq(lim, q_d_ind) {
    Fix(0L)
  } else if eq(lim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else {
    mfuncall(q_d_imagpart, list1(lim))
  }
}

///|
fn simplim_pctrealpart(e : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let lim = limit(cadr(e), var_, val, q_think)
  if eq(lim, q_d_und) {
    q_d_und
  } else if eq(lim, q_d_ind) {
    q_d_ind
  } else if eq(lim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else {
    mfuncall(q_d_realpart, list1(lim))
  }
}

///|
/// Limit of the Factorial function
fn simplimfact(expr : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let arglim = limit(cadr(expr), var_, val, q_think) // Limit of the argument.
  let mut arg2 = arglim
  if eq(arglim, q_d_inf) {
    q_d_inf
  } else if limit__memq(arglim, [q_d_minf, q_d_infinity, q_d_und, q_d_ind]) {
    q_d_und
  } else if zerop2(arglim).truthy() {
    Fix(1L)
  } else if (
      maxima_integerp(arglim).truthy() ||
      {
        arg2 = integer_representation_p(arglim)
        arg2.truthy()
      }
    ) &&
    eq(d_sign(arg2), q_d_neg) {
    // A negative integer or float or bigfloat representation.
    let dir = limit(
      add2(cadr(expr), mul2(Fix(-1L), arg2)),
      var_,
      val,
      q_think,
    )
    let even = mevenp(arg2).truthy()
    if (even && eq(dir, q_d_zeroa)) || (!even && eq(dir, q_d_zerob)) {
      q_d_minf
    } else if (even && eq(dir, q_d_zerob)) || (!even && eq(dir, q_d_zeroa)) {
      q_d_inf
    } else {
      throw_tag(q_limit, Nil)
    }
  } else {
    // Call simplifier to get value at the limit of the argument.
    simplify(mk(q_mfactorial, [arglim]))
  }
}

///|
fn simplim_pcterf__pcttanh(fn_ : Value, arg : Value) -> Value raise {
  let var_ = limit__var()
  let val = limit__val()
  let arglim = limit(arg, var_, val, q_think)
  if eq(arglim, q_d_inf) {
    Fix(1L)
  } else if eq(arglim, q_d_minf) {
    Fix(-1L)
  } else if eq(arglim, q_d_infinity) {
    let z = trisplit(arg)
    let rpart = car(z)
    let ipart = cdr(z)
    let rlim = limit(rpart, var_, val, q_think)
    if eq(fn_, q_p_tanh) {
      if equal(rlim, q_d_inf) {
        Fix(1L)
      } else if equal(rlim, q_d_minf) {
        Fix(-1L)
      } else {
        Nil
      }
    } else if eq(fn_, q_p_erf) {
      let mut ans = limit(
        mul2_star(rpart, power(ipart, Fix(-1L))),
        var_,
        symval(q_origval),
        q_think,
      )
      ans = maybe_asksign_real(add2_star(mk(q_mabs, [ans]), Fix(-1L)))
      if eq(ans, q_d_pos) || eq(ans, q_d_zero) {
        if eq(rlim, q_d_inf) {
          Fix(1L)
        } else if eq(rlim, q_d_minf) {
          Fix(-1L)
        } else {
          q_d_und
        }
      } else {
        q_d_und
      }
    } else {
      Nil
    }
  } else if eq(arglim, q_d_und) {
    q_d_und
  } else if limit__memq(arglim, [q_d_zeroa, q_d_zerob, q_d_ind]) {
    arglim
  } else {
    // Ignore tanh(%pi/2*%I) and multiples of the argument. erf (or tanh) of
    // a known value is just erf(arglim).
    simplify(list2(ncons(fn_), arglim))
  }
}

///|
fn in_domain_of_atan(z : Value) -> Value raise {
  let z = trisplit(z) // split z into real and imaginary parts
  let x = car(z)
  let y = cdr(z) // z = x+%i*y
  lbool(
    !(
      eq(t, meqp(x, Fix(0L))) && // Re(z) = 0
      (
        eq(t, mgqp(Fix(-1L), y)) || // -1 >= Im(z)
        eq(t, mgqp(y, Fix(1L)))
      )
    ),
  ) // Im(z) >= 1
}

///|
fn simplim_pctatan(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if eq(lim, q_d_zeroa) ||
    eq(lim, q_d_zerob) ||
    eq(lim, Fix(0L)) ||
    eq(lim, q_d_ind) {
    lim
  } else if eq(lim, q_d_und) || eq(lim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else if eq(lim, q_d_inf) {
    maxima_lit("%pi/2") // atan(inf) -> %pi/2
  } else if eq(lim, q_d_minf) {
    maxima_lit("-%pi/2") // atan(-inf) -> -%pi/2
  } else if in_domain_of_atan(ridofab(lim)).truthy() {
    // direct substitution
    ftake(q_p_atan, [ridofab(lim)])
  } else {
    limit(d_logarc(e), x, pt, q_think)
  }
}

///|
/// Most instances of atan2 are simplified to atan expressions, but this
/// routine handles tricky cases such as
/// limit(atan2((x^2-2), x^3-2*x), x, sqrt(2), minus). When possible, we
/// evaluate the limit of an atan2 expression using direct substitution.
fn simplim_pctatan2(e : Value, v : Value, pt : Value) -> Value raise {
  let mut y = second(e)
  let mut x = third(e)
  let mut xlim = with_special(q_ear_preserve_direction, t, () => limit(
    x,
    v,
    pt,
    q_think,
  ))
  let mut ylim = with_special(q_ear_preserve_direction, t, () => limit(
    y,
    v,
    pt,
    q_think,
  ))
  if eql(Fix(0L), xlim) {
    let dir = behavior(x, v, pt)
    if eql(dir, Fix(1L)) {
      xlim = q_d_zeroa
    } else if eql(dir, Fix(-1L)) {
      xlim = q_d_zerob
    }
  }
  if eql(Fix(0L), ylim) {
    let dir = behavior(y, v, pt)
    if eql(dir, Fix(1L)) {
      ylim = q_d_zeroa
    } else if eql(dir, Fix(-1L)) {
      ylim = q_d_zerob
    }
  }
  let mut xlim_z = ridofab(xlim)
  let mut ylim_z = ridofab(ylim)
  // For cases for which direct substitution fails, normalize x & y and try
  // again.
  let q = if eq(xlim, q_d_inf) {
    x
  } else if eq(xlim, q_d_minf) {
    mul2(Fix(-1L), x)
  } else if eq(ylim, q_d_inf) {
    y
  } else if eq(ylim, q_d_minf) {
    mul2(Fix(-1L), y)
  } else {
    Fix(1L)
  }
  if !eql(q, Fix(1L)) {
    x = div(x, q)
    y = div(y, q)
    xlim = limit(x, v, pt, q_think)
    ylim = limit(y, v, pt, q_think)
    xlim_z = ridofab(xlim)
    ylim_z = ridofab(ylim)
  }
  if eq(xlim, q_d_zeroa) && eq(ylim, q_d_zeroa) {
    // in quadrant I
    limit(ftake(q_p_atan, [div(y, x)]), v, pt, q_think)
  } else if eq(xlim, q_d_zerob) && eq(ylim, q_d_zeroa) {
    // in quadrant II
    add2(q_d__pctpi, limit(ftake(q_p_atan, [div(y, x)]), v, pt, q_think))
  } else if eq(xlim, q_d_zerob) && eq(ylim, q_d_zerob) {
    // in quadrant III
    sub(limit(ftake(q_p_atan, [div(y, x)]), v, pt, q_think), q_d__pctpi)
  } else if eq(xlim, q_d_zeroa) && eq(ylim, q_d_zerob) {
    // in quadrant IV
    limit(ftake(q_p_atan, [div(y, x)]), v, pt, q_think)
  } else if eq(q_d_zerob, ylim) && eq(t, mgrp(Fix(0L), xlim)) {
    mul2(Fix(-1L), q_d__pctpi)
  } else if eq(q_d_zerob, ylim) && eq(t, mgrp(xlim, Fix(0L))) {
    Fix(0L)
  } else if eq(q_d_zeroa, ylim) && eq(t, mgrp(Fix(0L), xlim)) {
    q_d__pctpi
  } else if eq(q_d_zeroa, ylim) && eq(t, mgrp(xlim, Fix(0L))) {
    Fix(0L)
  } else if eql(xlim, Fix(1L)) && eql(ylim, q_d_inf) {
    div(q_d__pctpi, Fix(2L))
  } else if eql(xlim, Fix(-1L)) && eql(ylim, Fix(0L)) {
    if eq(t, meqp(y, Fix(0L))) {
      q_d__pctpi
    } else {
      q_d_ind
    }
  } else if lenient_realp(xlim_z).truthy() &&
    lenient_realp(ylim_z).truthy() &&
    (eq(t, mnqp(ylim_z, Fix(0L))) || eq(t, mgrp(xlim_z, Fix(0L)))) {
    // Use direct substitution when ylim-z # 0 or xlim-z > 0. We need to
    // check that xlim-z & ylim-z are real too.
    ftake(q_p_atan2, [ylim_z, xlim_z])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
fn simplimsch(sch : Value, arg : Value) -> Value raise {
  if real_infinityp(arg).truthy() {
    if eq(sch, q_p_sinh) {
      arg
    } else {
      q_d_inf
    }
  } else if eq(arg, q_d_infinity) {
    q_d_infinity
  } else if eq(arg, q_d_ind) {
    q_d_ind
  } else if eq(arg, q_d_und) {
    q_d_und
  } else if eq(sch, q_p_sinh) && (eq(arg, q_d_zerob) || eq(arg, q_d_zeroa)) {
    arg
  } else {
    with_special(q_d_exponentialize, t, () => resimplify(
      list2(ncons(sch), ridofab(arg)),
    ))
  }
}

///|
/// simple limit of sin and cos
fn simplimsc(exp_ : Value, fn_ : Value, arg : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  if limit__memq(arg, [q_d_inf, q_d_minf, q_d_ind]) {
    q_d_ind
  } else if limit__memq(arg, [q_d_und, q_d_infinity]) {
    throw_tag(q_limit, Nil)
  } else if limit__memq(arg, [q_d_zeroa, q_d_zerob]) {
    if eq(fn_, q_p_sin) {
      arg
    } else {
      add2_star(Fix(1L), q_d_zerob)
    }
  } else {
    sincoshk(exp_, simplify(list2(ncons(fn_), ridofab(arg))), fn_)
  }
}

///|
fn simplim_pcttan(expr : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let b2 = bind(q_ear_preserve_direction, t)
  defer unbind(b2)
  let z = cadr(expr)
  let lim = limit(z, var_, val, q_think)
  let two_lim_over_pi = div(mul2(Fix(2L), lim), q_d__pctpi)
  if limit__memq(lim, [q_d_zeroa, q_d_zerob]) {
    // tan(zeroa) = zeroa, tan(zerob) = zerob
    lim
  } else if limit__memq(lim, [q_d_inf, q_d_minf, q_d_und, q_d_infinity]) {
    // tan{minf, inf, und, infinity} is undefined
    q_d_und
  } else if eq(lim, q_d_ind) {
    // When limit(z,var,val) = ind and Maxima can determine that cos(z) is
    // nonvanishing, return ind; otherwise return und.
    if eq(t, mnqp(ftake(q_p_cos, [z]), Fix(0L))) {
      q_d_ind
    } else {
      q_d_und
    }
  } else if d_featurep(two_lim_over_pi, q_d_integer).truthy() &&
    eq(q_d_yes, ask_integer(two_lim_over_pi, q_d_odd)) {
    // When 2*lim/%pi is an odd integer, tangent has a pole.
    let sgn = zero_fixup(
      d_ratdisrep(tlimit_taylor(sub(z, lim), var_, val, Fix(0L))),
      var_,
      val,
    ) // local analysis of pole
    if eq(sgn, q_d_zerob) {
      q_d_inf
    } else if eq(sgn, q_d_zeroa) {
      q_d_minf
    } else {
      throw_tag(q_limit, Nil)
    }
  } else if successful_limit_result_p(lim).truthy() {
    // Direct substitution.
    ftake(q_p_tan, [lim])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
/// The inverse trigonometric and hyperbolic functions are discontinuous
/// across their branch cuts, so the limit of one of them at a point on a cut
/// depends on the side from which the cut is approached. CUT-PART is the
/// part of the argument that vanishes on the cut. VALUE is the value of the
/// function on the cut itself, and MIRROR is its limit from the other side.
/// SIDE is 1 when the function is continuous from the side on which CUT-PART
/// is positive, and -1 when it is continuous from the other one. Return NIL
/// when the side cannot be determined.
fn branch_cut_limit(
  cut_part : Value,
  side : Value,
  value : Value,
  mirror : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  if zerop1(cut_part).truthy() {
    value
  } else {
    let direction = behavior(cut_part, var_, val)
    if eql(direction, side) {
      value
    } else if eql(direction, num_neg(side)) {
      mirror
    } else {
      Nil
    }
  }
}

///|
fn simplim_pctasinh(e : Value, x : Value, pt : Value) -> Value raise {
  let mut lim = limit(cadr(e), x, pt, q_think)
  if limit__memq(lim, [q_d_inf, q_d_minf, q_d_zeroa, q_d_zerob, q_d_ind, q_d_und]) {
    lim
  } else if eq(lim, q_d_infinity) {
    q_d_und
  } else {
    lim = ridofab(lim)
    let value = ftake(q_p_asinh, [lim])
    // Since asinh(z) = -%i*asin(%i*z), asinh is continuous at LIM exactly
    // when asin is continuous at %i*LIM. On the cut from %i to %i*inf asinh
    // is continuous from the right and its value from the left is
    // %i*%pi - asinh(z); on the cut from -%i to -%i*inf it is continuous
    // from the left and its value from the right is -%i*%pi - asinh(z).
    let w = mul2(q_d__pcti, lim)
    if in_domain_of_asin(w).truthy() {
      value // direct substitution
    } else {
      let re = car(trisplit(cadr(e)))
      let r = if eq(t, mgqp(Fix(-1L), w)) {
        branch_cut_limit(
          re,
          Fix(1L),
          value,
          sub(mul2(q_d__pcti, q_d__pctpi), value),
          x,
          pt,
        )
      } else if eq(t, mgqp(w, Fix(1L))) {
        branch_cut_limit(
          re,
          Fix(-1L),
          value,
          sub(muln_([Fix(-1L), q_d__pcti, q_d__pctpi]), value),
          x,
          pt,
        )
      } else {
        Nil
      }
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, t)
      }
    }
  }
}

///|
fn simplim_pctacosh(e : Value, x : Value, pt : Value) -> Value raise {
  let mut lim = limit(cadr(e), x, pt, q_think)
  if equal(ridofab(lim), Fix(1L)) {
    // Only from above 1 does acosh tend to zeroa. From below 1 it vanishes
    // along the imaginary axis, and when BEHAVIOR cannot tell the side, the
    // zero has no side either.
    if eql(Fix(1L), behavior(sub(cadr(e), Fix(1L)), x, pt)) {
      q_d_zeroa
    } else {
      Fix(0L)
    }
  } else if eq(lim, q_d_inf) {
    lim
  } else if eq(lim, q_d_minf) {
    q_d_infinity
  } else if limit__memq(lim, [q_d_und, q_d_ind, q_d_infinity]) {
    q_d_und
  } else {
    lim = ridofab(lim)
    let value = ftake(q_p_acosh, [lim])
    // Direct substitution when the argument stays off the cut.
    if off_negative_real_axisp(sub(lim, Fix(1L))).truthy() {
      value
    } else {
      // The argument approaches the branch cut of acosh, which runs along
      // the real axis from 1 to minf. There acosh is continuous from above,
      // and just below the cut its value is -acosh(x) between -1 and 1, and
      // acosh(x) - 2*%i*%pi below -1.
      let im = cdr(trisplit(cadr(e)))
      let r = if eq(t, mgqp(Fix(-1L), lim)) {
        branch_cut_limit(
          im,
          Fix(1L),
          value,
          sub(value, muln_([Fix(2L), q_d__pcti, q_d__pctpi])),
          x,
          pt,
        )
      } else if eq(t, mgqp(Fix(1L), lim)) && eq(t, mgqp(lim, Fix(-1L))) {
        branch_cut_limit(im, Fix(1L), value, neg(value), x, pt)
      } else {
        Nil
      }
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, t)
      }
    }
  }
}

///|
/// Compute limit(atanh(z),x,pt). If the limit of Z is +/-1, we need to take
/// into account which direction we're approaching it.
fn simplim_pctatanh(e : Value, x : Value, pt : Value) -> Value raise {
  let mut lim = limit(cadr(e), x, pt, q_think)
  if zerop2(lim).truthy() {
    lim
  } else if limit__memq(lim, [q_d_inf, q_d_minf, q_d_infinity]) {
    // However far out the argument goes, atanh(z) tends to %i*%pi/2 where
    // the imaginary part of z is positive and to -%i*%pi/2 where it is
    // negative. Along the real axis the argument stays on a branch cut,
    // where atanh takes the value from below.
    let imag = cdr(trisplit(cadr(e)))
    let side : Value = if zerop1(imag).truthy() {
      if eq(lim, q_d_inf) {
        Fix(-1L)
      } else if eq(lim, q_d_minf) {
        Fix(1L)
      } else {
        Nil
      }
    } else {
      let im = with_special(q_ear_preserve_direction, t, () => limit_catch(
        imag, x, pt,
      ))
      if limit__memq(im, [q_d_zeroa, q_d_inf]) {
        Fix(1L)
      } else if limit__memq(im, [q_d_zerob, q_d_minf]) {
        Fix(-1L)
      } else if eq(t, mgrp(im, Fix(0L))) {
        Fix(1L)
      } else if eq(t, mgrp(Fix(0L), im)) {
        Fix(-1L)
      } else {
        Nil
      }
    }
    if eql(side, Fix(1L)) {
      maxima_lit("%i*%pi/2")
    } else if eql(side, Fix(-1L)) {
      maxima_lit("-%i*%pi/2")
    } else {
      q_d_und
    }
  } else if limit__memq(lim, [q_d_ind, q_d_und]) {
    q_d_und
  } else if {
      lim = ridofab(lim)
      equal(lim, Fix(1L))
    } {
    // The limit at 1 should be complex infinity because atanh(x) is complex
    // for x > 1, but inf if we're approaching 1 from below.
    if eql(Fix(-1L), behavior(sub(cadr(e), Fix(1L)), x, pt)) {
      q_d_inf
    } else {
      q_d_infinity
    }
  } else if equal(lim, Fix(-1L)) {
    // Same as above, except for the limit is at -1.
    if eql(Fix(1L), behavior(add2(cadr(e), Fix(1L)), x, pt)) {
      q_d_minf
    } else {
      q_d_infinity
    }
  } else {
    let value = ftake(q_p_atanh, [lim])
    if in_domain_of_asin(lim).truthy() {
      value // direct substitution
    } else {
      // The argument approaches one of the branch cuts of atanh, which are
      // those of asin. Just above the cut from 1 to inf the value of atanh is
      // atanh(x) + %i*%pi, and just below the cut from -1 to minf it is
      // atanh(x) - %i*%pi.
      let im = cdr(trisplit(cadr(e)))
      let r = if eq(t, mgqp(lim, Fix(1L))) {
        branch_cut_limit(
          im,
          Fix(-1L),
          value,
          add2(value, mul2(q_d__pcti, q_d__pctpi)),
          x,
          pt,
        )
      } else if eq(t, mgqp(Fix(-1L), lim)) {
        branch_cut_limit(
          im,
          Fix(1L),
          value,
          sub(value, mul2(q_d__pcti, q_d__pctpi)),
          x,
          pt,
        )
      } else {
        Nil
      }
      if r.truthy() {
        r
      } else {
        throw_tag(q_limit, t)
      }
    }
  }
}

///|
fn simplim_pctasin(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if limit__memq(lim, [q_d_zeroa, q_d_zerob]) {
    lim // asin(zeoroa/b) = zeroa/b
  } else if limit__memq(lim, [q_d_minf, q_d_inf, q_d_infinity]) {
    q_d_infinity
  } else if eq(lim, q_d_ind) {
    q_d_ind // asin(ind)=ind
  } else if eq(lim, q_d_und) {
    q_d_und // asin(und)=und
  } else if in_domain_of_asin(lim).truthy() {
    // direct substitution
    ftake(q_p_asin, [lim])
  } else if freeof(x, e).truthy() {
    e // limit of constant--it happens!
  } else {
    // The argument approaches one of the branch cuts of asin, which run
    // along the real axis from 1 to inf and from -1 to minf (DLMF 4.23.20 &
    // 4.23.21). asin is continuous from above on the cut below -1 and from
    // below on the cut above 1.
    let im = cdr(trisplit(cadr(e))) // imaginary part of the argument
    let r = if eq(t, mgrp(lim, Fix(1L))) {
      branch_cut_limit(
        im,
        Fix(-1L),
        ftake(q_p_asin, [lim]),
        sub(q_d__pctpi, ftake(q_p_asin, [lim])),
        x,
        pt,
      )
    } else if eq(t, mgrp(Fix(-1L), lim)) {
      branch_cut_limit(
        im,
        Fix(1L),
        ftake(q_p_asin, [lim]),
        sub(mul2(Fix(-1L), q_d__pctpi), ftake(q_p_asin, [lim])),
        x,
        pt,
      )
    } else {
      Nil
    }
    if r.truthy() {
      r
    } else {
      throw_tag(q_limit, t)
    }
  }
}

///|
fn simplim_pctacos(e : Value, x : Value, pt : Value) -> Value raise {
  let lim = limit(cadr(e), x, pt, q_think)
  if limit__memq(lim, [q_d_zerob, q_d_zeroa]) {
    // acsos(zerob or zeroa) = %pi/2
    ftake(q_p_acos, [ridofab(lim)])
  } else if limit__memq(lim, [q_d_minf, q_d_inf, q_d_infinity]) {
    q_d_infinity
  } else if eq(lim, q_d_ind) {
    q_d_ind // acos(ind)=ind
  } else if eq(lim, q_d_und) {
    q_d_und // acos(und)=und
  } else if !successful_limit_result_p(lim).truthy() {
    throw_tag(q_limit, Nil)
  } else if in_domain_of_asin(lim).truthy() {
    // direct substitution--both asin & acos have the same branches
    ftake(q_p_acos, [lim])
  } else {
    // The argument approaches one of the branch cuts of acos, which are
    // those of asin (DLMF 4.23.24 & 4.23.25). Just above the cut from 1 to
    // inf its value is -acos(x), and just below the cut from -1 to minf its
    // value is 2*%pi - acos(x).
    let im = cdr(trisplit(cadr(e))) // imaginary part of the argument
    let r = if eq(t, mgrp(lim, Fix(1L))) {
      branch_cut_limit(
        im,
        Fix(-1L),
        ftake(q_p_acos, [lim]),
        neg(ftake(q_p_acos, [lim])),
        x,
        pt,
      )
    } else if eq(t, mgrp(Fix(-1L), lim)) {
      branch_cut_limit(
        im,
        Fix(1L),
        ftake(q_p_acos, [lim]),
        sub(mul2(Fix(2L), q_d__pctpi), ftake(q_p_acos, [lim])),
        x,
        pt,
      )
    } else {
      Nil
    }
    if r.truthy() {
      r
    } else {
      throw_tag(q_limit, t)
    }
  }
}

///|
/// Limit of an %integrate expression. For a definite integral
/// integrate(ee,var,a,b), when ee is free of the limit variable.
fn simplim_pctintegrate(e : Value, x : Value, pt : Value) -> Value raise {
  let ee = second(e) // ee = integrand
  let var_ = third(e) // integration variable
  let b0 = bind(q_var, var_)
  defer unbind(b0)
  let a = fourth(e) // lower limit or nil if indefinite
  let b = fifth(e) // upper limit or nil if indefinite
  if a.truthy() &&
    b.truthy() &&
    d_freeof(list([x, ee])).truthy() &&
    d_freeof(list([x, var_])).truthy() {
    let alim = ridofab(limit(a, x, pt, q_think))
    let blim = ridofab(limit(b, x, pt, q_think))
    if lenient_extended_realp(alim).truthy() &&
      lenient_extended_realp(blim).truthy() &&
      !eq(alim, q_d_infinity) &&
      !eq(blim, q_d_infinity) {
      let ans = ftake(q_p_integrate, [ee, var_, alim, blim])
      if consp(ans) && eq(caar(ans), q_p_integrate) {
        // could not find antideriv
        if eq(blim, q_d_inf) &&
          !eq(alim, q_d_minf) &&
          eq(d_sign(limit(ee, var_, blim, q_think)), q_d_pos) {
          // upper limit of integration growing with x: divergent, even if
          // could not find antideriv.
          q_d_inf
        } else {
          throw_tag(q_limit, t)
        }
      } else {
        ans // found antideriv, answer from ftake '%integrate
      }
    } else {
      throw_tag(q_limit, t)
    }
  } else {
    throw_tag(q_limit, t)
  }
}

///|
fn subftake(op : Value, subarg : Value, arg : Value) -> Value raise {
  simplifya(subfunmake(op, subarg, arg), t)
}

///|
fn off_one_to_inf(z : Value) -> Value raise {
  let z = trisplit(z) // split z into x+%i*y
  lbool(
    eq(t, mnqp(cdr(z), Fix(0L))) || // y # 0
    eq(t, mgrp(Fix(1L), car(z))),
  ) // x < 1
}

///|
fn simplim_pctli(expr : Value, x : Value, pt : Value) -> Value raise {
  let n = car(subfunsubs(expr))
  let e = car(subfunargs(expr))
  let elim = limit(e, x, pt, q_think)
  if freeof(x, n).truthy() {
    if eq(elim, q_d_minf) && integerp(n) && num_ge(n, Fix(2L)) {
      q_d_minf
    } else if eq(elim, q_d_inf) && integerp(n) && num_ge(n, Fix(2L)) {
      q_d_infinity
    } else if eql(ridofab(elim), Fix(1L)) ||
      (!extended_real_p(elim).truthy() && off_one_to_inf(elim).truthy()) {
      // Limit of li[s](1) can be evaluated by just substituting in 1. Same
      // for li[s](x) when x is < 1.
      subftake(q_d_li, list1(n), list1(elim))
    } else if !extended_real_p(elim).truthy() && !off_one_to_inf(elim).truthy() {
      // handle branch cut along line (1, inf). if we approach from negative
      // imaginary, result is the same as result on the line. if we approach
      // from positive imaginary, imaginary part of result has opposite sign.
      let dir = behavior(d_imagpart(e), limit__var(), limit__val())
      if eql(dir, Fix(-1L)) {
        subftake(q_d_li, list1(n), list1(elim))
      } else if eql(dir, Fix(1L)) {
        ftake(q_d_conjugate, [subftake(q_d_li, list1(n), list1(elim))])
      } else {
        throw_tag(q_limit, Nil)
      }
    } else {
      throw_tag(q_limit, Nil)
    }
  } else {
    // Claim ignorance when order depends on limit variable.
    throw_tag(q_limit, Nil)
  }
}

///|
fn simplim_dolpsi(order : Value, arg : Value, val : Value) -> Value raise {
  let b = bind(q_val, val)
  defer unbind(b)
  let mut order = order
  let mut arg = arg
  if length(order) != 1 && length(arg) != 1 {
    throw_tag(q_limit, Nil) |> ignore
  } else {
    order = car(order)
    arg = car(arg)
  }
  if equal(order, Fix(0L)) {
    let z = trisplit(arg)
    let mut rpart = car(z)
    let ipart = cdr(z)
    if !equal(ipart, Fix(0L)) {
      throw_tag(q_limit, Nil)
    } else {
      rpart = limit(rpart, limit__var(), val, q_think)
      if eq(rpart, q_d_zeroa) {
        q_d_minf
      } else if eq(rpart, q_d_zerob) {
        q_d_inf
      } else if eq(rpart, q_d_inf) {
        q_d_inf
      } else if eq(rpart, q_d_minf) {
        q_d_und
      } else if equal(getsignl(rpart), Fix(-1L)) {
        throw_tag(q_limit, Nil)
      } else {
        simplify(subfunmake(q_d_psi, list1(order), list1(rpart)))
      }
    }
  } else if integerp(order) &&
    num_gt(order, Fix(0L)) &&
    equal(limit(arg, limit__var(), val, q_think), q_d_inf) {
    if mevenp(order).truthy() {
      q_d_zerob
    } else if moddp(order).truthy() {
      q_d_zeroa
    } else {
      throw_tag(q_limit, Nil)
    }
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
fn simplim_pctinverse_jacobi_ns(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    Fix(0L)
  } else {
    mk(q_p_inverse_jacobi_ns, [arg, m])
  }
}

///|
fn simplim_pctinverse_jacobi_nc(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    mk(q_p_elliptic_kc, [m])
  } else {
    mk(q_p_inverse_jacobi_nc, [arg, m])
  }
}

///|
fn simplim_pctinverse_jacobi_sc(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    mk(q_p_elliptic_kc, [m])
  } else {
    mk(q_p_inverse_jacobi_sc, [arg, m])
  }
}

///|
fn simplim_pctinverse_jacobi_dc(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    mk(q_p_elliptic_kc, [m])
  } else {
    mk(q_p_inverse_jacobi_dc, [arg, m])
  }
}

///|
fn simplim_pctinverse_jacobi_cs(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    Fix(0L)
  } else {
    mk(q_p_inverse_jacobi_cs, [arg, m])
  }
}

///|
fn simplim_pctinverse_jacobi_ds(arg : Value, m : Value) -> Value raise {
  if eq(arg, q_d_inf) || eq(arg, q_d_minf) {
    Fix(0L)
  } else {
    mk(q_p_inverse_jacobi_ds, [arg, m])
  }
}

///|
fn simplim_pctsignum(e : Value, x : Value, pt : Value) -> Value raise {
  let e = limit(cadr(e), x, pt, q_think)
  if eq(q_d_minf, e) {
    Fix(-1L)
  } else if eq(q_d_inf, e) {
    Fix(1L)
  } else if eq(q_d_infinity, e) {
    q_d_ind
  } else if eq(q_d_ind, e) {
    q_d_ind
  } else if eq(q_d_und, e) {
    e
  } else if eq(q_d_zerob, e) {
    Fix(-1L)
  } else if eq(q_d_zeroa, e) {
    Fix(1L)
  } else {
    let sgn = mnqp(e, Fix(0L))
    if eq(t, sgn) {
      ftake(q_p_signum, [e])
    } else {
      throw_tag(q_limit, Nil) // don't know
    }
  }
}

///|
/// more functions for limit to handle
fn lfibtophi(e : Value) -> Value raise {
  if !involve(e, list1(q_d_fib)).truthy() {
    e
  } else if eq(caar(e), q_d_fib) {
    let lnorecurse = t
    d_fibtophi(list2(list1(q_d_fib), lfibtophi(cadr(e))), lnorecurse~)
  } else {
    cons(car(e), mapcar(x => lfibtophi(x), cdr(e)))
  }
}

///|
/// FOLLOWING CODE MAKES $LDEFINT WORK
fn d_ldefint(exp_ : Value, var_ : Value, ll : Value, ul : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_d_logabs, Nil)])
  defer unbind_all(bs)
  set(q_d_logabs, t) |> ignore
  let ans = sinint(exp_, var_)
  let mut a1 = toplevel__dollimit(list([ans, var_, ul, q_d_minus]))
  let mut a2 = toplevel__dollimit(list([ans, var_, ll, q_d_plus]))
  if limit__memq(a1, [q_d_inf, q_d_minf, q_d_infinity, q_d_und, q_d_ind]) {
    a1 = nounlimit(ans, var_, ul)
  }
  if limit__memq(a2, [q_d_inf, q_d_minf, q_d_infinity, q_d_und, q_d_ind]) {
    a2 = nounlimit(ans, var_, ll)
  }
  d_expand(sub_star(a1, a2))
}

///|
fn nounlimit(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  set(q_exp, restorelim(exp_)) |> ignore
  nconc(
    list([list1(q_p_limit), limit__exp(), var_, ridofab(val)]),
    if eq(val, q_d_zeroa) {
      list1(q_d_plus)
    } else if eq(val, q_d_zerob) {
      list1(q_d_minus)
    } else {
      Nil
    },
  )
}

///|
/// substitute inside noun form of %derivative for cases such as
///     limit('diff(x+2,x), x, 1) -> limit('diff(xx+3), xx, 0)
/// maxima-substitute with *atp* skips over %derivative
/// substitutes   diff(f(realvar), realvar, n) ->  diff(f(var+val), var, n)
fn derivative_subst(
  exp_ : Value,
  val : Value,
  var_ : Value,
  realvar : Value,
) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_val, val), (q_var, var_)])
  defer unbind_all(bs)
  if atom(exp_) {
    exp_
  } else if eq(q_p_derivative, caar(exp_)) {
    cons(
      car(exp_),
      cons(
        // the function being differentiated
        maxima_substitute(add2_star(val, var_), realvar, cadr(exp_)),
        cons(
          // the var of differentiation
          maxima_substitute(var_, realvar, caddr(exp_)),
          cdddr(exp_),
        ),
      ),
    ) // the order of the derivative
  } else {
    cons(
      car(exp_),
      mapcar(x => derivative_subst(x, val, var_, realvar), cdr(exp_)),
    )
  }
}

///|
fn oscip(e : Value) -> Value raise {
  let i = involve(e, list([q_p_sin, q_p_cos, q_p_tan]))
  if i.truthy() {
    i
  } else {
    among(q_d__pcti, p_einvolve(e))
  }
}

///|
/// Like OSCIP, but the dependency on VAR is explicit (second arg). Use this
/// instead when possible.
fn oscip_var(e : Value, var1 : Value) -> Value raise {
  let i = involve_var(e, var1, list([q_p_sin, q_p_cos, q_p_tan]))
  if i.truthy() {
    i
  } else {
    among(q_d__pcti, p_einvolve_var(e, var1))
  }
}

///|
fn p_einvolve(e : Value) -> Value raise {
  if among(q_d__pcte, e).truthy() {
    p_einvolve01(e)
  } else {
    Nil
  }
}

///|
fn p_einvolve01(e : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if mnump(e).truthy() {
    Nil
  } else if mexptp(e).truthy() &&
    eq(cadr(e), q_d__pcte) &&
    among(limit__var(), caddr(e)).truthy() {
    caddr(e)
  } else {
    some_value(x => p_einvolve(x), cdr(e))
  }
}

///|
/// Just like %EINVOLVE, except the dependency on VAR is explicit (second arg
/// here). Use this instead when possible.
fn p_einvolve_var(e : Value, var1 : Value) -> Value raise {
  if among(q_d__pcte, e).truthy() {
    // A copy of %ENVOLVE01, but for %EINVOLVE-VAR.
    if atom(e) {
      Nil
    } else if mnump(e).truthy() {
      Nil
    } else if mexptp(e).truthy() &&
      eq(cadr(e), q_d__pcte) &&
      among(var1, caddr(e)).truthy() {
      caddr(e)
    } else {
      some_value(ee => p_einvolve_var(ee, var1), cdr(e))
    }
  } else {
    Nil
  }
}
