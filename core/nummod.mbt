// Port of src/nummod.lisp: Maxima functions for floor, ceiling, mod,
// round, truncate and friends (Barton Willis).

///|
/// `(opcons op args...)` is `(ftake* op args...)`.
fn opcons(op : Value, args : Value) -> Value raise {
  simplifya(cons(list1(op), args), Nil)
}

///|
/// charfun(pred) evaluates to 1 when the predicate 'pred' evaluates to
/// true; it evaluates to 0 when 'pred' evaluates to false; otherwise, it
/// evaluates to a noun form.
fn simp_charfun(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  oneargcheck(e) |> ignore
  let e = take(list1(q_d_is), [maybe_simplifya(specrepcheck(second(e)), z)])
  let bool = with_special(q_d_prederror, Nil, () => mevalp(e))
  if eq(t, bool) {
    Fix(1L)
  } else if bool is Nil {
    Fix(0L)
  } else if op_equalp(e, list1(q_d_is)).truthy() {
    mk_simp(q_d_charfun, [second(e)])
  } else {
    mk_simp(q_d_charfun, [e])
  }
}

///|
fn integer_part_of_sum(e : Value) -> (Value, Value) raise {
  let mut i_sum : Value = Fix(0L)
  let mut n_sum : Value = Fix(0L)
  let mut o_sum : Value = Fix(0L)
  for ei in margs(e).iter() {
    if maxima_integerp(ei).truthy() {
      i_sum = add2(ei, i_sum)
    } else if ratnump(ei).truthy() || floatp(ei) || d_bfloatp(ei).truthy() {
      n_sum = add2(ei, n_sum)
    } else {
      o_sum = add2(ei, o_sum)
    }
  }
  let n = ftake_star(q_d_floor, [n_sum])
  i_sum = add2(i_sum, n)
  o_sum = add2(o_sum, sub(n_sum, n))
  (i_sum, o_sum)
}

///|
/// Return true if the expression can be formed using rational numbers,
/// logs, mplus, mexpt, or mtimes.
fn use_radcan_p(e : Value) -> Value raise {
  let r = d_ratnump(e)
  if r.truthy() {
    return r
  }
  lbool(
    op_equalp(e, list([q_p_log, q_mexpt, q_mplus, q_mtimes])).truthy() &&
    every(x => use_radcan_p(x).truthy(), cdr(e)),
  )
}

///|
/// `(bind-fpprec val body...)`
fn[T] nummod__bind_fpprec(val : Value, f : () -> T raise) -> T raise {
  with_specials(
    [
      (q_fpprec, Nil),
      (q_ear_bigfloatzero, Nil),
      (q_ear_bigfloatone, Nil),
      (q_ear_bfhalf, Nil),
      (q_ear_bfmhalf, Nil),
    ],
    () => with_special(q_d_fpprec, fpprec1(Nil, val), f),
  )
}

///|
/// When constantp(x) is true, we use bfloat evaluation to try to determine
/// the ceiling or floor. If numerical evaluation of e is ill-conditioned,
/// this function can misbehave. The evaluation is done with three values
/// for fpprec. When the floating point evaluations are inconsistent,
/// bailout and return nil.
fn pretty_good_floor_or_ceiling(
  x : Value,
  fn_ : Value,
  digits? : Value = Nil,
) -> Value raise {
  with_specials([(q_d_float2bf, t), (q_d_algebraic, t)], () => {
    let mut x = x
    let mut digits = if integerp(digits) && num_gt(Fix(0L), digits) {
      digits
    } else {
      Fix(25L)
    }
    catch_tag(q_done, () => {
      // To handle ceiling(%i^%i), we need to apply rectform. If bfloat
      // is improved, it might be possible to remove this call to rectform.
      x = d_rectform(x)
      if !d_freeof(list([q_d__pcti, q_d_minf, q_d_inf, q_d_und, q_d_infinity, x])).truthy() {
        throw_tag(q_done, Nil) |> ignore
      }
      // When x doesn't evaluate to a bigfloat, bailout and return nil.
      let mut f1 : Value = Nil
      nummod__bind_fpprec(digits, () => {
        f1 = d_bfloat(x)
        if !d_bfloatp(f1).truthy() {
          throw_tag(q_done, Nil) |> ignore
        }
      })
      digits = num_add(digits, Fix(20L))
      let mut f2 = nummod__bind_fpprec(digits, () => d_bfloat(x))
      if !d_bfloatp(f2).truthy() {
        throw_tag(q_done, Nil) |> ignore
      }
      digits = num_add(digits, Fix(20L))
      let mut f3 : Value = Nil
      let mut n : Value = Nil
      nummod__bind_fpprec(digits, () => {
        f3 = d_bfloat(x)
        if !d_bfloatp(f3).truthy() {
          throw_tag(q_done, Nil) |> ignore
        }
        // Let's say that the true value of x is in the interval
        // [f3 - |f3| * eps, f3 + |f3| * eps], where eps = 10^(20 - digits).
        // Define n to be the number of integers in this interval.
        let eps = power(d_bfloat(Fix(10L)), num_sub(Fix(20L), digits))
        let lb = sub(f3, mult(take(list1(q_mabs), [f3]), eps))
        let ub = add2(f3, mult(take(list1(q_mabs), [f3]), eps))
        // If n > 1, we're going to give up. Start by taking the
        // difference: if it's at least 2, then we know that n >= 2.
        if fpgreaterp(cdr(sub(ub, lb)), cdr(d_bfloat(Fix(2L)))).truthy() {
          throw_tag(q_done, Nil) |> ignore
        }
        n = sub(
          take(list1(q_d_ceiling), [ub]),
          take(list1(q_d_ceiling), [lb]),
        )
      })
      f1 = take(list1(fn_), [f1])
      f2 = take(list1(fn_), [f2])
      f3 = take(list1(fn_), [f3])
      // Provided f1 = f2 = f3 and n = 0, return f1.
      // If n = 1 and (use-radcan-p e) and ($radcan e) is a $ratnump,
      // return floor / ceiling of radcan(x).
      if num_eq(f1, f2) && num_eq(f2, f3) && num_eq(n, Fix(0L)) {
        f1
      } else if num_eq(f1, f2) &&
        num_eq(f2, f3) &&
        num_eq(n, Fix(1L)) &&
        use_radcan_p(x).truthy() {
        x = d_radcan(x)
        if d_ratnump(x).truthy() {
          take(list1(fn_), [x])
        } else {
          Nil
        }
      } else {
        Nil
      }
    })
  })
}

///|
fn nummod__compare_in(v : Value, opts : Array[String]) -> Bool {
  for o in opts {
    if equal(v, Str(o)) {
      return true
    }
  }
  false
}

///|
/// (a) The function fpentier rounds a bigfloat towards zero--we need to
///     check for that.
/// (b) floor(inf/minf) = inf/minf, floor(ind) = ind; floor(infinity)
///     remains unsimplified.
fn simp_floor(e : Value, e1 : Value, z : Value) -> Value raise {
  let mut e1 = e1
  oneargcheck(e) |> ignore
  let e = maybe_simplifya(specrepcheck(nth(1, e)), z)
  if numberp(e) {
    return floor1(e)
  }
  if ratnump(e).truthy() {
    return num_floor(cadr(e), b=caddr(e)).0
  }
  if d_bfloatp(e).truthy() {
    e1 = fpentier(e)
    return if minusp(cadr(e)) && !zerop1(sub(e1, e)).truthy() {
      one_minus(e1)
    } else {
      e1
    }
  }
  if maxima_integerp(e).truthy() {
    return e
  }
  if d_orderlessp(e, neg(e)).truthy() {
    return sub(Fix(0L), ftake_star(q_d_ceiling, [neg(e)]))
  }
  e1 = mget(e, q_d_numer)
  if e1.truthy() {
    let r = floor1(e1)
    if r.truthy() {
      return r
    }
  }
  if memq(e, list([q_d_inf, q_d_minf, q_d_ind, q_d_und])).truthy() {
    return e
  }
  // leave floor(infinity) as is
  if eq(e, q_d_zerob) {
    return Fix(-1L)
  }
  if eq(e, q_d_zeroa) {
    return Fix(0L)
  }
  if d_constantp(e).truthy() {
    let r = pretty_good_floor_or_ceiling(e, q_d_floor)
    if r.truthy() {
      return r
    }
  }
  if mplusp(e).truthy() {
    let (i_sum, o_sum) = integer_part_of_sum(e)
    let o_sum = if equal(i_sum, Fix(0L)) {
      mk_simp(q_d_floor, [o_sum])
    } else {
      ftake_star(q_d_floor, [o_sum])
    }
    return add2(i_sum, o_sum)
  }
  // handle 0 <= e < 1 implies floor(e) = 0 and
  // -1 <= e < 0 implies floor(e) = -1.
  if nummod__compare_in(d_compare(Fix(0L), e), ["<", "<="]) &&
    equal(d_compare(e, Fix(1L)), Str("<")) {
    return Fix(0L)
  }
  if nummod__compare_in(d_compare(Fix(-1L), e), ["<", "<="]) &&
    equal(d_compare(e, Fix(0L)), Str("<")) {
    return Fix(-1L)
  }
  mk_simp(q_d_floor, [e])
}

///|
fn floor_integral(x : Value) -> Value raise {
  let f = take(list1(q_d_floor), [x])
  muln_([f, div(Fix(1L), Fix(2L)), addn_([mul2(Fix(2L), x), Fix(-1L), neg(f)])])
}

///|
fn ceiling_integral(x : Value) -> Value raise {
  let f = take(list1(q_d_ceiling), [x])
  muln_([f, div(Fix(1L), Fix(2L)), addn_([Fix(1L), mul2(Fix(2L), x), neg(f)])])
}

///|
/// The limit of the argument with `*preserve-direction*` bound to t
/// (keeps $zeroa and $zerob).
fn nummod__arglim(arg : Value, var_ : Value, val : Value) -> Value raise {
  with_special(q_ear_preserve_direction, t, () => limit(
    arg,
    var_,
    val,
    q_think,
  ))
}

///|
fn simplim_pctfloor(expr : Value, var_ : Value, val : Value) -> Value raise {
  let arg = cadr(expr)
  let b = behavior(arg, var_, val)
  let arglimab = nummod__arglim(arg, var_, val)
  let arglim = ridofab(arglimab)
  if eq(arglim, q_d_ind) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_minf) {
    q_d_minf
  } else if eq(arglim, q_d_inf) {
    q_d_inf
  } else if num_eq(b, Fix(-1L)) && maxima_integerp(arglim).truthy() {
    sub_star(arglim, Fix(1L))
  } else if num_eq(b, Fix(1L)) && maxima_integerp(arglim).truthy() {
    arglim
  } else if d_constantp(arglim).truthy() && !maxima_integerp(arglim).truthy() {
    ftake(q_d_floor, [arglim])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
fn simp_ceiling(e : Value, e1 : Value, z : Value) -> Value raise {
  let mut e1 = e1
  oneargcheck(e) |> ignore
  let e = maybe_simplifya(specrepcheck(nth(1, e)), z)
  if numberp(e) {
    return ceiling1(e)
  }
  if ratnump(e).truthy() {
    return num_ceiling(cadr(e), b=caddr(e)).0
  }
  if d_bfloatp(e).truthy() {
    return sub(Fix(0L), ftake_star(q_d_floor, [sub(Fix(0L), e)]))
  }
  if maxima_integerp(e).truthy() {
    return e
  }
  if d_orderlessp(e, neg(e)).truthy() {
    return sub_star(Fix(0L), ftake_star(q_d_floor, [neg(e)]))
  }
  e1 = mget(e, q_d_numer)
  if e1.truthy() {
    let r = ceiling1(e1)
    if r.truthy() {
      return r
    }
  }
  if memq(e, list([q_d_inf, q_d_minf, q_d_ind, q_d_und])).truthy() {
    return e
  }
  // leave ceiling(infinity) as is
  if eq(e, q_d_zerob) {
    return Fix(0L)
  }
  if eq(e, q_d_zeroa) {
    return Fix(1L)
  }
  if d_constantp(e).truthy() {
    let r = pretty_good_floor_or_ceiling(e, q_d_ceiling)
    if r.truthy() {
      return r
    }
  }
  if mplusp(e).truthy() {
    let (i_sum, o_sum) = integer_part_of_sum(e)
    let o_sum = if equal(i_sum, Fix(0L)) {
      mk_simp(q_d_ceiling, [o_sum])
    } else {
      ftake_star(q_d_ceiling, [o_sum])
    }
    return add2(i_sum, o_sum)
  }
  // handle 0 < e <= 1 implies ceiling(e) = 1 and
  // -1 < e <= 0 implies ceiling(e) = 0.
  if equal(d_compare(Fix(0L), e), Str("<")) &&
    nummod__compare_in(d_compare(e, Fix(1L)), ["<", "<="]) {
    return Fix(1L)
  }
  if equal(d_compare(Fix(-1L), e), Str("<")) &&
    nummod__compare_in(d_compare(e, Fix(0L)), ["<", "<="]) {
    return Fix(0L)
  }
  mk_simp(q_d_ceiling, [e])
}

///|
fn simplim_pctceiling(expr : Value, var_ : Value, val : Value) -> Value raise {
  let arg = cadr(expr)
  let b = behavior(arg, var_, val)
  let arglimab = nummod__arglim(arg, var_, val)
  let arglim = ridofab(arglimab)
  if eq(arglim, q_d_ind) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_minf) {
    q_d_minf
  } else if eq(arglim, q_d_inf) {
    q_d_inf
  } else if num_eq(b, Fix(-1L)) && maxima_integerp(arglim).truthy() {
    arglim
  } else if num_eq(b, Fix(1L)) && maxima_integerp(arglim).truthy() {
    add2_star(arglim, Fix(1L))
  } else if d_constantp(arglim).truthy() && !maxima_integerp(arglim).truthy() {
    ftake(q_d_ceiling, [arglim])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
/// See "Concrete Mathematics," Section 3.21.
fn simp_nummod(e : Value, e1 : Value, z : Value) -> Value raise {
  ignore(e1)
  twoargcheck(e) |> ignore
  let x = maybe_simplifya(specrepcheck(cadr(e)), z)
  let y = maybe_simplifya(specrepcheck(caddr(e)), z)
  if zerop1(y).truthy() || zerop1(x).truthy() {
    return x
  }
  if equal(Fix(1L), y) {
    return sub(x, ftake_star(q_d_floor, [x]))
  }
  if d_constantp(x).truthy() && d_constantp(y).truthy() {
    return sub(x, mul2(y, ftake_star(q_d_floor, [div(x, y)])))
  }
  let e1 = d_gcd(x, y, Nil)
  if !equal(Fix(1L), e1) {
    mul2(e1, ftake_star(q_d_mod, [div(x, e1), div(y, e1)]))
  } else {
    mk_simp(q_d_mod, [x, y])
  }
}

///|
/// The function 'round' rounds a number to the nearest integer. For a
/// tie, round to the nearest even integer.  (def-simplifier round (e))
fn simp__pctround(form : Value, y : Value, p__pctsimpflag : Value) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(q_p_round), nummod__q_d_e),
    )
    |> ignore
  }
  let e = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_round), list1(e)), form)
  if d_featurep(e, q_d_integer).truthy() {
    // takes care of round(round(x)) --> round(x).
    e
  } else if memq(e, list([q_d_inf, q_d_minf, q_d_und, q_d_ind])).truthy() {
    e
  } else if eq(e, q_d_zerob) {
    Fix(0L)
  } else if eq(e, q_d_zeroa) {
    Fix(0L)
  } else {
    let lb = take(list1(q_d_floor), [e])
    let ub = take(list1(q_d_ceiling), [e])
    let sgn = csign(sub(sub(ub, e), sub(e, lb)))
    if eq(sgn, t) {
      give_up()
    } else if eq(sgn, q_d_neg) {
      ub
    } else if eq(sgn, q_d_pos) {
      lb
    } else if alike1(lb, ub).truthy() {
      // For floats that are integers, this can happen. Maybe featurep
      // should catch this.
      lb
    } else if eq(sgn, q_d_zero) && d_featurep(lb, q_d_even).truthy() {
      lb
    } else if eq(sgn, q_d_zero) && d_featurep(ub, q_d_even).truthy() {
      ub
    } else {
      let r = apply_reflection_simp(mop(form), e, b=t)
      if r.truthy() {
        r
      } else {
        give_up()
      }
    }
  }
}

///|
fn simplim_pctround(expr : Value, var_ : Value, val : Value) -> Value raise {
  let arg = cadr(expr)
  let b = behavior(arg, var_, val)
  let arglimab = nummod__arglim(arg, var_, val)
  let arglim = ridofab(arglimab)
  let half = symval(q_n1_sl_sl2)
  if eq(arglim, q_d_ind) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_infinity) {
    throw_tag(q_limit, Nil)
  } else if eq(arglim, q_d_minf) {
    q_d_minf
  } else if eq(arglim, q_d_inf) {
    q_d_inf
  } else if num_eq(b, Fix(-1L)) &&
    maxima_integerp(add2_star(half, arglim)).truthy() {
    sub_star(arglim, half)
  } else if num_eq(b, Fix(1L)) &&
    maxima_integerp(add2_star(half, arglim)).truthy() {
    add2_star(arglim, half)
  } else if d_constantp(arglim).truthy() &&
    !maxima_integerp(add2_star(half, arglim)).truthy() {
    ftake(q_p_round, [arglim])
  } else {
    throw_tag(q_limit, Nil)
  }
}

///|
/// Round a number towards zero.  (def-simplifier truncate (e))
fn simp__pcttruncate(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 1 {
    wna_err(
      form,
      required_arg_count=Fix(1L),
      pretty_name=list2(list1(q_p_truncate), nummod__q_d_e),
    )
    |> ignore
  }
  let e = simpcheck(nth(1, form), p__pctsimpflag)
  let give_up = () => eqtest(cons(list1(q_p_truncate), list1(e)), form)
  if d_featurep(e, q_d_integer).truthy() {
    // takes care of truncate(truncate(x)) --> truncate(x).
    e
  } else if memq(e, list([q_d_inf, q_d_minf, q_d_und, q_d_ind])).truthy() {
    e
  } else if eq(e, q_d_zerob) {
    Fix(0L)
  } else if eq(e, q_d_zeroa) {
    Fix(0L)
  } else {
    let sgn = csign(e)
    if memq(sgn, list([q_d_neg, q_d_nz])).truthy() {
      take(list1(q_d_ceiling), [e])
    } else if memq(sgn, list([q_d_zero, q_d_pz, q_d_pos])).truthy() {
      take(list1(q_d_floor), [e])
    } else {
      let r = apply_reflection_simp(mop(form), e, b=t)
      if r.truthy() {
        r
      } else {
        give_up()
      }
    }
  }
}

///|
/// integrate(signum(x),x) = |x|
fn signum_integral(x : Value) -> Value raise {
  take(list1(q_mabs), [x])
}

///|
/// integrate(unit_step(x),x) = (x + |x|)/2
fn unit_step_integral(x : Value) -> Value raise {
  div(add2(x, take(list1(q_mabs), [x])), Fix(2L))
}

///|
/// integrate(mod(x,a),x) = (mod(x,a)^2-a*mod(x,a)+a*x)/2
fn mod_integral(x : Value, a : Value) -> Value raise {
  let q = take(list1(q_d_mod), [x, a])
  div(addn_([mul2(q, q), muln_([Fix(-1L), a, q]), mul2(a, x)]), Fix(2L))
}

///|
let nummod__q_d_e : Value = sym("$e")

///|
fn nummod__bags() -> Value {
  list([q_mlist, q_d_matrix, q_mequal])
}

///|
fn init_nummod() -> Unit raise {
  d_put(q_d_nummod, Fix(3L), q_d_version) |> ignore
  // Let's remove built-in symbols from list for user-defined properties.
  set(q_d_props, remove(q_d_nummod, symval(q_d_props))) |> ignore
  putprop(q_d_charfun, q_simp_charfun, q_operators) |> ignore
  putprop(q_p_charfun, q_simp_charfun, q_operators) |> ignore
  putprop(q_d_floor, q_simp_floor, q_operators) |> ignore
  putprop(q_d_floor, q_tex_matchfix, q_tex) |> ignore
  putprop(
    q_d_floor,
    list2(list1(Str("\\left \\lfloor ")), Str(" \\right \\rfloor")),
    q_texsym,
  )
  |> ignore
  // $floor distributes over lists, matrices, and equations
  setf_get(q_d_floor, q_distribute_over, nummod__bags()) |> ignore
  putprop(q_d_entier, q_tex_matchfix, q_tex) |> ignore
  putprop(
    q_d_entier,
    list2(list1(Str("\\lfloor ")), Str(" \\rfloor")),
    q_texsym,
  )
  |> ignore
  // $entier and $fix distributes over lists, matrices, and equations
  setf_get(q_d_entier, q_distribute_over, nummod__bags()) |> ignore
  setf_get(q_d_fix, q_distribute_over, nummod__bags()) |> ignore
  putprop(q_d_floor, list2(list1(q_x), q_floor_integral), q_integral)
  |> ignore
  putprop(q_d_ceiling, list2(list1(q_x), q_ceiling_integral), q_integral)
  |> ignore
  putprop(q_d_ceiling, q_simp_ceiling, q_operators) |> ignore
  putprop(q_d_floor, q_simplim_pctfloor, q_simplim_pctfunction) |> ignore
  putprop(q_d_ceiling, q_tex_matchfix, q_tex) |> ignore
  putprop(
    q_d_ceiling,
    list2(list1(Str("\\left \\lceil ")), Str(" \\right \\rceil")),
    q_texsym,
  )
  |> ignore
  // $ceiling distributes over lists, matrices, and equations.
  setf_get(q_d_ceiling, q_distribute_over, nummod__bags()) |> ignore
  putprop(q_d_ceiling, q_simplim_pctceiling, q_simplim_pctfunction) |> ignore
  putprop(q_d_mod, q_simp_nummod, q_operators) |> ignore
  putprop(q_d_mod, q_tex_infix, q_tex) |> ignore
  putprop(q_d_mod, list1(Str(" \\rm{mod} ")), q_texsym) |> ignore
  putprop(q_d_mod, Fix(180L), q_tex_lbp) |> ignore
  putprop(q_d_mod, Fix(180L), q_tex_rbp) |> ignore
  // $mod distributes over lists, matrices, and equations
  setf_get(q_d_mod, q_distribute_over, nummod__bags()) |> ignore
  // This property is important to get round(round(x)) => round(x).
  setf_get(q_p_round, q_integer_valued, t) |> ignore
  setf_get(q_p_round, q_reflection_rule, q_odd_function_reflect) |> ignore
  // round distributes over lists, matrices, and equations.
  setf_get(q_p_round, q_distribute_over, nummod__bags()) |> ignore
  putprop(q_p_round, q_simplim_pctround, q_simplim_pctfunction) |> ignore
  // This property is important to get truncate(truncate(x)) =>
  // truncate(x).
  setf_get(q_p_truncate, q_integer_valued, t) |> ignore
  setf_get(q_p_truncate, q_reflection_rule, q_odd_function_reflect) |> ignore
  // truncate distributes over lists, matrices, and equations.
  setf_get(q_p_truncate, q_distribute_over, nummod__bags()) |> ignore
  putprop(q_p_signum, list2(list1(q_x), q_signum_integral), q_integral)
  |> ignore
  putprop(q_d_unit_step, list2(list1(q_x), q_unit_step_integral), q_integral)
  |> ignore
  // integrate(mod(x,a),a) doesn't have representation in terms of
  // functions known to Maxima.
  putprop(q_d_mod, list([list2(q_x, q_y), q_mod_integral, Nil]), q_integral)
  |> ignore
}
