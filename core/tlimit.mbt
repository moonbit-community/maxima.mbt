// Port of src/tlimit.lisp: Taylor-series based limits ($tlimit, $tldefint)
// and the method dispatcher LIMIT-BY-METHODS.
//
// LIMIT-BY-METHODS iterates over a list of limit methods and stops when a
// method is successful. A method is considered successful when it returns a
// value that is neither a boolean (often produced by a non-local exit) nor a
// limit nounform. Recursion is guarded by *limit-method-depth* (compared with
// *max-limit-depth*) and by fingerprints stored in
// *already-processed-limits*; the limit variable is normalized to
// *universal-limit-variable* so that alike limits are detected.
//
// When tlimit.lisp is compiled, VAR is a special variable (proclaimed by
// earlier files) but VAL is not; functions whose parameter is named VAR bind
// it dynamically.

///|
fn d_tlimit(args : Value) -> Value raise {
  with_special(q_limit_using_taylor, t, () => d_limit(args))
}

///|
fn d_tldefint(exp_ : Value, var_ : Value, ll : Value, ul : Value) -> Value raise {
  with_special(q_limit_using_taylor, t, () => d_ldefint(exp_, var_, ll, ul))
}

///|
/// Taylor cannot handle conjugate, ceiling, floor, unit_step, or signum
/// expressions, so tlimit does not try them. Expressions containing $ind are
/// also disallowed, as are acos and asin (see bug #4416).
fn tlimp(e : Value, x : Value) -> Value raise {
  if d_mapatom(e).truthy() && !eq(e, q_d_ind) && !eq(e, q_d_und) {
    return t
  }
  match e {
    Cons({ car: Cons({ car: op, .. }), cdr: args }) => {
      let ok1 = !among(x, e).truthy() ||
        !(
          eq(op, q_d_conjugate) ||
          eq(op, q_d_ceiling) ||
          eq(op, q_d_floor) ||
          eq(op, q_d_unit_step) ||
          eq(op, q_p_signum) ||
          eq(op, q_p_acos) ||
          eq(op, q_p_asin)
        )
      if !ok1 {
        return Nil
      }
      let ok2 = known_ps(op).truthy() ||
        (eq(op, q_mqapply) && known_ps(subfunname(e)).truthy()) ||
        eq(op, q_mplus) ||
        eq(op, q_mtimes) ||
        eq(op, q_mexpt) ||
        eq(op, q_p_log) ||
        get(op, q_grad).truthy() ||
        d_freeof(list([x, e])).truthy()
      if !ok2 {
        return Nil
      }
      lbool(every(q => tlimp(q, x).truthy(), args))
    }
    _ => Nil
  }
}

///|
/// Use `logarc` to transform all occurrences of `%atan2` subexpression in
/// `e`, but do not transform other log-like functions.
fn logarc_atan2(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if eq(caar(e), q_p_atan2) {
    logarc(
      q_p_atan2,
      list([logarc_atan2(second(e)), logarc_atan2(third(e))]),
    )
  } else {
    recur_apply(q_logarc_atan2, e)
  }
}

///|
/// In the expression `e`, replace all subexpressions of the form atan2(y,x),
/// where y is not explicitly equal to zero, by 2*atan((sqrt(x^2+y^2) - x)/y).
fn atan2_to_atan(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if is_op(e, q_p_atan2) {
    let y = second(e)
    let x = third(e)
    if zerop1(y).truthy() {
      e
    } else {
      mul2(
        Fix(2L),
        ftake(q_p_atan, [
          div(
            sub(
              ftake(q_mexpt, [
                add2(mul2(x, x), mul2(y, y)),
                div(Fix(1L), Fix(2L)),
              ]),
              x,
            ),
            y,
          ),
        ]),
      )
    }
  } else if d_subvarp(mop(e)).truthy() {
    // subscripted function: don't map onto the operator subscripts
    subfunmake(
      subfunname(e),
      subfunsubs(e),
      mapcar(q => atan2_to_atan(q), subfunargs(e)),
    )
  } else {
    fapply(caar(e), mapcar(q => atan2_to_atan(q), cdr(e)))
  }
}

///|
/// Returns T iff EXPR contains a %LOG subexpression that involves VAR and
/// %I, and whose argument becomes zero at PT.
fn has_complex_singular_log_p(
  expr : Value,
  var_ : Value,
  pt : Value,
) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  if atom(expr) {
    Nil
  } else if eq(caar(expr), q_p_log) {
    let arg = cadr(expr)
    if among(var_, arg).truthy() && among(q_d__pcti, arg).truthy() {
      if zerop1(no_err_sub_var(pt, arg, var_)).truthy() {
        t
      } else {
        has_complex_singular_log_p(arg, var_, pt)
      }
    } else {
      Nil
    }
  } else {
    some_value(arg => has_complex_singular_log_p(arg, var_, pt), cdr(expr))
  }
}

///|
/// Compute the Taylor series expansion of `e` at `pt` with respect to `x`.
/// If the expansion vanishes and the recursion depth `d` is less than 16,
/// retry with increased order. If recursion depth exceeds 16 or the
/// expansion fails, return nil; otherwise, return the Taylor expansion.
fn tlimit_taylor(
  e : Value,
  x : Value,
  pt : Value,
  n : Value,
  d? : Value = Fix(0L),
) -> Value raise {
  let tle = lbool(!has_complex_singular_log_p(e, x, pt).truthy())
  let bs = bind_all([
    (q_silent_taylor_flag, t),
    (q_d_taylordepth, Fix(8L)),
    (q_d_radexpand, Nil),
    (q_d_taylor_logexpand, tle),
    (q_d_logexpand, Nil),
  ])
  defer unbind_all(bs)
  if eq(pt, q_d_infinity) {
    // infinity is an illegitimate limit point
    Nil
  } else {
    let ee = d_totaldisrep(
      catch_tag(q_taylor_catch, () => d_taylor(e, list([x, pt, n]))),
    )
    if ee.truthy() && !eql(ee, Fix(0L)) {
      ee
    } else if ee.truthy() && num_lt(d, Fix(16L)) {
      // Retry if Taylor returns zero and depth is less than 16
      tlimit_taylor(
        e,
        x,
        pt,
        num_mul(Fix(2L), num_max(Fix(1L), n)),
        d=one_plus(d),
      )
    } else {
      Nil
    }
  }
}

///|
/// Attempt to compute the limit of `e` as `var` approaches `val` using a
/// Taylor expansion. If the Taylor expansion succeeds, apply limit methods to
/// the resulting series; otherwise apply the limit methods to `e`.
///
/// Facts learned by asksign during the Taylor expansion are stored in the
/// initial context; equalities found there are substituted into the
/// expression and the expansion is retried.
fn taylim(e : Value, var_ : Value, val : Value, flag? : Value = Nil) -> Value raise {
  ignore(flag)
  let bs = bind_all([
    (q_ear_already_processed_limits, symval(q_ear_already_processed_limits)),
    (q_ear_limit_method_depth, symval(q_ear_limit_method_depth)),
    (q_var, var_),
  ])
  defer unbind_all(bs)
  let mut redo = false
  let mut et : Value = Nil
  if tlimp(e, var_).truthy() {
    let mut e1 = stirling0(e)
    let pt = ridofab(val)
    // First Taylor attempt
    et = tlimit_taylor(e1, var_, pt, symval(q_d_lhospitallim), d=Fix(0L))
    // When asksign appends temporary facts, they are stored in the
    // initial context. Substitute all such facts into e1 and try again.
    for fct0 in cdr(d_facts(ctxt=q_d_initial)).iter() {
      if consp(fct0) && eq(q_d_equal, caar(fct0)) {
        redo = true
        let fct = sort_list(cdr(fct0), (a, b) => great(a, b).truthy())
        let r = limit__errcatch(() => maxima_substitute(cadr(fct), car(fct), e1))
        if r is Nil {
          throw_tag(q_limit, Nil) |> ignore
        } else {
          e1 = car(r)
        }
      }
    }
    // Retry Taylor after rewriting, if needed
    if redo {
      et = tlimit_taylor(e1, var_, pt, symval(q_d_lhospitallim), d=Fix(0L))
    }
    // If Taylor succeeded, set taylored to true and dispatch methods on et;
    // otherwise dispatch methods on e.
    if et.truthy() {
      with_special(q_taylored, t, () => limit_by_methods(
        et,
        var_,
        val,
        list([
          q_limit_sum_of_powers, q_limit_method_think, q_limit1, q_limit_method_reciprocal_limit_point,
        ]),
      ))
    } else {
      limit_by_methods(
        e,
        var_,
        val,
        list([
          q_limit_method_think, q_limit1, q_limit_method_reciprocal_limit_point,
        ]),
      )
    }
  } else {
    Nil
  }
}

///|
fn limit_method_think(e : Value, x : Value, pt : Value) -> Value raise {
  limit(e, x, pt, q_think)
}

///|
fn liminv_new_val(val : Value) -> Value raise {
  if eq(val, q_d_zeroa) {
    q_d_inf
  } else if eq(val, q_d_zerob) {
    q_d_minf
  } else if eq(val, q_d_inf) {
    q_d_zeroa
  } else if eq(val, q_d_minf) {
    q_d_zerob
  } else {
    Nil
  }
}

///|
/// Attempt to compute the limit of E as VAR approaches VAL by transforming
/// the limit point via reciprocal substitution.
fn limit_method_reciprocal_limit_point(
  e : Value,
  var_ : Value,
  val : Value,
) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  let ee = maxima_substitute(div(Fix(1L), var_), var_, e)
  let new_val = liminv_new_val(val)
  if new_val.truthy() {
    with_special(q_ear_preserve_direction, t, () => taylim(
      ee,
      var_,
      new_val,
      flag=Nil,
    ))
  } else {
    throw_tag(q_limit, t)
  }
}

///|
/// A limit method result is successful only if it is non-nil, not the
/// special inconclusive marker T, and not a %limit nounform.
fn successful_limit_result_p(ans : Value) -> Value raise {
  lbool(ans.truthy() && !eq(ans, t) && !among(q_p_limit, ans).truthy())
}

///|
/// Apply a sequence of limit methods to compute limit(e, x, pt).
///
/// Each method FN is called as (FN e x pt) and may return a value, NIL, or
/// throw to 'limit. The first value satisfying successful-limit-result-p is
/// returned. Recursion guards: *limit-method-depth* is compared with
/// *max-limit-depth*, and a fingerprint of (FN, e, x, pt) is recorded in
/// *already-processed-limits*; repeating a fingerprint aborts.
fn limit_by_methods(
  e : Value,
  x : Value,
  pt : Value,
  methods : Value,
) -> Value raise {
  // Initialize guards if not already bound
  let apl = symval(q_ear_already_processed_limits)
  let depth0 = {
    let d = symval(q_ear_limit_method_depth)
    if d.truthy() {
      d
    } else {
      Fix(0L)
    }
  }
  let bs = bind_all([
    (q_ear_already_processed_limits, if apl.truthy() { apl } else { Nil }),
    (q_ear_limit_method_depth, depth0),
  ])
  defer unbind_all(bs)
  if num_gt(symval(q_ear_limit_method_depth), symval(q_ear_max_limit_depth)) {
    throw_tag(q_limit, Nil) |> ignore
  }
  with_special(
    q_ear_limit_method_depth,
    one_plus(symval(q_ear_limit_method_depth)),
    () => catch_tag(q_limit_found, () => {
      for fn_ in methods.iter() {
        // recursion guard
        let u = symval(q_ear_universal_limit_variable)
        let fingerprint = ftake(q_mlist, [
          int(position(fn_, methods)),
          maxima_substitute(u, x, e),
          u,
          pt,
        ])
        for f in symval(q_ear_already_processed_limits).iter() {
          if alike1(fingerprint, f).truthy() {
            throw_tag(q_limit, Nil) |> ignore
          }
        }
        set(
          q_ear_already_processed_limits,
          cons(fingerprint, symval(q_ear_already_processed_limits)),
        )
        |> ignore
        // run method
        let ans = catch_tag(q_limit, () => funcall(fn_, [e, x, pt]))
        if successful_limit_result_p(ans).truthy() {
          throw_tag(q_limit_found, ans) |> ignore
        }
      }
      Nil
    }),
  )
}

///|
/// Return true if `e` is a monomial of the form `x^q`, where `q` is a
/// rational number. Also returns true if `e` is `x`.
fn power_of_x_p(e : Value, x : Value) -> Value raise {
  if eq(e, x) {
    t
  } else if mexptp(e).truthy() && eq(x, second(e)) {
    d_ratnump(third(e))
  } else {
    Nil
  }
}

///|
/// Return true iff `e` is a linear combination of monomials of the form
/// `x^q`, where `q` is a rational number (possibly zero).
fn sum_of_powers_p(e : Value, x : Value) -> Value raise {
  if d_mapatom(e).truthy() || freeof(x, e).truthy() {
    return t
  }
  let p = power_of_x_p(e, x)
  if p.truthy() {
    p
  } else if mtimesp(e).truthy() {
    lbool(
      every(
        q => freeof(x, q).truthy() || power_of_x_p(q, x).truthy(),
        cdr(e),
      ),
    )
  } else if mplusp(e).truthy() {
    lbool(every(q => sum_of_powers_p(q, x).truthy(), cdr(e)))
  } else {
    Nil
  }
}

///|
/// If `e` is a linear combination of terms like `x^q`, where `q` is an
/// explicit rational number, return limit(e, x, pt); otherwise, return nil.
/// The limit point `pt` must be one of `minf`, `zerob`, `zeroa`, `0`, or
/// `inf`.
fn limit_sum_of_powers(e : Value, x : Value, pt : Value) -> Value raise {
  if !sum_of_powers_p(e, x).truthy() {
    // not a sum of powers, return nil
    return Nil
  }
  if eq(pt, q_d_zeroa) || eq(pt, q_d_zerob) || eql(pt, Fix(0L)) {
    // Try direct substitution
    let b = bind(q_d_errormsg, Nil)
    defer unbind(b)
    let ans = limit__errcatch(() => maxima_substitute(Fix(0L), x, e))
    if ans is Nil {
      // direct substitution failed, transform limit point to inf or minf
      // and try again
      let cntx = d_supcontext(Nil)
      let g = gensym()
      defer {
        let _ = try Some(d_killcontext(list1(cntx))) catch { _ => None }

      }
      putprop(g, t, q_internal) |> ignore // ask no questions about the gensym
      assume(ftake(q_mgreaterp, [g, symval(q_ear_large_positive_number)]))
      |> ignore
      limit_sum_of_powers(
        resimplify(maxima_substitute(div(Fix(1L), g), x, e)),
        g,
        if eq(pt, q_d_zeroa) {
          q_d_inf
        } else {
          q_d_minf
        },
      )
    } else {
      // direct substitution succeeded--when the limit is zero, use zero-fixup
      let a = car(ans)
      if eq(t, meqp(a, Fix(0L))) {
        zero_fixup(e, x, pt)
      } else {
        a
      }
    }
  } else if eq(pt, q_d_minf) || eq(pt, q_d_inf) {
    // Set ee to a list of the additive terms of e
    let ee = if mplusp(e).truthy() { cdr(e) } else { list1(e) }
    // Replace each term ck*x^pk of the list `ee` by `ck . pk` and push them
    // in the list `ll`
    let mut ll : Value = Nil
    for ek in ee.iter() {
      let pk = sratsimp(mul2(x, div(sdiff(ek, x), ek)))
      let ck = sratsimp(div(ek, ftake(q_mexpt, [x, pk])))
      ll = cons(cons(ck, pk), ll)
    }
    // Sort the terms of `ll` and determine the highest power
    ll = sort_list(ll, (a, b) => eq(t, mgrp(cdr(a), cdr(b))))
    let pk = cdr(first(ll)) // pk is now the largest power
    // Process leading coefficients
    ll = mapcar(
      q => if eq(t, meqp(pk, cdr(q))) { car(q) } else { Fix(0L) },
      ll,
    )
    let ck = fapply(q_mplus, ll) // ck is now the leading coefficient
    if eql(pk, Fix(0L)) {
      // Leading term is ck x^0, so limit is ck
      ck
    } else if eq(t, mgrp(pk, Fix(0L))) {
      // Leading term is ck x^pk where pk > 0
      let sgn = maybe_asksign_real(ck)
      if eq(sgn, q_d_neg) {
        if eq(pt, q_d_inf) {
          q_d_minf
        } else {
          q_d_inf
        }
      } else if eq(sgn, q_d_pos) {
        if eq(pt, q_d_inf) {
          q_d_inf
        } else {
          q_d_minf
        }
      } else if eq(sgn, q_d_complex) || eq(sgn, q_d_imaginary) {
        q_d_infinity
      } else {
        Nil
      }
    } else if eq(t, mgrp(Fix(0L), pk)) {
      // leading term is ck x^pk where pk < 0: the limit is a zero, so
      // dispatch `zero-fixup`
      zero_fixup(mul2(ck, power(x, pk)), x, pt)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn init_tlimit() -> Unit raise {
  defvar_init(q_ear_universal_limit_variable, gensym())
  // For limits toward `inf`, assume that the limit variable exceeds
  // *large-positive-number*.
  defvar_init(q_ear_large_positive_number, expt(Fix(10L), Fix(8L)))
}
