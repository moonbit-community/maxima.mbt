// Port of src/limit.lisp, part 1: the top level ($limit, toplevel-$limit),
// assumptions, simpinf, LIMIT, LIMIT1 and helpers.
//
// I believe a large portion of this file is described in Paul Wang's
// thesis, "Evaluation of Definite Integrals by Symbolic Manipulation,"
// MIT/LCS/TR-92, Oct. 1971.
//
// Up to the Gruntz section (limit_4.mbt) the following are special
// variables, so a parameter or LET of one of these names is a dynamic
// binding and every reference goes through the symbol value cell:
// origval *indicator numer denom exp var val taylored logcombed
// $exponentialize lhp? lhcount loginprod? context *limit-assumptions*
// $expintrep limit-top, as well as the globally special *i*, sign, nn*.

///|
/// The special variable VAR.
fn limit__var() -> Value {
  symval(q_var)
}

///|
/// The special variable VAL.
fn limit__val() -> Value {
  symval(q_val)
}

///|
/// The special variable EXP.
fn limit__exp() -> Value {
  symval(q_exp)
}

///|
/// `(member x '(a b ...))` for a list of symbols (or fixnums).
fn limit__memq(x : Value, l : Array[Value]) -> Bool {
  for s in l {
    if eql(x, s) {
      return true
    }
  }
  false
}

///|
/// The Lisp macro ERRCATCH: `(list value)` on success, NIL when a Maxima
/// error, a Lisp error, or a throw to an errcatch tag (errorsw,
/// macsyma-quit, rat-err) happens.
fn limit__errcatch(f : () -> Value raise) -> Value raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  let bs = bind_all([(q_errcatch, ec), (q_ear_mdebug, Nil)])
  defer unbind_all(bs)
  let r : Result[Value, Error] = try Ok(f()) catch { e => Err(e) }
  match r {
    Ok(v) => list1(v)
    Err(LispError::Throw(tag, v)) =>
      if eq(tag, q_errorsw) || eq(tag, q_macsyma_quit) || eq(tag, q_rat_err) {
        // with-errcatch-tag-$errors: signal a Maxima error (for rat-err with
        // its own message), which the handler then cleans up after.
        let _ = try Some(
          with_special(q_ear_merror_signals__dolerror_p, t, () => if eq(
            tag, q_rat_err,
          ) {
            apply(q_merror, v)
          } else {
            merr("An error was caught by errcatch.", [])
          }),
        ) catch {
          _ => None
        }
        errlfun1(ec) |> ignore
        Nil
      } else {
        raise LispError::Throw(tag, v)
      }
    Err(LispError::ReturnFrom(_, _) as e) => raise e
    Err(LispError::Go(_) as e) => raise e
    Err(e) =>
      if is_maxima_error(e) {
        errlfun1(ec) |> ignore
        Nil
      } else {
        let msg = match e {
          LispError::SimpleError(s) => s
          LispError::Condition(_, s, _) => s
          _ => "Lisp error"
        }
        set(q_d_error, list([list2(q_mlist, q_simp), Str(msg)])) |> ignore
        if symval(q_d_errormsg).truthy() {
          d_errormsg() |> ignore
        }
        errlfun1(ec) |> ignore
        Nil
      }
  }
}

///|
fn putlimval(e : Value, v : Value) -> Value raise {
  let exp_ = mk(q_p_limit, [e, limit__var(), limit__val()])
  if assolike(exp_, symval(q_limit_answers)) is Nil {
    set(q_limit_answers, cons(cons(exp_, v), symval(q_limit_answers)))
    |> ignore
  }
  v
}

///|
fn getlimval(e : Value) -> Value raise {
  let exp_ = cons(list1(q_p_limit), list([e, limit__var(), limit__val()]))
  assolike(exp_, symval(q_limit_answers))
}

///|
/// macro LIMIT-CATCH
fn limit_catch(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  with_special(q_errorsw, t, () => {
    let ans = catch_tag(q_errorsw, () => catch_tag(q_limit, () => limit(
      exp_, var_, val, q_think,
    )))
    if ans is Nil || eq(ans, t) {
      Nil
    } else {
      ans
    }
  })
}

///|
fn d_limit(args : Value) -> Value raise {
  let mut first_try = toplevel__dollimit(args)
  if consp(first_try) && eq(caar(first_try), q_p_limit) {
    with_special(q_ear_getsignl_asksign_ok, t, () => toplevel__dollimit(args))
  } else {
    // The function toplevel-$limit sets $numer, $%enumer, %emode, and
    // $%e_to_numlog to false. When any of these option variables are true,
    // we resimplify the limit in the current context.
    if symval(q_d_numer).truthy() ||
      symval(q_d__pctenumer).truthy() ||
      symval(q_d__pctemode).truthy() ||
      symval(q_d__pcte_to_numlog).truthy() {
      first_try = resimplify(first_try)
    }
    first_try
  }
}

///|
/// Return true iff the expression e has a subexpression that is an
/// indefinite integral.
fn indefinite_integral_p(e : Value, x : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    Nil
  } else if eq(caar(e), q_p_integrate) && alike1(x, third(e)).truthy() {
    lbool(fourth(e) is Nil)
  } else {
    lbool(some(q => indefinite_integral_p(q, x).truthy(), cdr(e)))
  }
}

///|
fn toplevel__dollimit(args : Value) -> Value raise {
  let bs = bind_all([
    (q_ear_limit_assumptions, Nil),
    (q_ear_old_integer_info, Nil),
    (q_d_keepfloat, t),
    (q_d_numer, Nil),
    (q_d__pctenumer, Nil),
    (q_d__pctemode, t),
    (q_d__pcte_to_numlog, Nil),
    (q_limit_top, t),
  ])
  defer unbind_all(bs)
  if !symval(q_limitp).truthy() {
    set(q_ear_old_integer_info, symval(q_ear_integer_info)) |> ignore
    set(q_ear_integer_info, Nil) |> ignore
  }
  let r = limit__toplevel_body(args) catch {
    e => {
      restore_assumptions() |> ignore
      raise e
    }
  }
  restore_assumptions() |> ignore
  r
}

///|
/// The body of TOPLEVEL-$LIMIT inside its UNWIND-PROTECT.
fn limit__toplevel_body(args : Value) -> Value raise {
  let lenargs = length(args)
  let bs = bind_all([
    (q_lhcount, symval(q_d_lhospitallim)),
    (q_ear_behavior_count_now, Fix(0L)),
    (q_exp, Nil),
    (q_var, Nil),
    (q_val, Nil),
    (q_n_starindicator, Nil),
    (q_taylored, Nil),
    (q_origval, Nil),
    (q_logcombed, Nil),
    (q_lhp_q, Nil),
    (q_varlist, Nil),
    (q_genvar, Nil),
    (q_loginprod_q, Nil),
    (q_limit_answers, Nil),
    (q_limitp, t),
    (q_simplimplus_problems, Nil),
  ])
  defer unbind_all(bs)
  let mut dr : Value = Nil
  let mut ans : Value = Nil
  if !(lenargs == 3 || lenargs == 4 || lenargs == 1) {
    wna_err(q_d_limit) |> ignore
  }
  // Is it a LIST of Things?
  ans = limit_list(car(args), cdr(args))
  if ans.truthy() {
    return ans
  }
  let exp1 = specrepcheck(first(args))
  if atom(exp1) && (exp1 is Nil || eq(exp1, t)) {
    // The expression is 'T or 'NIL. Return immediately.
    return exp1
  }
  if lenargs == 1 {
    set(q_var, gensym()) |> ignore
    set(q_val, Fix(0L)) |> ignore
  } else {
    set(q_var, second(args)) |> ignore
    if d_constantp(limit__var()).truthy() {
      merr(
        "limit: second argument must be a variable, not a constant; found: ~M",
        [limit__var()],
      )
      |> ignore
    }
    if !(d_subvarp(limit__var()).truthy() || atom(limit__var())) {
      merr("limit: variable must be a symbol or subscripted symbol; found: ~M", [
        limit__var(),
      ])
      |> ignore
    }
    set(q_val, infsimp(third(args))) |> ignore
    // infsimp converts -inf to minf. it also converts -infinity to
    // infinity, although perhaps this should generate the error below.
    let v = limit__val()
    if !atom(v) && some(x => !freeof(x, v).truthy(), symval(q_ear_infinities)) {
      merr(
        "limit: third argument must be a finite value or one of: inf, minf, infinity; found: ~M",
        [v],
      )
      |> ignore
    }
    if eq(v, q_d_zeroa) {
      dr = q_d_plus
    }
    if eq(v, q_d_zerob) {
      dr = q_d_minus
    }
  }
  if lenargs == 4 {
    if !limit__memq(fourth(args), [q_d_plus, q_d_minus]) {
      merr("limit: direction must be either 'plus' or 'minus'; found: ~M", [
        fourth(args),
      ])
      |> ignore
    }
    dr = fourth(args)
  }
  if atom(limit__var()) && !among(limit__var(), limit__val()).truthy() {
    set(q_exp, exp1) |> ignore
  } else {
    // Var is funny so make it a gensym.
    let realvar = limit__var()
    set(q_var, gensym()) |> ignore
    set(q_exp, maxima_substitute(limit__var(), realvar, exp1)) |> ignore
    putprop(limit__var(), realvar, q_limitsub) |> ignore
  }
  // When exp involves an indefinite integral whose integration variable is
  // the limit variable, return a limit nounform. Do this even when limsubst
  // is true.
  if indefinite_integral_p(limit__exp(), limit__var()).truthy() {
    return cons(list1(q_p_limit), args)
  }
  set(q_varlist, ncons(limit__var())) |> ignore
  set(q_genvar, Nil) |> ignore
  set(q_origval, limit__val()) |> ignore
  // Transform limits to minf to limits to inf by replacing var with -var
  // everywhere.
  if eq(limit__val(), q_d_minf) {
    set(q_val, q_d_inf) |> ignore
    set(q_origval, q_d_inf) |> ignore
    set(q_exp, subin(mul2_star(Fix(-1L), limit__var()), limit__exp()))
    |> ignore
  }
  // Transform the limit value.
  if !infinityp(limit__val()).truthy() {
    with_special(q_ear_atp, t, () => {
      // *atp* prevents substitution from applying to vars bound by %sum,
      // %product, %integrate, %limit
      let realvar = limit__var()
      set(q_var, gensym()) |> ignore
      putprop(limit__var(), t, q_internal) |> ignore
      set(
        q_exp,
        derivative_subst(limit__exp(), limit__val(), limit__var(), realvar),
      )
      |> ignore
      set(
        q_exp,
        maxima_substitute(
          add2_star(limit__val(), limit__var()),
          realvar,
          limit__exp(),
        ),
      )
    })
    |> ignore
    set(
      q_val,
      if eq(dr, q_d_plus) {
        q_d_zeroa
      } else if eq(dr, q_d_minus) {
        q_d_zerob
      } else {
        Fix(0L)
      },
    )
    |> ignore
    set(q_origval, Fix(0L)) |> ignore
  }
  // Convert a limit from below to a limit from above.
  if !infinityp(limit__val()).truthy() && eq(dr, q_d_minus) {
    set(
      q_exp,
      maxima_substitute(mul2(Fix(-1L), limit__var()), limit__var(), limit__exp()),
    )
    |> ignore
    dr = q_d_plus
    set(q_val, q_d_zeroa) |> ignore
  }
  // Make assumptions about limit var being very small or very large.
  // Assumptions are forgotten upon exit.
  if lenargs != 1 {
    limit_context(limit__var(), limit__val(), dr) |> ignore
  }
  // Use $expand to resimplify `exp` in light of new assumptions. When `exp`
  // is free of the limit `var`, perform pure simplification using
  // ($expand exp 0 0); otherwise, call ($expand exp 1 0).
  let expop : Value = if d_freeof(list([limit__var(), limit__exp()])).truthy() {
    Fix(0L)
  } else {
    Fix(1L)
  }
  set(
    q_exp,
    resimplify(
      d_minfactorial(
        extra_simp(d_expand(limit__exp(), expop~, expon=Fix(0L))),
      ),
    ),
  )
  |> ignore
  if !(real_epsilonp(limit__val()).truthy() || infinityp(limit__val()).truthy()) {
    // if direction of limit not specified, compute from both sides
    ans = both_side(limit__exp(), limit__var(), limit__val())
  } else {
    set(q_exp, mabs_subst(limit__exp(), limit__var(), limit__val())) |> ignore
    // and find limit from one side
    ans = limit_catch(limit__exp(), limit__var(), limit__val())
    // try gruntz
    if !ans.truthy() {
      ans = catch_tag(q_taylor_catch, () => with_special(
        q_silent_taylor_flag,
        t,
        () => gruntz1(limit__exp(), limit__var(), limit__val(), Nil),
      ))
    }
    // try taylor series expansion if simple limit didn't work
    if ans is Nil &&
      symval(q_d_tlimswitch).truthy() &&
      !symval(q_limit_using_taylor).truthy() {
      ans = with_special(q_limit_using_taylor, t, () => limit_catch(
        limit__exp(),
        limit__var(),
        limit__val(),
      ))
    }
  }
  if ans.truthy() {
    clean_limit_exp(ans)
  } else {
    // failure: return nounform
    cons(list1(q_p_limit), args)
  }
}

///|
fn clean_limit_exp(exp_ : Value) -> Value raise {
  let e = restorelim(exp_)
  if symval(q_ear_preserve_direction).truthy() {
    e
  } else {
    ridofab(e)
  }
}

///|
/// Users who want limit to map over equality (mequal) will need to do that
/// manually.
fn limit_list(exp1 : Value, rest_ : Value) -> Value raise {
  if mbagp(exp1).truthy() && !mequalp(exp1).truthy() {
    cons(car(exp1), mapcar(x => toplevel__dollimit(cons(x, rest_)), cdr(exp1)))
  } else {
    Nil
  }
}

///|
/// Only works on entry!
fn limit_context(var_ : Value, val : Value, direction : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  if symval(q_limit_top).truthy() {
    let a = assume(
      ftake(q_mgreaterp, [q_prin_inf, symval(q_ear_large_positive_number)]),
    )
    set(
      q_ear_limit_assumptions,
      cons(a, make_limit_assumptions(var_, val, direction)),
    )
    |> ignore
    set(q_limit_top, Nil) |> ignore
  }
  symval(q_ear_limit_assumptions)
}

///|
fn make_limit_assumptions(
  var_ : Value,
  val : Value,
  direction : Value,
) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let new_assumptions : Value = Nil
  if var_ is Nil || val is Nil {
    Nil
  } else if !infinityp(val).truthy() && direction is Nil {
    Nil
  } else if eq(val, q_d_inf) {
    cons(
      assume(ftake(q_mgreaterp, [var_, symval(q_ear_large_positive_number)])),
      new_assumptions,
    )
  } else if eq(val, q_d_minf) {
    cons(
      assume(
        ftake(q_mgreaterp, [
          num_neg(symval(q_ear_large_positive_number)),
          var_,
        ]),
      ),
      new_assumptions,
    )
  } else if eq(direction, q_d_plus) {
    // All limits around 0
    cons(assume(ftake(q_mgreaterp, [var_, Fix(0L)])), new_assumptions)
  } else if eq(direction, q_d_minus) {
    cons(assume(ftake(q_mgreaterp, [Fix(0L), var_])), new_assumptions)
  } else {
    Nil
  }
}

///|
fn restore_assumptions() -> Value raise {
  for a in symval(q_ear_limit_assumptions).iter() {
    forget(a) |> ignore
  }
  if symval(q_ear_integer_info).truthy() && !symval(q_limitp).truthy() {
    for l in symval(q_ear_integer_info).iter() {
      i__dolremove(list2(cadr(l), caddr(l))) |> ignore
    }
    set(q_ear_integer_info, symval(q_ear_old_integer_info))
  } else {
    Nil
  }
}

///|
/// The optional arg allows the caller to decide on the value of
/// *preserve-direction*. Default is nil, since we immediately ridofab.
fn both_side(
  exp_ : Value,
  var_ : Value,
  val : Value,
  preserve? : Value = Nil,
) -> Value raise {
  let bs = bind_all([
    (q_exp, exp_),
    (q_var, var_),
    (q_val, val),
    (q_ear_preserve_direction, preserve),
  ])
  defer unbind_all(bs)
  let la = toplevel__dollimit(list([exp_, var_, val, q_d_plus]))
  // Immediately propagate an und without trying the other direction
  if eq(la, q_d_und) {
    return q_d_und
  }
  let lb = toplevel__dollimit(list([exp_, var_, val, q_d_minus]))
  // Immediately propagate an und
  if eq(lb, q_d_und) {
    return q_d_und
  }
  let ra = ridofab(la)
  let rb = ridofab(lb)
  // Since `equal` does not consider `equal(ind, ind)` to be true, we need an
  // explicit test for the `ind, ind` case.
  if (eq(ra, q_d_ind) && eq(rb, q_d_ind)) || eq(t, meqp(ra, rb)) {
    ra
  } else if !free(la, q_p_limit).truthy() || !free(lb, q_p_limit).truthy() {
    Nil
  } else {
    let infa = infinityp(la).truthy()
    let infb = infinityp(lb).truthy()
    if infa && infb {
      // inf + minf => infinity
      q_d_infinity
    } else if infa || infb {
      q_d_und
    } else {
      q_d_ind
    }
  }
}

///|
/// Return true when Maxima should return a limit nounform for
/// limit(e,x,var,val).
fn limunknown(e : Value, var_ : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  lbool(!limit_ok(e, var_).truthy())
}

///|
/// Return true when Maxima's limit code should be able to determine limit
fn limit_ok(e : Value, x : Value) -> Value raise {
  if mapatom(e).truthy() {
    // mapatoms are OK
    t
  } else if eq(caar(e), q_p_integrate) &&
    alike1(x, third(e)).truthy() &&
    fourth(e) is Nil {
    // return nil for an indefinite integral
    Nil
  } else if eq(caar(e), q_p_integrate) {
    // Return true for integrate(X,z,a,b) provided (a) freeof(x,X) (b)
    // limit-ok(a,x) and (c) limit-ok(b,x). (The value of the first form of
    // this clause is discarded, as in the Lisp code.)
    if limit_ok(fourth(e), x).truthy() {
      limit_ok(fifth(e), x) |> ignore
    }
    if symval(q_d_limsubst).truthy() {
      symval(q_d_limsubst)
    } else {
      d_freeof(list([third(e), x]))
    }
  } else {
    // when the operator of e either (a) has a simplim%function, (b) is a
    // simplifying operator (including subscripted operators), or (c) is
    // $fib, check that each argument of e is OK.
    let op = caar(e)
    let ok = get(op, q_operators).truthy() ||
      get(op, q_simplim_pctfunction).truthy() ||
      (eq(op, q_mqapply) && get(subfunname(e), q_specsimp).truthy()) ||
      eq(op, q_d_fib)
    if ok || symval(q_d_limsubst).truthy() {
      if every(q => limit_ok(q, x).truthy(), cdr(e)) {
        t
      } else {
        d_freeof(list([x, e]))
      }
    } else {
      Nil
    }
  }
}

///|
/// The function factosimp is not called by the limit code or by any code in
/// source.
fn factosimp(e : Value) -> Value raise {
  let mut e = e
  if involve(e, list([q_p_gamma])).truthy() {
    e = d_makefact(e)
  }
  if involve(e, list([q_mfactorial])).truthy() {
    e = simplify(d_minfactorial(e))
    e
  } else {
    e
  }
}

///|
/// Define sgn = csign(limit(z,var,val)). Return -1, 0, 1, or nil when sgn is
/// neg, zero, pos, or complex, imaginary or unknown (including when the
/// limit is ind), respectively. Also, when the limit is either zerob or
/// zeroa, return 0. This function only does an asksign when
/// *getsignl-asksign-ok* is true.
fn getsignl(z : Value) -> Value raise {
  let z = with_special(q_ear_preserve_direction, Nil, () => limit_catch(
    z,
    limit__var(),
    limit__val(),
  ))
  if eq(z, q_d_ind) || eq(z, q_d_und) || eq(z, q_d_infinity) {
    // Don't call csign on ind, und, infinity, zeroa, or zerob.
    Nil
  } else if eq(z, q_d_zeroa) {
    Fix(0L)
  } else if eq(z, q_d_zerob) {
    Fix(0L)
  } else {
    // SIGN-PREP refuses to ask about an expression whose imaginary part is
    // not EQUAL to 0. Z is a limit value, free of the limit variable, so ask
    // about it with LIMITP bound to NIL - the way CSIGN does, imaginary guard
    // included.
    let sgn = if symval(q_ear_getsignl_asksign_ok).truthy() &&
      freeof_extended_real(z).truthy() &&
      !eq(t, mnqp(d_imagpart(z), Fix(0L))) {
      with_specials([(q_sign_imag_errp, Nil), (q_limitp, Nil)], () => catch_tag(
        q_sign_imag_err,
        () => d_asksign(z),
      ))
    } else {
      d_csign(z)
    }
    if eq(sgn, q_d_pos) {
      Fix(1L)
    } else if eq(sgn, q_d_neg) {
      Fix(-1L)
    } else if eq(sgn, q_d_zero) {
      Fix(0L)
    } else {
      Nil
    }
  }
}

///|
fn restorelim(exp_ : Value) -> Value raise {
  if exp_ is Nil {
    Nil
  } else if atom(exp_) {
    if symbolp(exp_) {
      let s = get(exp_, q_limitsub)
      if s.truthy() {
        s
      } else {
        exp_
      }
    } else {
      exp_
    }
  } else if consp(car(exp_)) && eq(caar(exp_), q_mrat) {
    cons(car(exp_), cons(restorelim(cadr(exp_)), restorelim(cddr(exp_))))
  } else {
    cons(car(exp_), mapcar(x => restorelim(x), cdr(exp_)))
  }
}

///|
/// For each subexpression of e of the form abs(X), decide if abs(X) can be
/// replaced by -X or by X. Define ans = limit(X,var, val) and
/// bee = behavior(X,var,val). Cases:
///  (a) negative (ans = -1) & decreasing (bee = -1), do abs(X) --> -X
///  (b) positive (ans = 1) & increasing (bee = 1), do abs(X) --> X
///  (c) zero (ans = 0) & decreasing (bee = -1), do abs(X) --> -X
///  (d) zero (ans = 0) & X increasing (bee = 1), do abs(X) --> X
fn mabs_subst(e : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  if d_mapatom(e).truthy() {
    e
  } else if is_op(e, q_mabs) {
    // Found a subexpression of the form abs(X).
    let e = mabs_subst(cadr(e), var_, val) // recurse on mabs-subst
    let ans = getsignl(e)
    let bee = if ans.truthy() { behavior(e, var_, val) } else { Nil }
    if eql(ans, Fix(-1L)) && eql(bee, Fix(-1L)) {
      mul2(Fix(-1L), e) // negative & decreasing
    } else if eql(ans, Fix(1L)) && eql(bee, Fix(1L)) {
      e // positive & increasing
    } else if eql(ans, Fix(0L)) && eql(bee, Fix(-1L)) {
      mul2(Fix(-1L), e) // zero & decreasing
    } else if eql(ans, Fix(0L)) && eql(bee, Fix(1L)) {
      e // zero & increasing
    } else {
      ftake(q_mabs, [e]) // don't know
    }
  } else if d_subvarp(mop(e)).truthy() {
    // Map mabs-subst over a subscripted function.
    subfunmake(
      subfunname(e),
      mapcar(q => mabs_subst(q, var_, val), subfunsubs(e)),
      mapcar(q => mabs_subst(q, var_, val), subfunargs(e)),
    )
  } else {
    // Map mabs-subst over the expression.
    fapply(caar(e), mapcar(q => mabs_subst(q, var_, val), cdr(e)))
  }
}

///|
/// Called on an expression that might contain $INF, $MINF, $ZEROA, $ZEROB.
/// Tries to simplify it to sort out things like inf^inf or inf+1.
fn simpinf(exp_ : Value) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  simpinf_ic(exp_, infinity_count=count_general_inf(exp_))
}

///|
fn count_general_inf(expr : Value) -> Value raise {
  count_atoms_matching(
    lfunc("count-general-inf-pred", a => {
      let x = arg(a, 0)
      lbool(infinityp(x).truthy() || real_epsilonp(x).truthy())
    }),
    expr,
  )
}

///|
/// Count the number of atoms in the Maxima expression EXPR matching
/// PREDICATE, ignoring dummy variables and array indices.
fn count_atoms_matching(predicate : Value, expr : Value) -> Value raise {
  if atom(expr) {
    if funcall(predicate, [expr]).truthy() {
      Fix(1L)
    } else {
      Fix(0L)
    }
  } else if member(caar(expr), symval(q_dummy_variable_operators)).truthy() {
    // Don't count atoms that occur as a limit of %integrate, %sum, %product,
    // %limit etc.
    count_atoms_matching(predicate, cadr(expr))
  } else if member(q_array, car(expr)).truthy() {
    // Ignore array indices
    Fix(0L)
  } else {
    let mut s : Value = Fix(0L)
    for a in cdr(expr).iter() {
      s = num_add(s, count_atoms_matching(predicate, a))
    }
    s
  }
}

///|
fn simpinf_ic(exp_ : Value, infinity_count? : Value = Nil) -> Value raise {
  let b = bind(q_exp, exp_)
  defer unbind(b)
  if eql(infinity_count, Fix(0L)) {
    // A very slow identity transformation...
    exp_
  } else if eql(infinity_count, Fix(1L)) {
    // If there's only one infinity, we replace it by a variable and take the
    // limit as that variable goes to infinity. Use $gensym in case we can't
    // compute the answer and the limit leaks out.
    let v0 = inf_typep(exp_)
    let val = if v0.truthy() { v0 } else { epsilon_typep(exp_) }
    let b1 = bind(q_val, val)
    defer unbind(b1)
    let var_ = d_gensym()
    let b2 = bind(q_var, var_)
    defer unbind(b2)
    let expr = subst(var_, val, exp_)
    let lim = toplevel__dollimit(list([expr, var_, val]))
    // Now we look to see whether the computed limit is any simpler than what
    // we shoved in (which we'll define as "doesn't contain EXPR as a
    // subtree"). If so, return it. Otherwise, return the original form.
    if !subtree_p(
        expr,
        lim,
        test_=lfunc("equal", a => lbool(equal(arg(a, 0), arg(a, 1)))),
      ).truthy() {
      lim
    } else {
      exp_
    }
  } else {
    // If more than one infinity, we have to be a bit more careful.
    let arguments = mapcar(x => simpinf(x), cdr(exp_))
    let new_expression = cons(list1(caar(exp_)), arguments)
    if among(q_d_und, arguments).truthy() {
      // If any of the arguments are undefined, we are too.
      q_d_und
    } else if amongl(list([q_p_limit, q_d_ind]), arguments).truthy() {
      // If we ended up with something indeterminate, we punt and just return
      // the input.
      exp_
    } else if mexptp(exp_).truthy() {
      // Exponentiation & multiplication
      simpinf_expt(first(arguments), second(arguments))
    } else if mtimesp(exp_).truthy() {
      simpinf_times(arguments)
    } else {
      // Down to at most one infinity? We do this after exponentiation to
      // avoid zeroa^zeroa => 0^0, and after multiplication to avoid
      // zeroa * inf => 0 * inf => 0.
      let infinities_left = count_general_inf(new_expression)
      if num_le(infinities_left, Fix(1L)) {
        simpinf_ic(new_expression, infinity_count=infinities_left)
      } else if mplusp(exp_).truthy() {
        // Addition
        simpinf_plus(arguments)
      } else {
        // Give up!
        new_expression
      }
    }
  }
}

///|
/// When we have a product, we need to spot that zeroa * zerob = zerob,
/// zeroa * inf = und etc. Each of ARGUMENTS is either a number, computed
/// successfully by the recursive SIMPINF call, or maybe a %LIMIT noun-form.
fn simpinf_times(arguments : Value) -> Value raise {
  if member(Fix(0L), arguments).truthy() {
    if find_if(x => infinityp(x).truthy(), arguments).truthy() {
      q_d_und
    } else if every(x => atom(x), arguments) {
      Fix(0L)
    } else {
      limit__exp()
    }
  } else if member(q_d_infinity, arguments).truthy() {
    if every(x => atom(x), arguments) {
      q_d_infinity
    } else {
      limit__exp()
    }
  } else {
    simplimit(cons(list1(q_mtimes), arguments), limit__var(), limit__val())
  }
}

///|
/// Is X one of 0, zeroa, zerob (CL `case` with keys (0 $zeroa $zerob))?
fn limit__zero_star(x : Value) -> Bool {
  eql(x, Fix(0L)) || eq(x, q_d_zeroa) || eq(x, q_d_zerob)
}

///|
/// In the comments below, zero* represents one of 0, zeroa, zerob.
fn simpinf_expt(base : Value, exponent : Value) -> Value raise {
  if eq(base, q_d_inf) {
    // inf^inf = inf, inf^minf = 0, inf^zero* = und, inf^foo = inf^foo
    if eq(exponent, q_d_inf) {
      q_d_inf
    } else if eq(exponent, q_d_minf) {
      Fix(0L)
    } else if limit__zero_star(exponent) {
      q_d_und
    } else {
      mk(q_mexpt, [base, exponent])
    }
  } else if eq(base, q_d_minf) {
    // minf^inf = infinity, minf^minf = 0, minf^zero* = und
    if eq(exponent, q_d_inf) {
      q_d_infinity
    } else if eq(exponent, q_d_minf) {
      Fix(0L)
    } else if limit__zero_star(exponent) {
      q_d_und
    } else {
      mk(q_mexpt, [base, exponent])
    }
  } else if limit__zero_star(base) {
    // zero*^inf = 0, zero*^minf = und, zero*^zero* = und
    if eq(exponent, q_d_inf) {
      Fix(0L)
    } else if eq(exponent, q_d_minf) {
      q_d_und
    } else if limit__zero_star(exponent) {
      q_d_und
    } else {
      mk(q_mexpt, [base, exponent])
    }
  } else if !amongl(
      append(symval(q_ear_infinitesimals), symval(q_ear_infinities)),
      base,
    ).truthy() {
    // When a isn't crazy, try a^b = e^(b log(a))
    simpinf(power_star(q_d__pcte, mul2_star(exponent, mk(q_p_log, [base]))))
  } else {
    // No idea. Just return what we've found so far.
    mk(q_mexpt, [base, exponent])
  }
}

///|
/// We know that none of the arguments are infinitesimals, since SIMPINF
/// never returns one of them. As such, we partition our arguments into
/// infinities and everything else.
fn simpinf_plus(arguments : Value) -> Value raise {
  let mut bigs : Value = Nil
  let mut others : Value = Nil
  for arg in arguments.iter() {
    if infinityp(arg).truthy() {
      bigs = cons(arg, bigs)
    } else {
      others = cons(arg, others)
    }
  }
  bigs = limit__delete_duplicates_eql(bigs)
  if cdr(bigs).truthy() {
    // inf + minf or the like
    q_d_und
  } else if bigs.truthy() {
    // inf + smaller + stuff
    car(bigs)
  } else {
    cons(list1(q_mplus), others)
  }
}

///|
/// CL `delete-duplicates` with the default EQL test: later occurrences are
/// kept.
fn limit__delete_duplicates_eql(l : Value) -> Value {
  let c = Collector::new()
  let mut p = l
  while p is Cons(_) {
    let x = car(p)
    if !member(x, cdr(p)).truthy() {
      c.add(x)
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// CL `remove-duplicates` with an ALIKE1 test: later occurrences are kept.
fn limit__remove_duplicates_alike(l : Value) -> Value raise {
  let c = Collector::new()
  let mut p = l
  while p is Cons(_) {
    let x = car(p)
    let mut dup = false
    for y in cdr(p).iter() {
      if alike1(x, y).truthy() {
        dup = true
        break
      }
    }
    if !dup {
      c.add(x)
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// Simplify expression with zeroa or zerob.
fn simpab(small : Value) -> Value raise {
  if small is Nil {
    Nil
  } else if limit__memq(small, [
      q_d_zeroa, q_d_zerob, q_d_inf, q_d_minf, q_d_infinity,
    ]) {
    small
  } else if !free(small, q_d_ind).truthy() {
    // Not exactly right but not causing trouble now.
    q_d_ind
  } else if !free(small, q_d_und).truthy() {
    q_d_und
  } else if mapatom(small).truthy() {
    small
  } else {
    let new_small = subst(
      power_star(q_d_inf, Fix(-1L)),
      q_d_zeroa,
      subst(power_star(q_d_minf, Fix(-1L)), q_d_zerob, small),
    )
    with_special(q_ear_preserve_direction, t, () => simpinf(new_small))
  }
}

///|
/// Return true iff the expression e contains either a binary64 or a Maxima
/// big float number.
fn has_float(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    if floatp(e) {
      t
    } else {
      d_bfloatp(e)
    }
  } else {
    some_value(x => has_float(x), cdr(e))
  }
}

///|
/// *I* INDICATES: T => USE LIMIT1,THINK, NIL => USE SIMPLIMIT.
///
/// The function `limit1` dispatches `factor` on the expression `exp`. When
/// the expression involves a floating point number, these numbers are
/// converted to rational approximations, so this code dispatches
/// `simplimit` when `exp` contains a floating point number.
fn limit(exp_ : Value, var_ : Value, val : Value, ear_i : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val), (q_ear_i, ear_i)])
  defer unbind_all(bs)
  if among(q_d_und, limit__exp()).truthy() {
    return q_d_und
  }
  if eq(limit__var(), limit__exp()) {
    return limit__val()
  }
  if atom(limit__exp()) {
    return limit__exp()
  }
  // Throw an limit error for expressions such as limit(x < 8,x,0),
  // limit(diff(f(x),x),x,0), and ...
  if limunknown(limit__exp(), limit__var()).truthy() {
    return throw_tag(q_limit, t)
  }
  if !among(limit__var(), limit__exp()).truthy() {
    let e = limit__exp()
    return if amongl(list([q_d_inf, q_d_minf, q_d_infinity, q_d_ind]), e).truthy() {
      simpinf(e)
    } else if amongl(list([q_d_zeroa, q_d_zerob]), e).truthy() {
      // Simplify expression with zeroa or zerob.
      simpab(e)
    } else {
      e
    }
  }
  let g = getlimval(limit__exp())
  if g.truthy() {
    return g
  }
  let v = if symval(q_limit_using_taylor).truthy() &&
    symval(q_taylored) is Nil &&
    tlimp(limit__exp(), limit__var()).truthy() {
    taylim(limit__exp(), limit__var(), limit__val(), flag=symval(q_ear_i))
  } else if ratp(limit__exp(), limit__var()).truthy() {
    // Limit of a rational expression: for polynomial cases toward zero,
    // `limit-of-polynomial` returns the limit without expansion or other
    // transformations. For non-polynomial cases, call `ratlim`.
    let p = limit_of_polynomial(limit__exp(), limit__var(), limit__val())
    if p.truthy() {
      p
    } else {
      ratlim(limit__exp())
    }
  } else {
    // Rational in a root of VAR: RATLIM after VAR = T^K.
    let r = ratlim_in_root(limit__exp(), limit__var(), limit__val())
    if r.truthy() {
      r
    } else if has_float(limit__exp()).truthy() {
      simplimit(limit__exp(), limit__var(), limit__val())
    } else if eq(symval(q_ear_i), t) ||
      radicalp(limit__exp(), limit__var()).truthy() {
      limit1(limit__exp(), limit__var(), limit__val())
    } else if eq(symval(q_ear_i), q_think) {
      if mtimesp(limit__exp()).truthy() || mexptp(limit__exp()).truthy() {
        limit1(limit__exp(), limit__var(), limit__val())
      } else {
        simplimit(limit__exp(), limit__var(), limit__val())
      }
    } else {
      simplimit(limit__exp(), limit__var(), limit__val())
    }
  }
  putlimval(limit__exp(), v)
}

///|
/// The least K such that E is a rational function of VAR^(1/K), or NIL when
/// VAR occurs in E other than as a rational power of itself.
fn root_order(e : Value, var_ : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  if eq(e, var_) {
    Fix(1L)
  } else if atom(e) {
    Fix(1L)
  } else if mexptp(e).truthy() && eq(cadr(e), var_) {
    let p = caddr(e)
    if integerp(p) {
      Fix(1L)
    } else if ratnump(p).truthy() {
      caddr(p)
    } else {
      Nil
    }
  } else if mexptp(e).truthy() {
    if integerp(caddr(e)) {
      root_order(cadr(e), var_)
    } else {
      Nil
    }
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    let mut k : Value = Fix(1L)
    for f in cdr(e).iter() {
      let kf = root_order(f, var_)
      if kf.truthy() {
        k = num_lcm(k, kf)
      } else {
        return Nil
      }
    }
    k
  } else if free(e, var_).truthy() {
    Fix(1L)
  } else {
    Nil
  }
}

///|
/// E with VAR^(P/Q) replaced by T^(P*K/Q) and VAR by T^K, built without the
/// simplifier so that no absolute values appear - ROOT-ORDER must have
/// accepted E with this K.
fn root_subst(e : Value, var_ : Value, k : Value, tvar : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  if eq(e, var_) {
    mk(q_mexpt, [tvar, k])
  } else if atom(e) {
    e
  } else if mexptp(e).truthy() && eq(cadr(e), var_) {
    let p = caddr(e)
    mk(q_mexpt, [
      tvar,
      if integerp(p) {
        num_mul(k, p)
      } else {
        num_div(num_mul(k, cadr(p)), caddr(p))
      },
    ])
  } else if free(e, var_).truthy() {
    e
  } else {
    cons(list1(caar(e)), mapcar(f => root_subst(f, var_, k, tvar), cdr(e)))
  }
}

///|
/// For E rational in a root of VAR and VAL zeroa or inf, where VAR = T^K is
/// exact, the limit of E through RATLIM; otherwise NIL. An extended real in
/// E is a constant to RATLIM; those stay with SIMPLIMIT.
fn ratlim_in_root(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let k = if limit__memq(val, [q_d_zeroa, q_d_inf]) {
    root_order(exp_, var_)
  } else {
    Nil
  }
  if k.truthy() && num_gt(k, Fix(1L)) && freeof_extended_real(exp_).truthy() {
    let tvar = gensym(prefix="t")
    let e = simplify(root_subst(exp_, var_, k, tvar))
    putprop(tvar, t, q_internal) |> ignore
    if ratp(e, tvar).truthy() {
      with_special(q_var, tvar, () => ratlim(e))
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn limitsimp(exp_ : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_)])
  defer unbind_all(bs)
  limitsimp_expt(sin_sq_cos_sq_sub(exp_), var_)
}

///|
/// if var appears in base and power of expt, push var into power of expt
fn limitsimp_expt(exp_ : Value, var_ : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_)])
  defer unbind_all(bs)
  if atom(exp_) || mnump(exp_).truthy() || freeof(var_, exp_).truthy() {
    exp_
  } else if mexptp(exp_).truthy() &&
    !freeof(var_, cadr(exp_)).truthy() &&
    !freeof(var_, caddr(exp_)).truthy() {
    power_star(q_d__pcte, simplify(mk(q_p_log, [exp_])))
  } else {
    subst0(
      cons(list1(caar(exp_)), mapcar(x => limitsimp_expt(x, var_), cdr(exp_))),
      exp_,
    )
  }
}

///|
fn gather_args_of(e : Value, fn_ : Value, x : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    Nil
  } else if eq(fn_, caar(e)) && !freeof(x, e).truthy() {
    cdr(e)
  } else {
    let parts = mapcar(q => gather_args_of(q, fn_, x), cdr(e))
    // (reduce #'append parts)
    let mut acc : Value = Nil
    let mut started = false
    for p in parts.iter() {
      if started {
        acc = append(acc, p)
      } else {
        acc = p
        started = true
      }
    }
    limit__remove_duplicates_alike(acc)
  }
}

///|
/// Replace every subexpression of e of the form cos(X)^2 + sin(X)^2, where X
/// depends on x, by 1.
fn sin_sq_cos_sq_sub(e : Value, x? : Value) -> Value raise {
  let x = match x {
    Some(v) => v
    None => limit__var()
  }
  if d_mapatom(e).truthy() {
    e
  } else if mplusp(e).truthy() {
    let mut e = e
    let ccc = gather_args_of(e, q_p_cos, x)
    for g in ccc.iter() {
      let z = gensym()
      let mut ee = maxima_substitute(z, power(ftake(q_p_cos, [g]), Fix(2L)), e)
      ee = maxima_substitute(
        sub(Fix(1L), z),
        power(ftake(q_p_sin, [g]), Fix(2L)),
        ee,
      )
      if !freeof(z, ee).truthy() {
        ee = sratsimp(ee)
      }
      if freeof(z, ee).truthy() {
        e = ee
      }
    }
    e
  } else if eq(q_mqapply, caar(e)) {
    // maybe this isn't needed, but it's not wrong.
    subftake(
      caar(second(e)),
      mapcar(q => sin_sq_cos_sq_sub(q, x~), subfunsubs(e)),
      mapcar(q => sin_sq_cos_sq_sub(q, x~), subfunargs(e)),
    )
  } else {
    // map sin-sq-cos-sq-sub over the args
    fapply(caar(e), mapcar(q => sin_sq_cos_sq_sub(q, x~), cdr(e)))
  }
}

///|
fn expand_trigs(x : Value, var_ : Value) -> Value raise {
  let b = bind(q_var, var_)
  defer unbind(b)
  if atom(x) {
    x
  } else if mnump(x).truthy() {
    x
  } else if (eq(caar(x), q_p_sin) || eq(caar(x), q_p_cos)) &&
    !free(cadr(x), var_).truthy() {
    d_trigexpand(x)
  } else if member(q_array, car(x)).truthy() {
    // Some kind of array reference. Return it.
    x
  } else {
    simplify(cons(ncons(caar(x)), mapcar(x => expand_trigs(x, var_), cdr(x))))
  }
}

///|
/// The functionality of tansc has been blended into extra-simp, but tansc is
/// called by the definite integration code and by the limit code.
fn tansc(e : Value) -> Value raise {
  if !involve(
      e,
      list([
        q_p_cot, q_p_csc, q_p_binomial, q_p_sec, q_p_coth, q_p_sech, q_p_csch, q_p_acot,
        q_p_acsc, q_p_asec, q_p_acoth, q_p_asech, q_p_acsch, q_p_jacobi_ns, q_p_jacobi_nc,
        q_p_jacobi_cs, q_p_jacobi_ds, q_p_jacobi_dc,
      ]),
    ).truthy() {
    e
  } else {
    sratsimp(tansc1(e))
  }
}

///|
/// Look up OP in an alist given as pairs of symbols.
fn limit__sym_assoc(op : Value, al : Array[(Value, Value)]) -> Value? {
  for p in al {
    if eq(op, p.0) {
      return Some(p.1)
    }
  }
  None
}

///|
let limit__recip_trig : Array[(Value, Value)] = [
  (q_p_cot, q_p_tan),
  (q_p_coth, q_p_tanh),
  (q_p_sec, q_p_cos),
  (q_p_sech, q_p_cosh),
  (q_p_csc, q_p_sin),
  (q_p_csch, q_p_sinh),
]

///|
let limit__recip_jacobi : Array[(Value, Value)] = [
  (q_p_jacobi_nc, q_p_jacobi_cn),
  (q_p_jacobi_ns, q_p_jacobi_sn),
  (q_p_jacobi_cs, q_p_jacobi_sc),
  (q_p_jacobi_ds, q_p_jacobi_sd),
  (q_p_jacobi_dc, q_p_jacobi_cd),
]

///|
let limit__recip_inverse : Array[(Value, Value)] = [
  (q_p_acsc, q_p_asin),
  (q_p_asec, q_p_acos),
  (q_p_acot, q_p_atan),
  (q_p_acsch, q_p_asinh),
  (q_p_asech, q_p_acosh),
  (q_p_acoth, q_p_atanh),
]

///|
/// Shared body of TANSC1 and the local TANSC1-V of TANSC-VAR; `var1` is the
/// variable tested for the %binomial case and `rec` the recursive function.
fn limit__tansc1_body(
  e : Value,
  var1 : Value,
  rec : (Value) -> Value raise,
) -> Value raise {
  if atom(e) {
    return e
  }
  let e = cons(car(e), mapcar(x => rec(x), cdr(e)))
  let op = caar(e)
  match limit__sym_assoc(op, limit__recip_trig) {
    Some(r) => return rec(power_star(mk(r, [cadr(e)]), Fix(-1L)))
    None => ()
  }
  match limit__sym_assoc(op, limit__recip_jacobi) {
    // Converts Jacobi elliptic function to its reciprocal function.
    Some(r) => return rec(power_star(mk(r, [cadr(e), third(e)]), Fix(-1L)))
    None => ()
  }
  if eq(op, q_p_sinh) || eq(op, q_p_cosh) || eq(op, q_p_tanh) {
    return with_special(q_d_exponentialize, t, () => resimplify(e))
  }
  match limit__sym_assoc(op, limit__recip_inverse) {
    Some(r) => return list2(ncons(r), power(cadr(e), Fix(-1L)))
    None => ()
  }
  if eq(op, q_p_binomial) && among(var1, cdr(e)).truthy() {
    return div_star(
      mk(q_mfactorial, [cadr(e)]),
      mul2_star(
        mk(q_mfactorial, [add2(cadr(e), mul2_star(Fix(-1L), caddr(e)))]),
        mk(q_mfactorial, [caddr(e)]),
      ),
    )
  }
  e
}

///|
fn tansc1(e : Value) -> Value raise {
  limit__tansc1_body(e, limit__var(), x => tansc1(x))
}

///|
/// Like TANSC but dependency on VAR is explicit. Use this instead of TANSC
/// when possible.
fn tansc_var(e : Value, var1 : Value) -> Value raise {
  if !involve_var(
      e,
      var1,
      list([
        q_p_cot, q_p_csc, q_p_binomial, q_p_sec, q_p_coth, q_p_sech, q_p_csch, q_p_acot,
        q_p_acsc, q_p_asec, q_p_acoth, q_p_asech, q_p_acsch, q_p_jacobi_ns, q_p_jacobi_nc,
        q_p_jacobi_cs, q_p_jacobi_ds, q_p_jacobi_dc,
      ]),
    ).truthy() {
    e
  } else {
    sratsimp(limit__tansc1_v(e, var1))
  }
}

///|
/// Copy of TANSC1, but VAR replaced by VAR1.
fn limit__tansc1_v(e : Value, var1 : Value) -> Value raise {
  limit__tansc1_body(e, var1, x => limit__tansc1_v(x, var1))
}

///|
fn hyperex(ex : Value) -> Value raise {
  if !involve(
      ex,
      list([
        q_p_sin, q_p_cos, q_p_tan, q_p_asin, q_p_acos, q_p_atan, q_p_sinh, q_p_cosh, q_p_tanh,
        q_p_asinh, q_p_acosh, q_p_atanh,
      ]),
    ).truthy() {
    ex
  } else {
    hyperex0(ex)
  }
}

///|
fn hyperex0(ex : Value) -> Value raise {
  if atom(ex) {
    ex
  } else if eq(caar(ex), q_p_sinh) {
    div_star(
      add2_star(
        power_star(q_d__pcte, cadr(ex)),
        mul2_star(
          Fix(-1L),
          power_star(q_d__pcte, mul2_star(Fix(-1L), cadr(ex))),
        ),
      ),
      Fix(2L),
    )
  } else if eq(caar(ex), q_p_cosh) {
    div_star(
      add2_star(
        power_star(q_d__pcte, cadr(ex)),
        power_star(q_d__pcte, mul2_star(Fix(-1L), cadr(ex))),
      ),
      Fix(2L),
    )
  } else if limit__memq(caar(ex), [
      q_p_sin, q_p_cos, q_p_tan, q_p_asin, q_p_acos, q_p_atan, q_p_sinh, q_p_cosh, q_p_tanh,
      q_p_asinh, q_p_acosh, q_p_atanh,
    ]) &&
    among(limit__var(), ex).truthy() {
    hyperex1(ex)
  } else {
    cons(car(ex), mapcar(x => hyperex0(x), cdr(ex)))
  }
}

///|
fn hyperex1(ex : Value) -> Value raise {
  resimplify(ex)
}

///|
/// Used by tlimit also.
fn limit1(exp_ : Value, var_ : Value, val : Value) -> Value raise {
  let bs = bind_all([(q_exp, exp_), (q_var, var_), (q_val, val)])
  defer unbind_all(bs)
  let lhprogress_q = symval(q_lhp_q)
  let b2 = bind(q_lhp_q, Nil)
  defer unbind(b2)
  let mut ans = if !atom(exp_) { getlimval(exp_) } else { Nil }
  if ans.truthy() {
    return ans
  }
  if !infinityp(val).truthy() {
    ans = simplimsubst(val, exp_)
    if ans.truthy() {
      return ans
    }
  }
  // NUMDEN* => (values numerator denominator)
  let (n, dn) = numden_star(exp_)
  if !among(var_, dn).truthy() {
    return simplimit(div_star(simplimit(n, var_, val), dn), var_, val)
  } else if !among(var_, n).truthy() {
    return simplimit(
      mul2_star(
        n,
        simplimexpt(dn, Fix(-1L), simplimit(dn, var_, val), Fix(-1L)),
      ),
      var_,
      val,
    )
  } else if lhprogress_q.truthy() &&
    n_sl_hashalike(n, car(lhprogress_q)).truthy() &&
    n_sl_hashalike(dn, cdr(lhprogress_q)).truthy() {
    throw_tag(q_lhospital, Nil) |> ignore
  }
  limit2(n, dn, var_, val)
}

///|
/// If e/f is free of var (a special), return true. This code assumes that f
/// is not zero.
fn n_sl_hashalike(e : Value, f : Value) -> Value raise {
  let a = alike1(e, f)
  if a.truthy() {
    a
  } else {
    freeof(limit__var(), sratsimp(div(e, f)))
  }
}
