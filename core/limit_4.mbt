// Port of src/limit.lisp, part 4: the Gruntz algorithm, EXTRA-SIMP, and the
// top-level forms of limit.lisp (init_limit).
//
// Dominik Gruntz, "On Computing Limits in a Symbolic Manipulation System",
// PhD Dissertation ETH Zurich 1996.
//
// The algorithm identifies the most rapidly varying (MRV) subexpression,
// replaces it with a new variable w, rewrites the expression in terms of the
// new variable, and then repeats. It doesn't handle oscillating functions,
// and it assumes that everything is real.
//
// In this part of limit.lisp, EXP, VAR and VAL are lexical (the Lisp code
// declares them unspecial), except where VAR is explicitly declared special.

///|
/// most rapidly varying subexpression of expression exp with respect to
/// limit variable var. returns a list of subexpressions which are in the same
/// MRV equivalence class.
fn mrv(exp_ : Value, var_ : Value) -> Value raise {
  if freeof(var_, exp_).truthy() {
    Nil
  } else if eq(var_, exp_) {
    list1(var_)
  } else if mtimesp(exp_).truthy() {
    mrv_max(mrv(cadr(exp_), var_), mrv(muln(cddr(exp_), Nil), var_), var_)
  } else if mplusp(exp_).truthy() {
    mrv_max(mrv(cadr(exp_), var_), mrv(addn(cddr(exp_), Nil), var_), var_)
  } else if mexptp(exp_).truthy() {
    if freeof(var_, caddr(exp_)).truthy() {
      mrv(cadr(exp_), var_)
    } else if limit__memq(limitinf(logred(exp_), var_), [q_d_inf, q_d_minf]) {
      mrv_max(list1(exp_), mrv(caddr(exp_), var_), var_)
    } else {
      mrv_max(mrv(cadr(exp_), var_), mrv(caddr(exp_), var_), var_)
    }
  } else if mlogp(exp_).truthy() {
    mrv(cadr(exp_), var_)
  } else if length(cdr(exp_)) == 1 {
    mrv(cadr(exp_), var_)
  } else if length(cdr(exp_)) == 2 {
    mrv_max(mrv(cadr(exp_), var_), mrv(caddr(exp_), var_), var_)
  } else {
    tay_error(Str("mrv not implemented"), exp_)
  }
}

///|
/// takes two lists of expressions, f and g, and limit variable var. members
/// in each list are assumed to be in same MRV equivalence class. returns MRV
/// set of the union of the inputs - either f or g or the union of f and g.
fn mrv_max(f : Value, g : Value, var_ : Value) -> Value raise {
  if f is Nil {
    return g
  } else if g is Nil {
    return f
  } else if intersection(f, g).truthy() {
    return union_(f, g)
  }
  let c = mrv_compare(car(f), car(g), var_)
  if eq(c, q_op_gt) {
    f
  } else if eq(c, q_op_lt) {
    g
  } else if eq(c, q_op_eq) {
    union_(f, g)
  } else {
    merr("MRV-MAX: expected '>' '<' or '='; found: ~M", [c])
  }
}

///|
fn mrv_compare(a : Value, b : Value, var_ : Value) -> Value raise {
  let c = d_limit(
    list([div(ftake(q_p_log, [a]), ftake(q_p_log, [b])), var_, q_d_inf]),
  )
  if eql(c, Fix(0L)) {
    q_op_lt
  } else if limit__memq(c, [q_d_inf, q_d_minf]) {
    q_op_gt
  } else {
    q_op_eq
  }
}

///|
/// CL `stable-sort` of a list.
fn limit__stable_sort(
  l : Value,
  pred : (Value, Value) -> Bool raise,
) -> Value raise {
  let arr = list_to_array(l)
  // insertion sort: stable
  for i in 1..<arr.length() {
    let x = arr[i]
    let mut j = i - 1
    while j >= 0 && pred(x, arr[j]) {
      arr[j + 1] = arr[j]
      j = j - 1
    }
    arr[j + 1] = x
  }
  list(arr)
}

///|
/// rewrite expression exp by replacing members of MRV set omega with
/// expressions in terms of new variable wsym. return cons pair of new version
/// of exp and the log of the new variable wsym.
fn mrv_rewrite(exp_ : Value, omega : Value, var_ : Value, wsym : Value) -> Value raise {
  let mut exp_ = exp_
  let omega = limit__stable_sort(omega, (x, y) => length(mrv(x, var_)) >
    length(mrv(y, var_)))
  let g = car(last(omega))
  let logg = logred(g)
  let sig = equal(mrv_sign(logg, var_), Fix(1L))
  let w = if sig { div_star(Fix(1L), wsym) } else { wsym }
  let logw = if sig { mul2_star(Fix(-1L), logg) } else { logg }
  // rewrite each element of omega
  let rewritten = mapcar(
    f => {
      let logf = logred(f)
      let c = mrv_leadterm(div_star(logf, logg), var_, Nil)
      if !equal(cadr(c), Fix(0L)) {
        // The Gruntz method cannot produce a result for this input. Instead
        // of signaling a fatal error (merror), we perform a non-local exit.
        // This allows the limit code to continue trying other methods.
        throw_tag(q_taylor_catch, Nil) |> ignore
      }
      mul2_star(
        power_star(w, car(c)),
        power_star(q_d__pcte, sub_star(logf, mul2_star(car(c), logg))),
      )
    },
    omega,
  )
  mapcar2(
    (x, y) => {
      exp_ = syntactic_substitute(y, x, exp_)
      exp_
    },
    omega,
    rewritten,
  )
  |> ignore
  cons(exp_, logw)
}

///|
/// if log w(x) = h(x), rewrite all subexpressions of the form log(f(x)) as
/// log(w^-c f(x)) + c h(x) with c the unique constant such that w^-c f(x) is
/// strictly less rapidly varying than w.
fn mrv_rewrite_logs(exp_ : Value, wsym : Value, logw : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if mlogp(exp_).truthy() && !freeof(wsym, exp_).truthy() {
    let f = cadr(exp_)
    let c = funcall(q_d_lopow, [calculate_series(f, wsym), wsym])
    add2_star(
      list2(
        car(exp_),
        mul2_star(
          power_star(wsym, mul2_star(Fix(-1L), c)),
          mrv_rewrite_logs(f, wsym, logw),
        ),
      ),
      mul2_star(c, logw),
    )
  } else {
    cons(car(exp_), mapcar(e => mrv_rewrite_logs(e, wsym, logw), cdr(exp_)))
  }
}

///|
/// returns list of two elements: coeff and exponent of leading term of exp,
/// after rewriting exp in term of its MRV set omega.
fn mrv_leadterm(exp_ : Value, var_ : Value, omega : Value) -> Value raise {
  let mut new_omega : Value = Nil
  if freeof(var_, exp_).truthy() {
    return list2(exp_, Fix(0L))
  }
  for term in omega.iter() {
    if subexp(exp_, term).truthy() {
      new_omega = cons(term, new_omega)
    }
  }
  let mut omega = new_omega
  if omega is Nil {
    omega = mrv(exp_, var_)
  }
  if memq(var_, omega).truthy() {
    let omega_up = mrv_moveup(omega, var_)
    let e_up = car(mrv_moveup(list1(exp_), var_))
    let mrv_leadterm_up = mrv_leadterm(e_up, var_, omega_up)
    return mrv_movedown(mrv_leadterm_up, var_)
  }
  let wsym = gensym(prefix="w")
  let fl = mrv_rewrite(exp_, omega, var_, wsym)
  let f = car(fl)
  let logw = cdr(fl)
  let mut series = calculate_series(mrv_rewrite_logs(f, wsym, logw), wsym)
  series = maxima_substitute(logw, mk(q_p_log, [wsym]), series)
  let lo = funcall(q_d_lopow, [series, wsym])
  if !d_constantp(lo).truthy() || !free(series, q_p_derivative).truthy() {
    tay_error(Str("error in series expansion"), f) |> ignore
  }
  let coef = d_coeff(series, wsym, n=lo)
  if !free(coef, wsym).truthy() {
    tay_error(
      Str("MRV-LEADTERM: failed to extract leading coefficient; obtained"),
      coef,
    )
    |> ignore
  }
  list2(coef, lo)
}

///|
fn mrv_moveup(l : Value, var_ : Value) -> Value raise {
  mapcar(
    exp_ => simplify_log_of_exp(
      syntactic_substitute(mk(q_mexpt, [q_d__pcte, var_]), var_, exp_),
    ),
    l,
  )
}

///|
fn mrv_movedown(l : Value, var_ : Value) -> Value raise {
  mapcar(
    exp_ => syntactic_substitute(mk_simp(q_p_log, [var_]), var_, exp_),
    l,
  )
}

///|
/// test whether sub is a subexpression of exp
fn subexp(exp_ : Value, sub : Value) -> Value raise {
  let dummy = gensym()
  putprop(dummy, t, q_internal) |> ignore
  lbool(!alike1(maxima_substitute(dummy, sub, exp_), exp_).truthy())
}

///|
/// When $domain is $real, substitute the rectangular form for log(+/- %i) in
/// the expression e; when $domain is not $real, return the expression e
/// unchanged.
fn log_simp_plus_or_minus_i(e : Value) -> Value raise {
  if eq(q_d_real, symval(q_d_domain)) {
    maxima_substitute(
      div(mul2(q_d__pcti, q_d__pctpi), Fix(-2L)),
      ftake(q_p_log, [mul2(Fix(-1L), q_d__pcti)]),
      maxima_substitute(
        div(mul2(q_d__pcti, q_d__pctpi), Fix(2L)),
        ftake(q_p_log, [q_d__pcti]),
        e,
      ),
    )
  } else {
    e
  }
}

///|
/// Generate $lhospitallim terms of taylor expansion. Ideally we would use a
/// lazy series representation that generates more terms as higher order
/// terms cancel.
fn calculate_series(exp_ : Value, var_ : Value) -> Value raise {
  let cntx = d_supcontext(Nil)
  // Keep the user-level $TAYLOR_LOGEXPAND out of the Gruntz-internal series
  // arithmetic; same policy and same guard as TLIMIT-TAYLOR.
  let tle = lbool(!has_complex_singular_log_p(exp_, var_, Fix(0L)).truthy())
  let simplifier = lfunc("calculate-series-simplifier", a => sratsimp(
    extra_simp(arg(a, 0)),
  ))
  let was_internal = get(var_, q_internal)
  let bs = bind_all([
    (q_silent_taylor_flag, t),
    (q_d_taylordepth, Fix(8L)),
    (q_d_radexpand, Nil),
    (q_d_logexpand, Nil),
    (q_d_taylor_logexpand, tle),
    (q_d_taylor_simplifier, simplifier),
  ])
  defer unbind_all(bs)
  let r : Result[Value, Error] = try Ok({
    putprop(var_, t, q_internal) |> ignore
    let texp = partial_logarc(exp_, list1(q_p_atan))
    log_simp_plus_or_minus_i(
      catch_tag(q_taylor_catch, () => d_taylor(
        texp,
        list([var_, Fix(0L), symval(q_d_lhospitallim)]),
      )),
    )
  }) catch {
    e => Err(e)
  }
  d_killcontext(list1(cntx)) |> ignore
  if was_internal is Nil {
    remprop(var_, q_internal) |> ignore
  }
  match r {
    Ok(v) => v
    Err(e) => raise e
  }
}

///|
/// Given a Maxima expression e and a variable x, mrv-sign(e,x) returns the
/// sign of e in a neighborhood of real infinity, encoded as -1 for negative,
/// 0 for zero, and 1 for positive.
fn mrv_sign(e : Value, x : Value) -> Value raise {
  let sgn = mrv_sign_helper(e, x)
  if sgn is Nil {
    throw_tag(q_taylor_catch, Nil)
  } else {
    num_max(Fix(-1L), num_min(Fix(1L), sgn))
  }
}

///|
/// Map {$neg, $zero, $pos} --> {-1, 0, 1}. For all other inputs, throw an
/// error to taylor-catch.
fn mrv_sign_to_number(sgn : Value) -> Value raise {
  if eq(sgn, q_d_neg) {
    Fix(-1L)
  } else if eq(sgn, q_d_zero) {
    Fix(0L)
  } else if eq(sgn, q_d_pos) {
    Fix(1L)
  } else {
    // nil for pn, pz, nz, pnz, complex, or imaginary.
    throw_tag(q_taylor_catch, Nil)
  }
}

///|
/// The function mrv-sign-constant returns the mrv-sign of an expression that
/// is free of the variable x. An extended real input throws to taylor-catch.
fn mrv_sign_constant(e : Value) -> Value raise {
  if member(e, symval(q_extended_reals)).truthy() {
    throw_tag(q_taylor_catch, Nil)
  } else {
    mrv_sign_to_number(maybe_asksign(e))
  }
}

///|
/// Return the mrv-sign of e, where e is a sum.
fn mrv_sign_sum(e : Value, x : Value) -> Value raise {
  let mut minfterms : Value = Nil
  let mut infterms : Value = Nil
  let mut negterms : Value = Nil
  let mut posterms : Value = Nil
  let mut failedterms : Value = Nil
  // collect terms with the same value of mrv-sign-helper into lists
  for ek in cdr(e).iter() {
    let ans = mrv_sign_helper(ek, x)
    if eql(Fix(-2L), ans) {
      minfterms = cons(ek, minfterms)
    } else if eql(Fix(-1L), ans) {
      negterms = cons(ek, negterms)
    } else if eql(Fix(1L), ans) {
      posterms = cons(ek, posterms)
    } else if eql(Fix(2L), ans) {
      infterms = cons(ek, infterms)
    } else {
      failedterms = cons(ek, failedterms)
    }
  }
  if failedterms.truthy() {
    // Unable to find the mrv sign of one or more terms; throw an error.
    throw_tag(q_taylor_catch, Nil)
  } else if infterms.truthy() && minfterms is Nil {
    // at least one inf terms, but no minf terms, return 2
    Fix(2L)
  } else if minfterms.truthy() && infterms is Nil {
    // at least one minf terms, but no inf terms, return -2
    Fix(-2L)
  } else if minfterms is Nil && negterms is Nil {
    // no minf terms, no negative terms, return either 1 or 2
    if infterms.truthy() {
      Fix(2L)
    } else {
      Fix(1L)
    }
  } else if infterms is Nil && posterms is Nil {
    // no inf terms, no positive terms, return either -2 or -1
    if minfterms.truthy() {
      Fix(-2L)
    } else {
      Fix(-1L)
    }
  } else if infterms is Nil && minfterms is Nil {
    // no min or inf terms, hope csign can do it
    mrv_sign_to_number(d_csign(e))
  } else {
    // both minf terms and inf terms: do the inf or minf terms dominate?
    let ans = d_limit(
      list([
        div(fapply(q_mplus, infterms), mul2(Fix(-1L), fapply(q_mplus, minfterms))),
        x,
        q_d_inf,
      ]),
    )
    if eq(t, mgrp(ans, Fix(1L))) {
      Fix(2L) // infterms >> |minfterms|, return 2
    } else if eql(ans, Fix(0L)) {
      Fix(-2L) // infterms << |minfterms|, return -2
    } else if eql(ans, Fix(1L)) {
      let a = fapply(q_mplus, append(negterms, append(posterms, infterms)))
      let b = mul2(Fix(-1L), fapply(q_mplus, minfterms))
      let qq = tlimit_taylor(
        sratsimp(sub(div(a, b), Fix(1L))),
        x,
        q_d_inf,
        Fix(0L),
        d=Fix(3L),
      )
      if qq is Nil {
        throw_tag(q_taylor_catch, Nil) |> ignore
      }
      mrv_sign(d_ratdisrep(qq), x)
    } else {
      throw_tag(q_taylor_catch, Nil)
    }
  }
}

///|
/// Return the mrv-sign of the expression e, where e is a product.
fn mrv_sign_product(e : Value, x : Value) -> Value raise {
  let ee = mapcar(q => mrv_sign_helper(q, x), cdr(e))
  if some(q => q is Nil, ee) {
    // unable to find the sign of one term, dispatch csign on e.
    mrv_sign_to_number(d_csign(e))
  } else {
    let mut p : Value = Fix(1L)
    for s in ee.iter() {
      p = num_mul(p, s)
    }
    num_max(Fix(-2L), num_min(Fix(2L), p))
  }
}

///|
/// Return the mrv-sign of the expression e, where the operator of e is log.
/// We examine the mrv sign of both X and 1/X, where the input is log(X).
fn mrv_sign_log(e : Value, x : Value) -> Value raise {
  let ee = cadr(e)
  if eql(Fix(2L), mrv_sign_helper(ee, x)) {
    Fix(2L) // log(inf) = inf
  } else if eq(t, mgrp(ee, Fix(1L))) {
    Fix(1L) // log(>1) = pos
  } else if eql(Fix(2L), mrv_sign_helper(div(Fix(1L), ee), x)) {
    Fix(-2L) // log(zeroa) = minf
  } else if eq(t, mgrp(ee, Fix(0L))) && eq(t, mgrp(Fix(1L), ee)) {
    Fix(-1L) // log(0< & < 1) = neg
  } else {
    throw_tag(q_taylor_catch, Nil)
  }
}

///|
/// Return the mrv sign of the expression e, where e = X^Y. For the mrv sign
/// of an expression to be zero, it needs to be zero in a neighborhood of
/// infinity.
fn mrv_sign_mexpt(e : Value, x : Value) -> Value raise {
  let a = mrv_sign_helper(cadr(e), x)
  let b = mrv_sign_helper(caddr(e), x)
  if eql(a, Fix(1L)) && eql(b, Fix(-2L)) {
    Fix(1L) // pos^minf = pos
  } else if eql(a, Fix(1L)) && eql(b, Fix(2L)) && eq(t, mgrp(cadr(e), Fix(1L))) {
    Fix(2L) // {> 1}^inf = inf
  } else if eql(a, Fix(1L)) &&
    (eql(b, Fix(-1L)) || eql(b, Fix(1L)) || eql(b, Fix(2L))) {
    Fix(1L) // pos^{neg, pos} = pos
  } else if eql(a, Fix(2L)) && (eql(b, Fix(1L)) || eql(b, Fix(2L))) {
    Fix(2L) // inf^pos = inf & inf^inf = inf
  } else if eql(a, Fix(2L)) && (eql(b, Fix(-1L)) || eql(b, Fix(0L))) {
    Fix(1L) // inf^{neg, zero} = pos
  } else if eql(a, Fix(2L)) && eql(b, Fix(-2L)) {
    Fix(1L) // inf^minf = 1
  } else if eql(a, Fix(0L)) && (eql(b, Fix(1L)) || eql(b, Fix(2L))) {
    Fix(0L) // zero^{pos,inf} = 0
  } else {
    // For all other cases, let's dispatch csign or asksign
    mrv_sign_to_number(maybe_asksign(e))
  }
}

///|
fn atanp(e : Value) -> Value raise {
  lbool(consp(e) && eq(q_p_atan, caar(e)))
}

///|
/// Return the mrv-sign of the expression e, where e = atan(X).
fn mrv_sign_atan(e : Value, x : Value) -> Value raise {
  let sgn = mrv_sign_helper(cadr(e), x)
  if eql(Fix(-2L), sgn) || eql(Fix(-1L), sgn) {
    Fix(-1L) // atan(< 0) = -1
  } else if eql(Fix(2L), sgn) || eql(Fix(1L), sgn) {
    Fix(1L) // atan(> 0) = 1
  } else {
    throw_tag(q_taylor_catch, Nil)
  }
}

///|
fn mrv_sign_sin(e : Value, x : Value) -> Value raise {
  let sgn = mrv_sign_helper(div(Fix(1L), cadr(e)), x)
  if eql(sgn, Fix(2L)) {
    Fix(1L) // sin(zeroa) = 1
  } else if eql(sgn, Fix(-2L)) {
    Fix(-1L) // sin(zerob) = -1
  } else {
    throw_tag(q_taylor_catch, Nil)
  }
}

///|
/// Return the extended mrv sign of an expression: 2 for an expression that
/// is not bounded above in a neighborhood of infinity and -2 for one that is
/// not bounded below.
fn mrv_sign_helper(e : Value, x : Value) -> Value raise {
  if freeof(x, e).truthy() {
    mrv_sign_constant(e)
  } else if eq(e, x) {
    Fix(2L)
  } else if mtimesp(e).truthy() {
    mrv_sign_product(e, x)
  } else if mplusp(e).truthy() {
    mrv_sign_sum(e, x)
  } else if mexptp(e).truthy() {
    mrv_sign_mexpt(e, x)
  } else if mlogp(e).truthy() {
    mrv_sign_log(e, x)
  } else if atanp(e).truthy() {
    mrv_sign_atan(e, x)
  } else if sinp(e).truthy() {
    mrv_sign_sin(e, x)
  } else {
    // If the expression doesn't match any of the above, throw an error.
    throw_tag(q_taylor_catch, Nil)
  }
}

///|
/// gruntz algorithm for limit of exp as var goes to positive infinity
fn limitinf(exp_ : Value, var_ : Value) -> Value raise {
  let b = bind(q_d_exptsubst, Nil)
  defer unbind(b)
  if freeof(var_, exp_).truthy() {
    return exp_
  }
  let c0_e0 = mrv_leadterm(exp_, var_, Nil)
  let c0 = car(c0_e0)
  let e0 = cadr(c0_e0)
  let sig = mrv_sign(e0, var_)
  if equal(sig, Fix(1L)) {
    Fix(0L)
  } else if equal(sig, Fix(-1L)) {
    if equal(mrv_sign(c0, var_), Fix(1L)) {
      q_d_inf
    } else if equal(mrv_sign(c0, var_), Fix(-1L)) {
      q_d_minf
    } else {
      Nil
    }
  } else if equal(sig, Fix(0L)) {
    if equal(exp_, c0) {
      // example: gruntz(n^n/(n^n+(n-1)^n), n, inf);
      tay_error(Str(" infinite recursion in limitinf"), exp_) |> ignore
    }
    limitinf(c0, var_)
  } else {
    Nil
  }
}

///|
/// user-level function equivalent to $limit. direction must be specified if
/// limit point is not infinite. The arguments are checked and a failure of
/// taylor is caught.
fn d_gruntz(expr : Value, var_ : Value, val : Value, rest_ : Value) -> Value raise {
  if length(rest_) > 1 {
    merr("gruntz: too many arguments; expected just 3 or 4", []) |> ignore
  }
  let dir = car(rest_)
  let val = canonicalize_plus_inf(val)
  if !limit__memq(val, [q_d_inf, q_d_minf, q_d_zeroa, q_d_zerob]) &&
    !limit__memq(dir, [q_d_plus, q_d_minus]) {
    merr("gruntz: direction must be 'plus' or 'minus'", []) |> ignore
  }
  let ans = catch_tag(q_taylor_catch, () => with_special(
    q_silent_taylor_flag,
    t,
    () => gruntz1(expr, var_, val, list1(dir)),
  ))
  if ans is Nil || eq(ans, t) {
    if dir.truthy() {
      cons(list2(q_d_gruntz, q_simp), list([expr, var_, val, dir]))
    } else {
      cons(list2(q_d_gruntz, q_simp), list([expr, var_, val]))
    }
  } else {
    ans
  }
}

///|
/// Additional simplifications for the limit function. Specifically:
///   (a) replace every mapatom that is declared to be zero by zero
///   (b) dispatch radcan on expressions of the form (positive integer)^XXX
///   (c) log(negative number) --> log(-negative number) + %i*%pi
///   (d) apply cos(X)^2 + sin(X)^2 --> 1, when X depends on var
///   (e) convert, gamma functions, binomial coefficients, and beta functions
///       to factorial form
///   (f) do some reciprocial function transformations; for example
///       csc(X) --> 1/sin(X)
///   (g) do transformations similar to acsc(X) --> asin(1/X).
///   (h) convert fibonacci functions to power form.
/// VAR is read from the special variable.
fn extra_simp(e : Value) -> Value raise {
  let var_ = symval(q_var)
  let var_present = !freeof(var_, e).truthy()
  if extended_real_p(e).truthy() {
    // we don't want to call sign on ind, so catch this
    e
  } else if d_mapatom(e).truthy() {
    // if e is declared zero, return 0; otherwise e
    if eq(q_d_zero, d_csign(e)) {
      Fix(0L)
    } else {
      e
    }
  } else if mexptp(e).truthy() && integerp(cadr(e)) && num_gt(cadr(e), Fix(0L)) {
    // dispatch radcan on (positive integer)^Y
    d_radcan(ftake(q_mexpt, [cadr(e), extra_simp(caddr(e))]))
  } else if eq(q_p_log, caar(e)) &&
    d_numberp(cadr(e)).truthy() &&
    eq(t, mgrp(Fix(0L), cadr(e))) {
    // log(negative number) --> log(-negative number) + %i*%pi. This is needed
    // for a nice result for integrate(x^3/(exp(x)-1),x,0,inf), for example.
    add2(
      ftake(q_p_log, [mul2(Fix(-1L), cadr(e))]),
      mul2(q_d__pcti, q_d__pctpi),
    )
  } else if var_present && mplusp(e).truthy() {
    // When e isn't freeof var and e is a sum, map extra-simp over the
    // summands, add the results, and apply sin-sq-cos-sq-sub.
    sin_sq_cos_sq_sub(
      fapply(q_mplus, mapcar(x => extra_simp(x), cdr(e))),
      x=var_,
    )
  } else if var_present && eq(q_p_gamma, caar(e)) {
    // Convert gamma functions to factorials.
    ftake(q_mfactorial, [extra_simp(sub(cadr(e), Fix(1L)))])
  } else if var_present &&
    limit__memq(caar(e), [
      q_p_sinh, q_p_cosh, q_p_tanh, q_p_sech, q_p_csch, q_p_coth,
    ]) {
    // Exponentialize the hyperbolic functions.
    extra_simp(d_exponentialize(e))
  } else if var_present &&
    limit__memq(caar(e), [
      q_p_sec, q_p_csc, q_p_cot, q_p_jacobi_nc, q_p_jacobi_ns, q_p_jacobi_cs, q_p_jacobi_ds,
      q_p_jacobi_dc,
    ]) {
    // When X depends on var, apply reciprocal function identities such as
    // csc(X) --> 1/sin(X).
    div(
      Fix(1L),
      fapply(get(caar(e), q_recip), mapcar(x => extra_simp(x), cdr(e))),
    )
  } else if var_present && limit__memq(caar(e), [q_p_binomial, q_p_beta]) {
    // When X or Y depends on var, convert binomial(X,Y) to factorial form.
    // Same for beta(x,y).
    extra_simp(d_makefact(e))
  } else if var_present &&
    limit__memq(caar(e), [
      q_p_acsc, q_p_asec, q_p_acot, q_p_acsch, q_p_asech, q_p_acoth,
    ]) {
    // When X depends on var, do acsc(X) --> asin(1/X). Do the same for asec,
    // acot, acsch, asech, and acoth.
    ftake(get(get(get(caar(e), q_d_inverse), q_recip), q_d_inverse), [
      div(Fix(1L), extra_simp(cadr(e))),
    ])
  } else if var_present && eq(q_d_fib, caar(e)) {
    // When X depends on var, convert fib(X) to its power form.
    extra_simp(d_fibtophi(e))
  } else if var_present && eq(q_p_log_gamma, caar(e)) {
    // convert log_gamma(X) to log(gamma(X))
    extra_simp(ftake(q_p_log, [ftake(q_p_gamma, [cadr(e)])]))
  } else if var_present && eq(caar(e), q_p_expintegral_e) {
    // convert expintegral_e to an incomplete gamma expression
    let p = extra_simp(cadr(e))
    let arg = extra_simp(caddr(e))
    mul2(
      ftake(q_mexpt, [arg, sub(p, Fix(1L))]),
      ftake(q_p_gamma_incomplete, [sub(Fix(1L), p), arg]),
    )
  } else if d_subvarp(mop(e)).truthy() {
    // subscripted function
    subfunmake(
      subfunname(e),
      mapcar(x => extra_simp(x), subfunsubs(e)),
      mapcar(x => extra_simp(x), subfunargs(e)),
    )
  } else {
    fapply(caar(e), mapcar(x => extra_simp(x), cdr(e)))
  }
}

///|
/// Call extra-simp followed by a call to resimplify. This is analogous to
/// sratsimp.
fn resimp_extra_simp(e : Value) -> Value raise {
  resimplify(extra_simp(e))
}

///|
/// This function is for internal use in $limit. It standardizes the limit
/// point to inf and the limit variable to a gensym. Since the limit point is
/// possibly altered by this function, we need to make the appropriate
/// assumptions on the limit variable. This is done in a supcontext.
fn gruntz1(exp_ : Value, var_ : Value, val : Value, rest_ : Value) -> Value raise {
  if length(rest_) > 1 {
    merr("gruntz: too many arguments; expected just 3 or 4", []) |> ignore
  }
  let b = bind(q_d_logexpand, t) // gruntz needs $logexpand T
  defer unbind(b)
  let newvar_ = gensym(prefix="w")
  let dir = car(rest_)
  putprop(newvar_, t, q_internal) |> ignore // keep var from appearing in questions to user
  let mut exp_ = if eq(val, q_d_inf) {
    maxima_substitute(newvar_, var_, exp_)
  } else if eq(val, q_d_minf) {
    maxima_substitute(mul2_star(Fix(-1L), newvar_), var_, exp_)
  } else if eq(val, q_d_zeroa) {
    maxima_substitute(div_star(Fix(1L), newvar_), var_, exp_)
  } else if eq(val, q_d_zerob) {
    maxima_substitute(div_star(Fix(-1L), newvar_), var_, exp_)
  } else if eq(dir, q_d_plus) {
    maxima_substitute(
      add2_star(val, div_star(Fix(1L), newvar_)),
      var_,
      exp_,
    )
  } else if eq(dir, q_d_minus) {
    maxima_substitute(
      add2_star(val, div_star(Fix(-1L), newvar_)),
      var_,
      exp_,
    )
  } else {
    merr("gruntz: direction must be 'plus' or 'minus'; found: ~M", [dir])
  }
  let cx = d_supcontext(Nil)
  let r : Result[Value, Error] = try Ok({
    // *large-positive-number* < newvar
    mfuncall(
      q_d_assume,
      list1(ftake(q_mlessp, [symval(q_ear_large_positive_number), newvar_])),
    )
    |> ignore
    // *large-positive-number* < prin-inf
    mfuncall(
      q_d_assume,
      list1(ftake(q_mlessp, [symval(q_ear_large_positive_number), q_prin_inf])),
    )
    |> ignore
    d_activate(list1(cx)) |> ignore // not sure this is needed, but OK
    exp_ = resimplify(exp_) // simplify in new context
    // Additional simplifications. EXTRA-SIMP reads the limit variable from
    // the special VAR.
    let e0 = exp_
    exp_ = with_special(q_var, newvar_, () => resimp_extra_simp(sratsimp(e0)))
    limitinf(exp_, newvar_) // compute & return limit
  }) catch {
    e => Err(e)
  }
  d_killcontext(list1(cx)) |> ignore // kill context & forget all new facts.
  match r {
    Ok(v) => v
    Err(e) => raise e
  }
}

///|
/// substitute y for x in exp, similar to maxima-substitute but does not
/// simplify result
fn syntactic_substitute(y : Value, x : Value, exp_ : Value) -> Value raise {
  if alike1(x, exp_).truthy() {
    y
  } else if atom(exp_) {
    exp_
  } else {
    cons(car(exp_), mapcar(e => syntactic_substitute(y, x, e), cdr(exp_)))
  }
}

///|
/// log(exp(subexpr)) -> subexpr, without simplifying entire exp
fn simplify_log_of_exp(exp_ : Value) -> Value raise {
  if atom(exp_) {
    exp_
  } else if mlogp(exp_).truthy() &&
    mexptp(cadr(exp_)).truthy() &&
    eq(q_d__pcte, cadadr(exp_)) {
    caddr(cadr(exp_))
  } else {
    cons(car(exp_), mapcar(x => simplify_log_of_exp(x), cdr(exp_)))
  }
}

///|
fn init_limit() -> Unit raise {
  defvar_init(q_simplimplus_problems, Nil)
  defvar_init(q_limit_answers, Nil)
  defvar_init(q_limit_using_taylor, Nil)
  // Don't ask sign questions about $ind.
  putprop(q_d_ind, t, q_internal) |> ignore
  putprop(q_mabs, q_simplim_pctmabs, q_simplim_pctfunction) |> ignore
  set(q_low_star, Nil) |> ignore
  putprop(q_p_log, q_simplimln, q_simplim_pctfunction) |> ignore
  putprop(q_p_plog, q_simplimln, q_simplim_pctfunction) |> ignore
  putprop(q_p_limit, q_simplim_pctlimit, q_simplim_pctfunction) |> ignore
  putprop(q_d_unit_step, q_simplim_pctunit_step, q_simplim_pctfunction)
  |> ignore
  putprop(q_d_conjugate, q_simplim_pctconjugate, q_simplim_pctfunction)
  |> ignore
  putprop(q_d_imagpart, q_simplim_pctimagpart, q_simplim_pctfunction) |> ignore
  putprop(q_p_imagpart, q_simplim_pctimagpart, q_simplim_pctfunction) |> ignore
  putprop(q_d_realpart, q_simplim_pctrealpart, q_simplim_pctfunction) |> ignore
  putprop(q_p_realpart, q_simplim_pctrealpart, q_simplim_pctfunction) |> ignore
  putprop(q_mfactorial, q_simplimfact, q_simplim_pctfunction) |> ignore
  putprop(q_p_atan, q_simplim_pctatan, q_simplim_pctfunction) |> ignore
  defvar_init(
    q_extended_reals,
    append(
      symval(q_ear_infinitesimals),
      append(symval(q_ear_infinities), list([q_d_und, q_d_ind])),
    ),
  )
  putprop(q_p_atan2, q_simplim_pctatan2, q_simplim_pctfunction) |> ignore
  putprop(q_p_tan, q_simplim_pcttan, q_simplim_pctfunction) |> ignore
  putprop(q_p_asinh, q_simplim_pctasinh, q_simplim_pctfunction) |> ignore
  putprop(q_p_acosh, q_simplim_pctacosh, q_simplim_pctfunction) |> ignore
  putprop(q_p_atanh, q_simplim_pctatanh, q_simplim_pctfunction) |> ignore
  putprop(q_p_asin, q_simplim_pctasin, q_simplim_pctfunction) |> ignore
  putprop(q_p_acos, q_simplim_pctacos, q_simplim_pctfunction) |> ignore
  putprop(q_p_integrate, q_simplim_pctintegrate, q_simplim_pctfunction)
  |> ignore
  putprop(q_d_li, q_simplim_pctli, q_simplim_pctfunction) |> ignore
  putprop(q_p_li, q_simplim_pctli, q_simplim_pctfunction) |> ignore
  putprop(q_p_signum, q_simplim_pctsignum, q_simplim_pctfunction) |> ignore
  // This should be moved to the jacobi function code. And likely, we should
  // set the reciprocal property for the other jacobi functions.
  for q in limit__recip_jacobi {
    setf_get(q.0, q_recip, q.1) |> ignore
  }
}
