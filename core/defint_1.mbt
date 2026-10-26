// Port of src/defint.lisp (part 1): the definite integration package.
//
// defint does definite integration by trying to find an appropriate
// method for the integral in question.  The first thing that is looked
// at is the endpoints of the problem.
//
// References are to "Evaluation of Definite Integrals by Symbolic
// Manipulation", by Paul S. Wang.
//
// $defint is the top level function that takes the user input and does
// minor changes to make the integrand ready for the package.
//
// Next comes defint, which is the function that does the integration.
// It is often called recursively from the bowels of the package.  defint
// does some of the easy cases and dispatches to dintegrate, which first
// sees if the limits of integration are 0,inf or minf,inf (ztoinf,
// mtoinf); else it tries intsc1, ratfnt, zto1, dintrad, dintlog,
// dintexp, indefinite integration, term-by-term integration and changes
// of variable.
//
// NOTE: defint.lisp proclaims EXP special, so every Lisp parameter or
// LET variable named EXP is a dynamic binding of the special EXP (see
// ORDER-LIMITS, which negates the integrand by setting EXP).  Such
// functions bind `q_exp` and read it through `defint__exp()`.

///|
/// Current value of the special EXP.
fn defint__exp() -> Value {
  symval(q_exp)
}

///|
/// CL `unwind-protect`.
fn defint__up(body : () -> Value raise, cleanup : () -> Unit raise) -> Value raise {
  let v = body() catch {
    e => {
      cleanup()
      raise e
    }
  }
  cleanup()
  v
}

///|
/// `(andmapcar f l)`
fn defint__andmapcar(f : (Value) -> Value raise, l : Value) -> Value raise {
  let c = Collector::new()
  for x in l.iter() {
    let d = f(x)
    if d is Nil {
      return Nil
    }
    c.add(d)
  }
  c.result()
}

///|
/// The literal `((rat) n d)`.
fn defint__rat(n : Int64, d : Int64) -> Value {
  mk(q_rat, [Fix(n), Fix(d)])
}

///|
/// `(m- x)` = `(mul* -1 x)`
fn defint__mneg(x : Value) -> Value raise {
  mul2_star(Fix(-1L), x)
}

///|
/// `(with-default-quotient-dispflags body)`
fn[T] defint__dqd(f : () -> T raise) -> T raise {
  with_specials(
    [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
    f,
  )
}

///|
/// `(catch 'divergent ...)`
fn defint__catch_divergent(f : () -> Value raise) -> Value raise {
  catch_tag(q_divergent, f)
}

///|
/// `(catch 'pin%ex (pin%ex e ivar))`
fn defint__catch_pin(e : Value, ivar : Value) -> Value raise {
  catch_tag(q_pin_pctex, fn() { pin_pctex(e, ivar) })
}

///|
/// `(member x '(a b ...))` for symbols.
fn defint__memq(x : Value, syms : Array[Value]) -> Bool {
  for s in syms {
    if eq(x, s) {
      return true
    }
  }
  false
}

///|
fn d_defint(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  // Distribute $defint over equations, lists, and matrices.
  if mbagp(defint__exp()).truthy() {
    let e = defint__exp()
    return simplify(
      cons(car(e), mapcar(x => simplify(d_defint(x, ivar, ll, ul)), cdr(e))),
    )
  }
  let bs = bind_all([
    (q_ear_global_defint_assumptions, Nil),
    (q_ear_integer_info, Nil),
    (q_integerl, symval(q_integerl)),
    (q_nonintegerl, symval(q_nonintegerl)),
  ])
  defer unbind_all(bs)
  // (with-new-context (context) ...)
  let my_context = gensym(prefix="$ctxt")
  mfuncall(q_d_supcontext, list2(my_context, symval(q_context))) |> ignore
  defint__up(
    fn() {
      defint__up(fn() { defint__defint_top(ivar, ll, ul) }, fn() {
        forget_global_assumptions() |> ignore
      })
    },
    fn() { d_killcontext(list1(my_context)) |> ignore },
  )
}

///|
/// The inner LET of $DEFINT.
fn defint__defint_top(ivar0 : Value, ll0 : Value, ul0 : Value) -> Value raise {
  let mut ivar = ivar0
  let mut ll = ll0
  let mut ul = ul0
  let bs = bind_all([
    (q_ear_defint_assumptions, Nil),
    (q_ear_rad_poly_recur, Nil),
    (q_ear_sin_cos_recur, Nil),
    (q_ear_dintexp_recur, Nil),
    (q_ear_dintlog_recur, Fix(0L)),
    (q_ear_pcprntd, Nil),
    (q_ear_nodiverg, Nil),
    (q_d_logabs, Nil),
    (q_rp_polylogp, Nil),
    (q_d__pctedispflag, Nil),
    (q_d_m1pbranch, Nil),
  ])
  defer unbind_all(bs)
  let orig_exp = defint__exp()
  let orig_var = ivar
  let orig_ll = ll
  let orig_ul = ul
  make_global_assumptions() |> ignore // sets *global-defint-assumptions*
  set(q_exp, ratdisrep(defint__exp())) |> ignore
  ivar = ratdisrep(ivar)
  ll = ratdisrep(ll)
  ul = ratdisrep(ul)
  if d_constantp(ivar).truthy() {
    merr(
      "defint: variable of integration cannot be a constant; found ~M",
      [ivar],
    )
    |> ignore
  } else if d_subvarp(ivar).truthy() {
    ivar = gensym()
    set(q_exp, d_substitute(ivar, orig_var, expr=defint__exp())) |> ignore
  }
  if !atom(ivar) {
    merr(
      "defint: variable of integration must be a simple or subscripted variable.~%defint: found ~M",
      [ivar],
    )
    |> ignore
  } else if among(ivar, ul).truthy() || among(ivar, ll).truthy() {
    ivar = gensym()
    set(q_exp, d_substitute(ivar, orig_var, expr=defint__exp())) |> ignore
  }
  if !lenient_extended_realp(ll).truthy() {
    merr("defint: lower limit of integration must be real; found ~M", [ll])
    |> ignore
  }
  if !lenient_extended_realp(ul).truthy() {
    merr("defint: upper limit of integration must be real; found ~M", [ul])
    |> ignore
  }
  let ans = defint(defint__exp(), ivar, ll, ul)
  if ans.truthy() {
    let ans = subst(orig_var, ivar, ans)
    if atom(ans) {
      ans
    } else if free(ans, q_p_limit).truthy() &&
      free(ans, q_p_integrate).truthy() &&
      (
        !free(ans, q_d_inf).truthy() ||
        !free(ans, q_d_minf).truthy() ||
        !free(ans, q_d_infinity).truthy()
      ) {
      diverg()
    } else if !free(ans, q_d_und).truthy() {
      mk(q_p_integrate, [orig_exp, orig_var, orig_ll, orig_ul])
    } else {
      ans
    }
  } else {
    mk(q_p_integrate, [orig_exp, orig_var, orig_ll, orig_ul])
  }
}

///|
fn eezz(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if polyinx(defint__exp(), ivar, Nil).truthy() ||
    defint__catch_pin(defint__exp(), ivar).truthy() {
    set(q_exp, antideriv(defint__exp(), ivar)) |> ignore
    // If antideriv can't do it, returns nil; use limit to evaluate
    // every answer returned by antideriv.
    if defint__exp() is Nil {
      Nil
    } else {
      intsubs(defint__exp(), ll, ul, ivar)
    }
  } else {
    Nil
  }
}

///|
/// Hack the expression up for exponentials.  Is this expr a candidate
/// for SININT ?
fn sinintp(expr : Value, ivar : Value) -> Value raise {
  // limitp is bound to prevent questions from being asked about IVAR.
  let b0 = bind(q_limitp, Nil)
  defer unbind(b0)
  let expr = factor(expr)
  let (numer, denom) = defint__dqd(fn() { num_denom_split(expr) })
  if polyinx(numer, ivar, Nil).truthy() {
    if polyinx(denom, ivar, Nil).truthy() &&
      deg_lessp(denom, ivar, Fix(2L)).truthy() {
      t
    } else {
      Nil
    }
  } else {
    // ERF type things go here.
    let exponent = p_einvolve_var(numer, ivar)
    if polyinx(exponent, ivar, Nil).truthy() &&
      deg_lessp(exponent, ivar, Fix(2L)).truthy() {
      if free(denom, ivar).truthy() {
        t
      } else {
        Nil
      }
    } else {
      Nil
    }
  }
}

///|
fn deg_lessp(expr : Value, ivar : Value, power : Value) -> Value raise {
  if atom(expr) || mnump(expr).truthy() {
    t
  } else if mtimesp(expr).truthy() || mplusp(expr).truthy() {
    for op in cdr(expr).iter() {
      if !deg_lessp(op, ivar, power).truthy() {
        return Nil
      }
    }
    t
  } else if mexptp(expr).truthy() {
    if !alike1(cadr(expr), ivar).truthy() ||
      (
        numberp(caddr(expr)) &&
        !eq(asksign(add2_star(power, defint__mneg(caddr(expr)))), q_d_negative)
      ) {
      deg_lessp(cadr(expr), ivar, power)
    } else {
      Nil
    }
  } else if consp(expr) &&
    memq(q_array, car(expr)).truthy() &&
    !eq(ivar, caar(expr)) {
    // We have some subscripted variable that's not our variable (I
    // think), so it's deg-lessp.
    t
  } else {
    Nil
  }
}

///|
/// Either return an explicit antiderivative (not an integral nounform) of
/// 'a' with respect to 'ivar' or return nil when Maxima is unable to find
/// an antiderivative.
fn antideriv(a : Value, ivar : Value) -> Value raise {
  // setting limitp to true causes testsuite failures and asksign called
  // on gensyms
  let bs = bind_all([(q_limitp, Nil), (q_d_numer, Nil), (q_d_logabs, Nil)])
  defer unbind_all(bs)
  let ans = sinint(a, ivar)
  if among(q_p_integrate, ans).truthy() {
    Nil
  } else {
    ans
  }
}

///|
/// This routine tries to take a limit a couple of ways.
fn get_limit(exp_ : Value, ivar : Value, val : Value, dir? : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let mut ans = match dir {
    Some(d) => limit_no_err(list([defint__exp(), ivar, val, d]))
    None => limit_no_err(list([defint__exp(), ivar, val]))
  }
  if ans.truthy() && !among(q_p_limit, ans).truthy() {
    ans
  } else if defint__memq(val, [q_d_inf, q_d_minf]) {
    ans = limit_no_err(
      list([
        maxima_substitute(power(ivar, Fix(-1L)), ivar, defint__exp()),
        ivar,
        Fix(0L),
        if eq(val, q_d_inf) {
          q_d_plus
        } else {
          q_d_minus
        },
      ]),
    )
    if among(q_p_limit, ans).truthy() {
      Nil
    } else {
      ans
    }
  } else {
    Nil
  }
}

///|
fn limit_no_err(argvec : Value) -> Value raise {
  let b0 = bind(q_errorsw, t)
  defer unbind(b0)
  let ans = catch_tag(q_errorsw, fn() { d_limit(argvec) })
  if eq(ans, t) {
    Nil
  } else {
    ans
  }
}

///|
/// Test whether fun2 is inverse of fun1 at val.
fn test_inverse(
  fun1 : Value,
  var1 : Value,
  fun2 : Value,
  var2 : Value,
  val : Value,
) -> Value raise {
  let out1 = no_err_sub_var(val, fun1, var1)
  let out2 = no_err_sub_var(out1, fun2, var2)
  alike1(val, out2)
}

///|
/// Given ROOT = ((yx-a)/b)^(1/n), one root of yx = b*x^n+a, return a root
/// of that equation that is usable for the change of variable on the
/// integration interval [ll, ul]: a root that actually inverts NV on the
/// whole interval (for even N, -ROOT is a root as well), or, when no
/// single branch does, ROOT itself if INTCV2 may halve the symmetric
/// interval and double - which is valid only if the integrand (EXP) is
/// an even function, too. Otherwise, return NIL.
fn intcv_root(
  nv : Value,
  ivar : Value,
  root : Value,
  n : Value,
  ll : Value,
  ul : Value,
) -> Value raise {
  // R (an expression in 'YX) must invert NV at both finite endpoints of
  // the integration interval.
  let inversep = fn(r : Value) -> Bool raise {
    (
      real_infinityp(ll).truthy() ||
      test_inverse(nv, ivar, r, q_yx, ll).truthy()
    ) &&
    (
      real_infinityp(ul).truthy() ||
      test_inverse(nv, ivar, r, q_yx, ul).truthy()
    )
  }
  if inversep(root) {
    root
  } else if integerp(n) && evenp(n) && inversep(neg(root)) {
    neg(root)
  } else if zerop1(add2_star(ll, ul)).truthy() &&
    evenfn(nv, ivar).truthy() &&
    evenfn(defint__exp(), ivar).truthy() {
    // The doubling case: This must use the + branch. With -ROOT, the
    // transformed integrand changes sign, while the halved limits of
    // integration stay the same.
    root
  } else {
    Nil
  }
}

///|
/// Return T if E contains a radical in VAR, a power of an expression in
/// VAR to a non-integer rational exponent, whose base contains another
/// such radical.
fn nested_radical_p(e : Value, var_ : Value) -> Value raise {
  let radical_p = fn(e : Value) -> Bool raise {
    mexptp(e).truthy() &&
    ratnump(caddr(e)).truthy() &&
    among(var_, cadr(e)).truthy()
  }
  fn has_radical_p(e : Value) -> Bool raise {
    consp(e) &&
    consp(car(e)) &&
    (radical_p(e) || some(x => has_radical_p(x), cdr(e)))
  }
  fn nested_p(e : Value) -> Bool raise {
    consp(e) &&
    consp(car(e)) &&
    (
      (radical_p(e) && has_radical_p(cadr(e))) ||
      some(x => nested_p(x), cdr(e))
    )
  }
  lbool(nested_p(e))
}

///|
/// integration change of variable
///
/// With SKIP-NESTED, roots with nested radicals in 'YX, which the cubic
/// and quartic formulas give, are not used.
fn intcv(
  nv : Value,
  flag : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
  skip_nested? : Value = Nil,
) -> Value raise {
  let mut d = bx_star_starn_plusa(nv, ivar)
  let bs = bind_all([
    (q_n_starroots, Nil),
    (q_n_starfailures, Nil),
    (q_d_breakup, Nil),
  ])
  defer unbind_all(bs)
  if eq(ul, q_d_inf) && equal(ll, Fix(0L)) && equal(cadr(d), Fix(1L)) {
    Nil
  } else if eq(ivar, q_yx) {
    // new ivar cannot be same as old ivar
    Nil
  } else if d.truthy() {
    // This is a hack!  If nv is of the form b*x^n+a, we can solve the
    // equation manually instead of using solve.  Why?  Because solve
    // asks us for the sign of yx and that's bogus.
    //
    // Solve yx = b*x^n+a, for x. This gives one root,
    // x = ((yx-a)/b)^(1/n); INTCV-ROOT picks a usable root, if any.
    let a = car(d)
    let n = cadr(d)
    let b = caddr(d)
    let root = power_star(div(sub(q_yx, a), b), inv(n))
    d = intcv_root(nv, ivar, root, n, ll, ul)
    if d.truthy() {
      if flag.truthy() {
        intcv2(d, nv, ivar, ll, ul)
      } else {
        intcv1(d, nv, ivar, ll, ul)
      }
    } else {
      Nil
    }
  } else {
    // keep ivar from appearing in questions to user
    putprop(q_yx, t, q_internal) |> ignore
    solve(
      add2(q_yx, mul2(Fix(-1L), nv)),
      ivar,
      Fix(1L),
    )
    |> ignore
    // look for root that is inverse of nv
    d = Nil
    let mut roots = symval(q_n_starroots)
    while true {
      let root = caddr(car(roots))
      if root is Nil {
        break
      }
      if !(skip_nested.truthy() && nested_radical_p(root, q_yx).truthy()) &&
        (
          real_infinityp(ll).truthy() ||
          test_inverse(nv, ivar, root, q_yx, ll).truthy()
        ) &&
        (
          real_infinityp(ul).truthy() ||
          test_inverse(nv, ivar, root, q_yx, ul).truthy()
        ) {
        d = root
        break
      }
      roots = cddr(roots)
    }
    if d.truthy() {
      if flag.truthy() {
        intcv2(d, nv, ivar, ll, ul)
      } else {
        intcv1(d, nv, ivar, ll, ul)
      }
    } else {
      Nil
    }
  }
}

///|
/// d: original variable (ivar) as a function of 'yx
/// nv: new variable ('yx) as a function of original variable (ivar)
fn intcv1(d : Value, nv : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let (exp_yx, ll1, ul1) = intcv2_mv(d, nv, ivar, ll, ul)
  if equal(d_imagpart(ll1), Fix(0L)) &&
    equal(d_imagpart(ul1), Fix(0L)) &&
    !alike1(ll1, ul1).truthy() {
    defint(exp_yx, q_yx, ll1, ul1)
  } else {
    Nil
  }
}

///|
/// converts limits of integration to values for new variable 'yx
/// (primary value of INTCV2-MV).
fn intcv2(d : Value, nv : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  intcv2_mv(d, nv, ivar, ll, ul).0
}

///|
/// INTCV2 with its three values (exp-yx ll1 ul1).
fn intcv2_mv(
  d : Value,
  nv : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
) -> (Value, Value, Value) raise {
  // rewrites exp, the integrand in terms of ivar, the integrand in terms
  // of 'yx, and returns the new integrand.
  let intcv3 = fn(d : Value, nv : Value, ivar : Value) -> Value raise {
    let exp_yx = muln_star([
      sdiff(d, q_yx),
      subst(d, ivar, subst(q_yx, nv, defint__exp())),
    ])
    sratsimp(exp_yx)
  }
  let mut exp_yx = intcv3(d, nv, ivar)
  let mut ll1 : Value = Nil
  let c = if zerop1(add2_star(ll, ul)).truthy() &&
    evenfn(nv, ivar).truthy() &&
    // halving the symmetric interval and doubling is only valid for an
    // even integrand
    evenfn(defint__exp(), ivar).truthy() {
    exp_yx = mul2_star(Fix(2L), exp_yx)
    ll1 = limcp(nv, ivar, Fix(0L), q_d_plus)
    ll1
  } else {
    ll1 = limcp(nv, ivar, ll, q_d_plus)
    ll1
  }
  if c is Nil {
    return (Nil, Nil, Nil)
  }
  let ul1 = limcp(nv, ivar, ul, q_d_minus)
  if ul1 is Nil {
    return (Nil, Nil, Nil)
  }
  (exp_yx, ll1, ul1)
}

///|
/// wrapper around limit, returns nil if limit not found (nounform
/// returned), or undefined ($und or $ind)
fn limcp(a : Value, b : Value, c : Value, d : Value) -> Value raise {
  let ans = d_limit(list([a, b, c, d]))
  if !(
      ans is Nil ||
      among(q_p_limit, ans).truthy() ||
      among(q_d_ind, ans).truthy() ||
      among(q_d_und, ans).truthy()
    ) {
    ans
  } else {
    Nil
  }
}

///|
fn integrand_changevar(
  d : Value,
  newvar : Value,
  exp_ : Value,
  ivar : Value,
) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  mul2_star(sdiff(d, newvar), subst(d, ivar, defint__exp()))
}

///|
fn defint(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let old_assumptions = symval(q_ear_defint_assumptions)
  let bs = bind_all([
    (q_ear_current_assumptions, Nil),
    (q_limitp, t),
    (q_d_logabs, Nil),
  ])
  defer unbind_all(bs)
  defint__up(fn() { defint__defint_body(ivar, ll, ul) }, fn() {
    restore_defint_assumptions(
      old_assumptions,
      symval(q_ear_current_assumptions),
    )
    |> ignore
  })
}

///|
/// The PROG inside DEFINT.
fn defint__defint_body(ivar0 : Value, ll0 : Value, ul0 : Value) -> Value raise {
  let (ca, ll, ul) = make_defint_assumptions(q_noask, ivar0, ll0, ul0)
  set(q_ear_current_assumptions, ca) |> ignore
  {
    let b_exp = bind(q_exp, resimplify(defint__exp()))
    defer unbind(b_exp)
    let ivar = resimplify(ivar0)
    let bs = bind_all([
      (q_d_exptsubst, t),
      (q_ear_loopstop, Fix(0L)),
      (q_nn_star, Nil),
      (q_dn_star, Nil),
      (q_d_noprincipal, Nil),
    ])
    defer unbind_all(bs)
    let mut ans = defint_list(defint__exp(), ivar, ll, ul)
    if ans.truthy() {
      return ans
    } else if zerop1(defint__exp()).truthy() || alike1(ul, ll).truthy() {
      return Fix(0L)
    } else if !among(ivar, defint__exp()).truthy() {
      if defint__memq(ul, [q_d_inf, q_d_minf]) ||
        defint__memq(ll, [q_d_inf, q_d_minf]) {
        return diverg()
      } else {
        ans = mul2_star(defint__exp(), add2_star(ul, defint__mneg(ll)))
        return ans
      }
    } else {
      // Look for integrals which involve log and exp functions.  Maxima
      // has a special algorithm to get general results.
      ans = defint_log_exp(defint__exp(), ivar, ll, ul)
      if ans.truthy() {
        return ans
      }
    }
    let b_exp2 = bind(q_exp, rmconst1(defint__exp(), ivar))
    defer unbind(b_exp2)
    let c = car(defint__exp())
    let b_exp3 = bind(q_exp, p_i_out_of_denom(cdr(defint__exp())))
    defer unbind(b_exp3)
    let e = defint__exp()
    if !symval(q_d_nointegrate).truthy() &&
      !atom(e) &&
      (
        among(q_mqapply, e).truthy() ||
        !defint__memq(caar(e), [
          q_mexpt, q_mplus, q_mtimes, q_p_sin, q_p_cos, q_p_tan, q_p_sinh, q_p_cosh,
          q_p_tanh, q_p_log, q_p_asin, q_p_acos, q_p_atan, q_p_cot, q_p_acot, q_p_sec,
          q_p_asec, q_p_csc, q_p_acsc, q_p_derivative,
        ])
      ) {
      // Call ANTIDERIV with logabs disabled, because the Risch algorithm
      // assumes the integral of 1/x is log(x), not log(abs(x)).
      ans = with_special(q_d_logabs, Nil, fn() { antideriv(e, ivar) })
      if ans.truthy() {
        ans = intsubs(ans, ll, ul, ivar)
        return if ans.truthy() { mul2_star(c, ans) } else { Nil }
      } else {
        return Nil
      }
    }
    set(q_exp, tansc_var(defint__exp(), ivar)) |> ignore
    ans = initial_analysis(defint__exp(), ivar, ll, ul)
    if ans.truthy() {
      return mul2_star(c, ans)
    }
    Nil
  }
}

///|
fn defint_list(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let e = defint__exp()
  if mbagp(e).truthy() {
    let ans = cons(car(e), mapcar(sub_exp => defint(sub_exp, ivar, ll, ul), cdr(e)))
    if ans.truthy() {
      simplify(ans)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn initial_analysis(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let pole = if !symval(q_d_intanalysis).truthy() {
    q_d_no // don't do any checking.
  } else {
    poles_in_interval(defint__exp(), ivar, ll, ul)
  }
  if eq(pole, q_d_no) {
    if oddfn(defint__exp(), ivar).truthy() &&
      (
        (eq(ll, q_d_minf) && eq(ul, q_d_inf)) ||
        eq(d_sign(add2_star(ll, ul)), q_d_zero)
      ) {
      Fix(0L)
    } else {
      parse_integrand(defint__exp(), ivar, ll, ul)
    }
  } else if eq(pole, q_d_unknown) {
    Nil
  } else {
    principal_value_integral(defint__exp(), ivar, ll, ul, pole)
  }
}

///|
fn parse_integrand(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let mut ans = eezz(defint__exp(), ll, ul, ivar)
  if ans.truthy() {
    return ans
  }
  if ratp(defint__exp(), ivar).truthy() {
    ans = method_by_limits(defint__exp(), ivar, ll, ul)
    if ans.truthy() {
      return ans
    }
  }
  if mplusp(defint__exp()).truthy() {
    ans = intbyterm(defint__exp(), t, ivar, ll, ul)
    if ans.truthy() {
      return ans
    }
  }
  ans = method_by_limits(defint__exp(), ivar, ll, ul)
  if ans.truthy() {
    return ans
  }
  Nil
}

///|
fn rmconst1(e : Value, ivar : Value) -> Value raise {
  if !freeof(ivar, e).truthy() {
    partition(e, ivar, Fix(1L))
  } else {
    cons(e, Fix(1L))
  }
}

///|
fn method_by_limits(exp_ : Value, ivar : Value, ll0 : Value, ul0 : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let old_assumptions = symval(q_ear_defint_assumptions)
  let (ca, ll, ul) = make_defint_assumptions(q_noask, ivar, ll0, ul0)
  set(q_ear_current_assumptions, ca) |> ignore
  defint__up(
    fn() {
      if eq(ul, q_d_inf) && eq(ll, q_d_minf) {
        let v = mtoinf(defint__exp(), ivar, ll, ul)
        if v.truthy() {
          return v
        }
      }
      if eq(ul, q_d_inf) && equal(ll, Fix(0L)) {
        let v = ztoinf(defint__exp(), ivar, ll, ul)
        if v.truthy() {
          return v
        }
      }
      if equal(ll, Fix(0L)) &&
        freeof(ivar, ul).truthy() &&
        eq(d_asksign(ul), q_d_pos) {
        let v = zto1(defint__exp(), ivar, ul)
        if v.truthy() {
          return v
        }
      }
      dintegrate(defint__exp(), ivar, ll, ul)
    },
    fn() {
      restore_defint_assumptions(
        old_assumptions,
        symval(q_ear_defint_assumptions),
      )
      |> ignore
    },
  )
}

///|
fn dintegrate(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let bs = bind_all([
    (q_ear_scflag, Nil),
    (q_ear_dflag, Nil),
    (q_d__pctemode, t),
  ])
  defer unbind_all(bs)
  // NOT COMPLETE for sin's and cos's.
  if !symval(q_ear_sin_cos_recur).truthy() &&
    oscip_var(defint__exp(), ivar).truthy() {
    set(q_ear_scflag, t) |> ignore
    let v = intsc1(ll, ul, defint__exp(), ivar)
    if v.truthy() {
      return v
    }
  }
  if !symval(q_ear_rad_poly_recur).truthy() &&
    notinvolve_var(defint__exp(), ivar, list1(q_p_log)).truthy() &&
    !p_einvolve_var(defint__exp(), ivar).truthy() {
    let v = method_radical_poly(defint__exp(), ivar, ll, ul)
    if v.truthy() {
      return v
    }
  }
  if !equal(symval(q_ear_dintlog_recur), Fix(2L)) {
    let arg = involve_var(defint__exp(), ivar, list1(q_p_log))
    if arg.truthy() {
      let v = dintlog(defint__exp(), arg, ivar, ll, ul)
      if v.truthy() {
        return v
      }
    }
  }
  if !symval(q_ear_dintexp_recur).truthy() {
    let arg = p_einvolve_var(defint__exp(), ivar)
    if arg.truthy() {
      let v = dintexp(defint__exp(), ivar, ll, ul)
      if v.truthy() {
        return v
      }
    }
  }
  if !ratp(defint__exp(), ivar).truthy() {
    let mut ans = with_specials(
      [(q_d_trigexpandtimes, Nil), (q_d_trigexpandplus, t)],
      fn() { d_trigexpand(defint__exp()) },
    )
    if ans.truthy() {
      ans = d_expand(ans)
      if ans.truthy() && !alike1(ans, defint__exp()).truthy() {
        let v = intbyterm(ans, t, ivar, ll, ul)
        if v.truthy() {
          return v
        }
      }
    }
  }
  // Call ANTIDERIV with logabs disabled, because the Risch algorithm
  // assumes the integral of 1/x is log(x), not log(abs(x)).
  let ans = with_special(q_d_logabs, Nil, fn() { antideriv(defint__exp(), ivar) })
  if ans.truthy() {
    intsubs(ans, ll, ul, ivar)
  } else {
    Nil
  }
}

///|
fn method_radical_poly(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  // recursion stopper
  let b0 = bind(q_ear_rad_poly_recur, t)
  defer unbind(b0)
  if sinintp(defint__exp(), ivar).truthy() {
    let result = antideriv(defint__exp(), ivar)
    if result.truthy() {
      let v = intsubs(result, ll, ul, ivar)
      if v.truthy() {
        return v
      }
    }
  }
  if ratp(defint__exp(), ivar).truthy() {
    let result = ratfnt(defint__exp(), ivar, ll, ul)
    if result.truthy() {
      return result
    }
  }
  if !symval(q_ear_scflag).truthy() &&
    !eq(ul, q_d_inf) &&
    radicalp(defint__exp(), ivar).truthy() &&
    kindp34(ivar, ll, ul).truthy() {
    let result = cv(defint__exp(), ivar, ll, ul)
    if result.truthy() {
      return result
    }
  }
  Nil
}

///|
/// Return true iff the interval with endpoints 'll' (lower limit) and
/// 'ul' (upper limit) is symmetric.
fn symmetric_intervalp(ll : Value, ul : Value) -> Value raise {
  lbool(alike1(ul, neg(ll)).truthy() || (eq(ul, q_d_inf) && eq(ll, q_d_minf)))
}

///|
fn principal_value_integral(
  exp_ : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
  poles : Value,
) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if symmetric_intervalp(ll, ul).truthy() && oddfn(defint__exp(), ivar).truthy() {
    // odd integrand, symmetric interval
    principal() |> ignore
    return Fix(0L)
  }
  let anti_deriv = antideriv(defint__exp(), ivar)
  if anti_deriv.truthy() {
    if poles.truthy() {
      let (_, new_ll, new_ul) = order_limits(q_ask, ivar, ll, ul)
      let v = take_principal(anti_deriv, new_ll, new_ul, ivar, poles)
      if v.truthy() {
        v
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
/// adds up integrals of ranges between each pair of poles.  checks if
/// whole thing is divergent as limits of integration approach poles.
fn take_principal(
  anti_deriv : Value,
  ll : Value,
  ul : Value,
  ivar : Value,
  poles : Value,
) -> Value raise {
  let mut ans : Value = Fix(0L)
  let (merged_list, _, _) = interval_list(poles, ll, ul)
  let mut current_pole = cdr(merged_list)
  let mut previous_pole = merged_list
  while current_pole.truthy() {
    ans = add2_star(
      ans,
      intsubs(
        anti_deriv,
        add2_star(caar(previous_pole), q_epsilon),
        add2_star(caar(current_pole), defint__mneg(q_epsilon)),
        ivar,
      ),
    )
    current_pole = cdr(current_pole)
    previous_pole = cdr(previous_pole)
  }
  ans = get_limit(
    get_limit(ans, q_epsilon, Fix(0L), dir=q_d_plus),
    q_prin_inf,
    q_d_inf,
  )
  // Return section.
  if ans is Nil ||
    !free(ans, q_d_infinity).truthy() ||
    !free(ans, q_d_ind).truthy() {
    Nil
  } else if among(q_d_minf, ans).truthy() ||
    among(q_d_inf, ans).truthy() ||
    among(q_d_und, ans).truthy() {
    diverg()
  } else {
    principal() |> ignore
    ans
  }
}

///|
/// I think this takes the pole-list and replaces $MINF with -PRIN-INF and
/// $INF with PRIN-INF.  The lower and upper integration limits (ll, ul)
/// can also be modified to be -PRIN-INF and PRIN-INF.  These special
/// values are used in TAKE-PRINCIPAL.
fn interval_list(
  pole_list : Value,
  ll : Value,
  ul : Value,
) -> (Value, Value, Value) raise {
  let mut pole_list = pole_list
  let mut ll = ll
  let mut ul = ul
  let first_ = car(first(pole_list))
  let last_ = caar(last(pole_list))
  if eq(ul, last_) {
    if eq(ul, q_d_inf) {
      pole_list = subst(q_prin_inf, q_d_inf, pole_list)
    }
  } else {
    if eq(ul, q_d_inf) {
      ul = q_prin_inf
    }
    pole_list = append(pole_list, list1(cons(ul, q_ignored)))
  }
  if eq(ll, first_) {
    if eq(ll, q_d_minf) {
      pole_list = subst(defint__mneg(q_prin_inf), q_d_minf, pole_list)
    }
  } else {
    if eq(ll, q_d_minf) {
      ll = defint__mneg(q_prin_inf)
    }
    pole_list = append(list1(cons(ll, q_ignored)), pole_list)
  }
  (pole_list, ll, ul)
}

///|
/// Assumes EXP is a rational expression with no polynomial part and
/// converts the finite integration to integration over a half-infinite
/// interval.  The substitution y = (x-a)/(b-x) is used.  Equivalently,
/// x = (b*y+a)/(y+1).
fn cv(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if !(real_infinityp(ll).truthy() || real_infinityp(ul).truthy()) {
    // FIXME!  This is a hack.  We apply the transformation with
    // symbolic limits and then substitute the actual limits later.  That
    // way method-by-limits (usually?) sees a simpler integrand.
    let mut trans = integrand_changevar(
      div_star(add2(q_ll, mul2(q_ul, q_yx)), add2(Fix(1L), q_yx)),
      q_yx,
      defint__exp(),
      ivar,
    )
    // If the limit is a number, use $substitute so we simplify the
    // result.  Do we really want to do this?
    trans = if mnump(ll).truthy() {
      d_substitute(ll, q_ll, expr=trans)
    } else {
      subst(ll, q_ll, trans)
    }
    trans = if mnump(ul).truthy() {
      d_substitute(ul, q_ul, expr=trans)
    } else {
      subst(ul, q_ul, trans)
    }
    method_by_limits(trans, q_yx, Fix(0L), q_d_inf)
  } else {
    Nil
  }
}

///|
/// Integrate rational functions over a finite interval by doing the
/// polynomial part directly, and converting the rational part to an
/// integral from 0 to inf.  This is evaluated via residues.
fn ratfnt(exp_ : Value, ivar : Value, ll : Value, ul : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  // PQR divides the rational expression and returns the quotient and
  // remainder
  let e = pqr(defint__exp(), ivar)
  let try_antideriv = fn(e : Value, lo : Value, hi : Value) -> Value raise {
    let ans = antideriv(e, ivar)
    if ans.truthy() {
      intsubs(ans, lo, hi, ivar)
    } else {
      Nil
    }
  }
  if equal(Fix(0L), car(e)) {
    // No polynomial part
    let ans = try_antideriv(defint__exp(), ll, ul)
    if ans.truthy() {
      ans
    } else {
      cv(defint__exp(), ivar, ll, ul)
    }
  } else if equal(Fix(0L), cdr(e)) {
    // Only polynomial part
    eezz(car(e), ll, ul, ivar)
  } else {
    // A non-zero quotient and remainder.  Combine the results together.
    let ans = try_antideriv(div_star(cdr(e), symval(q_dn_star)), ll, ul)
    if ans.truthy() {
      add2(eezz(car(e), ll, ul, ivar), ans)
    } else {
      add2(
        eezz(car(e), ll, ul, ivar),
        cv(div_star(cdr(e), symval(q_dn_star)), ivar, ll, ul),
      )
    }
  }
}

///|
/// I think this takes a rational expression E, and finds the polynomial
/// part.  A cons is returned.  The car is the quotient and the cdr is
/// the remainder.
fn pqr(e : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_varlist, list1(ivar))
  defer unbind(b0)
  newvar(e) |> ignore
  let mut e = cdr(ratrep_star(e))
  set(q_dn_star, pdis(ratdenominator(e))) |> ignore
  e = pdivide(ratnumerator(e), ratdenominator(e))
  cons(simplify(rdis(car(e))), simplify(rdis(cadr(e))))
}

///|
fn intbyterm(
  exp_ : Value,
  ear_nodiverg : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  let b_nd = bind(q_ear_nodiverg, ear_nodiverg)
  defer unbind(b_nd)
  let saved_exp = defint__exp()
  if mplusp(defint__exp()).truthy() {
    let mut ans = defint__catch_divergent(fn() {
      defint__andmapcar(new_exp => defint(new_exp, ivar, ll, ul), cdr(defint__exp()))
    })
    if ans is Nil {
      Nil
    } else if eq(ans, q_divergent) {
      with_special(q_ear_nodiverg, Nil, fn() {
        ans = antideriv(saved_exp, ivar)
        if ans.truthy() {
          intsubs(ans, ll, ul, ivar)
        } else {
          Nil
        }
      })
    } else {
      sratsimp(addn(ans, Nil))
    }
  } else {
    // If leadop isn't plus don't do anything.
    Nil
  }
}

///|
fn kindp34(ivar : Value, ll : Value, ul : Value) -> Value raise {
  let d = numden_var(defint__exp(), ivar).1
  let a = zerop1(d_limit(list([d, ivar, ll, q_d_plus]))).truthy() &&
    eq(
      limit_pole(
        add2_star(defint__exp(), add2_star(defint__mneg(ll), ivar)),
        ivar,
        ll,
        q_d_plus,
      ),
      q_d_yes,
    )
  let b = zerop1(d_limit(list([d, ivar, ul, q_d_minus]))).truthy() &&
    eq(
      limit_pole(
        add2_star(defint__exp(), add2_star(ul, defint__mneg(ivar))),
        ivar,
        ul,
        q_d_minus,
      ),
      q_d_yes,
    )
  lbool(a || b)
}

///|
fn diverg() -> Value raise {
  if symval(q_ear_nodiverg).truthy() {
    throw_tag(q_divergent, q_divergent)
  } else {
    merr("defint: integral is divergent.", [])
  }
}

///|
/// May reorder the limits LL and UL so that LL <= UL.  (See
/// ORDER-LIMITS.)  Hence, this function also returns the possibly
/// updated values of LL and UL as additional values.
fn make_defint_assumptions(
  ask_or_not : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
) -> (Value, Value, Value) raise {
  let (result, ll, ul) = order_limits(ask_or_not, ivar, ll, ul)
  if result is Nil {
    return (Nil, ll, ul)
  }
  mapc(a => forget(a) |> ignore, symval(q_ear_defint_assumptions)) |> ignore
  set(q_ear_defint_assumptions, Nil) |> ignore
  let sign_ll = if eq(ll, q_d_inf) {
    q_d_pos
  } else if eq(ll, q_d_minf) {
    q_d_neg
  } else {
    d_sign(d_limit(list1(ll)))
  }
  let sign_ul = if eq(ul, q_d_inf) {
    q_d_pos
  } else if eq(ul, q_d_minf) {
    q_d_neg
  } else {
    d_sign(d_limit(list1(ul)))
  }
  let sign_ul_ll = if eq(ul, q_d_inf) && !eq(ll, q_d_inf) {
    q_d_pos
  } else if eq(ul, q_d_minf) && !eq(ll, q_d_minf) {
    q_d_neg
  } else {
    d_sign(d_limit(list1(add2_star(ul, defint__mneg(ll)))))
  }
  if eq(sign_ul_ll, q_d_pos) {
    let a1 = assume(mk(q_mgreaterp, [ivar, ll]))
    let a2 = assume(mk(q_mgreaterp, [ul, ivar]))
    set(q_ear_defint_assumptions, list2(a1, a2)) |> ignore
  } else if eq(sign_ul_ll, q_d_neg) {
    let a1 = assume(mk(q_mgreaterp, [ivar, ul]))
    let a2 = assume(mk(q_mgreaterp, [ll, ivar]))
    set(q_ear_defint_assumptions, list2(a1, a2)) |> ignore
  }
  let v = if eq(sign_ll, q_d_pos) && eq(sign_ul, q_d_pos) {
    let a = assume(mk(q_mgreaterp, [ivar, Fix(0L)]))
    set(q_ear_defint_assumptions, cons(a, symval(q_ear_defint_assumptions)))
  } else if eq(sign_ll, q_d_neg) && eq(sign_ul, q_d_neg) {
    let a = assume(mk(q_mgreaterp, [Fix(0L), ivar]))
    set(q_ear_defint_assumptions, cons(a, symval(q_ear_defint_assumptions)))
  } else {
    symval(q_ear_defint_assumptions)
  }
  (v, ll, ul)
}

///|
fn restore_defint_assumptions(
  old_assumptions : Value,
  assumptions : Value,
) -> Value raise {
  for a in assumptions.iter() {
    forget(a) |> ignore
  }
  for a in old_assumptions.iter() {
    assume(a) |> ignore
  }
  t
}

///|
fn make_global_assumptions() -> Value raise {
  set(
    q_ear_global_defint_assumptions,
    cons(
      assume(mk(q_mgreaterp, [q_ear_z, Fix(0L)])),
      symval(q_ear_global_defint_assumptions),
    ),
  )
  |> ignore
  // *Z* is a "zero parameter" for this package.  Its also used to
  // transform.  limit(exp,var,val,dir) -- limit(exp,tvar,0,dir)
  set(
    q_ear_global_defint_assumptions,
    cons(
      assume(mk(q_mgreaterp, [q_epsilon, Fix(0L)])),
      symval(q_ear_global_defint_assumptions),
    ),
  )
  |> ignore
  set(
    q_ear_global_defint_assumptions,
    cons(
      assume(mk(q_mlessp, [q_epsilon, Flo(1.0e-8)])),
      symval(q_ear_global_defint_assumptions),
    ),
  )
  |> ignore
  // EPSILON is used in principal value code to denote the familiar
  // mathematical entity.
  set(
    q_ear_global_defint_assumptions,
    cons(
      assume(mk(q_mgreaterp, [q_prin_inf, Flo(1.0e8)])),
      symval(q_ear_global_defint_assumptions),
    ),
  )
}

///|
/// PRIN-INF Is a special symbol in the principal value code used to
/// denote an end-point which is proceeding to infinity.
fn forget_global_assumptions() -> Value raise {
  for a in symval(q_ear_global_defint_assumptions).iter() {
    forget(a) |> ignore
  }
  if symval(q_ear_integer_info).truthy() {
    for a in symval(q_ear_integer_info).iter() {
      i__dolremove(list2(cadr(a), caddr(a))) |> ignore
    }
    t
  } else {
    Nil
  }
}

///|
/// Order the limits LL and UL so that LL <= UL, as expected.  Of course,
/// this changes the sign of the integrand (in EXP), so that's also
/// updated as well.  Since the order can be changed, the possibly
/// updated values of LL and UL are returned as additional values of this
/// function.
fn order_limits(
  ask_or_not : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
) -> (Value, Value, Value) raise {
  let mut ll = ll
  let mut ul = ul
  if !equal(d_imagpart(ll), Fix(0L)) || !equal(d_imagpart(ul), Fix(0L)) {
    return (Nil, ll, ul)
  }
  ll = canonicalize_plus_inf(ll)
  ul = canonicalize_plus_inf(ul)
  if eq(ll, ul) {
    // We have minf <= ll = ul <= inf
    ()
  } else if eq(ul, q_d_inf) {
    // We have minf <= ll < ul = inf
    ()
  } else if eq(ll, q_d_minf) {
    // We have minf = ll < ul < inf
    //
    // Now substitute
    //
    //   ivar -> -ivar
    //   ll  -> -ul
    //   ul  -> inf
    //
    // so that minf < ll < ul = inf
    set(q_exp, subin_var(defint__mneg(ivar), defint__exp(), ivar)) |> ignore
    ll = defint__mneg(ul)
    ul = q_d_inf
  } else if eq(ll, q_d_inf) ||
    equal(complm(ask_or_not, ll, ul), Fix(-1L)) {
    // We have minf <= ul < ll
    //
    // Now substitute
    //
    //   exp  -> -exp
    //   ll  <-> ul
    //
    // so that minf <= ll < ul
    set(q_exp, defint__mneg(defint__exp())) |> ignore
    let tmp = ll
    ll = ul
    ul = tmp
  }
  (t, ll, ul)
}

///|
fn complm(ask_or_not : Value, ll : Value, ul : Value) -> Value raise {
  let askflag = eq(ask_or_not, q_ask)
  if alike1(ul, ll).truthy() {
    return Fix(0L)
  }
  let a = if askflag {
    d_asksign(d_limit(list1(add2(ul, defint__mneg(ll)))))
  } else {
    d_sign(d_limit(list1(add2(ul, defint__mneg(ll)))))
  }
  if eq(a, q_d_pos) {
    Fix(1L)
  } else if eq(a, q_d_neg) {
    Fix(-1L)
  } else {
    Fix(1L)
  }
}

///|
/// Substitute a and b into integral e
///
/// Looks for discontinuties in integral, and works around them.  For
/// example, in
///
/// integrate(x^(2*n)*exp(-(x)^2),x)    ==>
/// -gamma_incomplete((2*n+1)/2,x^2)*x^(2*n+1)*abs(x)^(-2*n-1)/2
///
/// the integral has a discontinuity at x=0.
fn intsubs(e : Value, a : Value, b : Value, ivar : Value) -> Value raise {
  let b0 = bind(q_d_float, Nil)
  defer unbind(b0)
  // DISCONTINUITIES is asked once, here: Its answer says both where to
  // split and, passed on to WHOLE-INTSUBS, whether plain substitution at
  // the ends of a piece, instead of taking limits, is safe.
  let sexp = with_special(q_d_algebraic, t, fn() { sratsimp(e) })
  let discont = if symval(q_d_intanalysis).truthy() {
    discontinuities(sexp, ivar)
  } else {
    Nil
  }
  let edges = if !symval(q_d_intanalysis).truthy() {
    q_d_no // don't do any checking.
  } else {
    discontinuities_in_interval(discont, ivar, a, b)
  }
  if eq(edges, q_d_no) || eq(edges, q_d_unknown) {
    whole_intsubs(e, a, b, ivar, discontinuousp=discont)
  } else {
    let mut l = edges
    let mut total : Value = Nil
    while cdr(l).truthy() {
      let a1 = car(l)
      let b1 = cadr(l)
      total = cons(whole_intsubs(e, a1, b1, ivar, discontinuousp=discont), total)
      l = cdr(l)
    }
    if every(x => x.truthy(), total) {
      addn(total, Nil)
    } else {
      Nil
    }
  }
}

///|
/// Returns a list of unique expressions whose roots identify possible
/// discontinuities of EXPR with respect to IVAR.
fn discontinuities(expr : Value, ivar : Value) -> Value raise {
  let mut result : Value = Nil
  let add_unique = fn(item : Value) raise {
    if member_if(x => alike1(item, x).truthy(), result) is Nil {
      result = cons(item, result)
    }
  }
  let varyingp = fn(e : Value) -> Bool raise { !free(e, ivar).truthy() }
  let not_pos_pz = fn(x : Value) -> Bool raise {
    !defint__memq(d_csign(x), [q_d_pos, q_d_pz])
  }
  fn walk(e : Value) -> Unit raise {
    if atom(e) || !varyingp(e) {
      return
    }
    let op = caar(e)
    let args = cdr(e)
    let denom_op = cdr(
      assq(
        op,
        list([
          cons(q_p_tan, q_p_cos),
          cons(q_p_csc, q_p_sin),
          cons(q_p_sec, q_p_cos),
          cons(q_p_cot, q_p_sin),
          cons(q_p_csch, q_p_sinh),
          cons(q_p_coth, q_p_sinh),
        ]),
      ),
    )
    if eq(op, q_mexpt) {
      // x^y potentially has a discontinuity where x = 0, unless we can
      // prove that y is strictly positive.  Also, x^y is discontinuous
      // where x crosses the negative real axis, unless y is provably an
      // integer.  Note: "crossing the negative real axis" part cannot be
      // expressed in a SOLVE-compatible way. So we detect a possible
      // discontinuity wherever Im(x) = 0, unless we can show that Re(x)
      // cannot be negative. False positives don't cause wrong answers,
      // just more splitting.
      let base = first(args)
      let exponent = second(args)
      if varyingp(base) {
        if not_pos_pz(exponent) {
          add_unique(base)
        }
        if !maxima_integerp(exponent).truthy() {
          let ri = risplit(base)
          let re = car(ri)
          let im = cdr(ri)
          if varyingp(im) && not_pos_pz(re) {
            add_unique(im)
          }
        }
      }
    } else if eq(op, q_p_log) {
      // log(x) has a discontinuity in the imaginary part at x = 0 and
      // when crossing the negative real axis.
      add_unique(first(args))
      let ri = risplit(first(args))
      let re = car(ri)
      let im = cdr(ri)
      if varyingp(im) && not_pos_pz(re) {
        add_unique(im)
      }
    } else if denom_op.truthy() {
      // tan(x) = sin(x)/cos(x), csc(x) = 1/sin(x), sec(x) = 1/cos(x),
      // cot(x) = cos(x)/sin(x), so these have discontinuities where the
      // denominator becomes zero. The same applies to the hyperbolic
      // functions, but we can ignore tanh(x) and sech(x), because
      // cosh(x) cannot be zero.
      add_unique(ftake(denom_op, [first(args)]))
    } else if arcp(op).truthy() {
      // Rewrite an inverse trigonometric/hyperbolic function into its
      // logarithmic form, and process that.
      return walk(logarc(op, first(args)))
    } else if eq(op, q_p_atan2) {
      // atan2(y, x) has a discontinuity at y = 0 when x <= 0.
      let y = first(args)
      let x = second(args)
      if !eq(d_csign(x), q_d_pos) {
        if zerop1(y).truthy() && varyingp(x) {
          add_unique(x)
        } else if varyingp(y) {
          add_unique(y)
        }
      }
    } else if eq(op, q_p_signum) {
      // signum(x) has a discontinuity at x = 0.
      add_unique(first(args))
    } else if eq(op, q_p_gamma_incomplete) {
      // gamma_incomplete(a, z), unless a is a positive integer, has a
      // discontinuity at z = 0 and when crossing the negative real axis.
      let a = first(args)
      let z = second(args)
      if varyingp(z) &&
        !(maxima_integerp(a).truthy() && eq(d_csign(a), q_d_pos)) {
        add_unique(z)
        let ri = risplit(z)
        let re_z = car(ri)
        let im_z = cdr(ri)
        if varyingp(im_z) && not_pos_pz(re_z) {
          add_unique(im_z)
        }
      }
    } else {
      // The exponential integrals: expintegral_e1, expintegral_ei,
      // expintegral_ci and expintegral_chi have a logarithmic singularity
      // at 0 and a branch cut along the negative real axis.
      // expintegral_e(n, z) has the same, except for a non-positive
      // integer n, where it is elementary. expintegral_li(z) is
      // expintegral_ei(log(z)), so its cut is the real axis to the left
      // of 1. expintegral_si and expintegral_shi are entire.
      let cut_arg = if defint__memq(op, [
          q_p_expintegral_e1, q_p_expintegral_ei, q_p_expintegral_ci, q_p_expintegral_chi,
        ]) {
        first(args)
      } else if eq(op, q_p_expintegral_li) {
        sub(first(args), Fix(1L))
      } else if eq(op, q_p_expintegral_e) {
        if !(
            maxima_integerp(first(args)).truthy() &&
            defint__memq(d_csign(first(args)), [q_d_neg, q_d_nz, q_d_zero])
          ) {
          second(args)
        } else {
          Nil
        }
      } else {
        Nil
      }
      if cut_arg.truthy() {
        if varyingp(cut_arg) {
          add_unique(cut_arg)
          let ri = risplit(cut_arg)
          let re = car(ri)
          let im = cdr(ri)
          if varyingp(im) && not_pos_pz(re) {
            add_unique(im)
          }
        }
      } else if polylogp(e).truthy() {
        // The polylogarithm li[s](z) has a branch point at z = 1 and a
        // branch cut along the real axis to the right of it.
        let z = first(subfunargs(e))
        if varyingp(z) {
          add_unique(sub(z, Fix(1L)))
          let ri = risplit(z)
          let re = car(ri)
          let im = cdr(ri)
          if varyingp(im) &&
            !defint__memq(d_csign(sub(re, Fix(1L))), [q_d_neg, q_d_nz]) {
            add_unique(im)
          }
        }
      }
    }
    // TODO: Handle discontinuities of more special functions.
    // Recursively process the arguments.
    for arg in args.iter() {
      walk(arg)
    }
  }
  walk(expr)
  result
}

///|
/// returns list of places where the expressions in EXPRS, as returned by
/// DISCONTINUITIES, have a root in ivar.  list begins with ll and ends
/// with ul, and include any values between ll and ul.  return '$no if no
/// discontinuities found.
fn discontinuities_in_interval(
  exprs : Value,
  ivar : Value,
  ll : Value,
  ul : Value,
) -> Value raise {
  let roots = real_roots(exprs, ivar, multi=t)
  if eq(roots, q_d_no) {
    return q_d_no
  }
  let mut pole_list : Value = Nil
  for soltn in roots.iter() {
    if strictly_in_interval(soltn, ll, ul).truthy() {
      pole_list = cons(soltn, pole_list)
    }
  }
  if pole_list.truthy() {
    append(
      list1(ll),
      append(
        sort_list(pole_list, (x, y) => eq(d_asksign(sub(y, x)), q_d_pos)),
        list1(ul),
      ),
    )
  } else {
    q_d_no
  }
}

///|
/// Carefully substitute the integration limits A and B into the
/// expression E.
fn whole_intsubs(
  e : Value,
  a : Value,
  b : Value,
  ivar : Value,
  discontinuousp? : Value = Nil,
) -> Value raise {
  let v = easy_subs(e, a, b, ivar, discontinuousp=discontinuousp)
  if v.truthy() {
    return v
  }
  // Note: MAKE-DEFINT-ASSUMPTIONS may reorder the limits A and B.  So
  // just always use the limits returned by MAKE-DEFINT-ASSUMPTIONS.
  let (ca, a, b) = make_defint_assumptions(q_ask, ivar, a, b) // get forceful!
  set(q_ear_current_assumptions, ca) |> ignore
  with_special(q_d_algebraic, t, fn() {
    let e = sratsimp(e)
    let v = limit_subs(e, a, b, ivar)
    if v.truthy() {
      v
    } else {
      same_sheet_subs(e, a, b, ivar)
    }
  })
}

///|
/// Try easy substitutions.  Return NIL if we can't.
fn easy_subs(
  e : Value,
  ll : Value,
  ul : Value,
  ivar : Value,
  discontinuousp? : Value = Nil,
) -> Value raise {
  if infinityp(ll).truthy() || infinityp(ul).truthy() {
    // Infinite limits aren't easy
    return Nil
  }
  if polyinx(e, ivar, Nil).truthy() ||
    (
      !involve_var(
        e,
        ivar,
        list([
          q_p_log, q_p_asin, q_p_acos, q_p_atan, q_p_asinh, q_p_acosh, q_p_atanh, q_p_atan2,
          q_p_gamma_incomplete, q_p_expintegral_ei, q_p_signum,
        ]),
      ).truthy() &&
      // The list above is only a coarse screen.  DISCONTINUITIES, asked
      // by INTSUBS, knows more, such as the branch cut of a power with a
      // non-integer exponent.
      !discontinuousp.truthy() &&
      free(defint__dqd(fn() { d_denom(e) }), ivar).truthy()
    ) {
    // It's easy if we have a polynomial.  I (rtoy) think it's also easy
    // if the denominator is free of the integration variable and also if
    // the expression doesn't involve inverse functions.
    //
    // So just try to substitute the limits into the expression.  If no
    // errors are produced, we're done.
    let ll_val = no_err_sub_var(ll, e, ivar)
    let ul_val = no_err_sub_var(ul, e, ivar)
    if eq(ll_val, t) || eq(ul_val, t) {
      // no-err-sub has returned T. An error was catched.
      Nil
    } else if ll_val.truthy() && ul_val.truthy() {
      sub_star(ul_val, ll_val)
    } else {
      Nil
    }
  } else {
    Nil
  }
}

///|
fn limit_subs(e : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  if involve_var(
      e,
      ivar,
      list([q_p_atan, q_p_gamma_incomplete, q_p_expintegral_ei]),
    ).truthy() {
    Nil // functions with discontinuities
  } else {
    let e = d_multthru(e)
    let a1 = d_limit(list([e, ivar, ll, q_d_plus]))
    let a2 = d_limit(list([e, ivar, ul, q_d_minus]))
    combine_ll_ans_ul_ans(a1, a2)
  }
}

///|
/// check for divergent integral
fn combine_ll_ans_ul_ans(a1 : Value, a2 : Value) -> Value raise {
  let infs = [q_d_inf, q_d_minf, q_d_infinity]
  if defint__memq(a1, infs) {
    if defint__memq(a2, infs) {
      if eq(a2, a1) {
        Nil
      } else {
        diverg()
      }
    } else {
      diverg()
    }
  } else if defint__memq(a2, infs) {
    diverg()
  } else if defint__memq(a1, [q_d_und, q_d_ind]) ||
    defint__memq(a2, [q_d_und, q_d_ind]) {
    Nil
  } else {
    sub_star(a2, a1)
  }
}

///|
/// This function works only on things with ATAN's in them now.
fn same_sheet_subs(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  // POLES-IN-INTERVAL doesn't know about the poles of tan(x).  Call
  // trigsimp to convert tan into sin/cos, which POLES-IN-INTERVAL knows
  // how to handle.
  let b_exp2 = bind(q_exp, mfuncall(q_d_trigsimp, list1(defint__exp())))
  defer unbind(b_exp2)
  let poles = atan_poles(defint__exp(), ll, ul, ivar)
  // POLES -> ((mlist) ((mequal) ((%atan) foo) replacement) ......)
  // We can then use $SUBSTITUTE
  let ll_ans = limcp(defint__exp(), ivar, ll, q_d_plus)
  set(q_exp, sratsimp(d_substitute(poles, defint__exp()))) |> ignore
  let ul_ans = limcp(defint__exp(), ivar, ul, q_d_minus)
  if ll_ans.truthy() && ul_ans.truthy() {
    combine_ll_ans_ul_ans(ll_ans, ul_ans)
  } else {
    Nil
  }
}

///|
fn atan_poles(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  cons(list1(q_mlist), atan_pole1(defint__exp(), ll, ul, ivar))
}

///|
fn atan_pole1(exp_ : Value, ll : Value, ul : Value, ivar : Value) -> Value raise {
  let b_exp = bind(q_exp, exp_)
  defer unbind(b_exp)
  if mapatom(defint__exp()).truthy() {
    Nil
  } else if matanp(defint__exp()).truthy() {
    // neglect multiplicity and '$unknowns for now.
    let ri = trisplit(defint__exp())
    set(q_exp, car(ri)) |> ignore
    let ipart = cdr(ri)
    if !equal(sratsimp(ipart), Fix(0L)) {
      return Nil
    }
    let pole = poles_in_interval(
      with_special(q_d_algebraic, t, fn() { sratsimp(cadr(defint__exp())) }),
      ivar,
      ll,
      ul,
    )
    if pole.truthy() && !(eq(pole, q_d_unknown) || eq(pole, q_d_no)) {
      let mut llist : Value = Nil
      for p in pole.iter() {
        if zerop1(sub_star(car(p), ll)).truthy() {
          () // don't worry about discontinuity
        } else if zerop1(sub_star(car(p), ul)).truthy() {
          () //  at boundary of integration
        } else {
          let low_lim = d_limit(list([cadr(defint__exp()), ivar, car(p), q_d_minus]))
          let up_lim = d_limit(list([cadr(defint__exp()), ivar, car(p), q_d_plus]))
          if !eq(low_lim, up_lim) &&
            real_infinityp(low_lim).truthy() &&
            real_infinityp(up_lim).truthy() {
            let change = if eq(low_lim, q_d_minf) {
              defint__mneg(q_d__pctpi)
            } else {
              q_d__pctpi
            }
            llist = cons(
              list3(
                list2(q_mequal, q_simp),
                defint__exp(),
                add2_star(defint__exp(), change),
              ),
              llist,
            )
          }
        }
      }
      llist
    } else {
      Nil
    }
  } else {
    let mut llist : Value = Nil
    for x in cdr(defint__exp()).iter() {
      llist = append(llist, atan_pole1(x, ll, ul, ivar))
    }
    llist
  }
}

///|
fn init_defint() -> Unit raise {
  defvar_init(q_ear_defintdebug, Nil)
}
