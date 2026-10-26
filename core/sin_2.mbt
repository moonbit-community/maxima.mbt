// Port of src/sin.lisp (part 2): Method 4 (CHEBYF), Method 6
// (MONSTERTRIG, TRIGINT), the top level SININT, summations, Method 9
// (RATLOG), partial integration, POWERLIST, the derivative-divides
// algorithm DIFFDIV and the substitution helpers.

// ---------------------------------------------------------------------------
// Stage II
// Implementation of Method 4: Binomial Chebyschev

///|
/// exp = a*t^r1*(c1+c2*t^q)^r2, where var2 = t.
///
/// G&S 2.202 has says this integral can be expressed by elementary
/// functions ii:
///
/// 1. q is an integer
/// 2. (r1+1)/q is an integer
/// 3. (r1+1)/q+r2 is an integer.
///
/// I (rtoy) think that for this code to work, r1, r2, and q must be numbers.
fn chebyf(expr : Value, var2 : Value) -> Value raise {
  // Return NIL if the expression doesn't match.
  let mut w = m2_chebyform(expr, var2)
  if w is Nil {
    return Nil
  }
  if zerop1(sin__as(q_c1, w)).truthy() {
    // rtoy: Is it really possible to be in this routine with c1 =
    // 0?
    return mul2_star(
      // This factor is locally constant as long as t and
      // c2*t^q avoid log's branch cut.
      subliss(
        w,
        sin__pv(
          "((mtimes) a ((mexpt) @var2 ((mtimes) -1 q r2)) ((mexpt) ((mtimes) c2 ((mexpt) @var2 q)) r2))",
          var2,
        ),
      ),
      integrator(
        subliss(w, sin__pv("((mexpt) @var2 ((mplus) r1 ((mtimes) q r2)))", var2)),
        var2,
      ),
    )
  }
  let q = sin__as(q_q, w)
  // Reset parameters.  a = a/q, r1 = (1 - q + r1)/q
  let na = cons(q_a, div_star(sin__as(q_a, w), q))
  let nr1 = cons(
    q_r1,
    div_star(addn(list([Fix(1L), neg(simplify(q)), sin__as(q_r1, w)]), Nil), q),
  )
  w = cons(na, cons(nr1, w))
  let mut r1 = sin__as(q_r1, w)
  let mut r2 = sin__as(q_r2, w)
  // Write r1 = d1/n1, r2 = d2/n2, if possible.  Update w with
  // these values, if so.  If we can't, give up.  I (rtoy) think
  // this only happens if r1 or r2 can't be expressed as rational
  // numbers.  Hence, r1 and r2 have to be numbers, not variables.
  let mut d1 : Value = Nil
  let mut d2 : Value = Nil
  let mut n1 : Value = Nil
  let mut n2 : Value = Nil
  let ok = {
    d1 = denomfind(r1)
    d1.truthy()
  } &&
    {
      d2 = denomfind(r2)
      d2.truthy()
    } &&
    {
      n1 = integerp2(timesk(r1, d1))
      n1.truthy()
    } &&
    {
      n2 = integerp2(timesk(r2, d2))
      n2.truthy()
    } &&
    {
      // Exact r1 and r2, so that a float
      // exponent such as 2.0 becomes 2.
      let e1 = cons(q_d1, d1)
      let e2 = cons(q_d2, d2)
      let e3 = cons(q_n1, n1)
      let e4 = cons(q_n2, n2)
      r1 = div(n1, d1)
      let e5 = cons(q_r1, r1)
      r2 = div(n2, d2)
      let e6 = cons(q_r2, r2)
      w = list_star([e1, e2, e3, e4, e5, e6, w])
      w.truthy()
    }
  if !ok {
    return Nil
  }
  if integerp2(r1).truthy() && num_gt(r1, Fix(0L)) {
    // (r1+q-1)/q is positive integer.
    //
    // I (rtoy) think we are using the substitution z=(c1+c2*t^q).
    // Maxima thinks the resulting integral should then be
    //
    // a/q*c2^(-r1/q-1/q)*integrate(z^r2*(z-c1)^(r1/q+1/q-1),z)
    //
    let subst_expr = subliss(
      w,
      sin__pv("((mplus) c1 ((mtimes) c2 ((mexpt) @var2 q)))", var2),
    )
    let new_var = make_new_var(Str("chebyf"), expr=subst_expr)
    let integrand = expands(
      list1(
        subliss(
          w,
          // a*t^r2*c2^(-r1-1)
          sin__pat(
            "((mtimes) a ((mexpt) @newvar r2) ((mexpt) c2 ((mtimes) -1 ((mplus) r1 1))))",
            [("@newvar", new_var)],
          ),
        ),
      ),
      cdr(
        // (t-c1)^r1
        expandexpt(
          subliss(
            w,
            sin__pat("((mplus) @newvar ((mtimes) -1 c1))", [
              ("@newvar", new_var),
            ]),
          ),
          r1,
        ),
      ),
    )
    return substint(
      subst_expr,
      new_var,
      integrator(integrand, new_var),
      var2,
      expr,
    )
  } else if integerp2(r2).truthy() {
    // I (rtoy) think this is using the substitution z = t^(q/d1).
    //
    // The integral (as maxima will tell us) becomes
    //
    // a*d1/q*integrate(z^(n1/q+d1/q-1)*(c1+c2*z^d1)^r2,z)
    //
    // But be careful because the variable A in the code is
    // actually a/q.
    let subst_expr = subliss(
      w,
      sin__pv("((mexpt) @var2 ((mquotient) q d1))", var2),
    )
    let new_var = make_new_var(Str("chebyf"), expr=subst_expr)
    return substint(
      subst_expr,
      new_var,
      ratint(
        simplify(
          subliss(
            w,
            sin__pat(
              "((mtimes) d1 a ((mexpt) @newvar ((mplus) n1 d1 -1)) ((mexpt) ((mplus) ((mtimes) c2 ((mexpt) @newvar d1)) c1) r2))",
              [("@newvar", new_var)],
            ),
          ),
        ),
        new_var,
      ),
      var2,
      expr,
    )
  } else if integerp2(r1).truthy() && num_lt(r1, Fix(0L)) {
    // I (rtoy) think this is using the substitution
    //
    // z = (c1+c2*t^q)^(1/d2)
    //
    // With this substitution, maxima says the resulting integral
    // is
    //
    //  a/q*c2^(-r1/q-1/q)*d2*
    //    integrate(z^(n2+d2-1)*(z^d2-c1)^(r1/q+1/q-1),z)
    let subst_expr = subliss(
      w,
      sin__pv(
        "((mexpt) ((mplus) c1 ((mtimes) c2 ((mexpt) @var2 q))) ((mquotient) 1 d2))",
        var2,
      ),
    )
    let new_var = make_new_var(Str("chebyf"), expr=subst_expr)
    return substint(
      subst_expr,
      new_var,
      ratint(
        simplify(
          subliss(
            w,
            // This is essentially the integrand above, except A and R1
            // here are not the same as derived above.
            sin__pat(
              "((mtimes) a d2 ((mexpt) c2 ((mtimes) -1 ((mplus) r1 1))) ((mexpt) @newvar ((mplus) n2 d2 -1)) ((mexpt) ((mplus) ((mexpt) @newvar d2) ((mtimes) -1 c1)) r1))",
              [("@newvar", new_var)],
            ),
          ),
        ),
        new_var,
      ),
      var2,
      expr,
    )
  } else if integerp2(add2_star(r1, r2)).truthy() {
    // If we're here,  (r1-q+1)/q+r2 is an integer.
    //
    // I (rtoy) think this is using the substitution
    //
    // z = ((c1+c2*t^q)/t^q)^(1/d1)
    //
    // With this substitution, maxima says the resulting integral
    // is
    //
    // a*d2/q*c1^(r2+r1/q+1/q)*
    //   integrate(z^(d2*r2+d2-1)*(z^d2-c2)^(-r2-r1/q-1/q-1),z)
    let subst_expr = with_special(q_d_radexpand, q_d_all, () => {
      // Setting $radexpand to $all here gets rid of
      // ABS in the substitution.  I think that's ok in
      // this case.  See Bug 1654183.
      subliss(
        w,
        sin__pv(
          "((mexpt) ((mquotient) ((mplus) c1 ((mtimes) c2 ((mexpt) @var2 q))) ((mexpt) @var2 q)) ((mquotient) 1 d1))",
          var2,
        ),
      )
    })
    let new_var = make_new_var(Str("chebyf"), expr=subst_expr)
    return substint(
      subst_expr,
      new_var,
      ratint(
        simplify(
          subliss(
            w,
            sin__pat(
              "((mtimes) -1 a d1 ((mexpt) c1 ((mplus) r1 r2 1)) ((mexpt) @newvar ((mplus) n2 d1 -1)) ((mexpt) ((mplus) ((mexpt) @newvar d1) ((mtimes) -1 c2)) ((mtimes) -1 ((mplus) r1 r2 2))))",
              [("@newvar", new_var)],
            ),
          ),
        ),
        new_var,
      ),
      var2,
      expr,
    )
  } else {
    return mk(q_p_integrate, [expr, var2])
  }
}

///|
fn greaterratp(x1 : Value, x2 : Value) -> Value raise {
  if numberp(x1) && numberp(x2) {
    lbool(num_gt(x1, x2))
  } else if ratnump(x1).truthy() {
    greaterratp(quot(lfloat(cadr(x1)), caddr(x1)), x2)
  } else if ratnump(x2).truthy() {
    greaterratp(x1, quot(lfloat(cadr(x2)), caddr(x2)))
  } else {
    Nil
  }
}

///|
fn trig1(x : Value) -> Value raise {
  memq(car(x), sin__lit("(%sin %cos)"))
}

///|
fn supertrig(expr : Value, var2 : Value, trigarg : Value) -> Value raise {
  if freevar2(expr, var2).truthy() {
    t
  } else if atom(expr) {
    Nil
  } else if eq(caar(expr), q_mplus) || eq(caar(expr), q_mtimes) {
    lbool(
      supertrig(cadr(expr), var2, trigarg).truthy() &&
      (
        cddr(expr) is Nil ||
        supertrig(cons(car(expr), cddr(expr)), var2, trigarg).truthy()
      ),
    )
  } else if eq(caar(expr), q_mexpt) {
    lbool(
      supertrig(cadr(expr), var2, trigarg).truthy() &&
      supertrig(caddr(expr), var2, trigarg).truthy(),
    )
  } else if eq(caar(expr), q_p_log) {
    supertrig(cadr(expr), var2, trigarg)
  } else if memq(caar(expr), sin__lit("(%sin %cos %tan %sec %cot %csc)")).truthy() {
    if m2(cadr(expr), trigarg).truthy() {
      t
    } else if m2_b_starx_plusa(cadr(expr), var2).truthy() {
      set(q_ear_notsame, t) |> ignore
      Nil
    } else {
      supertrig(cadr(expr), var2, trigarg)
    }
  } else {
    supertrig(cadr(expr), var2, trigarg)
  }
}

///|
fn subst2s(ex : Value, pat : Value, var2 : Value) -> Value raise {
  if ex is Nil {
    Nil
  } else if m2(ex, pat).truthy() {
    var2
  } else if atom(ex) {
    ex
  } else {
    cons(subst2s(car(ex), pat, var2), subst2s(cdr(ex), pat, var2))
  }
}

///|
/// Match (c*x+b), where c and b are free of x
fn simple_trig_arg(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mplus) ((mtimes) ((coefftt) (c freevar2 @var2)) ((coefftt) (v varp2 @var2))) ((coeffpp) (b freevar2 @var2)))",
      var2,
    ),
  )
}

// ---------------------------------------------------------------------------
// Stage II
// Implementation of Method 6: Elementary function of trigonometric functions

///|
fn monstertrig(expr : Value, var2 : Value, trigarg : Value) -> Value raise {
  let bnd = bind(q_ear_notsame, Nil)
  defer unbind(bnd)
  let mut trigarg = trigarg
  if supertrig(expr, var2, trigarg).truthy() {
    // a: A product of trig functions and all trig functions have the same
    // argument trigarg. Maxima substitutes trigarg with a new variable
    // of integration and calls trigint to integrate the new problem.
    let new_var = make_new_var(Str("monstertrig"), expr=trigarg)
    let w = subst2s(expr, trigarg, new_var)
    let b = cdras(q_b, m2_b_starx_plusa(trigarg, var2))
    let a = substint(trigarg, new_var, trigint(div_star(w, b), new_var), var2, expr)
    return if isinop(a, q_p_integrate).truthy() {
      mk(q_p_integrate, [expr, var2])
    } else {
      a
    }
  }
  if symval(q_ear_notsame) is Nil {
    return Nil
  }
  // Check for an expression like a*trig1(m*x)*trig2(n*x),
  // where trig1 and trig2 are sin or cos.
  let y = m2(
    expr,
    sin__pv(
      "((mtimes) ((coefftt) (a freevar2 @var2)) (((b trig1)) ((mtimes) (x varp2 @var2) ((coefftt) (m freevar2 @var2)))) (((d trig1)) ((mtimes) (x varp2 @var2) ((coefftt) (n freevar2 @var2)))))",
      var2,
    ),
  )
  if y.truthy() {
    // The tests after this depend on values of b and d being
    // set.  Set them here unconditionally, before doing the
    // tests.
    let b = cdras(q_b, y)
    let d = cdras(q_d, y)
    if eq(car(b), q_p_sin) && eq(car(d), q_p_sin) {
      // We have a*sin(m*x)*sin(n*x).
      //
      // The integral is:
      // a*(sin((m-n)*x)/(2*(m-n))-sin((m+n)*x)/(2*(m+n)).  But if n
      // = m, the integral is x/2-sin(2*n*x)/(4*n).
      let n = cdras(q_n, y)
      let m = cdras(q_m, y)
      if eq(d_askequal(n, m), q_d_yes) {
        // n=m, so we have the integral of a*sin(n*x)^2 which is
        return subliss(
          y,
          sin__lit(
            "((mtimes) a ((mplus) ((mquotient) x 2) ((mtimes) -1 ((mquotient) ((%sin) ((mtimes) 2 n x)) ((mtimes) 4 n)))))",
          ),
        )
      } else {
        return subliss(
          y,
          sin__lit(
            "((mtimes) a ((mplus) ((mquotient) ((%sin) ((mtimes) ((mplus) m ((mtimes) -1 n)) x)) ((mtimes) 2 ((mplus) m ((mtimes) -1 n)))) ((mtimes) -1 ((mquotient) ((%sin) ((mtimes) ((mplus) m n) x)) ((mtimes) 2 ((mplus) m n))))))",
          ),
        )
      }
    } else if eq(car(b), q_p_cos) && eq(car(d), q_p_cos) {
      // We have a*cos(m*x)*cos(n*x).
      //
      // The integral is:
      // a*(sin((m-n)*x)/(2*(m-n))+sin((m+n)*x)/(2*(m+n)).  But when
      // n = m, the integral is sin(2*m*x)/(4*m)+x/2.
      let n = cdras(q_n, y)
      let m = cdras(q_m, y)
      if eq(d_askequal(n, m), q_d_yes) {
        return subliss(
          y,
          sin__lit(
            "((mtimes) a ((mplus) ((mquotient) ((%sin) ((mtimes) 2 n x)) ((mtimes) 4 n)) ((mquotient) x 2)))",
          ),
        )
      } else {
        return subliss(
          y,
          sin__lit(
            "((mtimes) a ((mplus) ((mquotient) ((%sin) ((mtimes) ((mplus) m ((mtimes) -1 n)) x)) ((mtimes) 2 ((mplus) m ((mtimes) -1 n)))) ((mquotient) ((%sin) ((mtimes) ((mplus) m n) x)) ((mtimes) 2 ((mplus) m n)))))",
          ),
        )
      }
    } else {
      // The following (destructively!) swaps the values of
      // m and n if first trig term is sin.  I (rtoy) don't
      // understand why this is needed.  The formula
      // doesn't depend on that.
      if eq(car(b), q_p_cos) {
        let w = cdras(q_m, y)
        if w.truthy() {
          rplacd(assq(q_m, y), cdras(q_n, y)) |> ignore
          rplacd(assq(q_n, y), w) |> ignore
        }
      }
      // We have a*cos(n*x)*sin(m*x).
      //
      // The integral is:
      // -a*(cos((m-n)*x)/(2*(m-n))+cos((m+n)*x)/(2*(m+n)).  But
      // if n = m, the integral is -cos(n*x)^2/(2*n).
      let n = cdras(q_n, y)
      let m = cdras(q_m, y)
      if eq(d_askequal(n, m), q_d_yes) {
        // This needs work.  For example
        // integrate(cos(m*x)*sin(2*m*x),x).  We ask if 2*m = m.
        // If the answer is yes, we return -cos(m*x)^2/(2*m).
        // But if 2*m=m, then m=0 and the integral must be 0.
        return subliss(
          y,
          sin__lit(
            "((mquotient) ((mtimes) -1 a ((mexpt) ((%cos) ((mtimes) n x)) 2)) ((mtimes) 2 n))",
          ),
        )
      } else {
        return subliss(
          y,
          sin__lit(
            "((mtimes) -1 a ((mplus) ((mquotient) ((%cos) ((mtimes) ((mplus) m ((mtimes) -1 n)) x)) ((mtimes) 2 ((mplus) m ((mtimes) -1 n)))) ((mquotient) ((%cos) ((mtimes) ((mplus) m n) x)) ((mtimes) 2 ((mplus) m n)))))",
          ),
        )
      }
    }
  }
  // b: At this point we have trig functions with different arguments,
  // but not a product of sin and cos.
  trigarg = var2
  let y = m2(
    expr,
    sin__pat(
      "((mtimes) ((coefftt) (a freevar2 @var2)) (((b trig1)) ((mtimes) (x varp2 @var2) ((coefftt) (n integerp2)))) ((coefftt) (c supertrig @var2 @trigarg)))",
      [("@var2", var2), ("@trigarg", trigarg)],
    ),
  )
  if y is Nil {
    return Nil
  }
  // We have a product of trig functions: trig1(n*x)*trig2(y).
  // trig1 is sin or cos, where n is a numerical integer. trig2 is not a sin
  // or cos. The cos or sin function is expanded.
  let a = cdras(q_a, y) // constant factor
  let c = cdras(q_c, y) // trig functions
  let expanded = if eq(car(cdras(q_b, y)), q_p_cos) {
    // expand cos(n*x)
    maxima_substitute(var2, q_x, supercosnx(integerp2(cdras(q_n, y))))
  } else {
    // expand sin(x*x)
    maxima_substitute(var2, q_x, supersinx(integerp2(cdras(q_n, y))))
  }
  integrator(d_expand(mk(q_mtimes, [a, c, expanded])), var2)
}

///|
fn trig2(x : Value) -> Value raise {
  memq(car(x), sin__lit("(%sin %cos %tan %cot %sec %csc)"))
}

///|
/// sin(n*x) for integer n /= 0.  Result not simplified.
fn supersinx(n : Value) -> Value raise {
  let i : Value = if num_lt(n, Fix(0L)) { Fix(-1L) } else { Fix(1L) }
  d_expand(mk(q_mtimes, [i, sinnx(timesk(i, n))]))
}

///|
/// cos(n*x) for integer n /= 0.  Result not simplified.
fn supercosnx(n : Value) -> Value raise {
  d_expand(
    cosnx(
      timesk(
        if num_lt(n, Fix(0L)) {
          Fix(-1L)
        } else {
          Fix(1L)
        },
        n,
      ),
    ),
  )
}

///|
/// sin(n*x) for integer n >= 1.  Result is not simplified.
fn sinnx(n : Value) -> Value raise {
  if equal(n, Fix(1L)) {
    sin__lit("((%sin) x)")
  } else {
    let t1 = mk(q_mtimes, [sin__lit("((%sin) x)"), cosnx(one_minus(n))])
    let t2 = mk(q_mtimes, [sin__lit("((%cos) x)"), sinnx(one_minus(n))])
    mk(q_mplus, [t1, t2])
  }
}

///|
/// cos(n*x) for integer n >= 1.  Result is not simplified.
fn cosnx(n : Value) -> Value raise {
  if equal(n, Fix(1L)) {
    sin__lit("((%cos) x)")
  } else {
    let t1 = mk(q_mtimes, [sin__lit("((%cos) x)"), cosnx(one_minus(n))])
    let t2 = mk(q_mtimes, [
      Fix(-1L),
      sin__lit("((%sin) x)"),
      sinnx(one_minus(n)),
    ])
    mk(q_mplus, [t1, t2])
  }
}

///|
fn poseven(x : Value) -> Value raise {
  lbool(even(x).truthy() && num_gt(x, Fix(-1L)))
}

///|
fn trigfree(x : Value) -> Value raise {
  if atom(x) {
    lbool(memq(x, sin__lit("(sin* cos* sec* tan*)")) is Nil)
  } else {
    lbool(trigfree(car(x)).truthy() && trigfree(cdr(x)).truthy())
  }
}

///|
fn rat1(
  expr : Value,
  aa : Value,
  bb : Value,
  cc : Value,
  offset? : Value = Fix(1L),
) -> Value raise {
  let bnd = bind(q_ear_notsame, Nil)
  defer unbind(bnd)
  if numberp(expr) && zerop(expr) {
    return Nil
  }
  let b1 = subst(bb, q_b, sin__lit("((mexpt) b (n even))"))
  set(q_ear_yy, rats(expr, aa, b1, cc, offset)) |> ignore
  if symval(q_ear_notsame) is Nil {
    symval(q_ear_yy)
  } else {
    Nil
  }
}

///|
fn rats(
  expr : Value,
  aa : Value,
  b1 : Value,
  cc : Value,
  offset : Value,
) -> Value raise {
  if eq(expr, aa) {
    q_x
  } else if atom(expr) {
    if memq(expr, sin__lit("(sin* cos* sec* tan*)")).truthy() {
      set(q_ear_notsame, t)
    } else {
      expr
    }
  } else {
    let y = m2(expr, b1)
    if y.truthy() {
      f3(y, cc, offset)
    } else {
      cons(car(expr), mapcar(g => rats(g, aa, b1, cc, offset), cdr(expr)))
    }
  }
}

///|
fn f3(y : Value, cc : Value, offset : Value) -> Value raise {
  maxima_substitute(
    cc,
    q_c,
    maxima_substitute(
      quot(sin__as(q_n, y), Fix(2L)),
      q_n,
      sin__pat("((mexpt) ((mplus) @offset ((mtimes) c ((mexpt) x 2))) n)", [
        ("@offset", offset),
      ]),
    ),
  )
}

///|
fn odd1(n : Value, cc : Value, offset? : Value = Fix(1L)) -> Value raise {
  if !numberp(n) {
    Nil
  } else if !zerop(num_rem(n, Fix(2L))) {
    set(
      q_ear_yz,
      maxima_substitute(
        cc,
        q_c,
        mk(q_mexpt, [
          sin__pat("((mplus) @offset ((mtimes) c ((mexpt) x 2)))", [
            ("@offset", offset),
          ]),
          quot(one_minus(n), Fix(2L)),
        ]),
      ),
    )
  } else {
    Nil
  }
}

///|
fn subvar(x : Value, var2 : Value) -> Value raise {
  maxima_substitute(var2, q_x, x)
}

///|
fn subvardlg(x : Value, var2 : Value) -> Value raise {
  mapcar(m => cons(maxima_substitute(var2, q_x, car(m)), cdr(m)), x)
}

///|
/// This appears to be the implementation of Method 6, pp.82 in Moses' thesis.
fn trigint(expr : Value, var2 : Value) -> Value raise {
  let bnds = bind_all([(q_ear_yy, Nil), (q_ear_yz, Nil)])
  defer unbind_all(bnds)
  // Transform trig(x) into trig* (for simplicity?)  Convert cot to
  // tan and csc to sin.
  let y2 = subliss(
    subvardlg(
      sin__lit(
        "((((%sin) x) . sin*) (((%cos) x) . cos*) (((%tan) x) . tan*) (((%cot) x) . ((mexpt) tan* -1)) (((%sec) x) . sec*) (((%csc) x) . ((mexpt) sin* -1)))",
      ),
      var2,
    ),
    expr,
  )
  if sin__debug() {
    format(t, "~& in TRIGINT:~%", []) |> ignore
    format(t, "~&   : y2 = ~A~%", [y2]) |> ignore
  }
  // Now transform tan to sin/cos and sec to 1/cos.
  let y1 = subliss(
    sin__lit(
      "((tan* . ((mtimes) sin* ((mexpt) cos* -1))) (sec* . ((mexpt) cos* -1)))",
    ),
    y2,
  )
  let mut y = y1
  if sin__debug() {
    format(t, "~&   : y  = ~A~%", [y]) |> ignore
  }
  let mut z = m2(
    y,
    sin__lit(
      "((mtimes) ((coefftt) (b trigfree)) ((mexpt) sin* (m poseven)) ((mexpt) cos* (n poseven)))",
    ),
  )
  if z.truthy() {
    // Case III:
    // Handle the case of sin^m*cos^n, m, n both non-negative and even.
    let m = cdras(q_m, z)
    let n = cdras(q_n, z)
    let aa = integerp2(
      num_mul(
        num_mul(Flo(0.5), if num_lt(m, n) { Fix(1L) } else { Fix(-1L) }),
        num_add(n, num_mul(Fix(-1L), m)),
      ),
    )
    let subst_expr = mul2(Fix(2L), var2)
    let new_var = make_new_var(Str("trigint"), expr=subst_expr)
    z = cons(cons(q_a, aa), z)
    z = cons(cons(q_x, new_var), z)
    if sin__debug() {
      format(t, "~& CASE III:~%", []) |> ignore
      format(t, "~&   : m, n = ~A ~A~%", [m, n]) |> ignore
      format(t, "~&   : a    = ~A~%", [aa]) |> ignore
      format(t, "~&   : z    = ~A~%", [z]) |> ignore
    }
    // integrate(sin(y)^m*cos(y)^n,y) is transformed to the following form:
    //
    // m < n:  integrate((sin(2*y)/2)^n*(1/2+1/2*cos(2*y)^((n-m)/2),y)
    // m >= n: integrate((sin(2*y)/2)^n*(1/2-1/2*cos(2*y)^((m-n)/2),y)
    let bz = cdras(q_b, z)
    let half = div(Fix(1L), Fix(2L))
    let integrand = if num_lt(m, n) {
      subliss(
        z,
        sin__lit(
          "((mtimes) ((mexpt) ((mtimes) ((rat simp) 1 2) ((%sin) x)) m) ((mexpt) ((mplus) ((rat simp) 1 2) ((mtimes) ((rat simp) 1 2) ((%cos) x))) a))",
        ),
      )
    } else {
      subliss(
        z,
        sin__lit(
          "((mtimes) ((mexpt) ((mtimes) ((rat simp) 1 2) ((%sin) x)) n) ((mexpt) ((mplus) ((rat simp) 1 2) ((mtimes) ((rat simp) -1 2) ((%cos) x))) a))",
        ),
      )
    }
    return mul3(
      bz,
      half,
      substint(
        subst_expr,
        new_var,
        integrator(integrand, new_var),
        var2,
        expr,
      ),
    )
  }
  // l1
  // Case IV:
  // I think this is case IV, working on the expression in terms of
  // sin and cos.
  //
  // Elem(x) means constants, x, trig functions of x, log and
  // inverse trig functions of x, and which are closed under
  // addition, multiplication, exponentiation, and substitution.
  //
  // Elem(f(x)) is the same as Elem(x), but f(x) replaces x in the
  // definition.
  if sin__debug() {
    format(t, "~& Case IV:~%", []) |> ignore
  }
  let mut repl : Value = Nil
  // target: 0 = getout, 1 = get3, 2 = get1, 3 = get2
  let target = if m2(
      y,
      sin__lit(
        "((coeffpt) (c rat1 sin* cos* -1) ((mexpt) cos* (n odd1 -1)))",
      ),
    ).truthy() &&
    {
      repl = mk(q_p_sin, [var2])
      repl.truthy()
    } {
    // The case cos^(2*n+1)*Elem(cos^2,sin).  Use the substitution z = sin.
    0
  } else if m2(
      y,
      sin__lit(
        "((coeffpt) (c rat1 cos* sin* -1) ((mexpt) sin* (n odd1 -1)))",
      ),
    ).truthy() &&
    {
      repl = mk(q_p_cos, [var2])
      repl.truthy()
    } {
    // The case sin^(2*n+1)*Elem(sin^2,cos).  Use the substitution z = cos.
    1
  } else {
    // Case V:
    // Transform sin and cos to tan and sec to see if the integral is
    // of the form Elem(tan, sec^2).  If so, use the substitution z = tan.
    if sin__debug() {
      format(t, "~& Case V:~%", []) |> ignore
    }
    y = subliss(
      sin__lit("((sin* (mtimes) tan* ((mexpt) sec* -1)) (cos* (mexpt) sec* -1))"),
      y2,
    )
    if rat1(y, q_tan_star, q_sec_star, Fix(1L)).truthy() &&
      {
        repl = mk(q_p_tan, [var2])
        repl.truthy()
      } {
      2
    } else if m2(
        y,
        sin__lit(
          "((coeffpt) (c rat1 sec* tan* 1 -1) ((mexpt) tan* (n odd1 1 -1)))",
        ),
      ).truthy() &&
      {
        repl = mk(q_p_sec, [var2])
        repl.truthy()
      } {
      set(q_ear_yy, mk(q_mquotient, [symval(q_ear_yy), q_x])) |> ignore
      0
    } else {
      repl = d_expand(expr)
      if !alike1(repl, expr).truthy() {
        return integrator(repl, var2)
      }
      y = subliss(
        sin__lit(
          "((sin* (mtimes) 2 x ((mexpt) ((mplus) 1 ((mexpt) x 2)) -1)) (cos* (mtimes) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) ((mexpt) ((mplus) 1 ((mexpt) x 2)) -1)))",
        ),
        y1,
      )
      y = mk(q_mtimes, [
        y,
        sin__lit("((mtimes) 2 ((mexpt) ((mplus) 1 ((mexpt) x 2)) -1))"),
      ])
      repl = subvar(
        sin__lit("((mquotient) ((%sin) x) ((mplus) 1 ((%cos) x)))"),
        var2,
      )
      3
    }
  }
  if target == 1 {
    // get3
    y = mk(q_mtimes, [Fix(-1L), symval(q_ear_yy), symval(q_ear_yz)])
  } else if target == 2 {
    // get1
    y = mk(q_mtimes, [
      sin__lit("((mexpt) ((mplus) 1 ((mexpt) x 2)) -1)"),
      symval(q_ear_yy),
    ])
  } else if target == 0 {
    // getout
    y = mk(q_mtimes, [symval(q_ear_yy), symval(q_ear_yz)])
  }
  // get2
  if sin__debug() {
    format(t, "~& Call the INTEGRATOR with:~%", []) |> ignore
    format(t, "~&   : y    = ~A~%", [y]) |> ignore
    format(t, "~&   : repl = ~A~%", [repl]) |> ignore
  }
  // See Bug 2880797.  We want atan(tan(x)) to simplify to x, so
  // set $triginverses to '$all.
  // In case INTEGRATOR fails below, the calling INTEGRATOR will eventually
  // try RISCHINT. Remember to use $TRIGINVERSES = '$ALL when doing so, as
  // this allows Maxima to correctly compute many definite integrals involving
  // trigonometric functions, e.g., integrate((1-cos(x))^(3/2), x, 0, 2*%pi).
  set(q_ear_risch_use_triginv_all, t) |> ignore
  // Do not integrate for the global variable VAR, but substitute it.
  // This way possible assumptions on VAR are no longer present. The
  // algorithm of DEFINT depends on this behavior. See Bug 3085498.
  let newvar = make_new_var(Str("trigint"), expr=repl)
  let yv = y
  let replv = repl
  with_special(q_d_triginverses, q_d_all, () => substint(
    replv,
    newvar,
    integrator(maxima_substitute(newvar, q_x, yv), newvar),
    var2,
    expr,
  ))
}

///|
/// `(with-new-context (context) ...)`
fn sin__with_new_context(f : () -> Value raise) -> Value raise {
  let my_context = gensym(prefix=invert_case("$CTXT"))
  d_supcontext(list([my_context, symval(q_context)])) |> ignore
  let r = f() catch {
    e => {
      d_killcontext(list1(my_context)) |> ignore
      raise e
    }
  }
  d_killcontext(list1(my_context)) |> ignore
  r
}

///|
/// This is the top level of the integrator
fn sinint(expr : Value, var2 : Value) -> Value raise {
  sin__with_new_context(() => {
    // *integrator-level* is a recursion counter for INTEGRATOR.  See
    // INTEGRATOR for more details.  Initialize it here.
    let bnd = bind(q_ear_integrator_level, Fix(0L))
    defer unbind(bnd)
    let mut expr = expr
    let mut var2 = var2
    // Sanity checks for variables
    if mnump(var2).truthy() {
      merr("integrate: variable must not be a number; found: ~:M", [var2])
      |> ignore
    }
    if d_ratp(var2).truthy() {
      var2 = ratdisrep(var2)
    }
    if d_ratp(expr).truthy() {
      expr = ratdisrep(expr)
    }
    let var2 = var2
    if mxorlistp(expr).truthy() {
      // Distribute over lists and matrices
      cons(car(expr), mapcar(y => sinint(y, var2), cdr(expr)))
    } else if !atom(var2) && memq(q_array, cdar(var2)).truthy() {
      // The symbolic integration code doesn't really deal very well with
      // subscripted variables, so if we have one then replace occurrences
      // of var2 with an atomic gensym and recurse.
      let dummy_var2 = make_new_var(Str("sinint"), expr=var2)
      maxima_substitute(
        var2,
        dummy_var2,
        sinint(maxima_substitute(dummy_var2, var2, expr), dummy_var2),
      )
    } else if mequalp(expr).truthy() {
      // If expr is an equality, integrate both sides and add an integration
      // constant
      let lhs = sinint(cadr(expr), var2)
      let rhs = sinint(caddr(expr), var2)
      let cnt = set(
        q_d_integration_constant_counter,
        num_add(symval(q_d_integration_constant_counter), Fix(1L)),
      )
      list3(
        car(expr),
        lhs,
        add2(rhs, d_concat(list([symval(q_d_integration_constant), cnt]))),
      )
    } else if atom(var2) && isinop(expr, var2).truthy() {
      // If var2 is an atom which occurs as an operator in expr, then return
      // a noun form.
      mk(q_p_integrate, [expr, var2])
    } else if zerop1(expr).truthy() {
      // special case because 0 will not pass sum-of-intsp test
      Fix(0L)
    } else {
      let ans = simplify(
        with_specials(
          [(q_d_opsubst, Nil), (q_varlist, Nil), (q_genvar, Nil)],
          () => integrator(expr, var2, stack=Nil),
        ),
      )
      if sum_of_intsp(ans, var2).truthy() {
        mk(q_p_integrate, [expr, var2])
      } else {
        ans
      }
    }
  })
}

///|
/// SUM-OF-INTSP
///
/// This is a heuristic that SININT uses to work out whether the result from
/// INTEGRATOR is worth returning or whether just to return a noun form. If
/// this function returns T, then SININT will return a noun form.
///
/// The logic, as I understand it (Rupert 01/2014):
///
///   (1) If I integrate f(x) wrt x and get an atom other than x or 0, either
///       something's gone horribly wrong, or this is part of a larger
///       expression. In the latter case, we can return T here because
///       hopefully something else interesting will make the top-level
///       return NIL.
///
///   (2) If I get a sum, return a noun form if every one of the summands is
///       no better than what I started with. (Presumably this is where the
///       name came from)
///
///   (3) If this is a noun form, it doesn't convey much information on its
///       own, so return T.
///
///   (4) If this is a product, something interesting has probably happened.
///       But I still want a noun form if the result is like
///       2*'integrate(f(x),x), so I'm only interested in terms in the
///       product that are not free of VAR. If one of those terms is worthy
///       of report, that's great: return NIL. Otherwise, return T if we saw
///       at least two things (eg splitting an integral into a product of two
///       integrals)
///
///   (5) If the result is free of VAR, we're in a similar position to (1).
///
///   (6) Otherwise something interesting (and hopefully useful) has
///       happened. Return NIL to tell SININT to report it.
fn sum_of_intsp(ans : Value, var2 : Value) -> Value raise {
  if atom(ans) {
    // Result of integration should never be a constant other than zero.
    // If the result of integration is zero, it is either because:
    // 1) a subroutine inside integration failed and returned nil,
    //    and (mul 0 nil) yielded 0, meaning that the result is wrong, or
    // 2) the original integrand was actually zero - this is handled
    //    with a separate special case in sinint
    lbool(!eq(ans, var2))
  } else if mplusp(ans).truthy() {
    lbool(every(e => sum_of_intsp(e, var2).truthy(), cdr(ans)))
  } else if eq(caar(ans), q_p_integrate) {
    t
  } else if mtimesp(ans).truthy() {
    let mut int_factors = 0
    let mut found = false
    for factor in cdr(ans).iter() {
      if !freeof(var2, factor).truthy() {
        if sum_of_intsp(factor, var2).truthy() {
          int_factors += 1
        } else {
          found = true
          break
        }
      }
    }
    lbool(!(found || 2 <= int_factors))
  } else if freeof(var2, ans).truthy() {
    t
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// Stage I
// Implementation of Method 2: Integrate a summation

///|
fn intsum(form : Value, var2 : Value) -> Value raise {
  let expr = cadr(form)
  let idx = caddr(form)
  let ll = cadddr(form)
  let ul = car(cddddr(form))
  if !atom(var2) ||
    !free(idx, var2).truthy() ||
    !free(ll, var2).truthy() ||
    !free(ul, var2).truthy() {
    return mk(q_p_integrate, [form, var2])
  }
  let pair = partition(expr, var2, Fix(1L))
  if mexptp(cdr(pair)).truthy() && eq(caddr(pair), var2) {
    let val = maxima_substitute(ll, idx, cadddr(pair))
    if equal(val, Fix(-1L)) {
      return add2(
        integrator(maxima_substitute(ll, idx, expr), var2),
        intsum1(expr, idx, add2(Fix(1L), ll), ul, var2),
      )
    } else if mlsp(val, Fix(-1L)).truthy() {
      return mk(q_p_integrate, [form, var2])
    }
  }
  intsum1(expr, idx, ll, ul, var2)
}

///|
fn intsum1(
  expr : Value,
  idx : Value,
  ll : Value,
  ul : Value,
  var2 : Value,
) -> Value raise {
  assume(mk(q_mgeqp, [idx, ll])) |> ignore
  if !eq(ul, q_d_inf) {
    assume(mk(q_mgeqp, [ul, idx])) |> ignore
  }
  simplifya(mk(q_p_sum, [integrator(expr, var2), idx, ll, ul]), t)
}

///|
fn finds(x : Value) -> Value raise {
  if atom(x) {
    memq(x, sin__lit("(%log %integrate %atan)"))
  } else {
    let r = finds(car(x))
    if r.truthy() {
      r
    } else {
      finds(cdr(x))
    }
  }
}

// ---------------------------------------------------------------------------
// Stage II
// Implementation of Method 9:
// Rational function times a log or arctric function

///|
/// ratlog is called for an expression containing a log or arctrig function
/// The integrand is like log(x)*f'(x). To obtain the result the technique of
/// partial integration is applied: log(x)*f(x)-integrate(1/x*f(x),x)
///
/// Only called by intform.
fn ratlog(var2 : Value, form : Value) -> Value raise {
  let y = form
  let c = sin__as(q_c, y)
  let y = integrator(c, var2)
  if finds(y).truthy() {
    return Nil
  }
  let d = sdiff(sin__as(q_a, form), var2)
  let z = integrator(mul2_star(y, d), var2)
  let d = sin__as(q_a, form)
  simplify(mk(q_mplus, [mk(q_mtimes, [y, d]), mk(q_mtimes, [Fix(-1L), z])]))
}

///|
/// partial-integration is an extension of the algorithm of ratlog to support
/// the technique of partial integration for more cases. The integrand
/// is like g(x)*f'(x) and the result is g(x)*f(x)-integrate(g'(x)*f(x),x).
///
/// Adding integrals properties for elementary functions led to infinite
/// recursion with integrate(z*expintegral_shi(z),z). This was resolved by
/// limiting the recursion depth. *integrator-level* needs to be at least 3
/// to solve
///  o  integrate(expintegral_ei(1/sqrt(x)),x)
///  o  integrate(sqrt(z)*expintegral_li(z),z)
/// while a value of 4 causes testsuite regressions with
///  o  integrate(z*expintegral_shi(z),z)
fn partial_integration(form : Value, var2 : Value) -> Value raise {
  let g = cdr(assq(q_a, form)) // part g(x)
  let df = cdr(assq(q_c, form)) // part f'(x)
  let f = integrator(df, var2) // integrate f'(x) wrt var2
  if isinop(f, q_p_integrate).truthy() || // no result or
    isinop(f, caar(g)).truthy() || // g in result
    num_gt(symval(q_ear_integrator_level), Fix(3L)) {
    Nil // we return nil
  } else {
    // Build the result: g(x)*f(x)-integrate(g'(x)*f(x))
    add2(
      mul2(f, g),
      mul2(Fix(-1L), integrator(mul2(f, sdiff(g, var2)), var2)),
    )
  }
}

///|
/// returns t if argument of every trig operation in y matches arg,
/// optionally filtering by occurrence of VAR
fn every_trigarg_alike(y : Value, arg : Value, var_? : Value = Nil) -> Value raise {
  with_special(q_var, var_, () => if atom(y) {
    t
  } else if optrig(caar(y)).truthy() {
    lbool(
      (var_.truthy() && freevar2(cadr(y), var_).truthy()) ||
      alike1(arg, cadr(y)).truthy(),
    )
  } else {
    lbool(every(expr => every_trigarg_alike(expr, arg, var_=var_).truthy(), cdr(y)))
  })
}

///|
/// return argument of first trig operation encountered in y,
/// optionally filtering by occurrence of VAR
fn find_first_trigarg(y : Value, var_? : Value = Nil) -> Value raise {
  with_special(q_var, var_, () => if atom(y) {
    Nil
  } else if optrig(caar(y)).truthy() &&
    !(var_.truthy() && freevar2(cadr(y), var_).truthy()) {
    cadr(y)
  } else {
    some_value(expr => find_first_trigarg(expr, var_=var_), cdr(y))
  })
}

///|
/// return constant factor that makes elements of alist match elements of
/// blist or nil if no match found
/// (we could replace this using rat package to divide alist and blist)
fn matchsum(alist : Value, blist : Value, var2 : Value) -> Value raise {
  // find coeff for first term of alist
  let s = m2(
    car(alist),
    sin__pv("((mtimes) ((coefftt) (a freevar2 @var2)) ((coefftt) (c true)))", var2),
  )
  let cc = sin__as(q_c, s)
  // find coeff for first term of blist
  let r = m2(
    car(blist),
    cons(
      list1(q_mtimes),
      cons(sin__pv("((coefftt) (b free12 @var2))", var2), if mtimesp(cc).truthy() {
        cdr(cc)
      } else {
        list1(cc)
      }),
    ),
  )
  if r is Nil {
    return Nil
  }
  let dd = simplify(
    mk(q_mtimes, [subliss(s, q_a), mk(q_mexpt, [subliss(r, q_b), Fix(-1L)])]),
  )
  // check that all terms match
  if m2(cons(list1(q_mplus), alist), timesloop(dd, blist)).truthy() {
    dd
  } else {
    Nil
  }
}

///|
fn timesloop(a : Value, b : Value) -> Value raise {
  cons(list1(q_mplus), mapcar(c => mul2_star(a, c), b))
}

///|
fn expands(arg1 : Value, arg2 : Value) -> Value raise {
  addn(mapcar(c => timesloop(c, arg1), arg2), Nil)
}

///|
/// possibly a bug: For var2 = x and dd =3, we have
/// expand(?subst10(x^9 * (x+x^6))) --> x^5+x^4, but
/// ?subst10(expand(x^9 * (x+x^6))) --> x^5+x^3. (Barton Willis)
fn subst10(ex : Value, var2 : Value, dd : Value, new_var : Value) -> Value raise {
  if atom(ex) {
    ex
  } else if eq(caar(ex), q_mexpt) && eq(cadr(ex), var2) {
    mk(q_mexpt, [new_var, integerp2(quot(caddr(ex), dd))])
  } else {
    cons(
      remove(q_simp, car(ex)),
      mapcar(c => subst10(c, var2, dd, new_var), cdr(ex)),
    )
  }
}

///|
fn sin__rat10(ex : Value, var2 : Value, power_list : Ref[Value]) -> Value raise {
  if freevar2(ex, var2).truthy() {
    t
  } else if varp2(ex, var2).truthy() {
    Nil
  } else if eq(caar(ex), q_mexpt) {
    if varp2(cadr(ex), var2).truthy() {
      if integerp2(caddr(ex)).truthy() {
        power_list.val = cons(caddr(ex), power_list.val)
        power_list.val
      } else {
        Nil
      }
    } else {
      lbool(
        sin__rat10(cadr(ex), var2, power_list).truthy() &&
        sin__rat10(caddr(ex), var2, power_list).truthy(),
      )
    }
  } else if eq(caar(ex), q_mplus) || eq(caar(ex), q_mtimes) {
    for u in cdr(ex).iter() {
      if !sin__rat10(u, var2, power_list).truthy() {
        return Nil
      }
    }
    t
  } else {
    Nil
  }
}

///|
fn powerlist(expr : Value, var2 : Value) -> Value raise {
  let y = m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (var varp2 @var2) (c integerp2)) ((coefftt) (a freevar2 @var2)) ((coefftt) (b true)))",
      var2,
    ),
  )
  let bb = sin__as(q_b, y)
  let cc = sin__as(q_c, y)
  let power_list : Ref[Value] = Ref(Nil)
  if !sin__rat10(bb, var2, power_list).truthy() {
    return Nil
  }
  let mut dd = one_plus(cc)
  for p in power_list.val.iter() {
    dd = num_gcd(dd, p)
  }
  if power_list.val is Nil {
    dd = num_abs(dd)
  }
  if eql(Fix(1L), dd) || zerop(dd) {
    return Nil
  }
  let subst_expr = mk(q_mexpt, [var2, dd])
  let new_var = make_new_var(Str("powerlist"), expr=subst_expr)
  substint(
    subst_expr,
    new_var,
    integrate5(
      simplify(
        mk(q_mtimes, [
          power_star(dd, Fix(-1L)),
          sin__as(q_a, y),
          mk(q_mexpt, [new_var, one_minus(quot(one_plus(cc), dd))]),
          subst10(bb, var2, dd, new_var),
        ]),
      ),
      new_var,
    ),
    var2,
    expr,
  )
}

// ---------------------------------------------------------------------------
// Stage I
// Implementation of Method 3: Derivative-divides algorithm

///|
/// This is the derivative-divides algorithm of Moses.
///
///                /
///                [
/// Look for form  I  c * op(u(x)) * u'(x) dx
///                ]
///                /
///
///  where:  c     is a constant
///          u(x)  is an elementary expression in x
///          u'(x) is its derivative
///          op    is an elementary operator:
///                - the identity, or
///                - any function that can be integrated by INTEGRALLOOKUPS
///
/// The method of solution, once the problem has been determined to
/// posses the form above, is to look up OP in a table and substitute
/// u(x) for each occurrence of x in the expression given in the table.
/// In other words, the method performs an implicit substitution y = u(x),
/// and obtains the integral of op(y)dy by a table look up.
fn diffdiv(expr : Value, var2 : Value) -> Value raise {
  if mexptp(expr).truthy() &&
    mplusp(cadr(expr)).truthy() &&
    integerp(caddr(expr)) &&
    num_lt(caddr(expr), Fix(6L)) &&
    num_gt(caddr(expr), Fix(0L)) {
    return integrator(expandexpt(cadr(expr), caddr(expr)), var2)
  }
  // If not a product, transform to a product with one term
  let expr = if mtimesp(expr).truthy() { expr } else { mk(q_mtimes, [expr]) }
  // Loop over the terms in expr
  let mut z = cdr(expr)
  while true {
    // a
    let y = car(z)
    // This m2 pattern matches const*(exp/y)
    let r = list2(
      list1(q_mplus),
      cons(
        list1(q_coeffpt),
        cons(sin__pv("(c free12 @var2)", var2), sin__remove1(y, cdr(expr))),
      ),
    )
    // Case u(var2) is the identity function. y is a term in exp.
    // Match if diff(y,var2) == c*(exp/y).
    // This even works when y is a function with multiple args.
    let w = m2(sdiff(y, var2), r)
    if w.truthy() {
      return muln(
        list([y, y, power_star(mul2_star(Fix(2L), sin__as(q_c, w)), Fix(-1L))]),
        Nil,
      )
    }
    // w is the arg in y.
    let w = if atom(y) || eq(caar(y), q_mplus) || eq(caar(y), q_mtimes) {
      y
    } else if length(cdr(y)) == 1 {
      // Take the argument of a function with one value.
      cadr(y)
    } else {
      // A function has multiple args, and exactly one arg depends on var2
      let arg_freevar = mapcar(v => freevar2(v, var2), cdr(y))
      if count_if(x => x is Nil, arg_freevar) == 1 {
        let mut args = cdr(y)
        let mut argf = arg_freevar
        while !(car(argf) is Nil) {
          args = cdr(args)
          argf = cdr(argf)
        }
        car(args)
      } else {
        Fix(0L)
      }
    }
    let x = sdiff(w, var2)
    let mut dd : Value = Nil
    let mut v : Value = Nil
    let w = if x.truthy() &&
      mplusp(x).truthy() &&
      {
        dd = sin__remove1(y, cdr(expr))
        dd.truthy()
      } &&
      {
        v = car(dd)
        v.truthy()
      } &&
      mplusp(v).truthy() &&
      cdr(dd) is Nil {
      dd = matchsum(cdr(x), cdr(v), var2)
      if dd.truthy() {
        list1(cons(q_c, dd))
      } else {
        Nil
      }
    } else {
      m2(x, r)
    }
    if w.truthy() {
      let x = integrallookups(y, var2)
      return if x is Nil {
        Nil
      } else if eq(w, t) {
        x
      } else {
        mul2_star(x, power_star(sin__as(q_c, w), Fix(-1L)))
      }
    }
    z = cdr(z)
    if z is Nil {
      return Nil
    }
  }
  Nil
}

///|
/// Alist is an alist consisting of a variable (symbol) and its value.  expr
/// is an expression.  For each entry in alist, substitute the corresponding
/// value into expr.
fn subliss(alist : Value, expr : Value) -> Value raise {
  let mut x = expr
  for a in alist.iter() {
    x = maxima_substitute(cdr(a), car(a), x)
  }
  x
}

///|
fn substint(
  x : Value,
  y : Value,
  expres : Value,
  var2 : Value,
  expr : Value,
) -> Value raise {
  if !atom(expres) && eq(caar(expres), q_p_integrate) {
    list3(car(expres), expr, var2)
  } else {
    substint1(maxima_substitute(x, y, expres), var2)
  }
}

///|
fn substint1(expr : Value, var2 : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if eq(caar(expr), q_p_integrate) &&
    cdddr(expr) is Nil &&
    !symbolp(caddr(expr)) &&
    !free(caddr(expr), var2).truthy() {
    simplify(
      mk(q_p_integrate, [mul2(cadr(expr), sdiff(caddr(expr), var2)), var2]),
    )
  } else {
    recur_apply(lfunc("substint1", args => substint1(arg(args, 0), var2)), expr)
  }
}
