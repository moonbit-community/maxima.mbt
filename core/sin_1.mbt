// Port of src/sin.lisp (part 1): the SIN heuristic integrator of Moses.
//
// Reference:  J. Moses, Symbolic Integration, MIT-LCS-TR-047, 12-1-1967.
// http://www.lcs.mit.edu/publications/pubs/pdf/MIT-LCS-TR-047.pdf.
//
// Part 1: predicates, INTFORM and INTEGRATOR (stage II and the main
// routine), SEPARC, the basic m2 patterns, stage I helpers, integral
// lookups, Method 1 (SUPEREXPT) and Method 3 (RATROOT).

// ---------------------------------------------------------------------------
// Pattern data.  Patterns are written as quoted Lisp text exactly as in the
// source; backquote insertions are placeholder symbols (`@var2`, `@expres`,
// `@op`, `@newvar`, `@trigarg`, `@offset`) replaced by `subst`.

///|
let sin__pat_cache : Map[String, Value] = {}

///|
/// Parse (once) the pattern text and substitute the placeholders.
fn sin__pat(src : String, subs : Array[(String, Value)]) -> Value raise {
  let tmpl = match sin__pat_cache.get(src) {
    Some(v) => v
    None => {
      let v = lread(src)
      sin__pat_cache[src] = v
      v
    }
  }
  let mut r = tmpl
  for s in subs {
    r = subst(s.1, sym(s.0), r)
  }
  r
}

///|
/// A quoted constant (shared, never to be mutated).
fn sin__lit(src : String) -> Value raise {
  sin__pat(src, [])
}

///|
/// A backquoted pattern whose only insertion is VAR2.
fn sin__pv(src : String, var2 : Value) -> Value raise {
  sin__pat(src, [("@var2", var2)])
}

///|
/// `(cdr (assoc key alist :test #'eq))`
fn sin__as(key : Value, alist : Value) -> Value {
  cdr(assq(key, alist))
}

///|
/// `(gensym prefix)` for a Lisp string prefix: CL names are upcased when
/// printed by Maxima, which is the port's case inversion.
fn sin__gensym(prefix : Value) -> Value {
  match prefix {
    Str(s) => gensym(prefix=invert_case(s))
    _ => gensym()
  }
}

///|
fn sin__debug() -> Bool {
  symval(q_ear_debug_integrate).truthy()
}

///|
/// `(remove item list :count 1)`
fn sin__remove1(item : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut done = false
  for x in l.iter() {
    if !done && eql(x, item) {
      done = true
    } else {
      c.add(x)
    }
  }
  c.result()
}

// ---------------------------------------------------------------------------
// Predicate functions

///|
/// This predicate is used with m2 pattern matcher.
/// A rational expression in var2.
fn rat8(ex : Value, var2 : Value) -> Value raise {
  if varp2(ex, var2).truthy() || freevar2(ex, var2).truthy() {
    t
  } else if eq(caar(ex), q_mplus) || eq(caar(ex), q_mtimes) {
    for u in cdr(ex).iter() {
      if !rat8(u, var2).truthy() {
        return Nil
      }
    }
    t
  } else if !eq(caar(ex), q_mexpt) {
    Nil
  } else if integerp(caddr(ex)) {
    rat8(cadr(ex), var2)
  } else {
    Nil
  }
}

///|
/// Predicate for m2 pattern matcher
fn rat8prime(c : Value, var2 : Value) -> Value raise {
  lbool(
    rat8(c, var2).truthy() && (!mnump(c).truthy() || !zerop1(c).truthy()),
  )
}

///|
/// Predicate for m2 patter matcher
fn elem(a : Value, expres : Value, var2 : Value) -> Value raise {
  if freevar2(a, var2).truthy() {
    t
  } else if atom(a) {
    Nil
  } else if m2(a, expres).truthy() {
    t
  } else {
    lbool(every(f => elem(f, expres, var2).truthy(), cdr(a)))
  }
}

///|
/// Like freevar0 (in hypgeo.lisp), but we take a second arg to specify
/// the variable instead of implicitly using VAR.
fn freevar02(m : Value, var2 : Value) -> Value raise {
  if equal(m, Fix(0L)) {
    Nil
  } else {
    freevar2(m, var2)
  }
}

///|
/// Like free1 in schatc, but takes an extra arg for the variable.
fn free12(a : Value, var2 : Value) -> Value raise {
  if pzerop(a) is Nil {
    free(a, var2)
  } else {
    Nil
  }
}

///|
fn rationalizer(x : Value) -> Value raise {
  let ex = simplify(d_factor(x))
  if !alike1(ex, x).truthy() {
    ex
  } else {
    Nil
  }
}

///|
fn expand_base_of_exp(e : Value, x : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if mexptp(e).truthy() && !freeof(x, e).truthy() {
    ftake(q_mexpt, [
      d_expand(second(e), expop=Fix(1L), expon=Fix(0L)),
      third(e),
    ])
  } else {
    recur_apply(
      lfunc("expand-base-of-exp", args => expand_base_of_exp(arg(args, 0), x)),
      e,
    )
  }
}

// ---------------------------------------------------------------------------
// Stage II of the Integrator
//
// Check if the problem can be transformed or solved by special methods.
// 11 Methods are implemented by Moses, some more have been added.
//
// POWERL is initialized in INTEGRATOR to NIL and can be modified in
// INTFORM in certain cases and is read by INTEGRATOR in some cases.
// Instead of a global special variable, the Lisp code uses a closure.

///|
let sin__powerl : Ref[Value] = Ref(Nil)

///|
fn sin__exp() -> Value {
  symval(q_ear_exp)
}

///|
fn intform(expres : Value, var2 : Value) -> Value raise {
  if freevar2(expres, var2).truthy() {
    return Nil
  }
  if atom(expres) {
    return Nil
  }
  let op = caar(expres)
  // Map the function intform over the arguments of a sum or a product
  if eq(op, q_mplus) || eq(op, q_mtimes) {
    return some_value(ex => intform(ex, var2), cdr(expres))
  }
  if eq(op, q_p_log) || arcp(op).truthy() {
    // Method 9: Rational function times a log or arctric function
    let arg = m2(
      sin__exp(),
      sin__pat(
        "((mtimes) ((@op) (b rat8 @var2)) ((coefftt) (c rat8prime @var2)))",
        [("@op", op), ("@var2", var2)],
      ),
    )
    if arg.truthy() {
      // Integrand is of the form R(x)*F(S(x)) where F is a log, or
      // arctric function and R(x) and S(x) are rational functions.
      return ratlog(var2, cons(cons(q_a, expres), arg))
    }
    let y = intform(cadr(expres), var2)
    if y.truthy() {
      return y
    }
    // Method 10: Rational function times log(b*x+a)
    if eq(op, q_p_log) {
      let z = m2_b_starx_plusa(cadr(expres), var2)
      if z.truthy() {
        let y = m2(
          sin__exp(),
          sin__pat(
            "((mtimes) ((coefftt) (c rat8 @var2)) ((coefftt) (d elem @expres @var2)))",
            [("@expres", expres), ("@var2", var2)],
          ),
        )
        if y.truthy() {
          let a = sin__as(q_a, z)
          let b = sin__as(q_b, z)
          let c = sin__as(q_c, y)
          let d = sin__as(q_d, y)
          let newvar = make_new_var(Str("intform"), expr=expres)
          // Substitute y = log(b*x+a) and integrate again
          let integrand = muln(
            list([
              maxima_substitute(
                mk(q_mquotient, [
                  mk(q_mplus, [
                    mk(q_mexpt, [q_d__pcte, newvar]),
                    mk(q_mtimes, [Fix(-1L), a]),
                  ]),
                  b,
                ]),
                var2,
                c,
              ),
              mk(q_mquotient, [mk(q_mexpt, [q_d__pcte, newvar]), b]),
              maxima_substitute(newvar, expres, d),
            ]),
            Nil,
          )
          return substint(
            expres,
            newvar,
            integrator(integrand, newvar),
            var2,
            sin__exp(),
          )
        }
      }
    }
    return Nil
  }
  // We have a special function with an integral on the property list.
  // After the integral property was defined for the trig functions,
  // in rev 1.52, need to exclude trig functions here.
  if !atom(car(expres)) &&
    !optrig(op).truthy() &&
    !eq(op, q_mexpt) &&
    get(op, q_integral).truthy() {
    if sin__debug() {
      format(t, "~&INTFORM: found 'INTEGRAL on property list~%", []) |> ignore
    }
    let arg = m2(
      sin__exp(),
      sin__pat(
        "((mtimes) ((@op) (b rat8 @var2)) ((coefftt) (c rat8prime @var2)))",
        [("@op", op), ("@var2", var2)],
      ),
    )
    if arg.truthy() {
      // A rational function times the special function.
      // Integrate with the method integration-by-parts.
      return partial_integration(cons(cons(q_a, expres), arg), var2)
    }
    // The method of integration-by-parts can not be applied.
    // Maxima tries to get a clue for the argument of the function which
    // allows a substitution for the argument.
    let r = intform(cadr(expres), var2)
    if r.truthy() {
      return r
    }
    return Nil
  }
  // Method 6: Elementary function of trigonometric functions
  if optrig(op).truthy() {
    let w = m2_b_starx_plusa(cadr(expres), var2)
    if w is Nil {
      return intform(cadr(expres), var2)
    } else {
      sin__powerl.val = t
      return monstertrig(sin__exp(), var2, cadr(expres))
    }
  }
  if eq(op, q_p_derivative) && eq(caar(sin__exp()), op) {
    let r = checkderiv(sin__exp(), var2)
    if r.truthy() {
      return r
    }
  }
  // Stop intform if we have not a power function.
  if !eq(op, q_mexpt) {
    return Nil
  }
  // Method 2: Substitution for an integral power
  if integerp(caddr(expres)) {
    return intform(cadr(expres), var2)
  }
  // Method 1: Elementary function of exponentials
  if freevar2(cadr(expres), var2).truthy() {
    let w = m2_b_starx_plusa(caddr(expres), var2)
    if w.truthy() {
      let ans = superexpt(sin__exp(), var2, cadr(expres), w)
      if ans.truthy() && freeof(q_p_integrate, ans).truthy() {
        return ans
      }
    }
    let r = intform(caddr(expres), var2)
    if r.truthy() {
      return r
    }
    if eq(q_d__pcte, cadr(expres)) && isinop(caddr(expres), q_p_log).truthy() {
      // Found something like exp(r*log(x))
      return with_specials(
        [(q_d__pcte_to_numlog, t), (q_d_radexpand, Nil)], // do not simplify sqrt(x^2) -> abs(x)
        () => {
          let nexp = resimplify(sin__exp())
          if alike1(sin__exp(), nexp).truthy() {
            Nil
          } else {
            set(q_ear_exp, nexp) |> ignore
            integrator(nexp, var2)
          }
        },
      )
    }
    return Nil
  }
  // The base is not a rational function. Try to get a clue for the base.
  if !rat8(cadr(expres), var2).truthy() {
    return intform(cadr(expres), var2)
  }
  // Method 3: Substitution for a rational root
  let w = m2_ratrootform(cadr(expres), var2) // e*(a*x+b) / (c*x+d)
  if w.truthy() && denomfind(caddr(expres)).truthy() { // expon is ratnum
    sin__powerl.val = t
    let r = ratroot(sin__exp(), var2, cadr(expres), w)
    if r.truthy() {
      return r
    }
    return inte(sin__exp(), var2)
  }
  // Method 4: Binomial - Chebyschev
  if !integerp1(caddr(expres)).truthy() { // 2*exponent not integer
    if m2_chebyform(sin__exp(), var2).truthy() {
      return chebyf(sin__exp(), var2)
    } else {
      return intform(cadr(expres), var2)
    }
  }
  // Method 5: Arctrigonometric substitution
  if m2_c_starx_hat2_plusb_starx_plusa(cadr(expres), var2).truthy() { // sqrt(c*x^2+b*x+a)
    // I think this is method 5, arctrigonometric substitutions.
    // (Moses, pg 80.)  The integrand is of the form
    // R(x,sqrt(c*x^2+b*x+a)).  This method first eliminates the b
    // term of the quadratic, and then uses an arctrig substitution.
    return inte(sin__exp(), var2)
  }
  // Method 4: Binomial - Chebyschev
  if m2_chebyform(sin__exp(), var2).truthy() {
    return chebyf(sin__exp(), var2)
  }
  // Expand expres.
  // Substitute the expanded factor into the integrand and try again.
  let w = d_expand(cadr(expres))
  if !m2(w, cadr(expres)).truthy() {
    set(q_ear_exp, maxima_substitute(w, cadr(expres), sin__exp())) |> ignore
    return intform(simplify(mk(q_mexpt, [w, caddr(expres)])), var2)
  }
  // Factor expres.
  // Substitute the factored factor into the integrand and try again.
  let w = rationalizer(cadr(expres))
  if w.truthy() {
    // The forms below used to have $radexpand set to $all.  But I
    // don't think we really want to do that here because that makes
    // sqrt(x^2) become x, which might be totally wrong.  This is one
    // reason why we returned -4/3 for the
    // integrate(sqrt(x+1/x-2),x,0,1).  We were replacing
    // sqrt((x-1)^2) with x - 1, which is totally wrong since 0 <= x
    // <= 1.
    let e = with_special(q_d_radexpand, symval(q_d_radexpand), () => maxima_substitute(
      w,
      cadr(expres),
      sin__exp(),
    ))
    set(q_ear_exp, e) |> ignore
    return intform(
      with_special(q_d_radexpand, q_d_all, () => simplify(
        mk(q_mexpt, [w, caddr(expres)]),
      )),
      var2,
    )
  }
  Nil
}

///|
/// This is the main integration routine.  It is called from sinint.
fn integrator(
  ear_exp : Value,
  var2 : Value,
  stack? : Value = Nil,
) -> Value raise {
  let b1 = bind(q_ear_exp, ear_exp)
  defer unbind(b1)
  let b2 = bind(q_ear_risch_use_triginv_all, Nil)
  defer unbind(b2)
  sin__powerl.val = Nil
  // Increment recursion counter
  set(q_ear_integrator_level, num_add(symval(q_ear_integrator_level), Fix(1L)))
  |> ignore
  // Trivial case. exp is not a function of var2.
  if freevar2(sin__exp(), var2).truthy() {
    return mul2_star(sin__exp(), var2)
  }
  // Remove constant factors
  let mut w = partition(sin__exp(), var2, Fix(1L))
  let const_ = car(w)
  set(q_ear_exp, cdr(w)) |> ignore
  // First stage, Method I: Integrate a sum.
  if mplusp(sin__exp()).truthy() {
    return mul2_star(const_, integrate1(cdr(sin__exp()), var2))
  }
  // Convert atan2(a,b) to atan(a/b) and try again.
  w = isinop(sin__exp(), q_p_atan2)
  if w.truthy() {
    set(
      q_ear_exp,
      maxima_substitute(
        take(list1(q_p_atan), [div(cadr(w), caddr(w))]),
        w,
        sin__exp(),
      ),
    )
    |> ignore
    return mul2_star(const_, integrator(sin__exp(), var2, stack=stack))
  }
  // First stage, Method II: Integrate sums.
  if !atom(sin__exp()) && eq(caar(sin__exp()), q_p_sum) {
    return mul2_star(const_, intsum(sin__exp(), var2))
  }
  // First stage, Method III: Try derivative-divides method.
  // This is the workhorse that solves many integrals.
  let mut y = diffdiv(sin__exp(), var2)
  if y.truthy() {
    return mul2_star(const_, y)
  }
  // At this point, we have EXP as a product of terms.  Make Y a
  // list of the terms of the product.
  y = if mtimesp(sin__exp()).truthy() {
    cdr(sin__exp())
  } else {
    list1(sin__exp())
  }
  // Second stage:
  // We're looking at each term of the product and check if we can
  // apply one of the special methods.
  let mut result : Value = Nil
  while true {
    // loop
    if !rat8(car(y), var2).truthy() {
      w = intform(car(y), var2)
      if w.truthy() {
        // Do not return a noun form as result at this point, because
        // we would like to check for further special integrals.
        // We store the result for later use.
        result = w
        if !isinop(w, q_p_integrate).truthy() {
          return mul2_star(const_, w)
        }
      }
      // Store a possible partial result
      result = w
      break // go special
    }
    // skip
    y = cdr(y)
    if y is Nil {
      // Method 8: Rational functions
      let pl = powerlist(sin__exp(), var2)
      return mul2_star(const_, if pl.truthy() {
        pl
      } else {
        ratint(sin__exp(), var2)
      })
    }
  }
  // special
  // Third stage: Try more general methods

  // SEPARC SETQS ARCPART AND COEF SUCH THAT
  // COEF*ARCEXP=EXP WHERE ARCEXP IS OF THE FORM
  // ARCFUNC^N AND COEF IS ITS ALGEBRAIC COEFFICIENT
  let (arcpart, coef) = separc_mv(sin__exp())
  let mut integrand : Value = Nil
  let ok = arcpart.truthy() &&
    !member_if(s => alike1(s, coef).truthy(), stack).truthy() &&
    {
      w = integrator(coef, var2, stack=cons(coef, stack))
      !isinop(w, q_p_integrate).truthy()
    } &&
    {
      integrand = mul2(w, sdiff(arcpart, var2))
      integrand.truthy()
    } &&
    !member_if(s => alike1(s, integrand).truthy(), stack).truthy() &&
    {
      let integ = integrand
      y = integrator(integ, var2, stack=cons(integrand, stack))
      !isinop(y, q_p_integrate).truthy()
    }
  if ok {
    return add2_star(
      mk(q_mtimes, [const_, w, arcpart]),
      mk(q_mtimes, [Fix(-1L), const_, y]),
    )
  }
  let r = {
    y = scep(sin__exp(), var2)
    if y.truthy() {
      if cddr(y).truthy() {
        integrator(d_trigreduce(sin__exp()), var2, stack=stack)
      } else {
        sce_int(car(y), cadr(y), var2)
      }
    } else if num_lt(symval(q_ear_integrator_level), Fix(4L)) &&
      {
        y = d_expand(sin__exp())
        !alike1(sin__exp(), y).truthy()
      } {
      // I don't understand why we do this. This
      // causes the stack overflow in Bug
      // 1487703, because we keep expanding *exp*
      // into a form that matches the original
      // and therefore we loop forever.  To
      // break this we keep track how how many
      // times we've tried this and give up
      // after 4 (arbitrarily selected) times.
      integrator(y, var2, stack=stack)
    } else if !sin__powerl.val.truthy() &&
      {
        y = powerlist(sin__exp(), var2)
        y.truthy()
      } {
      y
    } else if !symval(q_ear_in_risch_p).truthy() && // Not called from rischint
      {
        // Call RISCHINT, dynamically binding $TRIGINVERSES to
        // '$ALL if we earlier remembered to do so.
        let ti = if symval(q_ear_risch_use_triginv_all).truthy() {
          q_d_all
        } else {
          symval(q_d_triginverses)
        }
        y = with_special(q_d_triginverses, ti, () => rischint(
          sin__exp(),
          var2,
        ))
        y.truthy()
      } &&
      {
        // rischint has not found an integral but
        // returns a noun form. Do not return that
        // noun form as result at this point, but
        // store it for later use.
        result = y
        result.truthy()
      } &&
      !isinop(y, q_p_integrate).truthy() {
      y
    } else if {
        y = integrate_exp_special(sin__exp(), var2)
        y.truthy()
      } {
      // Maxima found an integral for a power function
      y
    } else if result.truthy() {
      // Integrate-exp-special has not found an integral
      // We look for a previous result obtained by
      // intform or rischint.
      result
    } else {
      mk(q_p_integrate, [sin__exp(), var2])
    }
  }
  mul2_star(const_, r)
}

///|
fn separc_mv(ex : Value) -> (Value, Value) raise {
  let arcpart : Ref[Value] = Ref(Nil)
  let coef : Ref[Value] = Ref(Nil)
  if sin__arcfuncp(ex) {
    arcpart.val = ex
    coef.val = Fix(1L)
  } else if consp(ex) && eq(caar(ex), q_mtimes) {
    sin__arclist(cdr(ex), arcpart, coef) |> ignore
    coef.val = if cdr(coef.val) is Nil {
      car(coef.val)
    } else {
      coef.val = cons(car(ex), nreverse(coef.val))
      coef.val
    }
  }
  (arcpart.val, coef.val)
}

///|
fn sin__arcfuncp(ex : Value) -> Bool raise {
  !atom(ex) &&
  (
    arcp(caar(ex)).truthy() ||
    eq(caar(ex), q_p_log) || // Experimentally treat logs also.
    (
      eq(caar(ex), q_mexpt) &&
      integerp2(caddr(ex)).truthy() &&
      num_gt(integerp2(caddr(ex)), Fix(0L)) &&
      sin__arcfuncp(cadr(ex))
    )
  )
}

///|
fn sin__arclist(
  l : Value,
  arcpart : Ref[Value],
  coef : Ref[Value],
) -> Value raise {
  if l is Nil {
    Nil
  } else if sin__arcfuncp(car(l)) && arcpart.val is Nil {
    arcpart.val = car(l)
    sin__arclist(cdr(l), arcpart, coef)
  } else {
    coef.val = cons(car(l), coef.val)
    sin__arclist(cdr(l), arcpart, coef)
  }
}

///|
fn separc(ex : Value) -> Value raise {
  separc_mv(ex).0
}

// ---------------------------------------------------------------------------
// Five pattern for the Integrator and other routines.

///|
/// This is matching the pattern e*(a*x+b)/(c*x+d), where
/// a, b, c, d, and e are free of x, and x is the variable of integration.
fn m2_ratrootform(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((coefftt) (e freevar2 @var2)) ((mplus) ((coeffpt) (a freevar2 @var2) (var varp2 @var2)) ((coeffpt) (b freevar2 @var2))) ((mexpt) ((mplus) ((coeffpt) (c freevar2 @var2) (var varp2 @var2)) ((coeffpt) (d freevar2 @var2))) -1))",
      var2,
    ),
  )
}

///|
/// This is for matching the pattern a*x^r1*(c1+c2*x^q)^r2.
fn m2_chebyform(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (var varp2 @var2) (r1 numberp)) ((mexpt) ((mplus) ((mtimes) ((coefftt) (c2 freevar2 @var2)) ((mexpt) (var varp2 @var2) (q free12 @var2))) ((coeffpp) (c1 freevar2 @var2))) (r2 numberp)) ((coefftt) (a freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Pattern to match b*x + a
fn m2_b_starx_plusa(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mplus) ((coeffpt) (b freevar2 @var2) (x varp2 @var2)) ((coeffpt) (a freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// This is the pattern c*x^2 + b * x + a.
fn m2_c_starx_hat2_plusb_starx_plusa(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mplus) ((coeffpt) (c freevar2 @var2) ((mexpt) (x varp2 @var2) 2)) ((coeffpt) (b freevar2 @var2) (x varp2 @var2)) ((coeffpt) (a freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// This is the pattern (a*x+b)*(c*x+d)
/// NOTE:  This doesn't seem to be used anywhere in Maxima.
fn m2_a_starx_plusb_slc_starx_plusd(expr : Value) -> Value raise {
  m2(
    expr,
    sin__lit(
      "((mtimes) ((mplus) ((coeffpt) (a freevar) (var varp)) ((coeffpt) (b freevar))) ((mplus) ((coeffpt) (c freevar) (var varp)) ((coeffpt) (d freevar))))",
    ),
  )
}

///|
fn optrig(x : Value) -> Value raise {
  memq(x, sin__lit("(%sin %cos %sec %tan %csc %cot)"))
}

// ---------------------------------------------------------------------------
// Stage I
// Implementation of Method 1: Integrate a sum

///|
/// after finding a non-integrable summand usually better to pass rest to risch
fn integrate1(expr : Value, var2 : Value) -> Value raise {
  let mut terms = expr
  let mut ans : Value = Nil
  while !(terms is Nil) {
    // don't gen li's for parts of integrand
    let term = car(terms)
    ans = cons(
      with_special(q_d_liflag, Nil, () => integrator(term, var2)),
      ans,
    )
    if !symval(q_ear_in_risch_p).truthy() && // Not called from rischint
      !free(car(ans), q_p_integrate).truthy() &&
      cdr(terms).truthy() {
      return addn(
        cons(rischint(cons(list1(q_mplus), terms), var2), cdr(ans)),
        Nil,
      )
    }
    terms = cdr(terms)
  }
  addn(ans, Nil)
}

///|
/// Product of SIN, COS, EXP of linear args.
fn scep(expr : Value, var2 : Value) -> Value raise {
  let mut trigl : Value = Nil
  let mut ex : Value = Nil
  if !mtimesp(expr).truthy() {
    return Nil
  }
  for fac in cdr(expr).iter() {
    if atom(fac) {
      return Nil
    } else if trig1(car(fac)).truthy() {
      if linearp(cadr(fac), var2).truthy() {
        trigl = cons(fac, trigl)
      } else {
        return Nil
      }
    } else if mexptp(fac).truthy() &&
      eq(cadr(fac), q_d__pcte) &&
      linearp(caddr(fac), var2).truthy() {
      // should be only one exponential factor
      ex = fac
    } else {
      return Nil
    }
  }
  cons(ex, trigl)
}

///|
/// Integrates exponential * sin or cos, all with linear args.
/// EXP is non-trivial.
fn sce_int(expr : Value, s_c : Value, var2 : Value) -> Value raise {
  let e_coef = car(islinear(caddr(expr), var2))
  let sc_coef = car(islinear(cadr(s_c), var2))
  let sc_arg = cadr(s_c)
  let abs_val = add2(power(e_coef, Fix(2L)), power(sc_coef, Fix(2L)))
  if zerop1(abs_val).truthy() {
    // The numerator is zero. Exponentialize the integrand and try again.
    integrator(d_exponentialize(mul2(expr, s_c)), var2)
  } else {
    mul2(
      div(expr, abs_val),
      add2(mul2(e_coef, s_c), if eq(caar(s_c), q_p_sin) {
        mul2_star(neg(sc_coef), mk(q_p_cos, [sc_arg]))
      } else {
        mul2_star(sc_coef, mk(q_p_sin, [sc_arg]))
      }),
    )
  }
}

///|
fn checkderiv(expr : Value, var2 : Value) -> Value raise {
  checkderiv1(cadr(expr), cddr(expr), Nil, var2)
}

///|
/// CHECKDERIV1 gets called on the expression being differentiated,
/// an alternating list of variables being differentiated with
/// respect to and powers thereof, and a reversed list of the latter
/// that have already been examined.  It returns either the antiderivative
/// or (), saying this derivative isn't wrt the variable of integration.
fn checkderiv1(
  expr : Value,
  wrt : Value,
  old_wrt : Value,
  var2 : Value,
) -> Value raise {
  if varp2(car(wrt), var2).truthy() {
    if equal(cadr(wrt), Fix(1L)) { // Power = 1?
      if cddr(wrt) is Nil { // single or partial
        if old_wrt is Nil {
          expr // single
        } else {
          // partial in old-wrt
          cons(list1(q_p_derivative), cons(expr, nreverse(old_wrt)))
        }
      } else {
        // Partial, return rest
        cons(
          list1(q_p_derivative),
          cons(expr, nconc(nreverse(old_wrt), cddr(wrt))),
        )
      }
    } else {
      // Higher order, reduce order
      let rev = nreverse(old_wrt)
      let lower = add2_star(cadr(wrt), Fix(-1L))
      cons(
        list1(q_p_derivative),
        cons(expr, nconc(rev, cons(car(wrt), cons(lower, cddr(wrt))))),
      )
    }
  } else if cddr(wrt) is Nil {
    Nil // Say it doesn't apply here
  } else {
    // Else we check later terms
    checkderiv1(
      expr,
      cddr(wrt),
      cons(cadr(wrt), cons(car(wrt), old_wrt)),
      var2,
    )
  }
}

///|
fn integrallookups(expr : Value, var2 : Value) -> Value raise {
  if eq(caar(expr), q_mqapply) {
    // Transform to functional form and try again.
    // For example:
    // ((MQAPPLY SIMP) (($PSI SIMP ARRAY) 1) $X)
    // => (($PSI) 1 $X)
    return integrallookups(
      cons(list1(caaadr(expr)), append(cdadr(expr), cddr(expr))),
      var2,
    )
  }
  // Lookup algorithm for integral of a special function.
  // The integral form is put on the property list, and can be a
  // lisp function of the args.  If the form is nil, or evaluates
  // to nil, then return noun form unevaluated.
  if !atom(car(expr)) {
    let mut form = get(caar(expr), q_integral)
    if form.truthy() {
      let dummy_args = car(form)
      if dummy_args.truthy() {
        let real_args = cdr(expr)
        if real_args.truthy() {
          // search through the args of expr and find the arg containing var2
          // look up the integral wrt this arg from form
          form = {
            let mut x = real_args
            let mut y = cdr(form)
            let mut found : Value = Nil
            while !(x is Nil || y is Nil) {
              if !freevar2(car(x), var2).truthy() {
                found = car(y)
                break
              }
              x = cdr(x)
              y = cdr(y)
            }
            found
          }
          // If form is a function then evaluate it with actual args
          if form.truthy() &&
            (
              !functionp_(form).truthy() ||
              {
                form = apply(form, real_args)
                form.truthy()
              }
            ) {
            if sin__debug() {
              format(t, "~&INTEGRALLOOKUPS: Found integral ~A.~%", [caar(expr)])
              |> ignore
            }
            return substitutel(real_args, dummy_args, form)
          }
        }
      }
    }
  }
  if eq(caar(expr), q_mplus) {
    return muln(list([mk_simp(q_rat, [Fix(1L), Fix(2L)]), expr, expr]), Nil)
  }
  Nil
}

///|
/// Define a little helper function to be used in antiderivatives.
/// Depending on the logabs flag and whether x can be non-real,
/// it either returns log(x) or log(abs(x)).
fn log_or_logabs(x : Value) -> Value raise {
  let x = if symval(q_d_logabs).truthy() &&
    memq(d_csign(x), list([q_d_complex, q_d_imaginary])) is Nil {
    ftake(q_mabs, [x])
  } else {
    x
  }
  ftake(q_p_log, [x])
}

///|
/// Define the antiderivative of tan(x), taking logabs into account.
fn integrate_tan(x : Value) -> Value raise {
  log_or_logabs(take(list1(q_p_sec), [x]))
}

///|
/// ... the same for csc(x) ...
fn integrate_csc(x : Value) -> Value raise {
  mul2(
    Fix(-1L),
    log_or_logabs(add2(take(list1(q_p_csc), [x]), take(list1(q_p_cot), [x]))),
  )
}

///|
/// ... the same for sec(x) ...
fn integrate_sec(x : Value) -> Value raise {
  log_or_logabs(add2(take(list1(q_p_sec), [x]), take(list1(q_p_tan), [x])))
}

///|
/// ... the same for cot(x) ...
fn integrate_cot(x : Value) -> Value raise {
  log_or_logabs(take(list1(q_p_sin), [x]))
}

///|
/// ... the same for coth(x) ...
fn integrate_coth(x : Value) -> Value raise {
  log_or_logabs(take(list1(q_p_sinh), [x]))
}

///|
/// ... the same for csch(x) ...
fn integrate_csch(x : Value) -> Value raise {
  log_or_logabs(
    take(list1(q_p_tanh), [mul2(mk_simp(q_rat, [Fix(1L), Fix(2L)]), x)]),
  )
}

///|
/// ... the same for acoth(x) ...
fn integrate_acoth(x : Value) -> Value raise {
  add2(
    mul2(x, ftake(q_p_acoth, [x])),
    mul2(
      mk_simp(q_rat, [Fix(1L), Fix(2L)]),
      log_or_logabs(sub(power(x, Fix(2L)), Fix(1L))),
    ),
  )
}

///|
/// integrate(x^n,x) = if n # -1 then x^(n+1)/(n+1) else log-or-logabs(x).
fn integrate_mexpt_1(x : Value, n : Value) -> Value raise {
  let n_is_minus_one = d_askequal(n, Fix(-1L))
  if eq(q_d_yes, n_is_minus_one) {
    log_or_logabs(x)
  } else {
    let n = add2(n, Fix(1L))
    div(take(list1(q_mexpt), [x, n]), n)
  }
}

///|
/// integrate(a^x,x) = a^x/log(a).
fn integrate_mexpt_2(a : Value, x : Value) -> Value raise {
  div(take(list1(q_mexpt), [a, x]), take(list1(q_p_log), [a]))
}

///|
fn integrate5(ex : Value, var2 : Value) -> Value raise {
  if rat8(ex, var2).truthy() {
    ratint(ex, var2)
  } else {
    integrator(ex, var2)
  }
}

///|
fn denomfind(x : Value) -> Value raise {
  if ratnump(x).truthy() {
    caddr(x)
  } else if !numberp(x) {
    Nil
  } else if !floatp(x) {
    Fix(1L)
  } else {
    cdr(maxima_rationalize(x))
  }
}

///|
/// Generates and prepares a symbol to be used as the new variable when
/// performing a substitution for the expression EXPR. Preparation includes:
/// - adding the 'INTERNAL property (so that no questions are asked about it),
/// - adding an assumption that the new variable is MEQUAL to EXPR, if EXPR
///   is non-NIL,
/// - adding a declaration that the new variable is '$COMPLEX/'$IMAGINARY if
///   EXPR's sign, as determined by $CSIGN, is '$COMPLEX/'$IMAGINARY, or
///   adding an assumption about the new variable's sign.
fn make_new_var(prefix : Value, expr? : Value = Nil) -> Value raise {
  let expr = simplify(expr)
  let new_var = sin__gensym(prefix)
  putprop(new_var, t, q_internal) |> ignore
  if expr.truthy() {
    assume(ftake(q_d_equal, [new_var, expr])) |> ignore
    let expr_sign = d_csign(expr)
    if memq(expr_sign, list([q_d_complex, q_d_imaginary])).truthy() {
      declare1(list1(new_var), t, expr_sign, q_kind) |> ignore
    } else {
      // The following code only ensures that NEW-VAR gets the sign of EXPR.
      // It would be much better to preserve any known lower/upper bounds,
      // e.g. if EXPR = log(x) and we know that 2 < x < 3, then assume that
      // log(2) < NEW-VAR < log(3).
      // Note that nothing of this would be necessary if SIGN made more use
      // of $EQUAL facts.
      let rel = if eq(expr_sign, q_d_pos) {
        q_mgreaterp
      } else if eq(expr_sign, q_d_pz) {
        q_mgeqp
      } else if eq(expr_sign, q_d_pn) {
        q_d_notequal
      } else if eq(expr_sign, q_d_zero) {
        q_d_equal
      } else if eq(expr_sign, q_d_neg) {
        q_mlessp
      } else if eq(expr_sign, q_d_nz) {
        q_mleqp
      } else {
        Nil
      }
      if rel.truthy() {
        assume(ftake(rel, [new_var, Fix(0L)])) |> ignore
      }
    }
  }
  new_var
}

// ---------------------------------------------------------------------------
// Stage II
// Implementation of Method 1: Elementary function of exponentials
//
// The following examples are integrated with this method:
//
//   integrate(exp(x)/(2+3*exp(2*x)),x)
//   integrate(exp(x+1)/(1+exp(x)),x)
//   integrate(10^x*exp(x),x)

///|
/// The common base.
let sin__base : Ref[Value] = Ref(Nil)

///|
/// The common power of the form b*x+a. The values are stored in a list
/// which is returned from m2.
let sin__pow : Ref[Value] = Ref(Nil)

///|
/// When T, the substitution is not possible.
let sin__exptflag : Ref[Value] = Ref(Nil)

///|
fn superexpt(
  expr : Value,
  var2 : Value,
  bas1 : Value,
  pow1 : Value,
) -> Value raise {
  let b = bind(q_d_logabs, Nil)
  defer unbind(b)
  sin__base.val = bas1
  sin__pow.val = pow1
  sin__exptflag.val = Nil
  let new_var = make_new_var(
    Str("superexpt"),
    expr=mk(q_mexpt, [
      sin__base.val,
      mk(q_mplus, [
        cdras(q_a, sin__pow.val),
        mk(q_mtimes, [cdras(q_b, sin__pow.val), var2]),
      ]),
    ]),
  )
  // Transform the integrand. At this point resimplify, because it is not
  // guaranteed, that a correct simplified expression is returned.
  // Use a new variable to prevent facts on the old variable to be wrongly used.
  let y = resimplify(elemxpt(expr, var2, new_var))
  if sin__exptflag.val.truthy() {
    return Nil
  }
  // Integrate the transformed integrand and substitute back.
  let subst_expr = mk(q_mexpt, [
    sin__base.val,
    mk(q_mplus, [
      cdras(q_a, sin__pow.val),
      mk(q_mtimes, [cdras(q_b, sin__pow.val), var2]),
    ]),
  ])
  let integrand = div(
    y,
    mul3(
      new_var,
      cdras(q_b, sin__pow.val),
      take(list1(q_p_log), [sin__base.val]),
    ),
  )
  d_multthru(
    substint(
      subst_expr,
      new_var,
      integrator(integrand, new_var),
      var2,
      expr,
    ),
  )
}

///|
/// Transform expressions like g^(b*x+a) to the common base base and
/// do the substitution y = base^(b*x+a) in the expr.
fn elemxpt(expr : Value, var2 : Value, new_var : Value) -> Value raise {
  if freevar2(expr, var2).truthy() {
    expr
  } else if atom(expr) {
    // var2 is the base of a subexpression. The transformation fails.
    sin__exptflag.val = t
    t
  } else if !eq(caar(expr), q_mexpt) {
    cons(car(expr), mapcar(c => elemxpt(c, var2, new_var), cdr(expr)))
  } else if !freevar2(cadr(expr), var2).truthy() {
    mk(q_mexpt, [
      elemxpt(cadr(expr), var2, new_var),
      elemxpt(caddr(expr), var2, new_var),
    ])
  } else if !eq(cadr(expr), sin__base.val) {
    // Transform the expression to the common base.
    elemxpt(
      mk(q_mexpt, [
        sin__base.val,
        muln_([
          power(take(list1(q_p_log), [sin__base.val]), Fix(-1L)),
          take(list1(q_p_log), [cadr(expr)]),
          caddr(expr),
        ]),
      ]),
      var2,
      new_var,
    )
  } else {
    // The exponent must be linear in the variable of integration.
    let mut w = m2_b_starx_plusa(caddr(expr), var2)
    if w is Nil {
      list3(car(expr), sin__base.val, elemxpt(caddr(expr), var2, new_var))
    } else {
      // Do the substitution y = g^(b*x+a).
      w = cons(cons(q_bb, cdras(q_b, sin__pow.val)), w)
      w = cons(cons(q_aa, cdras(q_a, sin__pow.val)), w)
      w = cons(cons(q_base, sin__base.val), w)
      subliss(
        w,
        sin__pat(
          "((mtimes) ((mexpt) base a) ((mexpt) base ((mquotient) ((mtimes) -1 aa b) bb)) ((mexpt) @newvar ((mquotient) b bb)))",
          [("@newvar", new_var)],
        ),
      )
    }
  }
}

// ---------------------------------------------------------------------------
// Stage II
// Implementation of Method 3:
// Substitution for a rational root of a linear fraction of x
//
// This method is applicable when the integrand is of the form:
//
//   /
//   [       a x + b n1/m1   a x + b n1/m2
//   I R(x, (-------)   ,   (-------)     , ...) dx
//   ]       c x + d         c x + d
//   /
//
// Substitute
//
//    (1) t = ((a*x+b)/(c*x+d))^(1/k), or
//
//    (2) x = (b-d*t^k)/(c*t^k-a)
//
// where k is the least common multiplier of m1, m2, ... and
//
//    (3) dx = k*(a*d-b*c)*t^(k-1)/(a-c*t^k)^2 * dt
//
// First, the algorithm calls the routine RAT3 to collect the roots of the
// form ((a*x+b)/(c*x+d))^(n/m) in the list ROOTLIST.
// search for the least common multiplier of m1, m2, ... then the
// substitutions (2) and (3) are done and the new problem is integrated.
// As always, W is an alist which associates to the coefficients
// a, b... (and to VAR) their values.

///|
fn sin__rat3(
  ex : Value,
  ind : Value,
  var2 : Value,
  ratroot2 : Value,
  rootlist : Ref[Value],
) -> Value raise {
  if freevar2(ex, var2).truthy() {
    t
  } else if atom(ex) {
    ind
  } else if eq(caar(ex), q_mtimes) || eq(caar(ex), q_mplus) {
    for u in cdr(ex).iter() {
      if !sin__rat3(u, ind, var2, ratroot2, rootlist).truthy() {
        return Nil
      }
    }
    t
  } else if !eq(caar(ex), q_mexpt) {
    sin__rat3(car(margs(ex)), t, var2, ratroot2, rootlist)
  } else if freevar2(cadr(ex), var2).truthy() {
    sin__rat3(caddr(ex), t, var2, ratroot2, rootlist)
  } else if integerp(caddr(ex)) {
    sin__rat3(cadr(ex), ind, var2, ratroot2, rootlist)
  } else if m2(cadr(ex), ratroot2).truthy() && denomfind(caddr(ex)).truthy() {
    rootlist.val = cons(denomfind(caddr(ex)), rootlist.val)
    rootlist.val
  } else {
    sin__rat3(cadr(ex), Nil, var2, ratroot2, rootlist)
  }
}

///|
/// ratroot2 is an expression of the form (a*x+b)/(c*x+d)
fn ratroot(
  expr : Value,
  var2 : Value,
  ratroot2 : Value,
  w : Value,
) -> Value raise {
  // List of powers of the expression ratroot2.
  let rootlist : Ref[Value] = Ref(Nil)
  // Check if the integrand has a chebyform, if so return the result.
  let y = chebyf(expr, var2)
  if y.truthy() {
    return y
  }
  // Check if the integrand has a suitably form and collect the roots
  // in the global special variable *ROOTLIST*.
  if !sin__rat3(expr, t, var2, ratroot2, rootlist).truthy() {
    return Nil
  }
  // Get the least common multiplier of m1, m2, ...
  let mut k : Value = Fix(1L)
  for r in rootlist.val.iter() {
    k = num_lcm(k, r)
  }
  let w1 = cons(cons(q_k, k), w)
  // Substitute for the roots.
  let new_var = make_new_var(
    Str("ratroot"),
    expr=power(ratroot2, power(k, Fix(-1L))),
  )
  let y = subst41(
    expr,
    subliss(
      w1,
      sin__pat(
        "((mquotient) ((mplus) ((mtimes) b e) ((mtimes) -1 d ((mexpt) @newvar k))) ((mplus) ((mtimes) c ((mexpt) @newvar k)) ((mtimes) -1 e a)))",
        [("@newvar", new_var)],
      ),
    ),
    new_var,
    k,
    ratroot2,
    var2,
  )
  // Integrate the new problem.
  let y = integrator(
    mul2(
      y,
      subliss(
        w1,
        sin__pat(
          "((mquotient) ((mtimes) e ((mplus) ((mtimes) a d k ((mexpt) @newvar ((mplus) -1 k))) ((mtimes) -1 ((mtimes) b c k ((mexpt) @newvar ((mplus) -1 k)))))) ((mexpt) ((mplus) ((mtimes) c ((mexpt) @newvar k)) ((mtimes) -1 a e)) 2))",
          [("@newvar", new_var)],
        ),
      ),
    ),
    new_var,
  )
  // Substitute back and return the result.
  substint(power(ratroot2, power(k, Fix(-1L))), new_var, y, var2, expr)
}

///|
/// Expression of the form x = (b*e-d*t^k)/(c*t^k-e*a).
let sin__rootform : Ref[Value] = Ref(Nil)

///|
/// The variable we substitute for the root (new-var).
let sin__rootvar : Ref[Value] = Ref(Nil)

///|
/// The original integration variable (var2).
let sin__oldvar : Ref[Value] = Ref(Nil)

///|
fn subst4(ex : Value, k : Value, ratroot2 : Value) -> Value raise {
  if freevar2(ex, sin__oldvar.val).truthy() {
    // SUBST4 is called from SUBST41 with OLDVAR equal to VAR
    // (from RATROOT).  Hence we can use FREEVAR2 to see if EX
    // is free of OLDVAR instead of using FREEVAR.
    ex
  } else if atom(ex) {
    sin__rootform.val
  } else if !eq(caar(ex), q_mexpt) {
    mapcar(u => subst4(u, k, ratroot2), ex)
  } else if m2(cadr(ex), ratroot2).truthy() {
    list3(car(ex), sin__rootvar.val, integerp2(timesk(k, caddr(ex))))
  } else {
    list3(
      car(ex),
      subst4(cadr(ex), k, ratroot2),
      subst4(caddr(ex), k, ratroot2),
    )
  }
}

///|
/// Note:  SUBST41 is only called from RATROOT. Arg B is the dummy variable,
/// and OLD-VAR is the original integration variable.
fn subst41(
  expr : Value,
  a : Value,
  b : Value,
  k : Value,
  ratroot2 : Value,
  old_var : Value,
) -> Value raise {
  sin__rootform.val = a
  sin__rootvar.val = b
  sin__oldvar.val = old_var
  // At this point resimplify, because it is not guaranteed, that a correct
  // simplified expression is returned.
  resimplify(subst4(expr, k, ratroot2))
}

///|
fn init_sin() -> Unit raise {
  defvar_init(q_ear_debug_integrate, Nil)
  // When T do not call the risch integrator. This flag can be set by the
  // risch integrator to avoid endless loops when calling the integrator
  // from risch.
  defvar_init(q_ear_in_risch_p, Nil)
  // Dynamically bound flag set to T by TRIGINT to tell INTEGRATOR to use
  // $TRIGINVERSES = '$ALL when ultimately trying RISCHINT
  defvar_init(q_ear_risch_use_triginv_all, Nil)
  // Define the antiderivatives of some elementary special functions.
  // Antiderivatives that depend on the logabs flag are defined further below.
  let props : Array[(Value, String)] = [
    (q_p_log, "((x) ((mplus) ((mtimes) x ((%log) x)) ((mtimes) -1 x)))"),
    (q_p_sin, "((x) ((mtimes) -1 ((%cos) x)))"),
    (q_p_cos, "((x) ((%sin) x))"),
    (q_p_sinh, "((x) ((%cosh) x))"),
    (q_p_cosh, "((x) ((%sinh) x))"),
    // No need to take logabs into account for tanh(x), because cosh(x) is
    // positive.
    (q_p_tanh, "((x) ((%log) ((%cosh) x)))"),
    (q_p_sech, "((x) ((%atan) ((%sinh) x)))"),
    (
      q_p_asin, "((x) ((mplus) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) ((rat) 1 2)) ((mtimes) x ((%asin) x))))",
    ),
    (
      q_p_acos, "((x) ((mplus) ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) ((rat) 1 2))) ((mtimes) x ((%acos) x))))",
    ),
    (
      q_p_atan, "((x) ((mplus) ((mtimes) x ((%atan) x)) ((mtimes) ((rat) -1 2) ((%log) ((mplus) 1 ((mexpt) x 2))))))",
    ),
    (
      q_p_acsc, "((x) ((mplus) ((mtimes) ((rat) -1 2) ((%log) ((mplus) 1 ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2))) ((rat) 1 2)))))) ((mtimes) ((rat) 1 2) ((%log) ((mplus) 1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2))) ((rat) 1 2))))) ((mtimes) x ((%acsc) x))))",
    ),
    (
      q_p_asec, "((x) ((mplus) ((mtimes) ((rat) 1 2) ((%log) ((mplus) 1 ((mtimes) -1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2))) ((rat) 1 2)))))) ((mtimes) ((rat) -1 2) ((%log) ((mplus) 1 ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x -2))) ((rat) 1 2))))) ((mtimes) x ((%asec) x))))",
    ),
    (
      q_p_acot, "((x) ((mplus) ((mtimes) x ((%acot) x)) ((mtimes) ((rat) 1 2) ((%log) ((mplus) 1 ((mexpt) x 2))))))",
    ),
    (
      q_p_asinh, "((x) ((mplus) ((mtimes) -1 ((mexpt) ((mplus) 1 ((mexpt) x 2)) ((rat) 1 2))) ((mtimes) x ((%asinh) x))))",
    ),
    (
      q_p_acosh, "((x) ((mplus) ((mtimes) -1 ((mexpt) ((mplus) -1 x) ((rat) 1 2)) ((mexpt) ((mplus) 1 x) ((rat) 1 2))) ((mtimes) x ((%acosh) x))))",
    ),
    (
      q_p_atanh, "((x) ((mplus) ((mtimes) x ((%atanh) x)) ((mtimes) ((rat) 1 2) ((%log) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2)))))))",
    ),
    (
      q_p_acsch, "((x) ((mplus) ((mtimes) ((rat) -1 2) ((%log) ((mplus) -1 ((mexpt) ((mplus) 1 ((mexpt) x -2)) ((rat) 1 2))))) ((mtimes) ((rat) 1 2) ((%log) ((mplus) 1 ((mexpt) ((mplus) 1 ((mexpt) x -2)) ((rat) 1 2))))) ((mtimes) x ((%acsch) x))))",
    ),
    (
      q_p_asech, "((x) ((mplus) ((mtimes) -1 ((%atan) ((mtimes) ((mexpt) ((mplus) -1 ((mexpt) x -1)) ((rat) 1 2)) ((mexpt) ((mplus) 1 ((mexpt) x -1)) ((rat) 1 2))))) ((mtimes) x ((%asech) x))))",
    ),
  ]
  for p in props {
    putprop(p.0, lread(p.1), q_integral) |> ignore
  }
  putprop(q_p_tan, list2(list1(q_x), q_integrate_tan), q_integral) |> ignore
  putprop(q_p_csc, list2(list1(q_x), q_integrate_csc), q_integral) |> ignore
  putprop(q_p_sec, list2(list1(q_x), q_integrate_sec), q_integral) |> ignore
  putprop(q_p_cot, list2(list1(q_x), q_integrate_cot), q_integral) |> ignore
  putprop(q_p_coth, list2(list1(q_x), q_integrate_coth), q_integral) |> ignore
  putprop(q_p_csch, list2(list1(q_x), q_integrate_csch), q_integral) |> ignore
  putprop(q_p_acoth, list2(list1(q_x), q_integrate_acoth), q_integral)
  |> ignore
  putprop(
    q_mexpt,
    list3(list2(q_x, q_n), q_integrate_mexpt_1, q_integrate_mexpt_2),
    q_integral,
  )
  |> ignore
}
