// Port of src/laplac.lisp: the Laplace transform ($laplace) and the inverse
// Laplace transform of rational functions ($ilt).

///|
/// `((rat) n d)` (unsimplified literal, as quoted in the Lisp source)
fn laplac__rat(n : Int, d : Int) -> Value {
  mk(q_rat, [int(n), int(d)])
}

///|
/// `(with-new-context (context) body)` from maxmac.lisp.
fn[T] laplac__with_new_context(f : () -> T raise) -> T raise {
  let my_context = gensym(prefix="$ctxt")
  d_supcontext(list2(my_context, symval(q_context))) |> ignore
  f() catch {
    e => {
      d_killcontext(list1(my_context)) |> ignore
      raise e
    }
  } noraise {
    v => {
      d_killcontext(list1(my_context)) |> ignore
      v
    }
  }
}

///|
/// `(meval `(($assume) ((mgreaterp) ,x 0)))`
fn laplac__assume_pos(x : Value) -> Unit raise {
  meval(list2(list1(q_d_assume), list3(list1(q_mgreaterp), x, int(0))))
  |> ignore
}

///|
/// `(errset ($defint f x a '$inf))` with errors silenced.
fn laplac__try_defint(f : Value, x : Value, a : Value) -> Value? raise {
  with_specials(
    [(q_errset, Nil), (q_errcatch, t), (q_d_errormsg, Nil), (q_ear_mdebug, Nil)],
    () => errset(() => d_defint(f, x, a, q_d_inf)),
  )
}

///|
/// COMPUTES %E**Z WHERE Z IS AN ARBITRARY EXPRESSION TAKING SOME OF THE WORK
/// AWAY FROM SIMPEXPT
fn exponentiate(pow : Value) -> Value raise {
  if zerop1(pow).truthy() {
    int(1)
  } else if equal(pow, int(1)) {
    q_d__pcte
  } else {
    power(q_d__pcte, pow)
  }
}

///|
/// REST IS A PRODUCT WITHOUT THE MTIMES.FIXUPREST PUTS BACK THE MTIMES
fn fixuprest(rest_ : Value) -> Value raise {
  if rest_ is Nil {
    int(1)
  } else if cdr(rest_).truthy() {
    cons(list1(q_mtimes), rest_)
  } else {
    car(rest_)
  }
}

///|
fn isquadraticp(e : Value, x : Value) -> Value raise {
  let b = sdiff(e, x)
  if zerop1(b).truthy() {
    list3(int(0), int(0), e)
  } else if freeof(x, b).truthy() {
    list3(int(0), b, maxima_substitute(int(0), x, e))
  } else {
    let b = islinear(b, x)
    if b.truthy() {
      list3(div_star(car(b), int(2)), cdr(b), maxima_substitute(int(0), x, e))
    } else {
      Nil
    }
  }
}

///|
/// INITIALIZES SOME GLOBAL VARIABLES THEN CALLS THE DISPATCHING FUNCTION
fn d_laplace(fun : Value, time_var : Value, parm : Value) -> Value raise {
  let mut fun = mratcheck(fun)
  if symval(q_ear_nounsflag).truthy() ||
    memq(q_p_laplace, symval(q_ear_nounl)).truthy() {
    fun = remlaplace(fun)
  }
  laplace(fun, time_var, parm)
}

///|
/// `(delete item list :count 1 :test #'eq)` on a fresh list.
fn laplac__delete_once(item : Value, l : Value) -> Value {
  let c = Collector::new()
  let mut found = false
  let mut p = l
  while p is Cons(_) {
    let x = car(p)
    if !found && eq(x, item) {
      found = true
    } else {
      c.add(x)
    }
    p = cdr(p)
  }
  c.result()
}

///|
/// LAMBDA BINDS SOME SPECIAL VARIABLES TO NIL AND DISPATCHES
fn remlaplace(e : Value) -> Value raise {
  if atom(e) {
    e
  } else {
    cons(
      laplac__delete_once(q_laplace, append(car(e), Nil)),
      mapcar(x => remlaplace(x), cdr(e)),
    )
  }
}

///|
fn laplace(
  fun : Value,
  time_var : Value,
  parm : Value,
  dvar? : Value = Nil,
) -> Value raise {
  // Handles easy cases and calls appropriate function on others.
  if mbagp(fun).truthy() {
    return cons(car(fun), mapcar(e => laplace(e, time_var, parm), cdr(fun)))
  }
  if equal(fun, int(0)) {
    return int(0)
  }
  if equal(fun, int(1)) {
    if zerop1(parm).truthy() {
      return simplify(list2(list1(q_d_delta), int(0)))
    } else {
      return power(parm, int(-1))
    }
  }
  if alike1(fun, time_var).truthy() {
    return power(parm, int(-2))
  }
  if atom(fun) || freeof(time_var, fun).truthy() {
    if zerop1(parm).truthy() {
      return mul2(fun, simplify(list2(list1(q_d_delta), int(0))))
    } else {
      return mul2(fun, power(parm, int(-1)))
    }
  }
  let op = caar(fun)
  // We store the result of laplace for further work.
  let mut result = if eq(op, q_mplus) {
    laplus(fun, time_var, parm)
  } else if eq(op, q_mtimes) {
    laptimes(cdr(fun), time_var, parm)
  } else if eq(op, q_mexpt) {
    lapexpt(fun, Nil, time_var, parm)
  } else if eq(op, q_p_sin) {
    lapsin(fun, Nil, Nil, time_var, parm)
  } else if eq(op, q_p_cos) {
    lapsin(fun, Nil, t, time_var, parm)
  } else if eq(op, q_p_sinh) {
    lapsinh(fun, Nil, Nil, time_var, parm)
  } else if eq(op, q_p_cosh) {
    lapsinh(fun, Nil, t, time_var, parm)
  } else if eq(op, q_p_log) {
    laplog(fun, time_var, parm)
  } else if eq(op, q_p_derivative) {
    lapdiff(fun, time_var, parm)
  } else if eq(op, q_p_integrate) {
    lapint(fun, time_var, parm, dvar)
  } else if eq(op, q_p_sum) {
    list([
      list1(q_p_sum),
      laplace(cadr(fun), time_var, parm),
      caddr(fun),
      cadddr(fun),
      car(cddddr(fun)),
    ])
  } else if eq(op, q_p_erf) {
    laperf(fun, time_var, parm)
  } else if eq(op, q_p_ilt) && eq(cadddr(fun), time_var) {
    if eq(parm, caddr(fun)) {
      cadr(fun)
    } else {
      subst(parm, caddr(fun), cadr(fun))
    }
  } else if eq(op, q_d_delta) {
    lapdelta(fun, Nil, time_var, parm)
  } else if memq(op, list2(q_p_hstep, q_d_unit_step)).truthy() {
    laphstep(fun, Nil, time_var, parm)
  } else {
    let op = d_get(op, q_d_laplace)
    if op.truthy() {
      mcall(op, list3(fun, time_var, parm))
    } else {
      lapdefint(fun, time_var, parm)
    }
  }
  if isinop(result, q_p_integrate).truthy() {
    // Laplace has not found a result but returns a definite
    // integral. This integral can contain internal integration
    // variables. Replace such a result with the noun form.
    result = list4(list1(q_p_laplace), fun, time_var, parm)
  }
  // Check if we have a result, when not call $specint.
  check_call_to__dolspecint(result, fun, time_var, parm)
}

///|
/// Check if laplace has found a result, when not try $specint.
fn check_call_to__dolspecint(
  result : Value,
  fun : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  if isinop(result, q_p_laplace).truthy() ||
    isinop(result, q_p_limit).truthy() || // Try $specint for incomplete results
    isinop(result, q_p_at).truthy() { // which contain %limit or %at too.
    // laplace returns a noun form or a result which contains %limit or %at.
    // We pass the function to $specint to look for more results.
    //
    // laplace assumes the parameter s to be positive and does a
    // declaration before an integration is done. Therefore we declare
    // the parameter of the Laplace transform to be positive before
    // we call $specint too.
    let res = laplac__with_new_context(() => {
      laplac__assume_pos(parm)
      d_specint(
        mul2(fun, power(q_d__pcte, mul3(int(-1), time_var, parm))),
        time_var,
      )
    })
    if isinop(res, q_p_specint).truthy() || isinop(res, q_d_specint).truthy() {
      // $specint has not found a result.
      result
    } else {
      // $specint has found a result
      res
    }
  } else {
    result
  }
}

///|
fn laplus(fun : Value, time_var : Value, parm : Value) -> Value raise {
  simplus(
    cons(list1(q_mplus), mapcar(e => laplace(e, time_var, parm), cdr(fun))),
    int(1),
    t,
  )
}

///|
/// EXPECTS A LIST (PERHAPS EMPTY) OF FUNCTIONS MULTIPLIED TOGETHER WITHOUT
/// THE MTIMES.  SEES IF IT CAN APPLY THE FIRST AS A TRANSFORMATION ON THE
/// REST OF THE FUNCTIONS
fn laptimes(fun : Value, time_var : Value, parm : Value) -> Value raise {
  if fun is Nil {
    return list3(list1(q_mexpt), parm, int(-1))
  }
  if cdr(fun) is Nil {
    return laplace(car(fun), time_var, parm)
  }
  if freeof(time_var, car(fun)).truthy() {
    return simptimes(
      list3(list1(q_mtimes), car(fun), laptimes(cdr(fun), time_var, parm)),
      int(1),
      t,
    )
  }
  if eq(car(fun), time_var) {
    return simptimes(
      list3(
        list1(q_mtimes),
        int(-1),
        sdiff(laptimes(cdr(fun), time_var, parm), parm),
      ),
      int(1),
      t,
    )
  }
  let op = caaar(fun)
  if eq(op, q_mexpt) {
    lapexpt(car(fun), cdr(fun), time_var, parm)
  } else if eq(op, q_mplus) {
    laplus(d_multthru(fixuprest(cdr(fun)), e2=car(fun)), time_var, parm)
  } else if eq(op, q_p_sin) {
    lapsin(car(fun), cdr(fun), Nil, time_var, parm)
  } else if eq(op, q_p_cos) {
    lapsin(car(fun), cdr(fun), t, time_var, parm)
  } else if eq(op, q_p_sinh) {
    lapsinh(car(fun), cdr(fun), Nil, time_var, parm)
  } else if eq(op, q_p_cosh) {
    lapsinh(car(fun), cdr(fun), t, time_var, parm)
  } else if eq(op, q_d_delta) {
    lapdelta(car(fun), cdr(fun), time_var, parm)
  } else if memq(op, list2(q_p_hstep, q_d_unit_step)).truthy() {
    laphstep(car(fun), cdr(fun), time_var, parm)
  } else {
    lapshift(car(fun), cdr(fun), time_var, parm)
  }
}

///|
/// The %E-CASE-LIN tag of LAPEXPT.
fn laplac__e_case_lin(
  ab : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  let result = if rest_.truthy() {
    sratsimp(
      d_at(
        laptimes(rest_, time_var, parm),
        list3(
          list1(q_mequal),
          parm,
          list3(list1(q_mplus), parm, afixsign(cadr(ab), Nil)),
        ),
      ),
    )
  } else {
    list3(
      list1(q_mexpt),
      list3(list1(q_mplus), parm, afixsign(cadr(ab), Nil)),
      int(-1),
    )
  }
  simptimes(
    list3(list1(q_mtimes), exponentiate(caddr(ab)), result),
    int(1),
    Nil,
  )
}

///|
/// The %E-CASE-QUAD tag of LAPEXPT.
fn laplac__e_case_quad(ab : Value, parm : Value) -> Value raise {
  let r = afixsign(car(ab), Nil)
  let mut result = list4(
    list1(q_mtimes),
    div_star(
      list3(list1(q_mexpt), div_star(q_d__pctpi, r), laplac__rat(1, 2)),
      int(2),
    ),
    exponentiate(
      div_star(
        list3(list1(q_mexpt), parm, int(2)),
        list3(list1(q_mtimes), int(4), r),
      ),
    ),
    list3(
      list1(q_mplus),
      int(1),
      list3(
        list1(q_mtimes),
        int(-1),
        list2(
          list1(q_p_erf),
          div_star(
            parm,
            list3(
              list1(q_mtimes),
              int(2),
              list3(list1(q_mexpt), r, laplac__rat(1, 2)),
            ),
          ),
        ),
      ),
    ),
  )
  if !equal(cadr(ab), int(0)) {
    result = maxima_substitute(
      list3(
        list1(q_mplus),
        parm,
        list3(list1(q_mtimes), int(-1), cadr(ab)),
      ),
      parm,
      result,
    )
  }
  simptimes(
    list3(list1(q_mtimes), exponentiate(caddr(ab)), result),
    int(1),
    Nil,
  )
}

///|
/// The NOLUCK tag of LAPEXPT.
fn laplac__noluck(
  fun : Value,
  base_of_fun : Value,
  power_ : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  if posint(power_).truthy() &&
    memq(
      caar(base_of_fun),
      list([q_mplus, q_p_sin, q_p_cos, q_p_sinh, q_p_cosh]),
    ).truthy() {
    laptimes(
      cons(
        base_of_fun,
        cons(
          if num_eq(power_, int(2)) {
            base_of_fun
          } else {
            list3(list1(q_mexpt), base_of_fun, one_minus(power_))
          },
          rest_,
        ),
      ),
      time_var,
      parm,
    )
  } else {
    lapshift(fun, rest_, time_var, parm)
  }
}

///|
/// HANDLES %E**(A*T+B)*REST(T), %E**(A*T**2+B*T+C),
/// 1/SQRT(A*T+B), OR T**K*REST(T)
fn lapexpt(
  fun : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  let base_of_fun = cadr(fun)
  let mut power_ = caddr(fun)
  if freeof(time_var, base_of_fun).truthy() {
    let ab = isquadraticp(
      if eq(base_of_fun, q_d__pcte) {
        power_
      } else {
        simptimes(
          list3(list1(q_mtimes), power_, list2(list1(q_p_log), base_of_fun)),
          int(1),
          Nil,
        )
      },
      time_var,
    )
    if ab.truthy() {
      if equal(car(ab), int(0)) {
        return laplac__e_case_lin(ab, rest_, time_var, parm)
      } else if rest_ is Nil {
        return laplac__e_case_quad(ab, parm)
      } else {
        return laplac__noluck(fun, base_of_fun, power_, rest_, time_var, parm)
      }
    }
  }
  if eq(base_of_fun, time_var) && freeof(time_var, power_).truthy() {
    // var-case
    if !(rest_ is Nil || freeof(time_var, fixuprest(rest_)).truthy()) {
      if posint(power_).truthy() {
        return afixsign(
          d_diff(list3(laptimes(rest_, time_var, parm), parm, power_)),
          even(power_),
        )
      } else if negint(power_).truthy() {
        return mydefint(
          hackit(power_, rest_, time_var, parm),
          createname(parm, num_neg(power_)),
          parm,
          parm,
        )
      } else {
        return laplac__noluck(fun, base_of_fun, power_, rest_, time_var, parm)
      }
    }
    // var-easy-case
    power_ = simplus(list3(list1(q_mplus), int(1), power_), int(1), t)
    if !eq(asksign(d_realpart(power_)), q_d_positive) {
      return laplac__noluck(fun, base_of_fun, power_, rest_, time_var, parm)
    }
    let mut result = list2(
      list2(list1(q_p_gamma), power_),
      list3(list1(q_mexpt), parm, afixsign(power_, Nil)),
    )
    if rest_.truthy() {
      result = nconc(result, rest_)
    }
    return simptimes(cons(list1(q_mtimes), result), int(1), Nil)
  }
  if alike1(laplac__rat(-1, 2), power_).truthy() && rest_ is Nil {
    let ab = islinear(base_of_fun, time_var)
    if ab.truthy() {
      let result = div_star(cdr(ab), car(ab))
      return simptimes(
        list4(
          list1(q_mtimes),
          list3(
            list1(q_mexpt),
            div_star(q_d__pctpi, list3(list1(q_mtimes), car(ab), parm)),
            laplac__rat(1, 2),
          ),
          exponentiate(list3(list1(q_mtimes), result, parm)),
          list3(
            list1(q_mplus),
            int(1),
            list3(
              list1(q_mtimes),
              int(-1),
              list2(
                list1(q_p_erf),
                list3(
                  list1(q_mexpt),
                  list3(list1(q_mtimes), result, parm),
                  laplac__rat(1, 2),
                ),
              ),
            ),
          ),
        ),
        int(1),
        Nil,
      )
    }
  }
  laplac__noluck(fun, base_of_fun, power_, rest_, time_var, parm)
}

///|
/// INTEGRAL FROM A TO INFINITY OF F(X)
fn mydefint(f : Value, x : Value, a : Value, parm : Value) -> Value raise {
  // We don't want any errors thrown by $defint to propagate, so we set
  // errset, errcatch, $errormsg and *mdebug*.  If $defint throws a error,
  // then no error message is printed and errset simply returns nil below.
  let tryint = if !d_unknown(f).truthy() {
    laplac__with_new_context(() => {
      laplac__assume_pos(parm)
      laplac__assume_pos(x)
      laplac__assume_pos(a)
      laplac__try_defint(f, x, a)
    })
  } else {
    None
  }
  match tryint {
    Some(v) => v
    None => list([list1(q_p_integrate), f, x, a, q_d_inf])
  }
}

///|
/// CREATES UNIQUE NAMES FOR VARIABLE OF INTEGRATION
fn createname(head : Value, tail : Value) -> Value raise {
  // (intern (format nil "~S~S" head tail)) on port symbol names.
  let h = match head {
    Sym(s) => s.name
    _ => prin1_to_string(head)
  }
  let tl = match tail {
    Sym(s) => s.name
    _ => prin1_to_string(tail)
  }
  Sym(intern(h + tl))
}

///|
/// REDUCES LAPLACE(F(T)/T**N,T,S) CASE TO LAPLACE(F(T)/T**(N-1),T,S) CASE
fn hackit(
  exponent : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  if equal(exponent, int(-1)) {
    let parm = createname(parm, int(1))
    laptimes(rest_, time_var, parm)
  } else {
    mydefint(
      hackit(one_plus(exponent), rest_, time_var, parm),
      createname(parm, num_sub(int(-1), exponent)),
      createname(parm, num_neg(exponent)),
      parm,
    )
  }
}

///|
/// MULTIPLIES FUNCT BY -1 IF SIGNSWITCH IS NIL
fn afixsign(funct : Value, signswitch : Value) -> Value raise {
  if signswitch.truthy() {
    funct
  } else {
    simptimes(list3(list1(q_mtimes), int(-1), funct), int(1), t)
  }
}

///|
fn lapshift(
  fun : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  if atom(fun) {
    merr("LAPSHIFT: expected a cons, not ~M", [fun])
  } else if memq(q_laplace, car(fun)).truthy() || rest_ is Nil {
    lapdefint(
      if rest_.truthy() {
        simptimes(cons(list1(q_mtimes), cons(fun, rest_)), int(1), t)
      } else {
        fun
      },
      time_var,
      parm,
    )
  } else {
    laptimes(
      append(rest_, list1(cons(append(car(fun), list1(q_laplace)), cdr(fun)))),
      time_var,
      parm,
    )
  }
}

///|
/// COMPUTES %E**(W*B*%I)*F(S-W*A*%I) WHERE W=-1 IF SIGN IS T ELSE W=1
fn mostpart(
  f : Value,
  parm : Value,
  sign : Value,
  a : Value,
  b : Value,
) -> Value raise {
  let substinfun = d_at(
    f,
    list3(
      list1(q_mequal),
      parm,
      list3(
        list1(q_mplus),
        parm,
        afixsign(list3(list1(q_mtimes), a, q_d__pcti), sign),
      ),
    ),
  )
  if zerop1(b).truthy() {
    substinfun
  } else {
    list3(
      list1(q_mtimes),
      exponentiate(
        afixsign(list3(list1(q_mtimes), b, q_d__pcti), lbool(sign is Nil)),
      ),
      substinfun,
    )
  }
}

///|
/// IF WHICHSIGN IS NIL THEN SIN TRANSFORM ELSE COS TRANSFORM
fn compose(
  fun : Value,
  parm : Value,
  whichsign : Value,
  a : Value,
  b : Value,
) -> Value raise {
  let result = list2(
    laplac__rat(1, 2),
    list3(
      list1(q_mplus),
      mostpart(fun, parm, t, a, b),
      afixsign(mostpart(fun, parm, Nil, a, b), whichsign),
    ),
  )
  sratsimp(
    simptimes(
      cons(
        list1(q_mtimes),
        if whichsign.truthy() {
          result
        } else {
          cons(q_d__pcti, result)
        },
      ),
      int(1),
      Nil,
    ),
  )
}

///|
/// FUN IS OF THE FORM SIN(A*T+B)*REST(T) OR COS
fn lapsin(
  fun : Value,
  rest_ : Value,
  trigswitch : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  let ab = islinear(cadr(fun), time_var)
  if ab.truthy() {
    if rest_.truthy() {
      compose(laptimes(rest_, time_var, parm), parm, trigswitch, car(ab), cdr(ab))
    } else {
      simptimes(
        list3(
          list1(q_mtimes),
          if zerop1(cdr(ab)).truthy() {
            if trigswitch.truthy() {
              parm
            } else {
              car(ab)
            }
          } else if trigswitch.truthy() {
            list3(
              list1(q_mplus),
              list3(list1(q_mtimes), parm, list2(list1(q_p_cos), cdr(ab))),
              list4(
                list1(q_mtimes),
                int(-1),
                car(ab),
                list2(list1(q_p_sin), cdr(ab)),
              ),
            )
          } else {
            list3(
              list1(q_mplus),
              list3(list1(q_mtimes), parm, list2(list1(q_p_sin), cdr(ab))),
              list3(list1(q_mtimes), car(ab), list2(list1(q_p_cos), cdr(ab))),
            )
          },
          list3(
            list1(q_mexpt),
            list3(
              list1(q_mplus),
              list3(list1(q_mexpt), parm, int(2)),
              list3(list1(q_mexpt), car(ab), int(2)),
            ),
            int(-1),
          ),
        ),
        int(1),
        Nil,
      )
    }
  } else {
    lapshift(fun, rest_, time_var, parm)
  }
}

///|
/// FUN IS OF THE FORM SINH(A*T+B)*REST(T) OR IS COSH
fn lapsinh(
  fun : Value,
  rest_ : Value,
  switch : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  if islinear(cadr(fun), time_var).truthy() {
    sratsimp(
      laplus(
        simplus(
          list3(
            list1(q_mplus),
            nconc(
              list3(
                list1(q_mtimes),
                list3(list1(q_mexpt), q_d__pcte, cadr(fun)),
                laplac__rat(1, 2),
              ),
              rest_,
            ),
            afixsign(
              nconc(
                list3(
                  list1(q_mtimes),
                  list3(list1(q_mexpt), q_d__pcte, afixsign(cadr(fun), Nil)),
                  laplac__rat(1, 2),
                ),
                rest_,
              ),
              switch,
            ),
          ),
          int(1),
          Nil,
        ),
        time_var,
        parm,
      ),
    )
  } else {
    lapshift(fun, rest_, time_var, parm)
  }
}

///|
/// FUN IS OF THE FORM LOG(A*T)
fn laplog(fun : Value, time_var : Value, parm : Value) -> Value raise {
  let ab = islinear(cadr(fun), time_var)
  if ab.truthy() && zerop1(cdr(ab)).truthy() {
    simptimes(
      list3(
        list1(q_mtimes),
        list4(
          list1(q_mplus),
          subfunmake(q_d_psi, list1(int(0)), list1(int(1))),
          list2(list1(q_p_log), car(ab)),
          list3(list1(q_mtimes), int(-1), list2(list1(q_p_log), parm)),
        ),
        list3(list1(q_mexpt), parm, int(-1)),
      ),
      int(1),
      Nil,
    )
  } else {
    lapdefint(fun, time_var, parm)
  }
}

///|
fn raiseup(fbase : Value, exponent : Value) -> Value raise {
  if equal(exponent, int(1)) {
    fbase
  } else {
    list3(list1(q_mexpt), fbase, exponent)
  }
}

///|
/// TAKES TRANSFORM OF HSTEP(A*T+B)*F(T)
fn laphstep(
  fun : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  let ab = islinear(cadr(fun), time_var)
  if ab.truthy() {
    let a = car(ab)
    let b = cdr(ab)
    let offset = div(b, a)
    let s = asksign(a)
    if eq(s, q_d_positive) {
      if eq(asksign(offset), q_d_negative) {
        mul2(
          exponentiate(mul2(offset, parm)),
          laplace(
            maxima_substitute(sub(time_var, offset), time_var, fixuprest(rest_)),
            time_var,
            parm,
          ),
        )
      } else {
        laptimes(rest_, time_var, parm)
      }
    } else if eq(s, q_d_negative) {
      if eq(asksign(offset), q_d_negative) {
        sub(
          laptimes(rest_, time_var, parm),
          mul2(
            exponentiate(mul2(offset, parm)),
            laplace(
              maxima_substitute(
                sub(time_var, offset),
                time_var,
                fixuprest(rest_),
              ),
              time_var,
              parm,
            ),
          ),
        )
      } else {
        int(0)
      }
    } else {
      mul2(fun, laptimes(rest_, time_var, parm))
    }
  } else {
    lapshift(fun, rest_, time_var, parm)
  }
}

///|
/// TAKES TRANSFORM OF DELTA(A*T+B)*F(T)
fn lapdelta(
  fun : Value,
  rest_ : Value,
  time_var : Value,
  parm : Value,
) -> Value raise {
  let ab = islinear(cadr(fun), time_var)
  if ab.truthy() {
    let recipa = power(car(ab), int(-1))
    let ab = div(cdr(ab), car(ab))
    let sign = asksign(ab)
    let recipa = simplifya(list2(list1(q_mabs), recipa), Nil)
    simplifya(
      if eq(sign, q_d_positive) {
        int(0)
      } else if eq(sign, q_d_zero) {
        list3(
          list1(q_mtimes),
          maxima_substitute(int(0), time_var, fixuprest(rest_)),
          recipa,
        )
      } else {
        list4(
          list1(q_mtimes),
          maxima_substitute(neg(ab), time_var, fixuprest(rest_)),
          list3(
            list1(q_mexpt),
            q_d__pcte,
            cons(list1(q_mtimes), cons(parm, list1(ab))),
          ),
          recipa,
        )
      },
      Nil,
    )
  } else {
    lapshift(fun, rest_, time_var, parm)
  }
}

///|
fn laperf(fun : Value, time_var : Value, parm : Value) -> Value raise {
  let ab = islinear(cadr(fun), time_var)
  if ab.truthy() && equal(cdr(ab), int(0)) {
    simptimes(
      list3(
        list1(q_mtimes),
        div_star(
          exponentiate(
            div_star(
              list3(list1(q_mexpt), parm, int(2)),
              list3(
                list1(q_mtimes),
                int(4),
                list3(list1(q_mexpt), car(ab), int(2)),
              ),
            ),
          ),
          parm,
        ),
        list3(
          list1(q_mplus),
          int(1),
          list3(
            list1(q_mtimes),
            int(-1),
            list2(
              list1(q_p_erf),
              div_star(parm, list3(list1(q_mtimes), int(2), car(ab))),
            ),
          ),
        ),
      ),
      int(1),
      Nil,
    )
  } else {
    lapdefint(fun, time_var, parm)
  }
}

///|
fn lapdefint(fun : Value, time_var : Value, parm : Value) -> Value raise {
  if !d_unknown(fun).truthy() {
    let mult = simptimes(
      list3(
        list1(q_mtimes),
        exponentiate(list4(list1(q_mtimes), int(-1), time_var, parm)),
        fun,
      ),
      int(1),
      Nil,
    )
    let tryint = laplac__with_new_context(() => {
      laplac__assume_pos(parm)
      // We don't want any errors thrown by $defint to propagate, so we set
      // errset, errcatch, $errormsg and *mdebug*.  If $defint throws a
      // error, then no error message is printed and errset simply returns
      // nil below.
      laplac__try_defint(mult, time_var, int(0))
    })
    match tryint {
      Some(v) => {
        let head = if listp(v) { caar(v) } else { Nil }
        if !eq(head, q_p_integrate) {
          return v
        }
      }
      None => ()
    }
  }
  list4(list1(q_p_laplace), fun, time_var, parm)
}

///|
/// FUN IS OF THE FORM DIFF(F(T),T,N) WHERE N IS A POSITIVE INTEGER
fn lapdiff(fun : Value, time_var : Value, parm : Value) -> Value raise {
  let mut fun = fun
  let mut difflist = copy_tree(cddr(fun))
  let mut newdlist = difflist
  let arg2 = list3(list1(q_mequal), time_var, int(0))
  let mut frontend : Value = Nil
  let mut degree : Value = Nil
  while true {
    if difflist is Nil {
      return cons(
        list1(q_p_derivative),
        cons(list4(list1(q_p_laplace), cadr(fun), time_var, parm), newdlist),
      )
    } else if eq(car(difflist), time_var) {
      degree = cadr(difflist)
      difflist = cddr(difflist)
      break
    }
    frontend = cdr(difflist)
    difflist = cdr(frontend)
  }
  // out
  if !posint(degree).truthy() {
    return list4(list1(q_p_laplace), fun, time_var, parm)
  }
  if frontend.truthy() {
    rplacd(frontend, difflist) |> ignore
  } else {
    newdlist = difflist
  }
  if newdlist.truthy() {
    fun = cons(list1(q_p_derivative), cons(cadr(fun), newdlist))
  } else {
    fun = cadr(fun)
  }
  let mut order = int(0)
  let mut resultlist : Value = Nil
  // loop
  while true {
    degree = num_sub(degree, int(1))
    resultlist = cons(
      list3(
        list1(q_mtimes),
        raiseup(parm, degree),
        d_at(d_diff(list3(fun, time_var, order)), arg2),
      ),
      resultlist,
    )
    order = num_add(order, int(1))
    if !num_gt(degree, int(0)) {
      break
    }
  }
  resultlist = if cdr(resultlist).truthy() {
    cons(list1(q_mplus), resultlist)
  } else {
    car(resultlist)
  }
  simplus(
    list3(
      list1(q_mplus),
      list3(list1(q_mtimes), raiseup(parm, order), laplace(fun, time_var, parm)),
      list3(list1(q_mtimes), int(-1), resultlist),
    ),
    int(1),
    Nil,
  )
}

///|
/// FUN IS OF THE FORM INTEGRATE(F(X)*G(T)*H(T-X),X,0,T)
fn lapint(
  fun : Value,
  time_var : Value,
  parm : Value,
  dvar : Value,
) -> Value raise {
  let mut dvar = dvar
  let mut newfun : Value = Nil
  let mut parm_list : Value = Nil
  let mut var_list : Value = Nil
  let mut var_parm_list : Value = Nil
  // 0: start, 1: notcon, 2: convolutiontest, 3: convolution
  let mut state = if dvar.truthy() { 3 } else { 0 }
  if state == 0 {
    newfun = cdr(fun)
    dvar = cadr(newfun)
    state = if cddr(newfun).truthy() &&
      zerop1(caddr(newfun)).truthy() &&
      eq(cadddr(newfun), time_var) {
      2
    } else {
      1
    }
  }
  if state == 2 {
    // convolutiontest
    newfun = d_factor(car(newfun))
    let mut f : Value = Nil
    if eq(caar(newfun), q_mtimes) {
      f = cadr(newfun)
      newfun = cddr(newfun)
    } else {
      f = newfun
      newfun = Nil
    }
    // gothrulist
    while true {
      if freeof(dvar, f).truthy() {
        parm_list = cons(f, parm_list)
      } else if freeof(time_var, f).truthy() {
        var_list = cons(f, var_list)
      } else if freeof(
          dvar,
          sratsimp(
            maxima_substitute(
              list3(list1(q_mplus), time_var, dvar),
              time_var,
              f,
            ),
          ),
        ).truthy() {
        var_parm_list = cons(f, var_parm_list)
      } else {
        state = 1
        break
      }
      if newfun.truthy() {
        f = car(newfun)
        newfun = cdr(newfun)
      } else {
        break
      }
    }
    if state == 2 {
      if parm_list.truthy() {
        return laplace(
          cons(
            list1(q_mtimes),
            nconc(
              parm_list,
              list1(
                list([
                  list1(q_p_integrate),
                  cons(list1(q_mtimes), append(var_list, var_parm_list)),
                  dvar,
                  int(0),
                  time_var,
                ]),
              ),
            ),
          ),
          time_var,
          parm,
          dvar~,
        )
      }
      state = 3
    }
  }
  if state == 1 {
    // notcon
    newfun = cdr(fun)
    if cddr(newfun).truthy() {
      if freeof(time_var, caddr(newfun)).truthy() &&
        freeof(time_var, cadddr(newfun)).truthy() {
        return list([
          list1(q_p_integrate),
          laplace(car(newfun), time_var, parm, dvar~),
          dvar,
          caddr(newfun),
          cadddr(newfun),
        ])
      } else {
        // giveup
        return list4(list1(q_p_laplace), fun, time_var, parm)
      }
    } else {
      return list3(
        list1(q_p_integrate),
        laplace(car(newfun), time_var, parm, dvar~),
        dvar,
      )
    }
  }
  // convolution
  simptimes(
    list3(
      list1(q_mtimes),
      laplace(
        d_expand(maxima_substitute(time_var, dvar, fixuprest(var_list))),
        time_var,
        parm,
        dvar~,
      ),
      laplace(
        d_expand(maxima_substitute(int(0), dvar, fixuprest(var_parm_list))),
        time_var,
        parm,
        dvar~,
      ),
    ),
    int(1),
    t,
  )
}

///|
/// EXP IS F(S)/G(S) WHERE F AND G ARE POLYNOMIALS IN S AND DEGR(F) < DEGR(G)
fn d_ilt(exp_ : Value, ils : Value, ilt : Value) -> Value raise {
  with_specials(
    [
      (q_varlist, Nil),
      (q_d_savefactors, t),
      (q_ear_checkfactors, Nil),
      (q_d_ratfac, Nil),
      (q_d_keepfloat, Nil),
    ],
    () => {
      // MAKES ILS THE MAIN VARIABLE
      set(q_varlist, list1(ils)) |> ignore
      newvar(exp_) |> ignore
      orderpointer(symval(q_varlist)) |> ignore
      let s_var = caadr(ratrep_star(ils))
      if !atom(exp_) && eq(caar(exp_), q_mequal) {
        list3(
          list1(q_mequal),
          d_ilt(cadr(exp_), ils, ilt),
          d_ilt(caddr(exp_), ils, ilt),
        )
      } else if zerop1(exp_).truthy() {
        int(0)
      } else if freeof(ils, exp_).truthy() {
        list3(list1(q_mtimes), exp_, list2(list1(q_d_delta), ilt))
      } else {
        ilt0(exp_, ils, ilt, s_var)
      }
    },
  )
}

///|
fn maxima_rationalp(le : Value, v : Value) -> Value raise {
  if le is Nil {
    t
  } else if !atom(car(le)) && !freeof(v, car(le)).truthy() {
    Nil
  } else {
    maxima_rationalp(cdr(le), v)
  }
}

///|
/// THIS FUNCTION DOES THE PARTIAL FRACTION DECOMPOSITION
fn ilt0(exp_ : Value, ils : Value, ilt : Value, s_var : Value) -> Value raise {
  if mplusp(exp_).truthy() {
    return simplus(
      cons(list1(q_mplus), mapcar(f => d_ilt(f, ils, ilt), cdr(exp_))),
      int(1),
      t,
    )
  }
  if !atom(exp_) && eq(caar(exp_), q_p_laplace) && eq(cadddr(exp_), ils) {
    return if eq(caddr(exp_), ilt) {
      cadr(exp_)
    } else {
      subst(ilt, caddr(exp_), cadr(exp_))
    }
  }
  let ratarg = ratrep_star(exp_)
  if !maxima_rationalp(symval(q_varlist), ils).truthy() {
    return list4(list1(q_p_ilt), exp_, ils, ilt)
  }
  let laplac_ratform = car(ratarg)
  let mut denom = ratdenominator(cdr(ratarg))
  let mut frpart = pdivide(ratnumerator(cdr(ratarg)), denom)
  let wholepart = car(frpart)
  frpart = ratqu(cadr(frpart), denom)
  if !zerop1(car(wholepart)).truthy() {
    return list4(list1(q_p_ilt), exp_, ils, ilt)
  } else if zerop1(car(frpart)).truthy() {
    return int(0)
  }
  let mut num = car(frpart)
  denom = cdr(frpart)
  let mut y = oldcontent(denom)
  let content = car(y)
  let mut real = cadr(y)
  let mut factor = pfactor(real)
  let mut parnumer : Value = Nil
  // loop
  while true {
    let mut apart : Value = Nil
    let mut bpart : Value = Nil
    if cddr(factor) is Nil {
      apart = real
      bpart = int(1)
      y = cons(cons(int(0), int(1)), cons(int(1), int(1)))
    } else {
      apart = pexpt(car(factor), cadr(factor))
      bpart = car(ratqu(real, apart))
      y = bprog(apart, bpart, s_var)
    }
    // skip
    frpart = cdr(
      ratdivide(
        ratti(ratnumerator(num), cdr(y), t),
        ratti(ratdenominator(num), ratti(content, apart, t), t),
      ),
    )
    parnumer = cons(
      ilt1(
        ratqu(
          ratnumerator(frpart),
          ratti(
            ratdenominator(frpart),
            ratti(ratdenominator(num), content, t),
            t,
          ),
        ),
        car(factor),
        cadr(factor),
        laplac_ratform,
        ils,
        ilt,
        s_var,
      ),
      parnumer,
    )
    factor = cddr(factor)
    if factor is Nil {
      return simplus(cons(list1(q_mplus), parnumer), int(1), t)
    }
    num = cdr(ratdivide(ratti(num, car(y), t), ratti(content, bpart, t)))
    real = bpart
  }
  Nil
}

///|
fn ilt1(
  p : Value,
  q : Value,
  k : Value,
  laplac_ratform : Value,
  ils : Value,
  ilt : Value,
  s_var : Value,
) -> Value raise {
  if onep1(k).truthy() {
    ilt3(p, laplac_ratform, ils, ilt, q, s_var)
  } else {
    let z = bprog(q, pderivative(q, s_var), s_var)
    ilt2(p, k, laplac_ratform, ils, ilt, z, q, s_var)
  }
}

///|
/// INVERTS P(S)/Q(S)**K WHERE Q(S)  IS IRREDUCIBLE
/// DOESN'T CALL ILT3 IF Q(S) IS LINEAR
fn ilt2(
  p : Value,
  k : Value,
  laplac_ratform : Value,
  ils : Value,
  ilt : Value,
  z : Value,
  q : Value,
  s_var : Value,
) -> Value raise {
  if onep1(k).truthy() {
    return ilt3(p, laplac_ratform, ils, ilt, q, s_var)
  }
  let k = num_sub(k, int(1))
  let a = ratti(p, car(z), t)
  let b = ratti(p, cdr(z), t)
  let y = pexpt(q, k)
  if !equal(pdegree(q, s_var), int(1)) || num_gt(pdegree(car(p), s_var), int(0)) {
    return simplus(
      list3(
        list1(q_mplus),
        ilt2(
          cdr(ratdivide(ratplus(a, ratqu(ratderivative(b, s_var), k)), y)),
          k,
          laplac_ratform,
          ils,
          ilt,
          z,
          q,
          s_var,
        ),
        d_multthru(
          simptimes(
            list4(
              list1(q_mtimes),
              ilt,
              power(k, int(-1)),
              ilt2(
                cdr(ratdivide(b, y)),
                k,
                laplac_ratform,
                ils,
                ilt,
                z,
                q,
                s_var,
              ),
            ),
            int(1),
            t,
          ),
        ),
      ),
      int(1),
      t,
    )
  }
  let a = disrep(polcoef(q, int(1), s_var), laplac_ratform)
  let b = disrep(polcoef(q, int(0), s_var), laplac_ratform)
  simptimes(
    list([
      list1(q_mtimes),
      disrep(p, laplac_ratform),
      raiseup(ilt, k),
      simpexpt(
        list3(
          list1(q_mexpt),
          q_d__pcte,
          list([
            list1(q_mtimes),
            int(-1),
            ilt,
            b,
            list3(list1(q_mexpt), a, int(-1)),
          ]),
        ),
        int(1),
        Nil,
      ),
      list3(list1(q_mexpt), a, num_sub(int(-1), k)),
      list3(list1(q_mexpt), factorial(k), int(-1)),
    ]),
    int(1),
    Nil,
  )
}

///|
/// INVERTS P(S)/Q(S) WHERE Q(S) IS IRREDUCIBLE
fn ilt3(
  p : Value,
  laplac_ratform : Value,
  ils : Value,
  ilt : Value,
  q : Value,
  s_var : Value,
) -> Value raise {
  fn coef(pol : Value, coef_ratform : Value) -> Value raise {
    disrep(ratqu(polcoef(car(p), pol, s_var), cdr(p)), coef_ratform)
  }

  fn lapsum(args : Array[Value]) -> Value {
    cons(list1(q_mplus), list(args))
  }

  fn lapprod(args : Array[Value]) -> Value {
    cons(list1(q_mtimes), list(args))
  }

  fn expo(args : Array[Value]) -> Value {
    cons(list1(q_mexpt), list(args))
  }

  let e = disrep(polcoef(q, int(0), s_var), laplac_ratform)
  let d = disrep(polcoef(q, int(1), s_var), laplac_ratform)
  let degr = pdegree(q, s_var)
  if equal(degr, int(1)) {
    return simptimes(
      lapprod([
        disrep(p, laplac_ratform),
        expo([d, int(-1)]),
        expo([q_d__pcte, lapprod([int(-1), ilt, e, expo([d, int(-1)])])]),
      ]),
      int(1),
      Nil,
    )
  }
  let c = disrep(polcoef(q, int(2), s_var), laplac_ratform)
  if !equal(degr, int(2)) {
    if equal(degr, int(3)) && zerop1(c).truthy() && zerop1(d).truthy() {
      // cubic
      let a = disrep(polcoef(q, int(3), s_var), laplac_ratform)
      let r = simpnrt(div_star(e, a), int(3))
      let d = div_star(
        disrep(p, laplac_ratform),
        lapprod([a, lapsum([expo([ils, int(3)]), expo([q_p_r, int(3)])])]),
      )
      return ilt0(
        maxima_substitute(r, q_p_r, d_partfrac(d, ils)),
        ils,
        ilt,
        s_var,
      )
    }
    return list4(
      list1(q_p_ilt),
      div_star(disrep(p, laplac_ratform), disrep(q, laplac_ratform)),
      ils,
      ilt,
    )
  }
  // quadratic
  let b0 = coef(int(0), laplac_ratform)
  let b1 = coef(int(1), laplac_ratform)
  let mut discrim = simplus(
    lapsum([lapprod([int(4), e, c]), lapprod([int(-1), d, d])]),
    int(1),
    Nil,
  )
  let mut sign = if free(discrim, q_d__pcti).truthy() {
    asksign(discrim)
  } else {
    q_d_positive
  }
  let mut term1 = list1(q_p_cos)
  let mut term2 = list1(q_p_sin)
  let degr = expo([
    q_d__pcte,
    lapprod([ilt, d, power(c, int(-1)), laplac__rat(-1, 2)]),
  ])
  if eq(sign, q_d_zero) {
    return simptimes(
      lapprod([
        degr,
        lapsum([
          div_star(b1, c),
          lapprod([
            div_star(
              lapsum([lapprod([int(2), b0, c]), lapprod([int(-1), b1, d])]),
              lapprod([int(2), c, c]),
            ),
            ilt,
          ]),
        ]),
      ]),
      int(1),
      Nil,
    )
  } else if eq(sign, q_d_negative) {
    term1 = list1(q_p_cosh)
    term2 = list1(q_p_sinh)
    discrim = simptimes(lapprod([int(-1), discrim]), int(1), t)
  }
  discrim = simpnrt(discrim, int(2))
  sign = simptimes(
    lapprod([
      lapsum([lapprod([int(2), b0, c]), lapprod([int(-1), b1, d])]),
      expo([discrim, int(-1)]),
    ]),
    int(1),
    Nil,
  )
  let c = power(c, int(-1))
  discrim = simptimes(
    lapprod([discrim, ilt, laplac__rat(1, 2), c]),
    int(1),
    t,
  )
  simptimes(
    lapprod([
      c,
      degr,
      lapsum([
        lapprod([b1, list2(term1, discrim)]),
        lapprod([sign, list2(term2, discrim)]),
      ]),
    ]),
    int(1),
    Nil,
  )
}

///|
fn init_laplac() -> Unit raise {
  // The properties NOUN and VERB give correct linear display
  putprop(q_d_laplace, q_p_laplace, q_verb) |> ignore
  putprop(q_p_laplace, q_d_laplace, q_noun) |> ignore
  putprop(q_d_ilt, q_p_ilt, q_verb) |> ignore
  putprop(q_p_ilt, q_d_ilt, q_noun) |> ignore
}
