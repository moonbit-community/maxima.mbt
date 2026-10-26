// Port of src/numerical/slatec/quadpack.lisp: the Maxima interface to the
// QUADPACK integration routines (quad_qag, quad_qags, quad_qagi, quad_qawc,
// quad_qawf, quad_qawo, quad_qaws, quad_qagp, quad_control).  The Fortran
// routines themselves are the package dii/maxima/slatec (@slatec).

// ---------------------------------------------------------------------------
// Private translation of the parts of plot.lisp's COERCE-FLOAT-FUN used by
// GET-INTEGRAND (plot.lisp is not part of the port).  The integrand is
// always coerced with $float, and it is always called while quadpack.lisp
// binds *PLOT-REALPART* to NIL.

///|
/// plot.lisp's MAYBE-REALPART with *PLOT-REALPART* = NIL: the real part of
/// X when its imaginary part is zero, else NIL.
fn quadpack__maybe_realpart(x : Value) -> Value raise {
  let ri = trisplit(x)
  if zerop1(cdr(ri)).truthy() {
    car(ri)
  } else {
    Nil
  }
}

///|
/// The Lisp ERRCATCH macro: `Some(value)` on success, None when a Maxima
/// or Lisp error (or a throw to an errcatch tag) occurred.
fn quadpack__errcatch(f : () -> Value raise) -> Value? raise {
  let ec = cons(symval(q_bindlist), symval(q_loclist))
  with_specials([(q_errcatch, ec), (q_ear_mdebug, Nil)], () => {
    let r = f() catch {
      LispError::Throw(tag, _) as e =>
        if eq(tag, q_macsyma_quit) || eq(tag, q_errorsw) || eq(tag, q_rat_err) {
          errlfun1(ec) |> ignore
          return None
        } else {
          raise e
        }
      LispError::ReturnFrom(_, _) as e => raise e
      LispError::Go(_) as e => raise e
      e => {
        if !is_maxima_error(e) {
          // We store the error report message in the error variable and
          // print the message if errormsg is true.
          let msg = match e {
            LispError::SimpleError(m) => m
            LispError::Condition(_, m, _) => m
            _ => e.to_string()
          }
          set(q_d_error, mk_simp(q_mlist, [Str(msg)])) |> ignore
          if symval(q_d_errormsg).truthy() {
            d_errormsg() |> ignore
          }
        }
        errlfun1(ec) |> ignore
        return None
      }
    }
    Some(r)
  })
}

///|
/// The check a compiled `(lambda (g1 ... gn) ...)` makes on its argument
/// count (a CL program error, not a Maxima error).
fn quadpack__check_nargs(actuals : Array[Value], nargs : Int) -> Unit raise {
  if actuals.length() != nargs {
    raise LispError::SimpleError(
      "invalid number of arguments: " + actuals.length().to_string(),
    )
  }
}

///|
/// COERCE-MAXIMA-FUNCTION-OR-MAXIMA-LAMBDA with :float-fun '$float.
fn quadpack__coerce_maxima_function(nargs : Int, expr : Value) -> Value {
  lfunc("coerce-maxima-function", actuals => {
    quadpack__check_nargs(actuals, nargs)
    with_specials(
      [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
      () => {
        // Just always try to convert the result with float-fun, which
        // handles things like $%pi.
        let result = quadpack__errcatch(() => d_float(
          quadpack__maybe_realpart(mapply(expr, list(actuals), t)),
        ))
        match result {
          Some(v) => v
          None => t
        }
      },
    )
  })
}

///|
/// COERCE-LISP-FUNCTION-OR-LISP-LAMBDA with :float-fun '$float.
fn quadpack__coerce_lisp_function(nargs : Int, expr : Value) -> Value {
  lfunc("coerce-lisp-function", actuals => {
    quadpack__check_nargs(actuals, nargs)
    with_specials(
      [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
      () => {
        let result = quadpack__maybe_realpart(apply(expr, list(actuals)))
        // Always use float-fun.
        d_float(result)
      },
    )
  })
}

///|
/// %COERCE-FLOAT-FUN with FLOAT-FUN = '$float: a Lisp function which
/// evaluates EXPR, a function name, lambda expression or general Maxima
/// expression in the variables LVARS, to a float (T when the evaluation
/// fails).
fn quadpack__coerce_float_fun(
  expr : Value,
  lvars : Value,
  fname : Value,
) -> Value raise {
  let nargs_of = (lv : Value) => if lv.truthy() { length(cdr(lv)) } else { 1 }
  let apply_form = () => {
    let a = if lvars.truthy() { lvars } else { mk(q_mlist, [gensym()]) }
    quadpack__coerce_float_fun(mk(q_d_apply, [expr, a]), a, fname)
  }
  // (A cons is never a CL function, so the first case of the Lisp code,
  // (and (consp expr) (functionp expr)), cannot occur.)
  if expr is Str(_) && getopr0(expr).truthy() {
    // expr is a string which names an operator (e.g. "!" "+" or a
    // user-defined operator)
    let a = if lvars.truthy() { lvars } else { mk(q_mlist, [gensym()]) }
    return quadpack__coerce_float_fun(
      mk(q_d_apply, [getopr0(expr), a]),
      a,
      fname,
    )
  }
  if symbolp(expr) &&
    !memq(expr, lvars).truthy() &&
    !d_constantp(expr).truthy() {
    if fboundp(expr) {
      return quadpack__coerce_lisp_function(nargs_of(lvars), expr)
    }
    let mexpr = mget(expr, q_mexpr)
    if mexpr.truthy() {
      // expr is name of a Maxima function defined by := or define
      let args = cdr(second(mexpr))
      return quadpack__coerce_maxima_function(length(args), expr)
    }
    if get(expr, q_mfexpr_star).truthy() ||
      mget(expr, q_mmacro).truthy() ||
      get(d_nounify(expr), q_operators).truthy() ||
      get(d_verbify(expr), q_operators).truthy() {
      return apply_form()
    }
    return merror(Str("~a: unknown function: ~M"), list2(fname, expr))
  }
  if expr is Cons(_) && eq(caar(expr), q_lambda) {
    let args = cdr(second(expr))
    return quadpack__coerce_maxima_function(length(args), expr)
  }
  // A general expression.
  let vars = cdr(
    if lvars.truthy() {
      lvars
    } else {
      d_sort(with_special(q_d_listconstvars, Nil, () => d_listofvars(expr)))
    },
  )
  let subscripted = remove_if(v => atom(v), vars)
  let symbols = remove_if(v => !atom(v), vars)
  let nargs = length(vars)
  // Catch any errors from evaluating the function.  We're assuming that if
  // an error is caught, the result is not a number.
  let evaluate = () => with_specials(
    [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
    () => match
      quadpack__errcatch(() => d_float(quadpack__maybe_realpart(meval(expr)))) {
      Some(v) => v
      None => t
    },
  )
  if subscripted is Nil {
    lfunc("coerce-float-fun", actuals => {
      quadpack__check_nargs(actuals, nargs)
      progv(vars, list(actuals), evaluate)
    })
  } else {
    // A subscripted variable is not a symbol and cannot be bound, so it is
    // MSET around the call and its old value put back.
    lfunc("coerce-float-fun", actuals => {
      quadpack__check_nargs(actuals, nargs)
      let saved = mapcar(v => meval(v), subscripted)
      let vals = Collector::new()
      let mut i = 0
      for v in vars.iter() {
        if i >= actuals.length() {
          break
        }
        if atom(v) {
          vals.add(actuals[i])
        } else {
          mset(v, actuals[i]) |> ignore
        }
        i = i + 1
      }
      // The restore has to run even when the evaluation exits non-locally.
      let restore = () => {
        let mut s = saved
        for v in subscripted.iter() {
          mset(v, car(s)) |> ignore
          s = cdr(s)
        }
      }
      let r = progv(symbols, vals.result(), evaluate) catch {
        e => {
          restore()
          raise e
        }
      }
      restore()
      r
    })
  }
}

// ---------------------------------------------------------------------------
// quadpack.lisp

///|
/// macro GET-INTEGRAND: `(coerce-float-fun fun `((mlist) ,var))`.
fn get_integrand(fun : Value, var_ : Value) -> Value raise {
  let lvars = mk(q_mlist, [var_])
  if !d_listp(lvars).truthy() {
    merr("coerce-float-fun: expecting a Maxima list, found: ~M", [lvars])
    |> ignore
  }
  quadpack__coerce_float_fun(fun, lvars, Str("coerce-float-fun"))
}

///|
fn float_or_lose(val : Value) -> Value raise {
  let v = d_float(val)
  if numberp(v) {
    v
  } else {
    raise LispError::SimpleError(
      format_to_string("~A is not a real floating-point number", [val]),
    )
  }
}

///|
/// macro FLOAT-INTEGRAND-OR-LOSE: convert the maxima function FUN of the
/// one variable VAR to a function returning a float that is suitable for
/// use as the integrand for the quadpack routines.  If the integrand cannot
/// be evaluated at the specified point, signal an error.
fn float_integrand_or_lose(
  name : Value,
  fun : Value,
  var_ : Value,
) -> Value raise {
  let f = get_integrand(fun, var_)
  lfunc("float-integrand", args => {
    let x = arg(args, 0)
    let result = funcall(f, [x])
    if !floatp(result) {
      merr(
        "~M: Numerical evaluation of ~M at ~M is not a float or is not defined",
        [name, fun, x],
      )
      |> ignore
    }
    result
  })
}

///|
/// The integrand as the @slatec routines want it.
fn quadpack__integrand(
  name : Value,
  fun : Value,
  var_ : Value,
) -> ((Double) -> Double raise) raise {
  let f = float_integrand_or_lose(name, fun, var_)
  x => to_double(funcall(f, [Flo(x)]))
}

///|
/// `(float-or-lose v)` as a Double.
fn quadpack__flo(v : Value) -> Double raise {
  to_double(float_or_lose(v))
}

///|
/// A Lisp integer argument passed to an f2cl INTEGER4 parameter.
fn quadpack__int4(v : Value) -> Int raise {
  match v {
    Fix(_) => to_int(v)
    _ =>
      raise LispError::SimpleError(
        format_to_string("The value ~S is not of type (SIGNED-BYTE 32)", [v]),
      )
  }
}

///|
/// The size argument of MAKE-ARRAY.
fn quadpack__array_size(n : Int) -> Int raise {
  if n < 0 {
    raise LispError::SimpleError(
      "The value " + n.to_string() + " is not of type (MOD 4611686018427387901)",
    )
  }
  n
}

///|
/// `(* k limit)` for the work array sizes (a Lisp error if LIMIT is not an
/// integer).
fn quadpack__times(k : Int, limit : Value) -> Int raise {
  match limit {
    Fix(_) => k * to_int(limit)
    _ =>
      raise LispError::SimpleError(
        format_to_string("The value ~S is not of type NUMBER", [limit]),
      )
  }
}

///|
/// The HANDLER-CASE around each QUADPACK call: any error signaled while
/// integrating makes the function return the noun form NOUN.  An MERROR at
/// top level is not a condition in Maxima (it prints its message and throws
/// to the top level); it signals MAXIMA-$ERROR only under
/// *MERROR-SIGNALS-$ERROR-P* or inside ERRCATCH.  Floating-point traps,
/// which SBCL signals and the @slatec routines do not, are detected by a
/// non-finite result.
fn quadpack__handler_case(
  body : () -> (Double, Double, Int, Int) raise,
  noun : () -> Value,
) -> Value raise {
  let r = body() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    e => {
      if is_maxima_error(e) &&
        !(
          symval(q_ear_merror_signals__dolerror_p).truthy() ||
          (!symval(q_ear_mdebug).truthy() && symval(q_errcatch).truthy())
        ) {
        raise e
      }
      if symval(q_ear_debug_quadpack).truthy() {
        write_string(e.to_string())
      }
      return noun()
    }
  }
  let (result, abserr, neval, ier) = r
  if result.is_nan() ||
    result.is_inf() ||
    abserr.is_nan() ||
    abserr.is_inf() {
    if symval(q_ear_debug_quadpack).truthy() {
      write_string("arithmetic error FLOATING-POINT-OVERFLOW signalled")
    }
    return noun()
  }
  mk(q_mlist, [Flo(result), Flo(abserr), int(neval), int(ier)])
}

///|
/// `((mequal) $name ,val)`
fn quadpack__opt(name : Value, val : Value) -> Value {
  mk(q_mequal, [name, val])
}

///|
fn d_quad_qag(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  key : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qag)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  if !(integerp(key) && num_ge(key, int(1)) && num_le(key, int(6))) {
    merr("~M: Key must be 1, 2, 3, 4, 5, or 6; found: ~M", [pretty_fname, key])
    |> ignore
  }
  let lenw = quadpack__array_size(quadpack__times(4, limit))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  quadpack__handler_case(
    () => {
      let (result, abserr, neval, ier, _last) = @slatec.dqag(
        quadpack__integrand(q_d_quad_qag, fun, var_),
        quadpack__flo(a),
        quadpack__flo(b),
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        quadpack__int4(key),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limit),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qag, [
      fun,
      var_,
      a,
      b,
      key,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
fn d_quad_qags(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qags)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  let lenw = quadpack__array_size(quadpack__times(4, limit))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  quadpack__handler_case(
    () => {
      let (result, abserr, neval, ier, _last) = @slatec.dqags(
        quadpack__integrand(q_d_quad_qags, fun, var_),
        quadpack__flo(a),
        quadpack__flo(b),
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limit),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qags, [
      fun,
      var_,
      a,
      b,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
fn d_quad_qagi(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qagi)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  // Massage the limits a and b into what Quadpack QAGI wants.
  // Cases to handle: (minf, x), (x, inf), (minf, inf).  Everything else is
  // an error.
  let fixup = (low : Value, high : Value) => {
    if eq(d_limit(list1(low)), q_d_minf) {
      if eq(d_limit(list1(high)), q_d_inf) {
        (int(0), int(2))
      } else {
        let bnd = d_float(high)
        (bnd, d_limit(list1(low)))
      }
    } else if eq(d_limit(list1(high)), q_d_inf) {
      let bnd = d_float(low)
      (bnd, d_limit(list1(high)))
    } else {
      merr("~M: Unexpected limits of integration: ~M, ~M~%", [
        pretty_fname,
        low,
        high,
      ])
      |> ignore
      (Nil, Nil)
    }
  }
  let (bound, inf_type) = fixup(a, b)
  let lenw = quadpack__array_size(quadpack__times(4, limit))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  let infinity = if eql(inf_type, Fix(1L)) || eq(inf_type, q_d_inf) {
    // Interval is [bound, infinity]
    1
  } else if eql(inf_type, Fix(-1L)) || eq(inf_type, q_d_minf) {
    // Interval is [-infinity, bound]
    -1
  } else if eql(inf_type, Fix(2L)) || eq(inf_type, q_d_both) {
    // Interval is [-infinity, infinity]
    2
  } else {
    raise LispError::SimpleError(
      prin1_to_string(inf_type) +
      " fell through ECASE expression. Wanted one of (1 $INF -1 $MINF 2 $BOTH).",
    )
  }
  quadpack__handler_case(
    () => {
      let (result, abserr, neval, ier, _last) = @slatec.dqagi(
        quadpack__integrand(q_d_quad_qagi, fun, var_),
        quadpack__flo(bound),
        infinity,
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limit),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qagi, [
      fun,
      var_,
      a,
      b,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
fn d_quad_qawc(
  fun : Value,
  var_ : Value,
  c : Value,
  a : Value,
  b : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qawc)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  let lenw = quadpack__array_size(quadpack__times(4, limit))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  quadpack__handler_case(
    () => {
      let (_c, result, abserr, neval, ier, _last) = @slatec.dqawc(
        quadpack__integrand(q_d_quad_qawc, fun, var_),
        quadpack__flo(a),
        quadpack__flo(b),
        quadpack__flo(c),
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limit),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qawc, [
      fun,
      var_,
      c,
      a,
      b,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
fn d_quad_qawf(
  fun : Value,
  var_ : Value,
  a : Value,
  omega : Value,
  trig : Value,
  epsabs? : Value = Flo(1.0e-10),
  limit? : Value = Fix(200L),
  maxp1? : Value = Fix(100L),
  limlst? : Value = Fix(10L),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qawf)
  let leniw = quadpack__times(1, limit)
  let lenw = quadpack__array_size(2 * leniw + quadpack__times(25, maxp1))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(leniw),
    0,
  )
  let integr = if eql(trig, Fix(1L)) || eq(trig, q_p_cos) || eq(trig, q_d_cos) {
    1
  } else if eql(trig, Fix(2L)) || eq(trig, q_p_sin) || eq(trig, q_d_sin) {
    2
  } else {
    merr("~M: the name of the trig function should be sin or cos, not ~M.", [
      pretty_fname,
      trig,
    ])
    |> ignore
    0
  }
  quadpack__handler_case(
    () => {
      let (_integr, result, abserr, neval, ier, _lst) = @slatec.dqawf(
        quadpack__integrand(q_d_quad_qawf, fun, var_),
        quadpack__flo(a),
        quadpack__flo(omega),
        integr,
        quadpack__flo(epsabs),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limlst),
        0,
        leniw,
        quadpack__int4(maxp1),
        lenw,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qawf, [
      fun,
      var_,
      a,
      omega,
      trig,
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
      quadpack__opt(q_d_maxp1, maxp1),
      quadpack__opt(q_d_limlst, limlst),
    ]),
  )
}

///|
fn d_quad_qawo(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  omega : Value,
  trig_name : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  maxp1? : Value = Fix(100L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qawo)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  let leniw = quadpack__times(1, limit)
  let lenw = quadpack__array_size(2 * leniw + quadpack__times(25, maxp1))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(leniw),
    0,
  )
  let integr = if eq(trig_name, q_p_cos) || eq(trig_name, q_d_cos) {
    1
  } else if eq(trig_name, q_p_sin) || eq(trig_name, q_d_sin) {
    2
  } else {
    merr("~M: the name of the trig function should be sin or cos, not ~M.", [
      pretty_fname,
      trig_name,
    ])
    |> ignore
    0
  }
  quadpack__handler_case(
    () => {
      let (_integr, result, abserr, neval, ier, _last) = @slatec.dqawo(
        quadpack__integrand(q_d_quad_qawo, fun, var_),
        quadpack__flo(a),
        quadpack__flo(b),
        quadpack__flo(omega),
        integr,
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        0.0,
        0.0,
        0,
        0,
        leniw,
        quadpack__int4(maxp1),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qawo, [
      fun,
      var_,
      a,
      b,
      omega,
      trig_name,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
      quadpack__opt(q_d_maxp1, maxp1),
    ]),
  )
}

///|
fn d_quad_qaws(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  alfa : Value,
  beta : Value,
  wfun : Value,
  epsrel? : Value = Flo(1.0e-08),
  limit? : Value = Fix(200L),
  epsabs? : Value = Flo(0.0),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qaws)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  let lenw = quadpack__array_size(quadpack__times(4, limit))
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  quadpack__handler_case(
    () => {
      let (_a, _b, _alfa, _beta, _int, result, abserr, neval, ier, _last) = @slatec.dqaws(
        quadpack__integrand(q_d_quad_qaws, fun, var_),
        quadpack__flo(a),
        quadpack__flo(b),
        quadpack__flo(alfa),
        quadpack__flo(beta),
        quadpack__int4(wfun),
        quadpack__flo(epsabs),
        quadpack__flo(epsrel),
        0.0,
        0.0,
        0,
        0,
        quadpack__int4(limit),
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qaws, [
      fun,
      var_,
      a,
      b,
      alfa,
      beta,
      wfun,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
fn d_quad_qagp(
  fun : Value,
  var_ : Value,
  a : Value,
  b : Value,
  points : Value,
  epsrel? : Value = Flo(1.0e-08),
  epsabs? : Value = Flo(0.0),
  limit? : Value = Fix(200L),
) -> Value raise {
  let pretty_fname = quadpack__pretty_fname(q_d_quad_qagp)
  quad_argument_check(pretty_fname, fun, var_, a, b) |> ignore
  if !listp(points) {
    raise LispError::SimpleError(
      format_to_string("The value ~S is not of type LIST", [points]),
    )
  }
  let npts2 = 2 + length(cdr(points))
  let p : FixedArray[Double] = FixedArray::make(npts2, 0.0)
  let leniw = {
    let l = quadpack__times(1, limit)
    let m = 3 * npts2 - 2
    if l > m {
      l
    } else {
      m
    }
  }
  let lenw = quadpack__array_size(2 * leniw - npts2)
  let work : FixedArray[Double] = FixedArray::make(lenw, 0.0)
  let iwork : FixedArray[Int] = FixedArray::make(
    quadpack__array_size(quadpack__times(1, limit)),
    0,
  )
  // Check the list of singular points.  Each point must be a real in the
  // open interval (a, b).  If the point is valid, save it to the array P.
  // Otherwise accumulate a list of the invalid points so we can print a
  // nice error message with a list of the invalid points.
  let a = float_or_lose(a)
  let b = float_or_lose(b)
  let invalid = Collector::new()
  let mut k = 0
  for xp in cdr(points).iter() {
    let x = float_or_lose(xp)
    if num_lt(a, x) && num_lt(x, b) {
      p[k] = to_double(x)
    } else {
      invalid.add(x)
    }
    k = k + 1
  }
  let invalid_points = invalid.result()
  // If there are invalid points, throw an error.
  if invalid_points.truthy() {
    merr("~M: singular points must be in the open interval (~M, ~M):  ~M", [
      pretty_fname,
      a,
      b,
      make_mlist_l(invalid_points),
    ])
    |> ignore
  }
  quadpack__handler_case(
    () => {
      let f = quadpack__integrand(q_d_quad_qagp, fun, var_)
      let fa = quadpack__flo(a)
      let fb = quadpack__flo(b)
      let fepsabs = quadpack__flo(epsabs)
      let fepsrel = quadpack__flo(epsrel)
      // IWORK has LIMIT elements, fewer than the LENIW DQAGP is told about
      // when there are many points; the Lisp then signals an array index
      // error inside DQAGP (caught below), where the MoonBit arrays would
      // abort.
      if leniw > iwork.length() {
        raise LispError::SimpleError(
          "Invalid index " +
          iwork.length().to_string() +
          " for (SIMPLE-ARRAY (SIGNED-BYTE 32) (" +
          iwork.length().to_string() +
          ")), should be a non-negative integer below " +
          iwork.length().to_string() +
          ".",
        )
      }
      let (result, abserr, neval, ier, _last) = @slatec.dqagp(
        f,
        fa,
        fb,
        npts2,
        p,
        fepsabs,
        fepsrel,
        0.0,
        0.0,
        0,
        0,
        leniw,
        lenw,
        0,
        iwork,
        work,
      )
      (result, abserr, neval, ier)
    },
    () => mk(q_d_quad_qagp, [
      fun,
      var_,
      a,
      b,
      points,
      quadpack__opt(q_d_epsrel, epsrel),
      quadpack__opt(q_d_epsabs, epsabs),
      quadpack__opt(q_d_limit, limit),
    ]),
  )
}

///|
/// Error checking similar to that done by $defint.
fn quad_argument_check(
  name : Value,
  exp_ : Value,
  var_ : Value,
  ll : Value,
  ul : Value,
) -> Value raise {
  ratdisrep(exp_) |> ignore
  let var_ = ratdisrep(var_)
  let ll = ratdisrep(ll)
  let ul = ratdisrep(ul)
  if d_constantp(var_).truthy() {
    merr("~M: Variable of integration not a variable: ~M", [name, var_])
    |> ignore
  }
  if !(d_subvarp(var_).truthy() || atom(var_)) {
    merr("~M: Improper variable of integration: ~M", [name, var_])
  } else if among(var_, ul).truthy() || among(var_, ll).truthy() {
    merr("~M: Limit contains variable of integration: ~M", [name, var_])
  } else {
    Nil
  }
}

///|
fn quad_control(parameter : Value, new_value? : Value = Nil) -> Value raise {
  let which = if eq(parameter, q_d_current_error) {
    1
  } else if eq(parameter, q_d_control) {
    2
  } else if eq(parameter, q_d_max_message) {
    4
  } else {
    merr("Parameter should be current_error, control, or max_message", [])
    |> ignore
    0
  }
  let ivalue = if new_value.truthy() { quadpack__int4(new_value) } else { 0 }
  int(@slatec.j4save(which, ivalue, new_value.truthy()))
}

///|
fn d_quad_control(parameter : Value, new_value : Value) -> Value raise {
  quad_control(
    parameter,
    new_value=if new_value.truthy() { car(new_value) } else { Nil },
  )
}

// ---------------------------------------------------------------------------
// DEFMFUN wrappers.  These functions take Maxima keyword options
// (epsrel = 1e-3, ...), which DEFMFUN converts with DEFMFUN-KEYWORDS, and
// report errors with the "pretty" function name built from the lambda
// list, e.g. quad_qags(fun,var,a,b,epsrel = 1.0e-8,limit = 200,epsabs = 0.0).

///|
/// Required parameters and keyword parameters (with their default values)
/// of each defmfun, in lambda-list order.
fn quadpack__lambda_list(name : Value) -> (Array[String], Array[(String, Value)]) {
  let qag_keys : Array[(String, Value)] = [
    ("epsrel", Flo(1.0e-08)),
    ("limit", Fix(200L)),
    ("epsabs", Flo(0.0)),
  ]
  if eq(name, q_d_quad_qag) {
    (["fun", "var", "a", "b", "key"], qag_keys)
  } else if eq(name, q_d_quad_qags) {
    (["fun", "var", "a", "b"], qag_keys)
  } else if eq(name, q_d_quad_qagi) {
    (["fun", "var", "a", "b"], qag_keys)
  } else if eq(name, q_d_quad_qawc) {
    (["fun", "var", "c", "a", "b"], qag_keys)
  } else if eq(name, q_d_quad_qawf) {
    (
      ["fun", "var", "a", "omega", "trig"],
      [
        ("epsabs", Flo(1.0e-10)),
        ("limit", Fix(200L)),
        ("maxp1", Fix(100L)),
        ("limlst", Fix(10L)),
      ],
    )
  } else if eq(name, q_d_quad_qawo) {
    (
      ["fun", "var", "a", "b", "omega", "trig_name"],
      [
        ("epsrel", Flo(1.0e-08)),
        ("limit", Fix(200L)),
        ("maxp1", Fix(100L)),
        ("epsabs", Flo(0.0)),
      ],
    )
  } else if eq(name, q_d_quad_qaws) {
    (["fun", "var", "a", "b", "alfa", "beta", "wfun"], qag_keys)
  } else {
    // $quad_qagp
    (
      ["fun", "var", "a", "b", "points"],
      [("epsrel", Flo(1.0e-08)), ("epsabs", Flo(0.0)), ("limit", Fix(200L))],
    )
  }
}

///|
/// %%PRETTY-FNAME of a quad_* function.
fn quadpack__pretty_fname(name : Value) -> Value {
  let (req, keys) = quadpack__lambda_list(name)
  let args : Array[Value] = req.map(s => sym("$" + s))
  for k in keys {
    args.push(quadpack__opt(sym("$" + k.0), k.1))
  }
  mk(name, args)
}

///|
/// The DEFMFUN wrapper of a quad_* function with keyword arguments: check
/// the number of arguments, convert the keyword options and call IMPL with
/// the required arguments and the keyword values (None when not given).
fn quadpack__defmfun(
  name : Value,
  impl_ : (Array[Value], Array[Value?]) -> Value raise,
) -> Unit {
  defun(name, args => {
    let (req, keys) = quadpack__lambda_list(name)
    let pretty_fname = quadpack__pretty_fname(name)
    let nreq = req.length()
    if args.length() < nreq {
      merr("~M: expected at least ~M arguments but got ~M: ~M", [
        pretty_fname,
        int(nreq),
        int(args.length()),
        cons(list1(q_mlist), list(args)),
      ])
      |> ignore
    }
    let kws = defmfun_keywords(
      pretty_fname,
      rest_args(args, nreq),
      list(keys.map(k => sym("$" + k.0))),
    )
    // CL &key parsing: the first occurrence of a keyword wins.
    let vals : Array[Value?] = keys.map(k => {
      let key = kw(k.0)
      let mut l = kws
      let mut found : Value? = None
      while l is Cons(_) {
        if eq(car(l), key) {
          found = Some(cadr(l))
          break
        }
        l = cddr(l)
      }
      found
    })
    impl_(args[0:nreq].to_array(), vals)
  })
}

///|
fn init_quadpack() -> Unit raise {
  quadpack__defmfun(q_d_quad_qag, (r, k) => d_quad_qag(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    epsrel?=k[0],
    limit?=k[1],
    epsabs?=k[2],
  ))
  quadpack__defmfun(q_d_quad_qags, (r, k) => d_quad_qags(
    r[0],
    r[1],
    r[2],
    r[3],
    epsrel?=k[0],
    limit?=k[1],
    epsabs?=k[2],
  ))
  quadpack__defmfun(q_d_quad_qagi, (r, k) => d_quad_qagi(
    r[0],
    r[1],
    r[2],
    r[3],
    epsrel?=k[0],
    limit?=k[1],
    epsabs?=k[2],
  ))
  quadpack__defmfun(q_d_quad_qawc, (r, k) => d_quad_qawc(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    epsrel?=k[0],
    limit?=k[1],
    epsabs?=k[2],
  ))
  quadpack__defmfun(q_d_quad_qawf, (r, k) => d_quad_qawf(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    epsabs?=k[0],
    limit?=k[1],
    maxp1?=k[2],
    limlst?=k[3],
  ))
  quadpack__defmfun(q_d_quad_qawo, (r, k) => d_quad_qawo(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    r[5],
    epsrel?=k[0],
    limit?=k[1],
    maxp1?=k[2],
    epsabs?=k[3],
  ))
  quadpack__defmfun(q_d_quad_qaws, (r, k) => d_quad_qaws(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    r[5],
    r[6],
    epsrel?=k[0],
    limit?=k[1],
    epsabs?=k[2],
  ))
  quadpack__defmfun(q_d_quad_qagp, (r, k) => d_quad_qagp(
    r[0],
    r[1],
    r[2],
    r[3],
    r[4],
    epsrel?=k[0],
    epsabs?=k[1],
    limit?=k[2],
  ))
  // defmfun $quad_control (parameter &rest new-value)
  let control_pretty = mk(q_d_quad_control, [
    sym("$parameter"),
    mk(q_mlist, [sym("$new-value")]),
  ])
  defun(q_d_quad_control, args => {
    if args.length() < 1 {
      merr("~M: expected at least ~M arguments but got ~M: ~M", [
        control_pretty,
        int(1),
        int(args.length()),
        cons(list1(q_mlist), list(args)),
      ])
      |> ignore
    }
    d_quad_control(args[0], rest_args(args, 1))
  })
}
