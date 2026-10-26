// Port of src/intpol.lisp: find_root and bf_find_root (interpolation
// routine by CFFK, bigfloat version by rtoy).
//
// FIND-ROOT-SUBR and INTERPOLATE-CHECK live in the BIGFLOAT package and
// use its generic arithmetic (bf_add, bf_lt, ...; see docs/BIGFLOAT.md).
//
// plot.lisp is not ported, so COERCE-FLOAT-FUN / COERCE-BFLOAT-FUN (and
// the helpers they need) are translated here as private functions.

///|
/// defmspec $interpolate: the old name of find_root.
fn d_interpolate(form : Value) -> Value raise {
  let s = implode(mstring(cons(list1(q_d_find_root), cdr(form))))
  format(
    t,
    "NOTE: The interpolate function has been renamed to find_root.\nThe variables intpolabs, intpolrel, and intpolerror have been renamed\nto find_root_abs, find_root_rel, and find_root_error, respectively.\nPerhaps you meant to enter `~a'.~%",
    [s],
  )
  |> ignore
  q_d_done
}

///|
/// FIND-ROOT-SUBR, returning all of its CL values: either the root (or
/// '$find_root_error) and two Nils, or (nil left right) when the function
/// or the bounds do not evaluate to numbers.
fn bf_find_root_subr_mv(
  f : Value,
  left : Value,
  right : Value,
  abserr? : Value,
  relerr? : Value,
) -> (Value, Value, Value) raise {
  let abserr = match abserr {
    Some(v) => v
    None => symval(q_d_find_root_abs)
  }
  let relerr = match relerr {
    Some(v) => v
    None => symval(q_d_find_root_rel)
  }
  // Try to convert to a BIGFLOAT type.  If that fails, just return the
  // argument.  Set the flags errset, errcatch, $errormsg and *mdebug* so we
  // can catch the error, but disable printing of any error messages.
  let convert = (s : Value) => with_specials(
    [
      (q_errset, Nil),
      (q_errcatch, t),
      (q_d_errormsg, Nil),
      (q_ear_mdebug, Nil),
    ],
    () => match errset(() => bf_to(s)) {
      Some(v) if v.truthy() => v
      _ => s
    },
  )
  // Don't want to bind $numer to T here.  This causes things like
  // log(400)^400 to be computed using double-floats (which overflows),
  // which is not what we want if we're doing bfloat arithmetic.
  let (left0, right0) = with_special(q_d__pctenumer, t, () => {
    let l = convert(left)
    let r = convert(right)
    (l, r)
  })
  let mut left = left0
  let mut right = right0
  if !(bf_numberp(left) && bf_numberp(right)) {
    // The interval boundaries must have numerical values
    return (Nil, left, right)
  }
  if bf_lt(right, left) {
    // Make left the lower and right the upper bound of the interval
    let tmp = left
    left = right
    right = tmp
  }
  let mut lin = 0
  let mut a = left
  let mut b = right
  let mut fa = convert(funcall(f, [maxima_to(left)]))
  let mut fb = convert(funcall(f, [maxima_to(right)]))
  if !(bf_numberp(fa) && bf_numberp(fb)) {
    return (Nil, a, b)
  }
  if bf_le(bf_abs(fa), bf_to(abserr)) {
    // If a or b is already small enough, return it as the root
    return (a, Nil, Nil)
  }
  if bf_le(bf_abs(fb), bf_to(abserr)) {
    return (b, Nil, Nil)
  }
  if bf_plusp(bf_mul(bf_float_sign(fa), bf_float_sign(fb))) {
    if eq(symval(q_d_find_root_error), t) {
      merror(
        Str("find_root: function has same sign at endpoints: ~M, ~M"),
        list2(
          mk(q_mequal, [list2(list1(q_f), a), fa]),
          mk(q_mequal, [list2(list1(q_f), b), fb]),
        ),
      )
      |> ignore
    } else {
      return (q_d_find_root_error, Nil, Nil)
    }
  }
  if bf_plusp(fa) {
    let tf = fa
    fa = fb
    fb = tf
    let ta = a
    a = b
    b = ta
  }
  // Use binary search to close in on the root
  while lin < 3 {
    let c = bf_mul(Flo(0.5), bf_add(a, b))
    let fc = convert(funcall(f, [maxima_to(c)]))
    if !bf_numberp(fc) {
      return (Nil, a, b)
    }
    if bf_interpolate_check(a, c, b, fc, abserr, relerr).truthy() {
      return (c, Nil, Nil)
    }
    if bf_lt(
        bf_abs(bf_sub(fc, bf_mul(Flo(0.5), bf_add(fa, fb)))),
        bf_mul(Flo(0.1), bf_sub(fb, fa)),
      ) {
      lin = lin + 1
    } else {
      lin = 0
    }
    if bf_plusp(fc) {
      fb = fc
      b = c
    } else {
      fa = fc
      a = c
    }
  }
  // Now use the regula falsi
  while true {
    let c = if bf_plusp(bf_add(fb, fa)) {
      bf_add(a, bf_mul(bf_sub(b, a), bf_div(fa, bf_sub(fa, fb))))
    } else {
      bf_add(b, bf_mul(bf_sub(a, b), bf_div(fb, bf_sub(fb, fa))))
    }
    let fc = convert(funcall(f, [maxima_to(c)]))
    if !bf_numberp(fc) {
      return (Nil, a, b)
    }
    if bf_interpolate_check(a, c, b, fc, abserr, relerr).truthy() {
      return (c, Nil, Nil)
    }
    if bf_plusp(fc) {
      fb = fc
      b = c
    } else {
      fa = fc
      a = c
    }
  }
  (Nil, Nil, Nil)
}

///|
/// FIND-ROOT-SUBR (primary value only); see `bf_find_root_subr_mv`.
fn bf_find_root_subr(
  f : Value,
  left : Value,
  right : Value,
  abserr? : Value,
  relerr? : Value,
) -> Value raise {
  bf_find_root_subr_mv(f, left, right, abserr?, relerr?).0
}

///|
/// INTERPOLATE-CHECK: true when c is close enough to the root.
fn bf_interpolate_check(
  a : Value,
  c : Value,
  b : Value,
  fc : Value,
  abserr : Value,
  relerr : Value,
) -> Value raise {
  let big_fc = bf_gt(bf_abs(fc), bf_to(abserr))
  let fc = bf_max(bf_abs(a), list1(bf_abs(b)))
  let ok = big_fc &&
    bf_gt(bf_abs(bf_sub(b, c)), bf_mul(bf_to(relerr), fc)) &&
    bf_gt(bf_abs(bf_sub(c, a)), bf_mul(bf_to(relerr), fc))
  lbool(!ok)
}

///|
/// First value of keyword `key` in the plist `plist`, as CL's keyword
/// argument parsing would find it.
fn intpol__plist_get(plist : Value, key : Value) -> Value? {
  let mut l = plist
  while l is Cons(_) {
    if eq(car(l), key) {
      return Some(cadr(l))
    }
    l = cddr(l)
  }
  None
}

///|
/// %FIND-ROOT: the shared body of find_root and bf_find_root.  (The
/// generated contract declares two values; only the first is meaningful,
/// the second is always nil.)
fn p_find_root(
  name : Value,
  fun_or_expr : Value,
  args : Value,
) -> (Value, Value) raise {
  // Extract the keyword arguments from args, if any.
  let non_keyword = Collector::new()
  let kws = Collector::new()
  for arg in args.iter() {
    if listp(arg) && eq(caar(arg), q_mequal) {
      kws.add(arg)
    } else {
      non_keyword.add(arg)
    }
  }
  let non_keyword = non_keyword.result()
  let mut keywords = kws.result()
  if keywords.truthy() {
    keywords = defmfun_keywords(name, keywords, list2(q_d_abserr, q_d_relerr))
  }
  // The name tells us what error values to use, how to coerce the
  // function, and what function to use to convert to the desired float
  // type.
  let float_fun = if eq(name, q_d_find_root) {
    q_d_float
  } else if eq(name, q_d_bf_find_root) {
    q_d_bfloat
  } else {
    raise LispError::SimpleError(
      prin1_to_string(name) +
      " fell through ECASE expression. Wanted one of ($FIND_ROOT $BF_FIND_ROOT).",
    )
  }
  let fl = (x : Value) => intpol__float_fun(float_fun, x)
  let abserr = intpol__plist_get(keywords, kw("abserr"))
  let relerr = intpol__plist_get(keywords, kw("relerr"))
  match length(non_keyword) {
    2 => {
      // function case: f, lo, hi
      let ff = intpol__coerce_float_fun(float_fun, fun_or_expr, [])
      let lo = fl(first(non_keyword))
      let hi = fl(second(non_keyword))
      let (result, left, right) = bf_find_root_subr_mv(
        ff,
        lo,
        hi,
        abserr?,
        relerr?,
      )
      let v = if bf_numberp(result) {
        maxima_to(result)
      } else if eq(result, q_d_find_root_error) {
        symval(q_d_find_root_error)
      } else {
        mk(name, [fun_or_expr, maxima_to(left), maxima_to(right)])
      }
      (v, Nil)
    }
    3 => {
      // expr case: expr, var, lo, hi
      let ff = intpol__coerce_float_fun(
        float_fun,
        sub(intpol__lhs(fun_or_expr), intpol__rhs(fun_or_expr)),
        [mk(q_mlist, [first(non_keyword)])],
      )
      let lo = fl(second(non_keyword))
      let hi = fl(third(non_keyword))
      let (result, left, right) = bf_find_root_subr_mv(
        ff,
        lo,
        hi,
        abserr?,
        relerr?,
      )
      let v = if bf_numberp(result) {
        maxima_to(result)
      } else if eq(result, q_d_find_root_error) {
        symval(q_d_find_root_error)
      } else {
        mk(name, [
          fun_or_expr,
          first(non_keyword),
          maxima_to(left),
          maxima_to(right),
        ])
      }
      (v, Nil)
    }
    _ =>
      // wrong number of args
      (wna_err(name), Nil)
  }
}

///|
/// defmfun $find_root (fun-or-expr &rest args)
fn d_find_root(fun_or_expr : Value, args : Value) -> Value raise {
  p_find_root(q_d_find_root, fun_or_expr, args).0
}

///|
/// defmfun $bf_find_root: like find_root but operates on bfloats and
/// returns a bfloat result.
fn d_bf_find_root(fun_or_expr : Value, args : Value) -> Value raise {
  p_find_root(q_d_bf_find_root, fun_or_expr, args).0
}

///|
fn init_intpol() -> Unit raise {
  ()
}

// ---------------------------------------------------------------------------
// Private translations of csimp.lisp's $lhs / $rhs (defined inside a LET
// there, so missing from the contract).

///|
let intpol__relational_ops : Array[String] = [
  "mlessp", "mleqp", "mequal", "mnotequal", "$equal", "$notequal", "mgeqp", "mgreaterp",
  "%mlessp", "%mleqp", "%mequal", "%mnotequal", "%equal", "%notequal", "%mgeqp",
  "%mgreaterp", "mdefine", "mdefmacro", "msetq", "mset", "marrow", "%mdefine",
  "%mdefmacro", "%msetq", "%mset", "%marrow",
]

///|
/// Is `rel` a relation or infix-operator expression for $lhs/$rhs?
fn intpol__relation_p(rel : Value) -> Bool raise {
  let op = caar(rel)
  match op {
    Sym(_) => {
      let n = symbol_name(op)
      intpol__relational_ops.contains(n) || eq(get(op, q_led), q_parse_infix)
    }
    _ => false
  }
}

///|
/// `($lhs rel)`
fn intpol__lhs(rel : Value) -> Value raise {
  if atom(rel) {
    rel
  } else if intpol__relation_p(rel) {
    cadr(rel)
  } else {
    rel
  }
}

///|
/// `($rhs rel)`
fn intpol__rhs(rel : Value) -> Value raise {
  if atom(rel) {
    Fix(0L)
  } else if intpol__relation_p(rel) {
    caddr(rel)
  } else {
    Fix(0L)
  }
}

// ---------------------------------------------------------------------------
// Private translation of plot.lisp's COERCE-FLOAT-FUN machinery.

///|
/// `(funcall float-fun x)` for '$float or '$bfloat.
fn intpol__float_fun(float_fun : Value, x : Value) -> Value raise {
  if eq(float_fun, q_d_bfloat) {
    d_bfloat(x)
  } else {
    d_float(x)
  }
}

///|
/// plot.lisp's MAYBE-REALPART with *PLOT-REALPART* at its default (true).
fn intpol__maybe_realpart(x : Value) -> Value raise {
  d_realpart(x)
}

///|
/// The Lisp ERRCATCH macro: `Some(value)` on success, None when a Maxima
/// or Lisp error (or a throw to an errcatch tag) occurred.
fn intpol__errcatch(f : () -> Value raise) -> Value? raise {
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
/// COERCE-MAXIMA-FUNCTION-OR-MAXIMA-LAMBDA: a Lisp function applying the
/// Maxima function or lambda `expr` and converting the result with
/// `float_fun`; it returns T when the evaluation fails.
fn intpol__coerce_maxima_function(
  nargs : Int,
  expr : Value,
  float_fun : Value,
) -> Value {
  ignore(nargs)
  lfunc("coerce-maxima-function", actuals => with_specials(
    [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
    () => {
      // Just always try to convert the result with float-fun, which
      // handles things like $%pi.
      let result = intpol__errcatch(() => intpol__float_fun(
        float_fun,
        intpol__maybe_realpart(mapply(expr, list(actuals), t)),
      ))
      match result {
        Some(v) => v
        None => t
      }
    },
  ))
}

///|
/// COERCE-LISP-FUNCTION-OR-LISP-LAMBDA: same as above, but call APPLY
/// instead of MAPPLY.
fn intpol__coerce_lisp_function(
  nargs : Int,
  expr : Value,
  float_fun : Value,
) -> Value {
  ignore(nargs)
  lfunc("coerce-lisp-function", actuals => with_specials(
    [(q_d_ratprint, Nil), (q_d_numer, t), (q_ear_nounsflag, t)],
    () => {
      let result = intpol__maybe_realpart(apply(expr, list(actuals)))
      // Always use float-fun.
      intpol__float_fun(float_fun, result)
    },
  ))
}

///|
/// COERCE-FLOAT-FUN / COERCE-BFLOAT-FUN (selected by `float_fun`): `rest`
/// holds the optional variable list and/or function name.
fn intpol__coerce_float_fun(
  float_fun : Value,
  expr : Value,
  rest : Array[Value],
) -> Value raise {
  let who = if eq(float_fun, q_d_bfloat) {
    "coerce-bfloat-fun"
  } else {
    "coerce-float-fun"
  }
  let mut lvars : Value = Nil
  let mut fname : Value = Str(who)
  match rest.length() {
    0 => ()
    1 =>
      if rest[0] is Str(_) {
        fname = rest[0]
      } else if d_listp(rest[0]).truthy() {
        lvars = rest[0]
        fname = Str("coerce-float-fun")
      } else {
        merr(who + ": expecting a Maxima list, found: ~M", [rest[0]]) |> ignore
      }
    2 => {
      if d_listp(rest[0]).truthy() {
        lvars = rest[0]
      } else {
        merr(who + ": expecting a Maxima list, found: ~M", [rest[0]]) |> ignore
      }
      if rest[1] is Str(_) {
        fname = rest[1]
      } else {
        merr(who + ": expecting a string, found: ~M", [rest[1]]) |> ignore
      }
    }
    _ => merr(who + ": two many arguments given.", []) |> ignore
  }
  intpol__p_coerce_float_fun(float_fun, expr, lvars, fname)
}

///|
/// %COERCE-FLOAT-FUN: return a Lisp function which evaluates EXPR to a
/// float (or bfloat).  EXPR may name a Lisp function, a Maxima function, a
/// DEFMSPEC function, a Maxima macro, an operator (as a string), or a
/// simplifying function; or be a Maxima lambda expression or a general
/// Maxima expression.
fn intpol__p_coerce_float_fun(
  float_fun : Value,
  expr : Value,
  lvars : Value,
  fname : Value,
) -> Value raise {
  let nargs_of = (lv : Value) => if lv.truthy() { length(cdr(lv)) } else { 1 }
  let apply_form = () => {
    let a = if lvars.truthy() { lvars } else { mk(q_mlist, [gensym()]) }
    intpol__p_coerce_float_fun(float_fun, mk(q_d_apply, [expr, a]), a, fname)
  }
  // (A cons is never a CL function, so the first case of the Lisp code,
  // (and (consp expr) (functionp expr)), cannot occur.)
  if expr is Str(s) && getopr0(expr).truthy() {
    // expr is a string which names an operator (e.g. "!" "+" or a
    // user-defined operator)
    ignore(s)
    let a = if lvars.truthy() { lvars } else { mk(q_mlist, [gensym()]) }
    return intpol__p_coerce_float_fun(
      float_fun,
      mk(q_d_apply, [getopr0(expr), a]),
      a,
      fname,
    )
  }
  if symbolp(expr) &&
    !memq(expr, lvars).truthy() &&
    !d_constantp(expr).truthy() {
    if fboundp(expr) {
      return intpol__coerce_lisp_function(nargs_of(lvars), expr, float_fun)
    }
    let mexpr = mget(expr, q_mexpr)
    if mexpr.truthy() {
      // expr is name of a Maxima function defined by := or define
      let args = cdr(second(mexpr))
      return intpol__coerce_maxima_function(length(args), expr, float_fun)
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
    return intpol__coerce_maxima_function(length(args), expr, float_fun)
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
  // We don't want to set $numer to T when coercing to a bigfloat.  By
  // doing so, things like log(400)^400 get converted to double-floats,
  // which causes a double-float overflow.
  let numer = lbool(!eq(float_fun, q_d_bfloat))
  // Catch any errors from evaluating the function.  We're assuming that if
  // an error is caught, the result is not a number.
  let evaluate = () => with_specials(
    [(q_d_ratprint, Nil), (q_d_numer, numer), (q_ear_nounsflag, t)],
    () => match
      intpol__errcatch(() => intpol__float_fun(
        float_fun,
        intpol__maybe_realpart(meval(expr)),
      )) {
      Some(v) => v
      None => t
    },
  )
  let check_args = (actuals : Array[Value]) => if actuals.length() != nargs {
    raise LispError::SimpleError(
      "invalid number of arguments: " + actuals.length().to_string(),
    )
  }
  if subscripted is Nil {
    lfunc("coerce-float-fun", actuals => {
      check_args(actuals)
      progv(vars, list(actuals), evaluate)
    })
  } else {
    // A subscripted variable is not a symbol and cannot be bound, so it is
    // MSET around the call and its old value put back.
    lfunc("coerce-float-fun", actuals => {
      check_args(actuals)
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
