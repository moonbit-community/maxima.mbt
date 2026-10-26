// Port of src/intpol.lisp: find_root and bf_find_root (interpolation
// routine by CFFK, bigfloat version by rtoy).
//
// FIND-ROOT-SUBR and INTERPOLATE-CHECK live in the BIGFLOAT package and
// use its generic arithmetic (bf_add, bf_lt, ...; see docs/BIGFLOAT.md).

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
      let ff = intpol__coerce(float_fun, fun_or_expr, Nil)
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
      let ff = intpol__coerce(
        float_fun,
        sub(intpol__lhs(fun_or_expr), intpol__rhs(fun_or_expr)),
        list1(mk(q_mlist, [first(non_keyword)])),
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
/// (funcall coerce-float expr . rest): COERCE-FLOAT-FUN or
/// COERCE-BFLOAT-FUN, according to FLOAT-FUN.
fn intpol__coerce(float_fun : Value, expr : Value, rest_ : Value) -> Value raise {
  if eq(float_fun, q_d_bfloat) {
    coerce_bfloat_fun(expr, rest_)
  } else {
    coerce_float_fun(expr, rest_)
  }
}
