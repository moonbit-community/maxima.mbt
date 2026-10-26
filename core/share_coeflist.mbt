// Port of share/contrib/format/coeflist.lisp (Bruce R. Miller, NIST):
// coefficient lists of polynomials, trigonometric sums and series
// ($coeffs, $trig_coeffs, $taylor_coeffs, $series_coeffs, ...).

///|
/// (defmacro mexp-lookup (item alist) `(assolike ,item ,alist))
fn mexp_lookup(item : Value, alist : Value) -> Value raise {
  assolike(item, alist)
}

///|
/// (defmacro mlist* (arg1 &rest more-args) `(list* '(mlist simp) ,arg1
/// ,@more-args))
fn mlist_star(arg1 : Value, more_args : Value) -> Value raise {
  let hdr = list2(q_mlist, q_simp)
  if more_args is Nil {
    cons(hdr, arg1)
  } else {
    let items = [hdr, arg1]
    for x in more_args.iter() {
      items.push(x)
    }
    list_star(items)
  }
}

///|
/// `(mlist* a)` for a single argument.
fn share_coeflist__mlist1(a : Value) -> Value raise {
  mlist_star(a, Nil)
}

// ---------------------------------------------------------------------------
// Needed, but unrelated, stuff.

///|
/// Returns an mlist of all subexpressions of expr which `match' predicate.
/// Predicate(expr,args,...) returns non-nil if the expression matches.
fn d_matching_parts(expr : Value, predicate : Value, args : Value) -> Value raise {
  let mut matches : Value = Nil
  fn srch(expr : Value) -> Unit raise {
    let mut expr = expr
    if specrepp(expr).truthy() {
      expr = specdisrep(expr)
    }
    if mfuncall(predicate, cons(expr, args)).truthy() {
      if !some(m => alike1(expr, m).truthy(), matches) {
        matches = cons(expr, matches)
      }
    }
    if !atom(expr) {
      for x in cdr(expr).iter() {
        srch(x)
      }
    }
  }

  srch(expr)
  share_coeflist__mlist1(matches)
}

///|
/// Return an mlist of all unique function calls of the function(s) FCNS in
/// EXPR.
fn d_function_calls(expr : Value, functions : Value) -> Value raise {
  // Coerce fcns to a list of function names.
  let fcns = mapcar(
    x => {
      let x = getopr(x)
      let v = get(x, q_verb)
      if v.truthy() {
        v
      } else {
        x
      }
    },
    functions,
  )
  d_matching_parts(
    expr,
    lfunc("function-calls-predicate", a => {
      let p = a[0]
      lbool(listp(p) && memq(caar(p), fcns).truthy())
    }),
    Nil,
  )
}

///|
/// Return an mlist of all unique arguments used by FCNS in EXPR.
fn d_function_arguments(expr : Value, functions : Value) -> Value raise {
  share_coeflist__mlist1(
    remove_duplicates(
      cdr(map1(list2(q_d_args, d_function_calls(expr, functions)))),
      pred2=(a, b) => alike1(a, b).truthy(),
    ),
  )
}

///|
/// $totaldisrep only `disrep's CRE (mrat), but not POIS!
fn totalspecdisrep(expr : Value) -> Value raise {
  if atom(expr) {
    expr
  } else if !(among(q_mrat, expr).truthy() || among(q_mpois, expr).truthy()) {
    expr
  } else if eq(caar(expr), q_mrat) {
    ratdisrep(expr)
  } else if eq(caar(expr), q_mpois) {
    d_outofpois(expr)
  } else {
    cons(remove(q_ratsimp, car(expr)), mapcar(x => totalspecdisrep(x), cdr(expr)))
  }
}

// ---------------------------------------------------------------------------
// Variable Lists: a list of variables, simple expressions and specs like
// OPERATOR(fcn,...) (all calls to fcn in the expression) or
// MATCH(fcn,arg..) (subexpressions passing FCN(subexpr,args..)).

///|
fn instanciate_variable_list(
  vars : Value,
  expr : Value,
  caller : Value,
  max_vars? : Value = Nil,
) -> Value raise {
  let ivars = mapcan(
    v_ => {
      let var_ = totalspecdisrep(v_)
      let key = if listp(var_) { caar(var_) } else { Nil }
      if eq(key, q_d_operator) {
        cdr(d_function_calls(expr, cdr(var_)))
      } else if eq(key, q_d_match) {
        cdr(d_matching_parts(expr, cadr(var_), cddr(var_)))
      } else {
        list1(var_)
      }
    },
    vars,
  )
  if max_vars.truthy() && num_gt(int(length(ivars)), max_vars) {
    merr("Too many variables for ~M: ~M", [caller, share_coeflist__mlist1(ivars)])
    |> ignore
  }
  ivars
}

// ---------------------------------------------------------------------------
// Helpers

///|
/// Similar to lisp:reduce with the :key keyword.
fn cl_reduce(function : Value, list_ : Value, key : Value) -> Value raise {
  share_coeflist__reduce((a, b) => funcall(function, [a, b]), list_, x => funcall(
    key,
    [x],
  ))
}

///|
/// CL-REDUCE with MoonBit closures.
fn share_coeflist__reduce(
  function : (Value, Value) -> Value raise,
  list_ : Value,
  key : (Value) -> Value raise,
) -> Value raise {
  if list_ is Nil {
    return Nil
  }
  let mut result = key(car(list_))
  for item in cdr(list_).iter() {
    result = function(result, key(item))
  }
  result
}

///|
fn map_mlist(list_ : Value) -> Value raise {
  mapcar(e => share_coeflist__mlist1(e), list_)
}

///|
fn share_coeflist__add2(a : Value, b : Value) -> Value raise {
  add(list2(a, b))
}

///|
fn share_coeflist__mul2(a : Value, b : Value) -> Value raise {
  mul(list2(a, b))
}

// ---------------------------------------------------------------------------
// Coefficient List = Pseudo-polynomial : as list of ((coefficient
// power(s) ...) ...), pairs sorted into increasing order of the power(s);
// 0 is represented by NIL. The ordering of A & B is the `sign' of A-B, the
// sign of the coefficient of the leading term (SIGNUM1).

///|
/// Add two CLISTs
fn clist_add(l1 : Value, l2 : Value) -> Value raise {
  let mut l1 = l1
  let mut l2 = l2
  let mut result : Value = Nil
  while l1.truthy() && l2.truthy() {
    let mut p1 = cdar(l1)
    let mut p2 = cdar(l2)
    while !(p1 is Nil || !alike1(car(p1), car(p2)).truthy()) {
      p1 = cdr(p1)
      p2 = cdr(p2)
    }
    if p1.truthy() {
      if plusp(signum1(sub(car(p1), car(p2)))) {
        result = cons(car(l2), result)
        l2 = cdr(l2)
      } else {
        result = cons(car(l1), result)
        l1 = cdr(l1)
      }
    } else {
      // If power is same, combine and accumulate result, unless zero.
      let c3 = add(list2(caar(l1), caar(l2)))
      if !zerop1(c3).truthy() {
        result = cons(cons(c3, cdar(l1)), result)
      }
      l1 = cdr(l1)
      l2 = cdr(l2)
    }
  }
  if l1.truthy() || l2.truthy() {
    nconc(nreverse(result), if l1.truthy() { l1 } else { l2 })
  } else {
    nreverse(result)
  }
}

///|
/// Multiply two CLISTs. Optional ORDER is for use by series arithmetic
/// (single variable): truncates powers>order.
fn clist_mul(l1 : Value, l2 : Value, order? : Value = Nil) -> Value raise {
  if !(l1.truthy() && l2.truthy()) {
    return Nil
  }
  let (l1, l2) = if length(l1) > length(l2) { (l2, l1) } else { (l1, l2) }
  let rl2 = reverse(l2)
  let mul1 = fn(pair1 : Value) raise {
    let c1 = car(pair1)
    let p1 = cdr(pair1)
    let mut result : Value = Nil
    for i2 in rl2.iter() {
      let p = mapcar2((a, b) => share_coeflist__add2(a, b), p1, cdr(i2))
      if !(order.truthy() && great(car(p), order).truthy()) {
        result = cons(cons(share_coeflist__mul2(c1, car(i2)), p), result)
      }
    }
    result
  }
  share_coeflist__reduce((a, b) => clist_add(a, b), l1, mul1)
}

///|
/// Take the Nth power of a CLIST, using "binary expansion of the exponent"
/// method. Built-in code to handle P^2, instead of P*P. Assumes n>0.
fn clist_pow(l : Value, n : Value) -> Value raise {
  if l is Nil {
    Nil
  } else if cdr(l) is Nil {
    // single term, trivial
    list1(
      cons(
        power(caar(l), n),
        mapcar(p => d_expand(share_coeflist__mul2(p, n)), cdar(l)),
      ),
    )
  } else {
    let mut l_i = l
    let mut l_n : Value = if oddp(n) { l } else { Nil }
    let mut bits = ash(n, -1)
    while !zerop(bits) {
      // Square l^i
      let mut sq : Value = Nil
      let mut ll = reverse(l_i)
      while ll.truthy() {
        let c1 = caar(ll)
        let c1_2 = share_coeflist__mul2(Fix(2L), c1)
        let p1 = cdar(ll)
        let mut psq = list1(
          cons(
            power(c1, Fix(2L)),
            mapcar2((a, b) => share_coeflist__add2(a, b), p1, p1),
          ),
        )
        for lll in cdr(ll).iter() {
          psq = cons(
            cons(
              share_coeflist__mul2(c1_2, car(lll)),
              mapcar2((a, b) => share_coeflist__add2(a, b), p1, cdr(lll)),
            ),
            psq,
          )
        }
        sq = if sq.truthy() { clist_add(sq, psq) } else { psq }
        ll = cdr(ll)
      }
      l_i = sq
      if oddp(bits) {
        l_n = if l_n.truthy() { clist_mul(l_n, l_i) } else { l_i }
      }
      bits = ash(bits, -1)
    }
    l_n
  }
}

///|
/// An MBAG includes lists, arrays and equations. Given the list of
/// {list|array|equation} elements which have been converted to CLIST's,
/// combine them into a single clist whose coefficients are
/// {list|array|equation}s.
fn clist_mbag(op : Value, clists : Value) -> Value raise {
  // the `zero' of a matrix is an mlist of 0's!!!
  let z = if eq(op, q_d_matrix) {
    share_coeflist__mlist1(
      list(Array::make(length(cdr(car(car(car(clists))))), Fix(0L))),
    )
  } else {
    Fix(0L)
  }
  // does key l1 precede l2?
  let keylessp = fn(l1 : Value, l2 : Value) raise {
    let mut l1 = l1
    let mut l2 = l2
    while !(l1 is Nil || !alike1(car(l1), car(l2)).truthy()) {
      l1 = cdr(l1)
      l2 = cdr(l2)
    }
    l1.truthy() && minusp(signum1(sub(car(l1), car(l2))))
  }
  let keys = share_coeflist__reduce(
    (a, b) => union1(a, b),
    clists,
    e => mapcar(x => cdr(x), e),
  )
  mapcar(
    p => cons(
      cons(
        list1(op),
        mapcar(
          l => {
            let mut found : Value = Nil
            for x in l.iter() {
              if consp(x) && alike(p, cdr(x)).truthy() {
                found = x
                break
              }
            }
            let c = car(found)
            if c.truthy() {
              c
            } else {
              z
            }
          },
          clists,
        ),
      ),
      p,
    ),
    sort_list(keys, keylessp),
  )
}

///|
/// Transform an expression into its polynomial coefficient list form.
fn d_coeffs(expr : Value, vars : Value) -> Value raise {
  let expr = totalspecdisrep(expr)
  let vs = instanciate_variable_list(vars, expr, q_d_coeffs)
  let nvs = length(vs)
  let zeros = list(Array::make(nvs, Fix(0L)))
  let mut cache : Value = Nil
  // preload the cache w/ encoded variables
  for v in vs.iter() {
    let u = Array::make(nvs, Value::Fix(0L))
    u[position(v, vs)] = Value::Fix(1L)
    cache = cons(cons(v, list1(cons(Fix(1L), list(u)))), cache)
  }
  fn gcf(expr : Value) -> Value raise {
    let v = mexp_lookup(expr, cache)
    if v.truthy() {
      return v
    }
    let r = {
    let op = if listp(expr) { caar(expr) } else { Nil }
    if mbagp(expr).truthy() {
      clist_mbag(op, mapcar(x => gcf(x), cdr(expr)))
    } else if op is Nil || !dependsall(expr, vs).truthy() {
      list1(cons(expr, zeros))
    } else if eq(op, q_mplus) {
      share_coeflist__reduce((a, b) => clist_add(a, b), cdr(expr), x => gcf(x))
    } else if eq(op, q_mtimes) {
      share_coeflist__reduce((a, b) => clist_mul(a, b), cdr(expr), x => gcf(x))
    } else if eq(op, q_mexpt) {
      // Check that we can actually compute X^Y
      let x = gcf(cadr(expr))
      let y = caddr(expr)
      if y.truthy() &&
        (
          (integerp(y) && plusp(y)) || // Either integer y > 0
          (
            cdr(x) is Nil && // or x is a single monomial
            !dependsall(y, vs).truthy() && // w/ y must be free of vars
            (
              eql(symval(q_d_radexpand), q_d_all) || // & dont care about cuts
              integerp(y) || // or y is an integer
              every(p => zerop1(p).truthy() || onep(p).truthy(), cdar(x)) // or x is linear in vars.
            )
          )
        ) {
        clist_pow(x, y)
      } else {
        list1(cons(expr, zeros))
      }
    } else {
      list1(cons(expr, zeros))
    }
    }
    cache = cons(cons(expr, r), cache)
    r
  }

  mlist_star(mlist_star(q_d__pctpoly, list1(vs)), list1(map_mlist(gcf(expr))))
}

///|
/// Inverse of above: make an expression out of clist. Actually works for
/// SERIES & Taylor too.
fn unclist(clist : Value, vars : Value) -> Value raise {
  // CL MAPCAR signals a type error when VARS is not a list (as it is for
  // the single variable passed by $partition_series/$partition_taylor).
  if clist is Cons(_) && !listp(vars) {
    raise LispError::SimpleError(
      "The value " + prin1_to_string(vars) + " is not of type LIST",
    )
  }
  addn(
    mapcar(
      e => share_coeflist__mul2(
        cadr(e),
        muln(mapcar2((a, b) => power(a, b), vars, cddr(e)), t),
      ),
      clist,
    ),
    t,
  )
}

// ---------------------------------------------------------------------------
// TRIG SERIES: [[%trig, v_1, ...] sine_list, cosine_list], with
// sine_list: [[c,m_1,...],[c',m_1',...]....]

///|
/// Is L1 < (0 0 0 ...)? ie. is first non-zero element negative?
fn list_negp(l1 : Value) -> Value raise {
  for i1 in l1.iter() {
    if !zerop1(i1).truthy() {
      return lbool(eql(Fix(-1L), signum1(i1)))
    }
  }
  Nil
}

///|
fn tlist_add(l1 : Value, l2 : Value) -> Value raise {
  mapcar2((a, b) => clist_add(a, b), l1, l2)
}

///|
/// Multiply a cos or sin list by another. c1p is T if L1 is cosine list,
/// c2p ditto.
fn tlist_mul1(l1 : Value, l2 : Value, c1p : Value, c2p : Value) -> Value raise {
  let (l1, l2, c1p, c2p) = if length(l2) > length(l1) {
    // Swap so that L2 is the shortest.
    (l2, l1, c2p, c1p)
  } else {
    (l1, l2, c1p, c2p)
  }
  if l2 is Nil {
    return Nil
  }
  let c1 = c1p.truthy()
  let c2 = c2p.truthy()
  // cos * sines -> -1, else +1
  let s1 = if c1 && !c2 { Value::Fix(-1L) } else { Value::Fix(1L) }
  // either are cosines -> +1 else -1
  let s2 = if c1 || c2 { Value::Fix(1L) } else { Value::Fix(-1L) }
  // result is sines -> -1 else +1
  let s3 = if c1 != c2 { Value::Fix(-1L) } else { Value::Fix(1L) }
  let rl1 = reverse(l1)
  let mul1 = fn(pr2 : Value) raise {
    let c2v = car(pr2)
    let m2 = cdr(pr2)
    if every(x => zerop1(x).truthy(), m2) {
      if c2 {
        mapcar(pr => cons(share_coeflist__mul2(c2v, car(pr)), cdr(pr)), l1)
      } else {
        Nil
      }
    } else {
      let mut t1 : Value = Nil
      let mut t2 : Value = Nil
      let mut t3 : Value = Nil
      for i1 in rl1.iter() {
        let c1v = car(i1)
        let m1 = cdr(i1)
        let cc = div(share_coeflist__mul2(c1v, c2v), Fix(2L))
        t1 = cons(
          cons(share_coeflist__mul2(s1, cc), mapcar2((a, b) => sub(a, b), m1, m2)),
          t1,
        )
        t2 = cons(
          cons(
            share_coeflist__mul2(s2, cc),
            mapcar2((a, b) => share_coeflist__add2(a, b), m1, m2),
          ),
          t2,
        )
      }
      while t1.truthy() && list_negp(cdar(t1)).truthy() {
        t3 = cons(
          cons(share_coeflist__mul2(s3, caar(t1)), mapcar(x => neg(x), cdar(t1))),
          t3,
        )
        t1 = cdr(t1)
      }
      // sin(0) ? remove it.
      if minusp(s3) && every(x => zerop1(x).truthy(), cdar(t1)) {
        t1 = cdr(t1)
      }
      clist_add(clist_add(t1, t3), t2)
    }
  }
  share_coeflist__reduce((a, b) => clist_add(a, b), l2, mul1)
}

///|
fn tlist_mul(l1 : Value, l2 : Value) -> Value raise {
  let sin1 = car(l1)
  let cos1 = cadr(l1)
  let sin2 = car(l2)
  let cos2 = cadr(l2)
  list2(
    clist_add(tlist_mul1(cos1, sin2, t, Nil), tlist_mul1(sin1, cos2, Nil, t)),
    clist_add(tlist_mul1(cos1, cos2, t, t), tlist_mul1(sin1, sin2, Nil, Nil)),
  )
}

///|
fn tlist_pow(l : Value, n : Value, zeros : Value) -> Value raise {
  let sin = car(l)
  let cos = cadr(l)
  // single {cos or sin}^n: use explicit formula
  let pow1 = fn(coef : Value, m : Value, sinp : Bool) raise {
    let s : Int64 = if sinp { -1L } else { 1L }
    // by this point, n better be a fixnum!
    let nn = to_int(n).to_int64()
    let mut c = share_coeflist__mul2(
      if sinp && oddp(num_floor(n, b=Fix(2L)).0) {
        Fix(-1L)
      } else {
        Fix(1L)
      },
      div(power(coef, n), power(Fix(2L), Fix(nn - 1L))),
    )
    let mut result : Value = Nil
    let mut k : Int64 = 0L
    let mut kk : Int64 = nn
    while kk > 0L {
      let kkv = Value::Fix(kk)
      result = cons(cons(c, mapcar(mm => share_coeflist__mul2(kkv, mm), m)), result)
      k = k + 1L
      c = share_coeflist__mul2(c, div(Fix(s * (nn - (k - 1L))), Fix(k)))
      kk = kk - 2L
    }
    let pow = result
    if nn % 2L == 0L {
      list2(Nil, cons(cons(div(c, Fix(2L)), zeros), pow))
    } else if sinp {
      list2(pow, Nil)
    } else {
      list2(Nil, pow)
    }
  }
  if cos is Nil && sin is Nil {
    // 0^n
    list2(Nil, Nil)
  } else if zerop1(n).truthy() {
    list2(Nil, list1(cons(Fix(1L), zeros)))
  } else if cdr(cos) is Nil && sin is Nil {
    // cos^n
    pow1(caar(cos), cdar(cos), false)
  } else if cdr(sin) is Nil && cos is Nil {
    // sin^n
    pow1(caar(sin), cdar(sin), true)
  } else {
    // Compute using "binary expansion" method.
    let mut l_i : Value = Nil
    let mut l_n : Value = Nil
    let mut bits = n
    while !zerop(bits) {
      l_i = if l_i.truthy() { tlist_mul(l_i, l_i) } else { l }
      if oddp(bits) {
        l_n = if l_n.truthy() { tlist_mul(l_n, l_i) } else { l_i }
      }
      bits = ash(bits, -1)
    }
    l_n
  }
}

///|
/// Encode a call to %sin or %cos
fn encode_tlist(expr : Value, vs : Value) -> Value raise {
  // trig(arg)
  let mut arg = d_expand(cadr(expr))
  let mut m = mapcar(
    v => {
      let mm = d_coeff(arg, v)
      arg = sub(arg, share_coeflist__mul2(mm, v))
      mm
    },
    vs,
  )
  let mut sign = 1L
  // Make sure multiples are normalized
  if list_negp(m).truthy() {
    m = mapcar(x => neg(x), m)
    sign = -1L
  }
  if eql(caar(expr), q_p_cos) {
    if zerop1(arg).truthy() {
      list2(Nil, list1(cons(Fix(1L), m)))
    } else {
      list2(
        list1(
          cons(share_coeflist__mul2(Fix(-sign), funcall(q_d_sin, [arg])), m),
        ),
        list1(cons(funcall(q_d_cos, [arg]), m)),
      )
    }
  } else if zerop1(arg).truthy() {
    list2(list1(cons(Fix(sign), m)), Nil)
  } else {
    list2(
      list1(cons(share_coeflist__mul2(Fix(sign), funcall(q_d_cos, [arg])), m)),
      list1(cons(funcall(q_d_sin, [arg]), m)),
    )
  }
}

///|
/// Transform an expression into its trigonometric coefficient list form.
fn d_trig_coeffs(expr : Value, vars : Value) -> Value raise {
  let expr = totalspecdisrep(expr)
  let vars = instanciate_variable_list(vars, expr, q_d_alt_trig_coeffs)
  let zeros = list(Array::make(length(vars), Fix(0L)))
  let mut cache : Value = Nil
  fn gcf(expr : Value) -> Value raise {
    let v = mexp_lookup(expr, cache)
    if v.truthy() {
      return v
    }
    let r = {
    let op = if listp(expr) { caar(expr) } else { Nil }
    if mbagp(expr).truthy() {
      let elements = mapcar(x => gcf(x), cdr(expr))
      list2(
        clist_mbag(op, mapcar(x => car(x), elements)),
        clist_mbag(op, mapcar(x => cadr(x), elements)),
      )
    } else if op is Nil || !dependsall(expr, vars).truthy() {
      list2(Nil, list1(cons(expr, zeros)))
    } else if eq(op, q_p_sin) || eq(op, q_p_cos) {
      encode_tlist(expr, vars)
    } else if eq(op, q_mplus) {
      share_coeflist__reduce((a, b) => tlist_add(a, b), cdr(expr), x => gcf(x))
    } else if eq(op, q_mtimes) {
      share_coeflist__reduce((a, b) => tlist_mul(a, b), cdr(expr), x => gcf(x))
    } else if eq(op, q_mexpt) {
      // x^y Check that we can actually compute: need int y >0
      let x = gcf(cadr(expr))
      let y = caddr(expr)
      if y.truthy() && integerp(y) && plusp(y) {
        tlist_pow(x, y, zeros)
      } else {
        list2(Nil, list1(cons(expr, zeros)))
      }
    } else {
      list2(Nil, list1(cons(expr, zeros)))
    }
    }
    cache = cons(cons(expr, r), cache)
    r
  }

  mlist_star(
    mlist_star(q_d__pcttrig, list1(vars)),
    list1(map_mlist(mapcar(x => map_mlist(x), gcf(expr)))),
  )
}

///|
fn untlist(tlist : Value, vars : Value) -> Value raise {
  let un1 = fn(lst : Value, trig : Value) raise {
    let un2 = fn(e : Value) raise {
      share_coeflist__mul2(cadr(e), ftake_star(trig, [multl(cddr(e), vars)]))
    }
    addn(mapcar(e => un2(e), lst), t)
  }
  addn(mapcar2((a, b) => un1(a, b), tlist, list2(q_p_sin, q_p_cos)), t)
}

// ---------------------------------------------------------------------------
// SERIES & TAYLOR: [[%series,variable,order],[c,p],[c',p'],...] or
// [[%taylor,variable,order],...]. TAYLOR computes the Taylor expansion;
// SERIES only expands over arithmetic functions (+,*,exp) and is faster.

///|
fn d_taylor_coeffs(expr : Value, var_ : Value, order : Value) -> Value raise {
  let expr = totalspecdisrep(expr)
  let var_ = car(
    instanciate_variable_list(
      list1(var_),
      expr,
      q_d_taylor_coeffs,
      max_vars=Fix(1L),
    ),
  )
  fn make1(expr : Value) -> Value raise {
    if mbagp(expr).truthy() {
      clist_mbag(caar(expr), mapcar(x => make1(x), cdr(expr)))
    } else if freeof(var_, expr).truthy() {
      list1(list2(expr, Fix(0L)))
    } else {
      let r = d_taylor(expr, list3(var_, Fix(0L), order))
      let ohdr = car(r)
      let hdr = list4(car(ohdr), cadr(ohdr), caddr(ohdr), cadddr(ohdr))
      if eq(cadr(r), q_ps) {
        mapcar(
          p => list2(
            specdisrep(cons(hdr, cdr(p))),
            ftake_star(q_rat, [caar(p), cdar(p)]),
          ),
          cddddr(r),
        )
      } else {
        list1(list2(specdisrep(cons(hdr, cdr(r))), Fix(0L)))
      }
    }
  }

  mlist_star(
    mlist_star(q_d__pcttaylor, list3(var_, order, Nil)),
    list1(map_mlist(make1(expr))),
  )
}

///|
/// Compute the N-th power of S through ORDER.
fn slist_pow(s : Value, n : Value, order : Value) -> Value raise {
  if s is Nil {
    return Nil
  }
  let m = cadar(s)
  let nm = share_coeflist__mul2(n, m)
  let s_m = caar(s)
  // 1st term of result
  let mut p = list1(list2(power(s_m, n), nm))
  if cdr(s) is Nil {
    // Single term: then trivial single term (unless high order)
    let g = great(nm, order)
    if g.truthy() {
      g
    } else {
      p
    }
  } else {
    let g = share_coeflist__reduce(
      (a, b) => d_gcd(a, b, Nil),
      s,
      x => sub(cadr(x), m),
    )
    let kmax = div(sub(order, nm), g)
    let mut k : Value = Fix(1L)
    while !great(k, kmax).truthy() {
      let ff = div(add(list2(Fix(1L), n)), k)
      let mut trms : Value = Nil
      for s in cdr(s).iter() {
        let i = div(sub(cadr(s), m), g)
        if lessthan(k, i).truthy() {
          break
        }
        let item = add(list2(nm, share_coeflist__mul2(sub(k, i), g)))
        let mut e : Value = Nil
        let mut pp = p
        while pp is Cons(_) {
          if like(item, cadr(car(pp))).truthy() {
            e = pp
            break
          }
          pp = cdr(pp)
        }
        // multthru limits expression depth
        if e.truthy() {
          trms = cons(
            d_multthru(
              muln_([sub(share_coeflist__mul2(i, ff), Fix(1L)), car(s), caar(e)]),
            ),
            trms,
          )
        }
      }
      let pk = d_multthru(div(addn(trms, t), s_m))
      if !zerop1(pk).truthy() {
        p = cons(list2(pk, add(list2(nm, share_coeflist__mul2(k, g)))), p)
      }
      k = num_add(k, Fix(1L))
    }
    nreverse(p)
  }
}

///|
fn d_series_coeffs(expr : Value, var_ : Value, order : Value) -> Value raise {
  let expr = totalspecdisrep(expr)
  let v = car(
    instanciate_variable_list(
      list1(var_),
      expr,
      q_d_series_coeffs,
      max_vars=Fix(1L),
    ),
  )
  let v = d_ratdisrep(v)
  // find minimum power of v in expr (for mult)
  fn mino(expr : Value) -> Value raise {
    let op = if listp(expr) { caar(expr) } else { Nil }
    if like(expr, v).truthy() {
      // Trivial case: expr is V itself
      Fix(1L)
    } else if d_atom(expr).truthy() || freeof(v, expr).truthy() {
      // `constant' case
      Fix(0L)
    } else if memq(op, list4(q_mplus, q_mlist, q_mequal, q_d_matrix)).truthy() {
      share_coeflist__reduce(
        (u, w) => d_lmin(list3(list2(q_mlist, q_simp), u, w)),
        cdr(expr),
        x => mino(x),
      )
    } else if eq(op, q_mtimes) {
      share_coeflist__reduce((a, b) => share_coeflist__add2(a, b), cdr(expr), x => mino(
        x,
      ))
    } else if eq(op, q_mexpt) && d_numberp(caddr(expr)).truthy() {
      // can we compute?
      share_coeflist__mul2(mino(cadr(expr)), caddr(expr))
    } else {
      // oh, well, Treat it as constant.
      Fix(0L)
    }
  }

  fn gcf(expr : Value, order : Value) -> Value raise {
    let op = if listp(expr) { caar(expr) } else { Nil }
    if like(expr, v).truthy() {
      // Trivial case: expr is V itself
      list1(list2(Fix(1L), Fix(1L)))
    } else if d_atom(expr).truthy() || freeof(v, expr).truthy() {
      // `constant' case
      list1(list2(expr, Fix(0L)))
    } else if mbagp(expr).truthy() {
      clist_mbag(op, mapcar(el => gcf(el, order), cdr(expr)))
    } else if eq(op, q_mplus) {
      share_coeflist__reduce((a, b) => clist_add(a, b), cdr(expr), el => gcf(
        el, order,
      ))
    } else if eq(op, q_mtimes) {
      let ms = mapcar(x => mino(x), cdr(expr))
      let mtot = addn(ms, t)
      let mut prod = list1(list2(Fix(1L), Fix(0L)))
      if great(mtot, order).truthy() {
        Nil
      } else {
        let mut terms = cdr(expr)
        let mut m = ms
        while terms.truthy() {
          let term = gcf(car(terms), sub(add(list2(order, car(m))), mtot))
          prod = clist_mul(term, prod, order=order)
          terms = cdr(terms)
          m = cdr(m)
        }
        prod
      }
    } else if eq(op, q_mexpt) && d_numberp(caddr(expr)).truthy() {
      // can we compute?
      slist_pow(gcf(cadr(expr), order), caddr(expr), order)
    } else {
      // just treat it as constant.
      list1(list2(expr, Fix(0L)))
    }
  }

  mlist_star(
    mlist_star(q_d__pctseries, list3(v, order, Nil)),
    list1(map_mlist(gcf(expr, order))),
  )
}

///|
fn unslist(clist : Value, vars : Value) -> Value raise {
  d_trunc(unclist(clist, vars))
}

///|
/// Find the coefficient associated with keys (powers or multiples) in the
/// coefficient list clist.
fn d_get_coef(clist : Value, keys : Value) -> Value raise {
  let kind = if d_listp(clist).truthy() && d_listp(cadr(clist)).truthy() {
    cadr(cadr(clist))
  } else {
    Nil
  }
  let sublist = if eq(kind, q_d__pctpoly) ||
    eq(kind, q_d__pctseries) ||
    eq(kind, q_d__pcttaylor) {
    cddr(clist)
  } else if eq(kind, q_d__pcttrig) {
    let k = car(keys)
    if eq(k, q_d_sin) || eq(k, q_p_sin) {
      cdr(caddr(clist))
    } else if eq(k, q_d_cos) || eq(k, q_p_cos) {
      cdr(cadddr(clist))
    } else {
      merr("First KEY must be SIN or COS", [])
    }
  } else {
    merr("Unknown coefficient list type: ~M", [clist])
  }
  for x in sublist.iter() {
    if alike(keys, cddr(x)).truthy() {
      let c = cadr(x)
      return if c.truthy() { c } else { Fix(0L) }
    }
  }
  Fix(0L)
}

///|
/// Reconstruct a macsyma expression from a coefficient list.
fn d_uncoef(cl : Value) -> Value raise {
  let spec = if d_listp(cl).truthy() { cadr(cl) } else { Nil }
  let kind = if d_listp(spec).truthy() { cadr(spec) } else { Nil }
  if eq(kind, q_d__pctpoly) {
    unclist(cddr(cl), cddr(spec))
  } else if eq(kind, q_d__pctseries) || eq(kind, q_d__pcttaylor) {
    unslist(cddr(cl), cddr(spec))
  } else if eq(kind, q_d__pcttrig) {
    untlist(mapcar(x => cdr(x), cddr(cl)), cddr(spec))
  } else {
    merr("UNCOEF: Unrecognized COEFFS form: ~M", [cl])
  }
}

///|
/// Partition a polynomial, trig series or series into those terms whose
/// powers (or multiples) pass a certain test, and those who dont. The TEST
/// is applied to the exponents or multiples of each term.
fn partition_clist(list_ : Value, test_ : Value) -> (Value, Value) raise {
  if test_ is Nil {
    (Nil, list_)
  } else if eq(test_, t) {
    (list_, Nil)
  } else {
    let mut pass : Value = Nil
    let mut fail : Value = Nil
    for item in list_.iter() {
      if d_is_boole_eval(mapply(test_, cddr(item), q_d_partition_test)).truthy() {
        pass = cons(item, pass)
      } else {
        fail = cons(item, fail)
      }
    }
    (nreverse(pass), nreverse(fail))
  }
}

///|
fn d_partition_poly(expr : Value, test_ : Value, vars : Value) -> Value raise {
  let clist = d_coeffs(expr, vars)
  let vars = cddr(cadr(clist))
  let (p, f) = partition_clist(cddr(clist), test_)
  mlist_star(unclist(p, vars), list2(unclist(f, vars), Nil))
}

///|
fn d_partition_trig(
  expr : Value,
  sintest : Value,
  costest : Value,
  vars : Value,
) -> Value raise {
  let tlist = d_trig_coeffs(expr, vars)
  let vars = cddr(cadr(tlist))
  let (sp, sf) = partition_clist(cdr(caddr(tlist)), sintest)
  let (cp, cf) = partition_clist(cdr(cadddr(tlist)), costest)
  mlist_star(untlist(list2(sp, cp), vars), list2(untlist(list2(sf, cf), vars), Nil))
}

///|
fn d_partition_series(
  expr : Value,
  test_ : Value,
  var_ : Value,
  order : Value,
) -> Value raise {
  let clist = d_series_coeffs(expr, var_, order)
  let var_ = caddr(cadr(clist))
  let (p, f) = partition_clist(cddr(clist), test_)
  mlist_star(unslist(p, var_), list2(unslist(f, var_), Nil))
}

///|
fn d_partition_taylor(
  expr : Value,
  test_ : Value,
  var_ : Value,
  order : Value,
) -> Value raise {
  let clist = d_taylor_coeffs(expr, var_, order)
  let var_ = caddr(cadr(clist))
  let (p, f) = partition_clist(cddr(clist), test_)
  mlist_star(unslist(p, var_), list2(unslist(f, var_), Nil))
}

///|
fn init_share_coeflist() -> Unit raise {

}
