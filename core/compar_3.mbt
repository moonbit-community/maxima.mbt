// Port of src/compar.lisp, part 3: sign handlers for the elementary
// functions, min/max, integer/parity predicates, the database interface
// (DCOMPARE and the order search, DADD*, COMPSPLT) and the top-level forms.

///|
/// asec, acsc, asech, acoth and acsch are reciprocal argument forms of
/// functions whose sign SIGN already knows: asec(x) = acos(1/x) etc.
fn sign_asec_slacsc_slasech_slacsch_slacoth(x : Value) -> Value raise {
  if eq(q_d_zero, sign_star(cadr(x))) {
    // Of these five, acoth(0) = -%i*%pi/2 is the only one defined at zero.
    if eq(caar(x), q_p_acoth) {
      if compar__cs() {
        set(q_sign, q_d_imaginary)
      } else {
        imag_err(x)
      }
    } else {
      dbzs_err(x)
    }
  } else {
    // Rewrite asec(x) = acos(1/x) etc., and call SIGN on that. Don't go
    // through the simplifier: a tellsimp rule might undo the rewrite.
    let f = get(get(get(caar(x), q_d_inverse), q_recip), q_d_inverse)
    sign(list2(list1(f), inv(cadr(x))))
  }
}

///|
/// acot(x) = atan(1/x) for x # 0, and acot(0) = %pi/2: for real x, acot(x) is
/// positive for x >= 0, negative for x < 0, and never zero.
fn sign_acot(x : Value) -> Value raise {
  let arg = cadr(x)
  sign(arg) |> ignore
  let arg_sign = compar__sign()
  let s = if compar__in(arg_sign, [q_d_pos, q_d_zero, q_d_pz]) {
    q_d_pos
  } else if eq(arg_sign, q_d_neg) {
    q_d_neg
  } else if compar__in(arg_sign, [q_d_pn, q_d_nz, q_d_pnz]) {
    q_d_pn
  } else if compar__in(arg_sign, [q_d_complex, q_d_imaginary]) {
    q_d_complex
  } else {
    arg_sign
  }
  set(q_sign, s) |> ignore
  set(q_minus, Nil) |> ignore
  set(q_evens, Nil) |> ignore
  // For $ASKSIGN: a nonzero ARG has the sign of acot(ARG).
  set(
    q_odds,
    if eq(compar__sign(), q_d_pn) {
      list1(if eq(arg_sign, q_d_pn) { arg } else { x })
    } else {
      Nil
    },
  )
}

///|
/// atan(%i*y) = %i*atanh(y) and asinh(%i*y) = %i*asin(y) are imaginary only
/// for -1 <= y <= 1.
fn sign_atan_slasinh(x : Value) -> Value raise {
  sign_oddfun(x) |> ignore
  if eq(compar__sign(), q_d_imaginary) {
    compar__set4(q_d_complex, Nil, Nil, Nil)
  }
  Nil
}

///|
/// tan(%i*y) = %i*tanh(y) and cot(%i*y) = -%i*coth(y) are imaginary, and tan
/// and cot of other non-real arguments are complex.
fn sign_tan_slcot(x : Value) -> Value raise {
  let k = if compar__cs() { sign_star(cadr(x)) } else { Nil }
  if eq(k, q_d_imaginary) {
    compar__set4(q_d_imaginary, Nil, Nil, Nil)
    Nil
  } else if eq(k, q_d_complex) {
    compar__set4(q_d_complex, Nil, Nil, Nil)
    Nil
  } else {
    sign_oddfun(x)
  }
}

///|
/// sign(sin(x)) for -%pi <= x <= %pi. Works by setting the special SIGN.
fn sign_sin(e : Value) -> Value raise {
  let mut x = cadr(e)
  let mut y : Value = Fix(0L)
  // When *complexsign* is true, find the rectangular form of the argument.
  if compar__cs() {
    x = risplit(x)
    y = cdr(x)
    x = car(x)
  }
  let mpi = mul2(Fix(-1L), q_d__pctpi)
  if eql(y, Fix(0L)) &&
    eq(t, mgqp(x, mul2(Fix(-1L), q_d__pctpi))) &&
    eq(t, mgqp(q_d__pctpi, x)) {
    // When y = 0 and -%pi <= x <= %pi, sign(sin(x)) = sign(x)
    sign(x) |> ignore
    // sin(x) = 0 at the closed endpoints, so a strict interior sign weakens
    // to include zero when x can reach the nearer endpoint.
    let sg = compar__sign()
    if eq(sg, q_d_pos) && !eq(t, mgrp(q_d__pctpi, x)) {
      compar__set4(q_d_pz, Nil, list1(e), Nil)
    } else if eq(sg, q_d_neg) && !eq(t, mgrp(x, mpi)) {
      compar__set4(q_d_nz, Nil, list1(e), Nil)
    } else if eq(sg, q_d_pn) {
      if !(eq(t, mgrp(q_d__pctpi, x)) && eq(t, mgrp(x, mul2(Fix(-1L), q_d__pctpi)))) {
        set(q_sign, q_d_pnz) |> ignore
      }
      set(q_odds, list1(e)) |> ignore
      set(q_evens, Nil) |> ignore
      set(q_minus, Nil) |> ignore
    } else if compar__in(sg, [q_d_pz, q_d_nz, q_d_pnz]) {
      set(q_odds, list1(e)) |> ignore
      set(q_evens, Nil) |> ignore
      set(q_minus, Nil) |> ignore
    }
  } else if compar__cs() && !eql(y, Fix(0L)) {
    // When *complexsign* is true & y # 0, set sign to complex.
    set(q_sign, q_d_complex) |> ignore
  } else {
    set(q_sign, q_d_pnz) |> ignore
  }
  Nil
}

///|
fn sign_cos(e : Value) -> Value raise {
  let mut x = cadr(e)
  let mut y : Value = Fix(0L)
  if compar__cs() {
    x = risplit(x)
    y = cdr(x)
    x = car(x)
  }
  if eql(y, Fix(0L)) &&
    eq(t, mgqp(x, div(q_d__pctpi, Fix(-2L)))) &&
    eq(t, mgqp(div(mul2(Fix(3L), q_d__pctpi), Fix(2L)), x)) {
    // When y = 0 and -%pi/2 <= x <= 3 %pi/2, sign(cos(x)) = sign(%pi/2-x)
    sign(sub(div(q_d__pctpi, Fix(2L)), x)) |> ignore
    let sg = compar__sign()
    if eq(sg, q_d_pos) && !eq(t, mgrp(x, div(q_d__pctpi, Fix(-2L)))) {
      compar__set4(q_d_pz, Nil, list1(e), Nil)
    } else if eq(sg, q_d_neg) &&
      !eq(t, mgrp(div(mul2(Fix(3L), q_d__pctpi), Fix(2L)), x)) {
      compar__set4(q_d_nz, Nil, list1(e), Nil)
    } else if eq(sg, q_d_pn) {
      if !(
          eq(t, mgrp(x, div(q_d__pctpi, Fix(-2L)))) &&
          eq(t, mgrp(div(mul2(Fix(3L), q_d__pctpi), Fix(2L)), x))
        ) {
        set(q_sign, q_d_pnz) |> ignore
      }
      set(q_odds, list1(e)) |> ignore
      set(q_evens, Nil) |> ignore
      set(q_minus, Nil) |> ignore
    } else if compar__in(sg, [q_d_pz, q_d_nz, q_d_pnz]) {
      set(q_odds, list1(e)) |> ignore
      set(q_evens, Nil) |> ignore
      set(q_minus, Nil) |> ignore
    }
  } else if compar__cs() && !eql(y, Fix(0L)) {
    set(q_sign, q_d_complex) |> ignore
  } else {
    set(q_sign, q_d_pnz) |> ignore
  }
  Nil
}

///|
/// When -1<x<=0, ceiling(x) simplifies to 0 before reaching this function.
fn sign_ceiling(x : Value) -> Value raise {
  let x = cadr(x) // ceiling(x) --> x
  set(
    q_sign,
    if eq(t, mgrp(x, Fix(0L))) {
      q_d_pos // ceiling(> 0) = pos
    } else if eq(t, mgrp(x, Fix(-1L))) {
      q_d_pz // ceiling(> -1) = pz
    } else if eq(t, mgqp(Fix(-1L), x)) {
      q_d_neg // ceiling(<= -1) = neg
    } else if eq(t, mgrp(Fix(0L), x)) {
      q_d_nz // ceiling( < 0) = nz
    } else {
      q_d_pnz
    },
  )
}

///|
fn sign_floor(x : Value) -> Value raise {
  let x = cadr(x) // floor(x) --> x
  set(
    q_sign,
    if eq(t, mgqp(x, Fix(1L))) {
      q_d_pos // floor(>= 1) = pos
    } else if eq(t, mgqp(x, Fix(0L))) {
      q_d_pz // floor(>= 0) = pz
    } else if eq(t, mgrp(Fix(0L), x)) {
      q_d_neg // floor(< 0) = neg
    } else if eq(t, mgqp(Fix(0L), x)) {
      q_d_nz // floor(<= 0) = nz
    } else {
      q_d_pnz
    },
  )
}

// Compare min/max.

///|
/// The MINMAXFORMS substitution, applied to a sign value: the identity for
/// min, the dual (neg<->pos, nz<->pz, max<->min, inf<->minf) for max.
fn compar__minmax_dual(op : Value, s : Value) -> Value {
  if eq(op, q_d_min) {
    s
  } else if eq(s, q_d_neg) {
    q_d_pos
  } else if eq(s, q_d_pos) {
    q_d_neg
  } else if eq(s, q_d_nz) {
    q_d_pz
  } else if eq(s, q_d_pz) {
    q_d_nz
  } else if eq(s, q_d_max) {
    q_d_min
  } else if eq(s, q_d_min) {
    q_d_max
  } else if eq(s, q_d_inf) {
    q_d_minf
  } else if eq(s, q_d_minf) {
    q_d_inf
  } else {
    s
  }
}

///|
/// `(minmaxforms op body)`: if op is min, the body; otherwise the body with
/// the sign constants negated. BODY is the list of (evaluated) body values.
fn minmaxforms(op : Value, body : Value) -> Value raise {
  let b = car(body)
  if eq(op, q_d_min) {
    b
  } else {
    sublis(
      list([
        cons(q_d_neg, q_d_pos),
        cons(q_d_nz, q_d_pz),
        cons(q_d_pz, q_d_nz),
        cons(q_d_pos, q_d_neg),
        cons(q_d_max, q_d_min),
        cons(q_d_min, q_d_max),
        cons(q_d_inf, q_d_minf),
        cons(q_d_minf, q_d_inf),
      ]),
      b,
    )
  }
}

///|
fn sign_minmax(op : Value, args : Value) -> Value raise {
  let mut sgn = compar__minmax_dual(op, q_d_pos) // identity element for min
  let end = compar__minmax_dual(op, q_d_neg)
  let mut l = args
  while !(l is Nil || eq(sgn, end)) {
    sgn = sminmax(op, sgn, sign_star(car(l)))
    l = cdr(l)
  }
  compar__set4(
    sgn,
    Nil,
    if !compar__in(sgn, [q_d_pos, q_d_neg, q_d_zero]) {
      list1(cons(list1(op), args))
    } else {
      Nil
    },
    Nil,
  )
  sgn
}

///|
/// sign(op(a,b)) = sminmax(sign(a),sign(b)); op is $min/$max; s1/s2 in neg,
/// nz, zero, pz, pos, pn, pnz. The order of the clauses is important.
fn sminmax(op : Value, s1 : Value, s2 : Value) -> Value raise {
  let f = (s : Value) => compar__minmax_dual(op, s)
  if eq(s1, f(q_d_pos)) {
    s2
  } else if eq(s2, f(q_d_pos)) {
    s1
  } else if eq(s1, s2) {
    s1
  } else if eq(s1, f(q_d_neg)) || eq(s2, f(q_d_neg)) {
    f(q_d_neg)
  } else if eq(s1, f(q_d_nz)) || eq(s2, f(q_d_nz)) {
    f(q_d_nz)
  } else if eq(s1, q_d_zero) {
    if eq(s2, f(q_d_pz)) {
      q_d_zero
    } else {
      f(q_d_nz)
    }
  } else if eq(s2, q_d_zero) {
    if eq(s1, f(q_d_pz)) {
      q_d_zero
    } else {
      f(q_d_nz)
    }
  } else {
    q_d_pnz
  }
}

///|
fn minmaxp(ex : Value) -> Value raise {
  if atom(ex) {
    Nil
  } else if eq(caar(ex), q_d_min) || eq(caar(ex), q_d_max) {
    caar(ex)
  } else {
    Nil
  }
}

///|
/// sign of l-r; nil if unknown (not PNZ)
fn signdiff_minmax(l : Value, r : Value) -> Value raise {
  let lm = minmaxp(l)
  let rm = minmaxp(r)
  let ll = if lm.truthy() { cdr(l) } else { Nil }
  let rr = if rm.truthy() { cdr(r) } else { Nil }
  let op = if rm.truthy() { rm } else { lm }
  let f = (s : Value) => compar__minmax_dual(op, s)
  if eq(lm, rm) {
    // min(a,...) - min(b,...)
    let (_, onlyl, onlyr) = intersect_info(ll, rr)
    if onlyl is Nil {
      f(q_d_pz) // min(a,b) - min(a,b,c)
    } else if onlyr is Nil {
      f(q_d_nz) // min(a,b,c) - min(a,b)
    } else {
      Nil
    }
  } else if lm is Nil {
    // a - min(a,b)
    if memalike(l, rr).truthy() {
      f(q_d_pz)
    } else {
      Nil
    }
  } else if rm is Nil {
    // min(a,b) - a
    if memalike(r, ll).truthy() {
      f(q_d_nz)
    } else {
      Nil
    }
  } else if !set_disjointp(ll, rr).truthy() {
    // max(a,q,r) - min(a,s,t)
    f(q_d_pz)
  } else {
    Nil
  }
}

///|
fn intersect_info(a : Value, b : Value) -> (Value, Value, Value) raise {
  let both = []
  let onlya = []
  let onlyb = []
  // DO-MERGE-ASYM with LIKE as equality and $ORDERLESSP as order.
  let mut l1 = a
  let mut l2 = b
  while true {
    if l1 is Nil {
      while l2.truthy() {
        onlyb.push(car(l2))
        l2 = cdr(l2)
      }
      break
    } else if l2 is Nil {
      while l1.truthy() {
        onlya.push(car(l1))
        l1 = cdr(l1)
      }
      break
    } else if like(car(l1), car(l2)).truthy() {
      both.push(car(l1))
      l1 = cdr(l1)
      l2 = cdr(l2)
    } else if d_orderlessp(car(l1), car(l2)).truthy() {
      onlya.push(car(l1))
      l1 = cdr(l1)
    } else {
      onlyb.push(car(l2))
      l2 = cdr(l2)
    }
  }
  (list(both), list(onlya), list(onlyb))
}

///|
fn sign_posfun(xx : Value) -> Value raise {
  // A function declared $POSFUN is positive for real arguments, and for all
  // if it is also declared $REAL. Take the signs of the arguments anyways, to
  // not swallow errors. If any argument is non-real, return $COMPLEX.
  let rp0 = get(caar(xx), q_real_valued)
  let realp_ = if rp0.truthy() { rp0 } else { kindp(caar(xx), q_d_real) }
  let sgns = mapcar(
    a => if realp_.truthy() {
      with_special(q_sign_imag_errp, Nil, () => catch_tag(q_sign_imag_err, () => sign_star(
        a,
      )))
    } else {
      sign_star(a)
    },
    margs(xx),
  )
  let s = if !realp_.truthy() &&
    intersection(sgns, list2(q_d_imaginary, q_d_complex)).truthy() {
    q_d_complex
  } else {
    q_d_pos
  }
  compar__set4(s, Nil, Nil, Nil)
  Nil
}

///|
fn sign_oddfun(x : Value) -> Value raise {
  let kind = kind_any_of(caar(x), list2(q_d_increasing, q_d_decreasing))
  if eq(kind, q_d_increasing) {
    // Take the sign of the argument
    sign(cadr(x))
  } else if eq(kind, q_d_decreasing) {
    // Take the sign of negative of the argument
    sign(neg(cadr(x)))
  } else {
    // If the sign of the argument is zero, then we're done. Otherwise, punt
    // to SIGN-ANY.
    sign(cadr(x)) |> ignore
    if !eq(compar__sign(), q_d_zero) {
      sign_any(x)
    } else {
      Nil
    }
  }
}

///|
/// The sign function of csc, sec, csch and coth, each the reciprocal of the
/// function its RECIP property names: sign(f(x)) = sign(1/g(x)).
fn sign_csc_slsec_slcsch_slcoth(x : Value) -> Value raise {
  sign(inv(ftake(get(caar(x), q_recip), [cadr(x)])))
}

///|
fn imag_err(x : Value) -> Value raise {
  if symval(q_sign_imag_errp).truthy() {
    merr("sign: argument cannot be non-real; found ~M", [x])
  } else {
    throw_tag(q_sign_imag_err, t)
  }
}

///|
fn dbzs_err(x : Value) -> Value raise {
  merr("sign: division by zero in ~M", [x])
}

///|
fn log0_err(x : Value) -> Value raise {
  merr("sign: encountered log(0) in ~M", [x])
}

///|
/// Return true iff e is an expression with operator op1, op2,...,or opn.
fn op_equalp(e : Value, op : Value) -> Value raise {
  lbool(consp(e) && consp(car(e)) && some(s => equal(caar(e), s), op))
}

///|
/// Return true iff the operator of a is a Maxima relation operator.
fn mrelationp(a : Value) -> Value raise {
  op_equalp(
    a,
    list([q_mlessp, q_mleqp, q_mequal, q_mnotequal, q_mgeqp, q_mgreaterp]),
  )
}

///|
/// This version of featurep applies ratdisrep to the first argument, so that
/// featurep(rat(n),integer) --> true when n has been declared an integer.
fn d_featurep(e : Value, ind : Value) -> Value raise {
  let mut e = d_ratdisrep(e)
  if atom(e) && !eq(ind, q_d_alphabetic) {
    // Match the behavior of declare("operatorname", ...).
    e = getopr(e)
  }
  if !symbolp(ind) {
    return merr("featurep: second argument must be a symbol; found ~M", [ind])
  }
  // Properties not related to the assume database.
  if member(ind, symval(q_opers)).truthy() {
    let v = safe_get(e, ind)
    if v.truthy() {
      return v
    }
  }
  if compar__in(ind, [q_d_evfun, q_d_evflag, q_d_bindtest, q_d_nonarray]) {
    let v = safe_get(e, stripdollar(ind))
    if v.truthy() {
      return v
    }
  }
  if eq(ind, q_d_noun) && safe_get(e, stripdollar(ind)).truthy() {
    return t
  }
  if compar__in(ind, [q_d_scalar, q_d_nonscalar, q_d_mainvar]) {
    let v = mget(e, ind)
    if v.truthy() {
      return v
    }
  }
  if eq(ind, q_d_feature) && member(e, symval(q_d_features)).truthy() {
    return t
  }
  if eq(ind, q_d_alphabetic) && stringp(e) {
    match e {
      Str(s) => {
        let alphabet = symval(q_ear_alphabet)
        for c in s {
          if member(Char(c), alphabet) is Nil {
            return Nil
          }
        }
        return t
      }
      _ => ()
    }
  }
  // Properties related to the assume database.
  if eq(ind, q_d_integer) {
    maxima_integerp(e)
  } else if eq(ind, q_d_noninteger) {
    nonintegerp(e)
  } else if eq(ind, q_d_even) {
    mevenp(e)
  } else if eq(ind, q_d_odd) {
    moddp(e)
  } else if eq(ind, q_d_real) {
    if atom(e) {
      if numberp(e) {
        t
      } else {
        let k = kindp(e, q_d_real)
        if k.truthy() {
          k
        } else {
          lbool(numberp(numer(e)))
        }
      }
    } else {
      zerop1(d_imagpart(e))
    }
  } else if eq(ind, q_d_complex) {
    // "complex" in the sense of "has an imaginary part that's not literally
    // 0", not in the strict mathematical sense.
    if symbolp(e) {
      kindp(e, q_d_complex)
    } else {
      lbool(!zerop1(d_imagpart(e)).truthy())
    }
  } else if eq(ind, q_d_imaginary) {
    // "imaginary": real part literally 0 and imaginary part not literally 0.
    if symbolp(e) {
      kindp(e, q_d_imaginary)
    } else {
      let ri = trisplit(e)
      lbool(zerop1(car(ri)).truthy() && !zerop1(cdr(ri)).truthy())
    }
  } else if symbolp(e) {
    kindp(e, ind)
  } else {
    Nil
  }
}

///|
fn maxima_integerp(x : Value) -> Value raise {
  if integerp(x) {
    return t
  }
  if mnump(x).truthy() {
    return Nil
  }
  if symbolp(x) {
    let k = kindp(x, q_d_integer)
    if k.truthy() {
      return k
    }
    let c = check_integer_facts(x)
    if c.truthy() {
      return c
    }
  }
  let x_op = if consp(x) && consp(car(x)) { caar(x) } else { Nil }
  with_special(q_d_prederror, Nil, fn() {
    if x_op is Nil {
      Nil
    } else if !symbolp(x_op) {
      Nil // fix for mqapply at some point?
    } else if eq(x_op, q_mrat) {
      lbool(integerp(cadr(x)) && equal(cddr(x), Fix(1L)))
    } else if get(x_op, q_maps_integers_to_integers).truthy() &&
      every(y => maxima_integerp(y).truthy(), margs(x)) {
      // mtimes and mplus are generally handled by this clause
      t
    } else if eq(x_op, q_mtimes) {
      // Special case for 1/2*...*even
      lbool(
        mnump(cadr(x)).truthy() &&
        integerp(mul2(Fix(2L), cadr(x))) &&
        every(y => maxima_integerp(y).truthy(), cddr(x)) &&
        some(s => d_featurep(s, q_d_even).truthy(), rest(margs(x))),
      )
    } else if eq(x_op, q_mexpt) {
      lbool(
        every(y => maxima_integerp(y).truthy(), margs(x)) &&
        (
          eql(cadr(x), Fix(-1L)) ||
          mevalp(mlsp(caddr(x), Fix(0L))) is Nil
        ),
      )
    } else if eq(x_op, q_mfactorial) {
      // ! in Maxima allows real arguments
      lbool(
        maxima_integerp(cadr(x)).truthy() &&
        !mevalp(mlsp(cadr(x), Fix(0L))).truthy(),
      )
    } else if eq(x_op, q_p_gamma) {
      lbool(
        maxima_integerp(cadr(x)).truthy() &&
        !mevalp(mlsp(cadr(x), Fix(1L))).truthy(),
      )
    } else {
      // other x-ops
      let v = d_featurep(d_verbify(x_op), q_d_integervalued)
      if v.truthy() {
        v
      } else {
        get(x_op, q_integer_valued)
      }
    }
  })
}

///|
/// Checks the facts database for EQUAL(X, E) or EQUAL(E, X) facts, where E is
/// known to be integer/noninteger/even/odd. MODE 'INTEGER: T iff X is provably
/// equal to an integer; 'NONINTEGER: to a noninteger; 'EVOD: $EVEN/$ODD.
/// Negative facts give NIL.
fn check_integer_facts(x : Value, mode? : Value = q_integer) -> Value raise {
  for fact in cdr(facts1(x)).iter() {
    if !atom(fact) && eq(caar(fact), q_d_equal) {
      let e = if eq(cadr(fact), x) {
        caddr(fact) // equal(x, e)
      } else if eq(caddr(fact), x) {
        cadr(fact) // equal(e, x) -> normalize
      } else {
        Nil
      }
      if e.truthy() {
        if eq(mode, q_integer) || eq(mode, q_noninteger) {
          // A decisive fact of EITHER kind ends the scan.
          let c = if symbolp(e) {
            kind_any_of(e, list2(q_d_integer, q_d_noninteger))
          } else if maxima_integerp(e).truthy() {
            q_d_integer
          } else if nonintegerp(e).truthy() {
            q_d_noninteger
          } else {
            Nil
          }
          if c.truthy() {
            return lbool(
              eq(
                c,
                if eq(mode, q_integer) {
                  q_d_integer
                } else {
                  q_d_noninteger
                },
              ),
            )
          }
        } else if eq(mode, q_evod) {
          // Parity of X. A noninteger E is decisive (X then has no parity).
          let c = if symbolp(e) {
            kind_any_of(e, list([q_d_even, q_d_odd, q_d_noninteger]))
          } else {
            let ev = evod(e)
            if ev.truthy() {
              ev
            } else if nonintegerp(e).truthy() {
              q_d_noninteger
            } else {
              Nil
            }
          }
          if eq(c, q_d_even) || eq(c, q_d_odd) {
            return c
          } else if eq(c, q_d_noninteger) {
            return Nil
          }
        } else {
          merr("check-integer-facts: unknown mode: ~M", [mode]) |> ignore
        }
      }
    }
  }
  Nil
}

///|
fn nonintegerp(e : Value) -> Value raise {
  if symbolp(e) {
    // declared noninteger
    let k = kindp(e, q_d_noninteger)
    if k.truthy() {
      return k
    }
    let c = check_noninteger_facts(e)
    if c.truthy() {
      return c
    }
  }
  if mnump(e).truthy() {
    // all floats are noninteger and integers are not nonintegers
    lbool(!integerp(e))
  } else if d_ratp(e).truthy() {
    nonintegerp(d_ratdisrep(e))
  } else {
    lbool(eq(t, mgrp(e, take(list1(q_d_floor), [e]))))
  }
}

///|
/// Look into the database for symbols which are declared to be equal to a
/// noninteger or an expression which is a noninteger.
fn check_noninteger_facts(x : Value) -> Value raise {
  check_integer_facts(x, mode=q_noninteger)
}

///|
fn intp(l : Value) -> Value raise {
  lbool(every(x => maxima_integerp(x).truthy(), cdr(l)))
}

///|
fn mevenp(e : Value) -> Value raise {
  if integerp(e) {
    lbool(!oddp(e))
  } else if mnump(e).truthy() {
    Nil
  } else {
    lbool(eq(q_d_even, evod(e)))
  }
}

///|
fn moddp(e : Value) -> Value raise {
  if integerp(e) {
    lbool(oddp(e))
  } else if mnump(e).truthy() {
    Nil
  } else {
    lbool(eq(q_d_odd, evod(e)))
  }
}

///|
/// An extended evod that recognizes that abs(even) is even and abs(odd) is
/// odd.
fn evod(e : Value) -> Value raise {
  if integerp(e) {
    if oddp(e) {
      q_d_odd
    } else {
      q_d_even
    }
  } else if mnump(e).truthy() {
    Nil
  } else if symbolp(e) {
    let k = kind_any_of(e, list2(q_d_even, q_d_odd))
    if k.truthy() {
      k
    } else {
      // Check the database for facts.
      check_integer_facts(e, mode=q_evod)
    }
  } else if eq(q_mtimes, caar(e)) {
    evod_mtimes(e)
  } else if eq(q_mplus, caar(e)) {
    evod_mplus(e)
  } else if eq(q_mabs, caar(e)) {
    evod(cadr(e))
  } else if eq(q_mexpt, caar(e)) {
    evod_mexpt(e)
  } else {
    Nil
  }
}

///|
fn evod_mtimes(x : Value) -> Value raise {
  let mut flag = q_d_odd
  for y in cdr(x).iter() {
    let ev = evod(y)
    if eq(q_d_odd, ev) {
      ()
    } else if eq(q_d_even, ev) {
      flag = q_d_even
    } else if maxima_integerp(y).truthy() {
      if eq(q_d_odd, flag) {
        flag = Nil
      }
    } else {
      return Nil
    }
  }
  flag
}

///|
fn evod_mplus(x : Value) -> Value raise {
  let mut flag = false
  for y in cdr(x).iter() {
    let ev = evod(y)
    if eq(q_d_odd, ev) {
      flag = !flag
    } else if eq(q_d_even, ev) {
      ()
    } else {
      return Nil
    }
  }
  if flag {
    q_d_odd
  } else {
    q_d_even
  }
}

///|
fn evod_mexpt(x : Value) -> Value raise {
  if integerp(caddr(x)) && !minusp(caddr(x)) {
    evod(cadr(x))
  } else {
    Nil
  }
}

///|
/// `(c-dobj x...)` = `(list x...)`
fn c_dobj(x : Value) -> Value raise {
  x
}

///|
/// DCOMPARE is the database's answer to "How do X and Y compare?". It leaves
/// the verdict in SIGN, the sign of X - Y, and the difference itself in ODDS.
/// The infinities are settled here rather than in DCOMP.
fn dcompare(x : Value, y : Value) -> Value raise {
  set(q_odds, list1(sub(x, y))) |> ignore
  set(q_evens, Nil) |> ignore
  set(q_minus, Nil) |> ignore
  set(
    q_sign,
    if eq(x, y) {
      q_d_zero
    } else if eq(q_d_inf, x) || eq(q_d_minf, y) {
      q_d_pos
    } else if eq(q_d_minf, x) || eq(q_d_inf, y) {
      q_d_neg
    } else {
      dcomp(x, y)
    },
  )
}

///|
/// The node for a symbol or a compound expression, provided it carries facts.
/// "No node" and "empty node" are the same answer, '$PNZ.
fn compar__resolve_object(z : Value) -> Value raise {
  let nd = dinternp(z)
  if nd.truthy() && zl_get(nd, q_data).truthy() {
    nd
  } else {
    Nil
  }
}

///|
/// The order search: DCOMP (X Y) answers "What is the sign of X - Y?" with a
/// depth-first walk over the fact graph from the source X, accumulating the
/// answer as a label on the target Y. DEQ, DGR, DLS, DGQ, DLQ and DNQ are the
/// six states of the walk ("X = N", "X > N", ...). MGQP and MLQP record that
/// the target was reached along a ">=" and a "<=" path.
fn dcomp(x : Value, y : Value) -> Value raise {
  with_specials([(q_mgqp, Nil), (q_mlqp, Nil)], fn() {
    let mut x = x
    let mut y = y
    if mnump(x).truthy() {
      // Two numbers are pure arithmetic.
      if mnump(y).truthy() {
        return rgrp(x, y)
      }
      // A number on the left is the source, resolved below.
      y = compar__resolve_object(y)
    } else if mnump(y).truthy() {
      x = compar__resolve_object(x)
      if x.truthy() {
        // The target only has to carry the answer: its own node if the
        // database has one, otherwise a bare cell.
        let nd = dinternp(y)
        y = if nd.truthy() { nd } else { dbnode(y) }
      }
    } else {
      x = compar__resolve_object(x)
      if x.truthy() {
        y = compar__resolve_object(y)
      }
    }
    if x is Nil || y is Nil {
      q_d_pnz
    } else {
      clear() |> ignore
      if mnump(x).truthy() {
        // The source must have edges to leave by: use the number's own node,
        // or enter the graph at the two chain nodes it belongs between.
        let nd = dinternp(x)
        if nd.truthy() {
          deq(nd, y) |> ignore
        } else {
          let (same, above, below) = dnum_neighbors(x)
          if same.truthy() {
            deq(same, y) |> ignore
          } else if !(below.truthy() && dgr(below, y).truthy()) {
            if above.truthy() {
              dls(above, y) |> ignore
            }
          }
        }
      } else {
        deq(x, y) |> ignore
      }
      // Whatever the walk established about the target, if anything.
      let l = zl_get(y, q_n_pluslabs)
      if l.truthy() {
        l
      } else {
        q_d_pnz
      }
    }
  })
}

///|
fn deq(x : Value, y : Value) -> Value raise {
  if dmark(x, q_d_zero).truthy() {
    return Nil
  }
  if eq(x, y) {
    return t
  }
  // X = (car x), so X against (car y) is exactly the numeric comparison.
  if dnump(x).truthy() && dnump(y).truthy() {
    let r = rgrp(car(x), car(y))
    let v = if eq(r, q_d_zero) {
      deq(y, y)
    } else if eq(r, q_d_pos) {
      dgr(y, y)
    } else {
      dls(y, y)
    }
    if v.truthy() {
      return v
    }
  }
  for d in zl_get(x, q_data).iter() {
    if visiblep(d).truthy() && deqf(x, y, d).truthy() {
      return t
    }
  }
  Nil
}

///|
fn deqf(x : Value, y : Value, f : Value) -> Value raise {
  let r = caar(f)
  if eq(q_meqp, r) {
    if eq(x, cadar(f)) {
      deq(caddar(f), y)
    } else {
      deq(cadar(f), y)
    }
  } else if eq(q_mgrp, r) {
    if eq(x, cadar(f)) {
      dgr(caddar(f), y)
    } else {
      dls(cadar(f), y)
    }
  } else if eq(q_mgqp, r) {
    if eq(x, cadar(f)) {
      dgq(caddar(f), y)
    } else {
      dlq(cadar(f), y)
    }
  } else if eq(q_mnqp, r) {
    if eq(x, cadar(f)) {
      dnq(caddar(f), y)
    } else {
      dnq(cadar(f), y)
    }
  } else {
    Nil
  }
}

///|
fn dgr(x : Value, y : Value) -> Value raise {
  if dmark(x, q_d_pos).truthy() {
    return Nil
  }
  if eq(x, y) {
    return t
  }
  // The target has already been reached along a "<=" path: in a consistent
  // database no ">" path reaches it too. Give up this branch only.
  if symval(q_mlqp).truthy() {
    return Nil
  }
  // X > (car x), so (car x) >= (car y) gives X > (car y).
  if dnump(x).truthy() &&
    dnump(y).truthy() &&
    compar__in(rgrp(car(x), car(y)), [q_d_pos, q_d_zero]) {
    let v = dgr(y, y)
    if v.truthy() {
      return v
    }
  }
  for d in zl_get(x, q_data).iter() {
    if visiblep(d).truthy() && dgrf(x, y, d).truthy() {
      return t
    }
  }
  Nil
}

///|
fn dgrf(x : Value, y : Value, f : Value) -> Value raise {
  let r = caar(f)
  if eq(q_mgrp, r) {
    if eq(x, cadar(f)) {
      dgr(caddar(f), y)
    } else {
      Nil
    }
  } else if eq(q_mgqp, r) {
    if eq(x, cadar(f)) {
      dgr(caddar(f), y)
    } else {
      Nil
    }
  } else if eq(q_meqp, r) {
    if eq(x, cadar(f)) {
      dgr(caddar(f), y)
    } else {
      dgr(cadar(f), y)
    }
  } else {
    Nil
  }
}

///|
fn dls(x : Value, y : Value) -> Value raise {
  if dmark(x, q_d_neg).truthy() {
    return Nil
  }
  if eq(x, y) {
    return t
  }
  // Mirror of the MLQP clause in DGR.
  if symval(q_mgqp).truthy() {
    return Nil
  }
  // X < (car x), so (car x) <= (car y) gives X < (car y).
  if dnump(x).truthy() &&
    dnump(y).truthy() &&
    compar__in(rgrp(car(x), car(y)), [q_d_neg, q_d_zero]) {
    let v = dls(y, y)
    if v.truthy() {
      return v
    }
  }
  for d in zl_get(x, q_data).iter() {
    if visiblep(d).truthy() && dlsf(x, y, d).truthy() {
      return t
    }
  }
  Nil
}

///|
fn dlsf(x : Value, y : Value, f : Value) -> Value raise {
  let r = caar(f)
  if eq(q_mgrp, r) {
    if eq(x, caddar(f)) {
      dls(cadar(f), y)
    } else {
      Nil
    }
  } else if eq(q_mgqp, r) {
    if eq(x, caddar(f)) {
      dls(cadar(f), y)
    } else {
      Nil
    }
  } else if eq(q_meqp, r) {
    if eq(x, cadar(f)) {
      dls(caddar(f), y)
    } else {
      dls(cadar(f), y)
    }
  } else {
    Nil
  }
}

///|
fn dgq(x : Value, y : Value) -> Value raise {
  let sgn = zl_get(x, q_n_pluslabs)
  // A label already on X combines with "X >= this node": $NZ makes it an
  // equality, $PN a strict inequality, $POS or $ZERO is already as strong.
  if eq(sgn, q_d_pos) || eq(sgn, q_d_zero) {
    Nil
  } else if eq(q_d_nz, sgn) {
    deq(x, y)
  } else if eq(q_d_pn, sgn) {
    dgr(x, y)
  } else if dmark(x, q_d_pz).truthy() {
    Nil
  } else if eq(x, y) {
    set(q_mgqp, t) |> ignore
    Nil
  } else {
    if dnump(x).truthy() && dnump(y).truthy() {
      let r = rgrp(car(x), car(y))
      let v = if eq(r, q_d_pos) {
        dgr(y, y)
      } else if eq(r, q_d_zero) {
        dgq(y, y)
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
    for d in zl_get(x, q_data).iter() {
      if visiblep(d).truthy() && dgqf(x, y, d).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
fn dgqf(x : Value, y : Value, f : Value) -> Value raise {
  let r = caar(f)
  if eq(q_mgrp, r) {
    if eq(x, cadar(f)) {
      dgr(caddar(f), y)
    } else {
      Nil
    }
  } else if eq(q_mgqp, r) {
    if eq(x, cadar(f)) {
      dgq(caddar(f), y)
    } else {
      Nil
    }
  } else if eq(q_meqp, r) {
    if eq(x, cadar(f)) {
      dgq(caddar(f), y)
    } else {
      dgq(cadar(f), y)
    }
  } else {
    Nil
  }
}

///|
fn dlq(x : Value, y : Value) -> Value raise {
  let sgn = zl_get(x, q_n_pluslabs)
  if eq(sgn, q_d_neg) || eq(sgn, q_d_zero) {
    Nil
  } else if eq(q_d_pz, sgn) {
    deq(x, y)
  } else if eq(q_d_pn, sgn) {
    dls(x, y)
  } else if dmark(x, q_d_nz).truthy() {
    Nil
  } else if eq(x, y) {
    set(q_mlqp, t) |> ignore
    Nil
  } else {
    // X <= (car x); mirrors DGQ.
    if dnump(x).truthy() && dnump(y).truthy() {
      let r = rgrp(car(x), car(y))
      let v = if eq(r, q_d_neg) {
        dls(y, y)
      } else if eq(r, q_d_zero) {
        dlq(y, y)
      } else {
        Nil
      }
      if v.truthy() {
        return v
      }
    }
    for d in zl_get(x, q_data).iter() {
      if visiblep(d).truthy() && dlqf(x, y, d).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
fn dlqf(x : Value, y : Value, f : Value) -> Value raise {
  let r = caar(f)
  if eq(q_mgrp, r) {
    if eq(x, caddar(f)) {
      dls(cadar(f), y)
    } else {
      Nil
    }
  } else if eq(q_mgqp, r) {
    if eq(x, caddar(f)) {
      dlq(cadar(f), y)
    } else {
      Nil
    }
  } else if eq(q_meqp, r) {
    if eq(x, cadar(f)) {
      dlq(caddar(f), y)
    } else {
      dlq(cadar(f), y)
    }
  } else {
    Nil
  }
}

///|
fn dnq(x : Value, y : Value) -> Value raise {
  let sgn = zl_get(x, q_n_pluslabs)
  if eq(sgn, q_d_pos) || eq(sgn, q_d_neg) {
    Nil
  } else if eq(q_d_pz, sgn) {
    dgr(x, y)
  } else if eq(q_d_nz, sgn) {
    dls(x, y)
  } else if dmark(x, q_d_pn).truthy() {
    Nil
  } else if eq(x, y) {
    Nil
  } else {
    // X # (car x) constrains (car y) only where the two numbers are equal.
    if dnump(x).truthy() &&
      dnump(y).truthy() &&
      eq(q_d_zero, rgrp(car(x), car(y))) {
      let v = dnq(y, y)
      if v.truthy() {
        return v
      }
    }
    for d in zl_get(x, q_data).iter() {
      if visiblep(d).truthy() && dnqf(x, y, d).truthy() {
        return t
      }
    }
    Nil
  }
}

///|
fn dnqf(x : Value, y : Value, f : Value) -> Value raise {
  if eq(q_meqp, caar(f)) {
    if eq(x, cadar(f)) {
      dnq(caddar(f), y)
    } else {
      dnq(cadar(f), y)
    }
  } else {
    Nil
  }
}

// The six sign labels stand for sets of possible signs of X - node:
// $POS={+}, $ZERO={0}, $NEG={-}, $PZ={0,+}, $NZ={-,0}, $PN={-,+}, and their
// conjunction is set intersection.

///|
fn sign_label_bits(s : Value) -> Value raise {
  Fix(
    if eq(s, q_d_pos) {
      1L
    } else if eq(s, q_d_zero) {
      2L
    } else if eq(s, q_d_pz) {
      3L
    } else if eq(s, q_d_neg) {
      4L
    } else if eq(s, q_d_pn) {
      5L
    } else if eq(s, q_d_nz) {
      6L
    } else {
      7L
    },
  )
}

///|
/// The conjunction of two sign labels, or NIL when they contradict.
fn sign_label_meet(a : Value, b : Value) -> Value raise {
  let table : Array[Value] = [
    Nil, q_d_pos, q_d_zero, q_d_pz, q_d_neg, q_d_pn, q_d_nz, q_d_pnz,
  ]
  table[to_int(logand(sign_label_bits(a), sign_label_bits(b)))]
}

///|
/// Mark the sign of X, relative to the current comparison point for DCOMP,
/// to be M; X ends up carrying the conjunction of its old label and M.
/// Returns T if that leaves nothing new (including a contradiction), so the
/// caller closes its branch; NIL when the label tightened.
fn dmark(x : Value, m : Value) -> Value raise {
  let mut old = zl_get(x, q_n_pluslabs)
  // A label left by the BEG/QUEUE+P engine is a bit cell, not a sign symbol:
  // treat it as no label.
  if !symbolp(old) {
    old = Nil
  }
  if eq(m, old) {
    return t
  }
  let meet = if old.truthy() { sign_label_meet(old, m) } else { m }
  if meet is Nil {
    t // Contradiction: keep OLD, close the branch.
  } else if eq(meet, old) {
    t // Nothing new: close the branch.
  } else {
    if symval(q_dbtrace).truthy() {
      mtell(
        list([
          Str("DMARK: marking ~M ~M"),
          if atom(x) {
            x
          } else {
            car(x)
          },
          meet,
        ]),
      )
      |> ignore
    }
    // Push on every store, so the next CLEAR sweeps the label.
    push_special(x, q_n_pluslabs) |> ignore
    cput(x, meet, q_n_pluslabs) |> ignore
    Nil
  }
}

///|
fn daddgr(flag : Value, x : Value) -> Value raise {
  let (lhs, rhs) = compsplt(x)
  mdata(flag, q_mgrp, lhs, rhs) |> ignore
  if mnump(lhs).truthy() || constant(lhs).truthy() {
    list3(list1(q_mlessp), rhs, lhs)
  } else {
    list3(list1(q_mgreaterp), lhs, rhs)
  }
}

///|
fn daddgq(flag : Value, x : Value) -> Value raise {
  let (lhs, rhs) = compsplt(x)
  mdata(flag, q_mgqp, lhs, rhs) |> ignore
  if mnump(lhs).truthy() || constant(lhs).truthy() {
    list3(list1(q_mleqp), rhs, lhs)
  } else {
    list3(list1(q_mgeqp), lhs, rhs)
  }
}

///|
fn daddeq(flag : Value, x : Value) -> Value raise {
  let (lhs, rhs) = compsplt_eq(x)
  mdata(flag, q_meqp, lhs, rhs) |> ignore
  list3(list1(q_d_equal), lhs, rhs)
}

///|
fn daddnq(flag : Value, x : Value) -> Value raise {
  let (lhs, rhs) = compsplt_eq(x)
  if mtimesp(lhs).truthy() && equal(rhs, Fix(0L)) {
    // A product is non-zero iff all factors are non-zero: always learn, but
    // unlearn only if ALL factors are known to be non-zero.
    if flag.truthy() || every(term => eq(t, mnqp(term, Fix(0L))), cdr(lhs)) {
      for term in cdr(lhs).iter() {
        daddnq(flag, term) |> ignore
      }
    }
  } else if mexptp(lhs).truthy() &&
    mexptp(rhs).truthy() &&
    integerp(caddr(lhs)) &&
    integerp(caddr(rhs)) &&
    equal(caddr(lhs), caddr(rhs)) {
    // File the relation itself, and the facts that follow from it: x^n # y^n
    // implies x # y, and x # -y as well when n is even. Always learn, but
    // unlearn only if the relation is itself known.
    if flag.truthy() || eq(t, mnqp(lhs, rhs)) {
      mdata(flag, q_mnqp, lhs, rhs) |> ignore
      let ds = if oddp(caddr(lhs)) {
        list1(sub(cadr(lhs), cadr(rhs)))
      } else {
        list2(sub(cadr(lhs), cadr(rhs)), add2(cadr(lhs), cadr(rhs)))
      }
      for d in ds.iter() {
        daddnq(flag, d) |> ignore
      }
    }
  } else {
    mdata(flag, q_mnqp, lhs, rhs) |> ignore
  }
  list2(list1(q_mnot), list3(list1(q_d_equal), lhs, rhs))
}

// The following functions are used by asksign to write answers into the
// database, in the global context $initial (not a local context which might
// be destroyed before the evaluation has finished). clearsign removes them.

///|
fn tdpos(x : Value) -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    daddgr(t, x) |> ignore
    push_special(cons(x, q_d_pos), q_ear_local_signs)
  })
}

///|
fn tdneg(x : Value) -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    daddgr(t, neg(x)) |> ignore
    push_special(cons(x, q_d_neg), q_ear_local_signs)
  })
}

///|
fn tdzero(x : Value) -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    daddeq(t, x) |> ignore
    push_special(cons(x, q_d_zero), q_ear_local_signs)
  })
}

///|
fn tdpn(x : Value) -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    daddnq(t, x) |> ignore
    push_special(cons(x, q_d_pn), q_ear_local_signs)
  })
}

///|
fn tdpz(x : Value) -> Value raise {
  with_special(q_context, q_d_initial, fn() {
    daddgq(t, x) |> ignore
    push_special(cons(x, q_d_pz), q_ear_local_signs)
  })
}

///|
fn compsplt_eq(x : Value) -> (Value, Value) raise {
  let (l0, r0) = compsplt(x)
  let mut lhs = l0
  let mut rhs = r0
  if equal(lhs, Fix(0L)) {
    lhs = rhs
    rhs = Fix(0L)
  }
  if equal(rhs, Fix(0L)) &&
    (
      mexptp(lhs).truthy() ||
      (
        !atom(lhs) &&
        kind_all_of_p(caar(lhs), list2(q_d_oddfun, q_d_increasing)).truthy()
      )
    ) {
    compsplt_eq(cadr(lhs))
  } else {
    (lhs, rhs)
  }
}

///|
fn mdata(flag : Value, r : Value, x : Value, y : Value) -> Value raise {
  if flag.truthy() {
    let dx = dintern(x)
    let dy = dintern(y)
    mfact(r, dx, dy)
  } else {
    let x = dinternp(x)
    let y = dinternp(y)
    if x.truthy() && y.truthy() {
      mkill(r, x, y)
    } else {
      Nil
    }
  }
}

///|
fn mfact(r : Value, x : Value, y : Value) -> Value raise {
  let f = datum(list3(r, x, y))
  cntxt(f, symval(q_context)) |> ignore
  addf(f, x) |> ignore
  addf(f, y)
}

///|
fn mkill(r : Value, x : Value, y : Value) -> Value raise {
  let f = car(datum(list3(r, x, y)))
  kcntxt(f, symval(q_context)) |> ignore
  maxima_remf(f, x) |> ignore
  maxima_remf(f, y)
}

///|
fn mkind(x : Value, y : Value) -> Value raise {
  let dx = dintern(x)
  let dy = dintern(y)
  kind(dx, dy)
}

///|
/// Each argument is a float, bigfloat, integer, or Maxima rational. Maxima
/// rationals are converted to Lisp rationals to make them comparable.
fn rgrp(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  if d_bfloatp(x).truthy() || d_bfloatp(y).truthy() {
    let xx = x
    let yy = y
    x = with_special(q_d_float2bf, t, () => cadr(d_bfloat(sub(xx, yy))))
    y = Fix(0L)
  }
  if !numberp(x) {
    x = num_div(cadr(x), caddr(x))
  }
  if !numberp(y) {
    y = num_div(cadr(y), caddr(y))
  }
  if num_gt(x, y) {
    q_d_pos
  } else if num_gt(y, x) {
    q_d_neg
  } else {
    q_d_zero
  }
}

///|
fn mcons(x : Value, l : Value) -> Value raise {
  cons(car(l), cons(x, cdr(l)))
}

///|
fn flip(s : Value) -> Value raise {
  if eq(q_d_pos, s) {
    q_d_neg
  } else if eq(q_d_neg, s) {
    q_d_pos
  } else if eq(q_d_pz, s) {
    q_d_nz
  } else if eq(q_d_nz, s) {
    q_d_pz
  } else {
    s
  }
}

///|
fn strongp(x : Value, y : Value) -> Value raise {
  if eq(q_d_pnz, y) {
    t
  } else if eq(q_d_pnz, x) {
    Nil
  } else {
    memq(y, list([q_d_pz, q_d_nz, q_d_pn]))
  }
}

///|
fn munformat(form : Value) -> Value raise {
  if atom(form) {
    form
  } else {
    cons(caar(form), mapcar(f => munformat(f), cdr(form)))
  }
}

///|
fn declaration_inconsistent_p(var_ : Value, prop : Value) -> Value raise {
  let prop2 = assq(prop, symval(q_ear_inconsistent_declarations))
  let f = falsep(list3(q_kind, var_, prop))
  if f.truthy() {
    f
  } else if prop2.truthy() {
    truep(list3(q_kind, var_, cdr(prop2)))
  } else {
    Nil
  }
}

///|
/// This function is for $DECLARE to use.
fn declarekind(var_ : Value, prop : Value) -> Value raise {
  if truep(list3(q_kind, var_, prop)).truthy() {
    t
  } else if declaration_inconsistent_p(var_, prop).truthy() {
    merr("declare: inconsistent declaration ~:M", [mk(q_d_declare, [var_, prop])])
  } else {
    mkind(var_, prop) |> ignore
    t
  }
}

// These functions reformat expressions to be stored in the data base.

///|
/// A list of all the atoms in X that aren't either numbers or constants whose
/// numerical value we know.
fn unknown_atoms(x : Value) -> Value raise {
  with_special(q_d_listconstvars, t, () => remove_if(
    s => mget(s, q_d_numer).truthy(),
    cdr(d_listofvars(x)),
  ))
}

///|
/// Rewrite X = a^b to a simpler expression that has the same sign: if b is
/// odd, or b = n/d with n and d odd, remove the exponent (not for an even n,
/// and the n/d case not in complex mode with domain : complex). If b has a
/// negative sign, return a^-b. Otherwise return X unmodified.
fn rewrite_mexpt_retaining_sign(x : Value) -> Value raise {
  if !mexptp(x).truthy() {
    return x
  }
  let base = cadr(x)
  let exponent = caddr(x)
  if eq(evod(exponent), q_d_odd) ||
    (
      !(
        symval(q_ear_compsplt_for_sign).truthy() &&
        eq(symval(q_d_domain), q_d_complex)
      ) &&
      {
        let (num, denom) = with_specials(
          [
            (q_d_exptdispflag, t),
            (q_d_pfeformat, Nil),
            (q_d__pctedispflag, Nil),
          ],
          () => num_denom_split(exponent),
        )
        // A denominator of 1 means b is not a quotient.
        !eql(denom, Fix(1L)) &&
        eq(evod(denom), q_d_odd) &&
        eq(evod(num), q_d_odd)
      }
    ) {
    base
  } else if negp(exponent).truthy() {
    inv(x)
  } else {
    x
  }
}

///|
/// Split X into (LHS, RHS) so that X>0 <=> LHS > RHS: a canonical form for X
/// that can be stored in the database and looked up later. COMPSPLT-SINGLE
/// handles X with only one unknown symbol, COMPSPLT-GENERAL the rest.
fn compsplt(x : Value) -> (Value, Value) raise {
  let (l0, r0) : (Value, Value) = if atom(x) || atom(car(x)) {
    (x, Fix(0L))
  } else if cdr(unknown_atoms(x)) is Nil {
    compsplt_single(x)
  } else {
    compsplt_general(x)
  }
  let mut lhs = l0
  let mut rhs = r0
  let mut swapped = false
  // If lhs is zero, swap lhs and rhs to make the following code simpler.
  if equal(lhs, Fix(0L)) {
    lhs = rhs
    rhs = Fix(0L)
    swapped = true
  }
  // If LHS is a lone power that REWRITE-MEXPT-RETAINING-SIGN changes, split
  // the result from scratch, so that (x+1)^3>0 becomes x>-1.
  if equal(rhs, Fix(0L)) && mexptp(lhs).truthy() {
    let new_ = rewrite_mexpt_retaining_sign(lhs)
    if !eq(new_, lhs) {
      return compsplt(if swapped { neg(new_) } else { new_ })
    }
  }
  if equal(rhs, Fix(0L)) {
    // Rewrite mexpts in factors so that e.g. x^3/y>0 becomes x*y>0.
    lhs = if mtimesp(lhs).truthy() {
      cons(car(lhs), mapcar(f => rewrite_mexpt_retaining_sign(f), cdr(lhs)))
    } else {
      rewrite_mexpt_retaining_sign(lhs)
    }
  }
  // Undo swapping lhs and rhs.
  if swapped {
    (rhs, lhs)
  } else {
    (lhs, rhs)
  }
}

///|
fn compsplt_single(x : Value) -> (Value, Value) raise {
  with_special(q_success, Nil, fn() {
    let mut exp = list2(x, Fix(0L))
    while !(symval(q_success).truthy() || symbols(cadr(exp)).truthy()) {
      if atom(car(exp)) {
        set(q_success, t) |> ignore
      } else if eq(caaar(exp), q_mplus) {
        exp = splitsum(exp)
      } else if eq(caaar(exp), q_mtimes) {
        exp = splitprod(exp)
      } else {
        set(q_success, t) |> ignore
      }
    }
    (car(exp), cadr(exp))
  })
}

///|
fn compsplt_general(x : Value) -> (Value, Value) raise {
  // Let compsplt-single work on it first to treat constant factors/terms.
  let (lhs, rhs) = compsplt_single(x)
  let x = sub(lhs, rhs)
  if atom(x) || atom(car(x)) {
    // An atom or a single level list: we won't change it any.
    (x, Fix(0L))
  } else if negp(x).truthy() {
    // A negative expression but not a sum: get rid of the negative sign.
    (Fix(0L), neg(x))
  } else if cdddr(x).truthy() ||
    !eq(caar(x), q_mplus) ||
    intersect_star(symbols(cadr(x)), symbols(caddr(x))).truthy() {
    // Not a sum, or a sum with more than 2 terms, or with symbols common to
    // both summands: do nothing.
    (x, Fix(0L))
  } else if (negp(cadr(x)).truthy() || mnump(cadr(x)).truthy()) &&
    !negp(caddr(x)).truthy() {
    // -x + y gives (y, x)
    (caddr(x), neg(cadr(x)))
  } else if !negp(cadr(x)).truthy() &&
    (negp(caddr(x)).truthy() || mnump(caddr(x)).truthy()) {
    // x - y gives (x, y)
    (cadr(x), neg(caddr(x)))
  } else if negp(cadr(x)).truthy() && negp(caddr(x)).truthy() {
    // - x - y gives (0, x+y)
    (Fix(0L), neg(x))
  } else {
    // Give up! (x, 0)
    (x, Fix(0L))
  }
}

///|
fn negp(x : Value) -> Value raise {
  if mtimesp(x).truthy() {
    mnegp(cadr(x))
  } else {
    Nil
  }
}

///|
fn splitsum(exp_ : Value) -> Value raise {
  let mut llist = cdar(exp_)
  let mut lhs1 = car(exp_)
  let mut rhs1 = cadr(exp_)
  while llist.truthy() {
    if memq(q_d_inf, llist).truthy() {
      rhs1 = add2(q_d_inf, sub_star(rhs1, addn(llist, t)))
      lhs1 = add2(q_d_inf, sub_star(lhs1, addn(llist, t)))
      llist = Nil
    } else if memq(q_d_minf, llist).truthy() {
      rhs1 = add2(q_d_minf, sub_star(rhs1, addn(llist, t)))
      lhs1 = add2(q_d_minf, sub_star(lhs1, addn(llist, t)))
      llist = Nil
    } else if symbols(car(llist)) is Nil {
      lhs1 = sub(lhs1, car(llist))
      rhs1 = sub(rhs1, car(llist))
    }
    llist = cdr(llist)
  }
  if mplusp(lhs1).truthy() {
    set(q_success, t) |> ignore
  }
  list2(lhs1, rhs1)
}

///|
fn splitprod(exp_ : Value) -> Value raise {
  // The DO binds SIGN, MINUS, EVENS and ODDS (specials) to NIL.
  compar__with_signs(fn() {
    let mut flipsign = false
    let mut lhs1 = car(exp_)
    let mut rhs1 = cadr(exp_)
    let mut llist = cdar(exp_)
    while llist.truthy() {
      if symbols(car(llist)) is Nil {
        sign(car(llist)) |> ignore
        if eq(compar__sign(), q_d_neg) {
          flipsign = !flipsign
        }
        if eq(compar__sign(), q_d_pos) || eq(compar__sign(), q_d_neg) {
          lhs1 = div(lhs1, car(llist))
          rhs1 = div(rhs1, car(llist))
        }
      }
      llist = cdr(llist)
    }
    if mtimesp(lhs1).truthy() {
      set(q_success, t) |> ignore
    }
    if flipsign {
      set(q_success, t) |> ignore
      list2(rhs1, lhs1)
    } else {
      list2(lhs1, rhs1)
    }
  })
}

///|
fn symbols(x : Value) -> Value raise {
  with_special(q_d_listconstvars, symval(q_p_initiallearnflag), () => cdr(
    d_listofvars(x),
  ))
}

///|
/// %initiallearnflag is only necessary so that %PI, %E, etc. can be LEARNed.
fn initialize_numeric_constant(c : Value) -> Value raise {
  with_specials([(q_context, q_d_global), (q_p_initiallearnflag, t)], () => learn(
    mk(q_mequal, [c, mget(c, q_d_numer)]),
    t,
  ))
}

///|
/// Adds database assumptions for $zeroa and $zerob to the global context.
fn initialize_zeroab(c : Value) -> Value raise {
  with_specials([(q_context, q_d_global), (q_p_initiallearnflag, t)], fn() {
    if eq(c, q_d_zeroa) {
      learn(mk(q_mgreaterp, [q_d_zeroa, Fix(0L)]), t)
    } else if eq(c, q_d_zerob) {
      learn(mk(q_mlessp, [q_d_zerob, Fix(0L)]), t)
    } else {
      Nil
    }
  })
}

///|
fn compar__sign_fn(name : String, f : (Value) -> Value raise) -> Value {
  lfunc(name, args => f(arg(args, 0)))
}

///|
fn init_compar() -> Unit raise {
  putprop(q_d_context, q_asscontext, q_assign) |> ignore
  putprop(q_d_is, q_simp__dolis, q_operators) |> ignore
  putprop(q_p_is, q_simp__dolis, q_operators) |> ignore
  putprop(q_d_maybe, q_simp__dolis, q_operators) |> ignore
  putprop(q_p_maybe, q_simp__dolis, q_operators) |> ignore
  // The presence of OPERS tells SIMPLIFYA to call OPER-APPLY, which calls
  // NARY1 to flatten nested "and" and "or" expressions.
  putprop(q_mand, t, q_opers) |> ignore
  putprop(q_mor, t, q_opers) |> ignore
  putprop(q_mnot, q_simp_mnot, q_operators) |> ignore
  putprop(q_mand, q_simp_mand, q_operators) |> ignore
  putprop(q_mor, q_simp_mor, q_operators) |> ignore
  set(q_limitp, Nil) |> ignore
  putprop(q_d_und, t, q_sysconst) |> ignore
  putprop(q_d_ind, t, q_sysconst) |> ignore
  putprop(q_d_zeroa, t, q_sysconst) |> ignore
  putprop(q_d_zerob, t, q_sysconst) |> ignore
  defvar_init(q_indefinites, list2(q_d_und, q_d_ind))
  let sign_functions : Array[(Value, Value)] = [
    (q_mtimes, q_sign_mtimes),
    (q_mplus, q_sign_mplus),
    (q_mexpt, q_sign_mexpt),
    (q_p_log, q_sign_log),
    (q_mabs, q_sign_mabs),
    (q_d_min, compar__sign_fn("sign-minmax", x => sign_minmax(caar(x), cdr(x)))),
    (q_d_max, compar__sign_fn("sign-minmax", x => sign_minmax(caar(x), cdr(x)))),
    (q_p_csc, q_sign_csc_slsec_slcsch_slcoth),
    (q_p_sec, q_sign_csc_slsec_slcsch_slcoth),
    (q_p_csch, q_sign_csc_slsec_slcsch_slcoth),
    (q_p_coth, q_sign_csc_slsec_slcsch_slcoth),
    (q_p_acos, q_sign_asin_slacos_slatanh),
    (q_p_asin, q_sign_asin_slacos_slatanh),
    (q_p_atan, q_sign_atan_slasinh),
    (q_p_acot, q_sign_acot),
    (q_p_asinh, q_sign_atan_slasinh),
    (q_p_acosh, q_sign_acosh),
    (q_p_atanh, q_sign_asin_slacos_slatanh),
    (q_p_asec, q_sign_asec_slacsc_slasech_slacsch_slacoth),
    (q_p_acsc, q_sign_asec_slacsc_slasech_slacsch_slacoth),
    (q_p_acsch, q_sign_asec_slacsc_slasech_slacsch_slacoth),
    (q_p_asech, q_sign_asec_slacsc_slasech_slacsch_slacoth),
    (q_p_acoth, q_sign_asec_slacsc_slasech_slacsch_slacoth),
    (q_p_tan, q_sign_tan_slcot),
    (q_p_cot, q_sign_tan_slcot),
    (q_p_signum, compar__sign_fn("sign-signum", x => sign(cadr(x)))),
    (q_p_erf, compar__sign_fn("sign-erf", x => sign(cadr(x)))),
    (
      q_d_li,
      compar__sign_fn("sign-li", fn(x) {
        let z = first(margs(x))
        let n = cadadr(x)
        if mnump(n).truthy() &&
          eq(t, mgrp(z, Fix(0L))) &&
          eq(t, mgrp(Fix(1L), z)) {
          sign(z)
        } else {
          sign_any(x)
        }
      }),
    ),
  ]
  for sf in sign_functions {
    putprop(sf.0, sf.1, q_sign_function) |> ignore
  }
  // The REAL-RANGE property of a function that is real for every real
  // argument (carg: for every argument): the bounds (LO HI) of its values,
  // each NIL for no bound, else (BOUND INCLUSIVE-P).
  for s in lread(
      "((%sin ((-1 t) (1 t))) (%cos ((-1 t) (1 t))) (%signum ((-1 t) (1 t))) (%cosh ((1 t) ())) (%sech ((0 ()) (1 t))) (%erf ((-1 ()) (1 ()))) (%erfc ((0 ()) (2 ()))) (%tanh ((-1 ()) (1 ()))) (%atan ((((mtimes simp) ((rat simp) -1 2) $%pi) ()) (((mtimes simp) ((rat simp) 1 2) $%pi) ()))) (%atan2 ((((mtimes simp) -1 $%pi) ()) ($%pi t))) (%carg ((((mtimes simp) -1 $%pi) ()) ($%pi t))))",
    ).iter() {
    putprop(first(s), second(s), q_real_range) |> ignore
  }
  putprop(q_p_sin, q_sign_sin, q_sign_function) |> ignore
  putprop(q_p_cos, q_sign_cos, q_sign_function) |> ignore
  putprop(q_d_ceiling, q_sign_ceiling, q_sign_function) |> ignore
  putprop(q_d_floor, q_sign_floor, q_sign_function) |> ignore
  // Give a function the maps-integers-to-integers property when it is
  // integer valued on the integers; the integer-valued property when its
  // range is a subset of the integers.
  for s in [q_mplus, q_mtimes, q_mabs, q_d_max, q_d_min, q_p_signum] {
    putprop(s, t, q_maps_integers_to_integers) |> ignore
  }
  for s in [
    q_d_floor, q_p_floor, q_d_ceiling, q_p_ceiling, q_d_charfun, q_p_unit_step,
    q_d_unit_step,
  ] {
    putprop(s, t, q_integer_valued) |> ignore
  }
  with_special(q_context, q_d_global, fn() {
    mapc(
      p => true_star(p) |> ignore,
      lread(
        "((par ($even $odd) $integer) (kind $integer $rational) (kind $irrational $noninteger) (par ($rational $irrational) $real) (kind $imaginary $complex) (kind $imaginary $noninteger) (kind $%i $imaginary) (kind $%e $irrational) (kind $%pi $irrational) (kind $%gamma $noninteger) (kind $%gamma $real) (kind $%phi $irrational) (kind $%catalan $noninteger) (kind $%catalan $real) (kind %log $increasing) (kind mabs $evenfun) (kind %signum $oddfun) (kind %sin $oddfun) (kind %cos $evenfun) (kind %tan $oddfun) (kind %csc $oddfun) (kind %sec $evenfun) (kind %cot $oddfun) (kind %asin $increasing) (kind %asin $oddfun) (kind %atan $increasing) (kind %atan $oddfun) (kind $delta $evenfun) (kind %sinh $increasing) (kind %sinh $oddfun) (kind %cosh $posfun) (kind %cosh $evenfun) (kind %tanh $increasing) (kind %tanh $oddfun) (kind %coth $oddfun) (kind %csch $oddfun) (kind %sech $evenfun) (kind %sech $posfun) (kind %erfc $posfun) (kind %asinh $increasing) (kind %asinh $oddfun) (kind %acosh $increasing) (kind %acosh $complex) (kind %atanh $increasing) (kind %atanh $oddfun) (kind $li $complex) (kind %lambert_w $complex) (kind %cabs $real) (kind %cabs $evenfun))",
      ),
    )
  })
  |> ignore
  // Create an initial context for the user which is a subcontext of $global.
  d_newcontext(list1(q_d_initial)) |> ignore
}
