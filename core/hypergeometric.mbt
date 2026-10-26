// Port of src/hypergeometric.lisp: the hypergeometric function simplifier
// and its numerical evaluation (Barton Willis).
//
// For numerical evaluation of the hypergeometric functions, the method uses
// a running error. When the error is too large, the value of fpprec is
// increased and the evaluation is redone with the larger value of fpprec.
// The option variable max_fpprec is the largest value for fpprec Maxima
// will try.

///|
/// `(bind-fpprec val body)` from float.lisp.
fn[T] hyp__bind_fpprec(val : Value, f : () -> T raise) -> T raise {
  let bs = bind_all([
    (q_fpprec, Nil),
    (q_ear_bigfloatzero, Nil),
    (q_ear_bigfloatone, Nil),
    (q_ear_bfhalf, Nil),
    (q_ear_bfmhalf, Nil),
  ])
  defer unbind_all(bs)
  let b = bind(q_d_fpprec, fpprec1(Nil, val))
  defer unbind(b)
  f()
}

///|
/// `#.(/ (log 2) (log 10))`: CL `(log 2)` of an integer is a single float,
/// so this read-time constant is a single float.
fn hyp__log10_2_single() -> Float {
  let ln2 : Float = Float::from_double(0.6931471805599453)
  let ln10 : Float = Float::from_double(2.302585092994046)
  ln2 / ln10
}

///|
/// `(ceiling (* n #.(/ (log 2) (log 10))))` in CL single-float arithmetic.
fn hyp__ceiling_digits(n : Value) -> Value raise {
  let p : Float = Float::from_int(to_int(n)) * hyp__log10_2_single()
  int(p.to_double().ceil().to_int())
}

///|
/// The functions `$second`, `$third` of comm.lisp (defined there by the
/// `make-nth` macrolet).
fn hyp__mnth(e : Value, i : Int, name : Value) -> Value raise {
  let e = format1(e)
  atomchk(e, name, Nil) |> ignore
  if length(margs(e)) < i {
    merror(Str("~:M: no such element in ~M"), list2(name, e)) |> ignore
  }
  nth(i - 1, margs(e))
}

///|
/// Lisp `ignore-errors` around a two-valued call: on error, `(nil, nil)`.
fn hyp__ignore_errors2(
  f : () -> (Value, Value) raise,
) -> (Value, Value) raise {
  f() catch {
    LispError::Throw(_, _) as e => raise e
    LispError::ReturnFrom(_, _) as e => raise e
    LispError::Go(_) as e => raise e
    _ => (Nil, Nil)
  }
}

///|
/// If the length of l is n, return true; otherwise signal wna-err = (wrong
/// number of arguments, by the way).
fn argument_length_check(l : Value, n : Value) -> Value raise {
  if consp(l) && consp(first(l)) && equal(n, int(length(margs(l)))) {
    t
  } else {
    wna_err(caar(l))
  }
}

///|
/// When multiple_value_return is nil, multiple_values(e1,e2,...) --> e1;
/// otherwise multiple_values(e1,e2,...) --> multiple_values(e1,e2,...).
fn simp_multiple_values(e : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  if symval(q_d_multiple_value_return).truthy() {
    cons(list2(q_d_multiple_values, q_simp), mapcar(s => simpcheck(s, z), cdr(e)))
  } else {
    simpcheck(cadr(e), z)
  }
}

///|
/// Detect undefined and polynomial cases.
fn classify_hypergeometric(a : Value, b : Value, x : Value) -> Value raise {
  let mut ah : Value = Nil
  let mut bh : Value = Nil

  // Let bh = the greatest member of b that is a negative integer. If there
  // is no such member, set bh = nil.
  for bk in b.iter() {
    if integerp(bk) && num_le(bk, Fix(0L)) && (bh is Nil || num_gt(bk, bh)) {
      bh = bk
    }
  }

  // Let ah = the greatest member of a that is a negative integer. If there
  // is no such member, set ah = nil.
  for ak in a.iter() {
    if integerp(ak) && num_le(ak, Fix(0L)) && (ah is Nil || num_gt(ak, ah)) {
      ah = ak
    }
  }

  // Undefined when either (1) ah is nil and bh is non-nil or (2) ah and bh
  // are non-nil and ah >= bh, and each member of a and b are numbers.
  if every(s => d_numberp(s).truthy(), a) &&
    every(s => d_numberp(s).truthy(), b) &&
    ((ah is Nil && bh.truthy()) ||
    (ah.truthy() && bh.truthy() && num_ge(bh, ah))) {
    q_undefined
  } else if ah.truthy() ||
    zerop1(d_ratdisrep(x)).truthy() ||
    (d_taylorp(x).truthy() &&
    eql(Fix(0L), hyp__mnth(d_first(d_taylorinfo(x)), 2, q_d_second)) &&
    integerp(hyp__mnth(d_first(d_taylorinfo(x)), 3, q_d_third))) {
    q_polynomial
  } else {
    q_nonpolynomial
  }
}

///|
/// The function simpcheck changes taylor polynomials to general form; so
/// use tsimpcheck: if e is a taylor polynomial, simplify; otherwise,
/// simpcheck.
fn tsimpcheck(e : Value, z : Value) -> Value raise {
  if d_taylorp(e).truthy() || d_ratp(e).truthy() {
    simplifya(e, z)
  } else {
    simpcheck(e, z)
  }
}

///|
/// hypergeometric(a,b,x) is entire (commutes with conjugate) when
/// length(a) < length(b) + 1. Also hypergeometric(a,b,x) is analytic inside
/// the unit disk. Outside the unit disk, conjugate gives a nounform.
fn conjugate_hypergeometric(l : Value) -> Value raise {
  let a = first(l)
  let b = second(l)
  let x = third(l)
  if num_lt(d_length(a), num_add(Fix(1L), d_length(b))) ||
    eq(t, mgrp(Fix(1L), take(list1(q_mabs), [x]))) {
    take(list1(q_p_hypergeometric), [
      take(list1(q_d_conjugate), [a]),
      take(list1(q_d_conjugate), [b]),
      take(list1(q_d_conjugate), [x]),
    ])
  } else {
    list2(list2(q_d_conjugate, q_simp), take(list1(q_p_hypergeometric), [a, b, x]))
  }
}

///|
fn lenient_complex_p(e : Value) -> Value raise {
  lbool(
    d_freeof(
      list([
        q_d_infinity,
        q_d_und,
        q_d_ind,
        q_d_inf,
        q_d_minf,
        q_d_false,
        q_d_true,
        t,
        Nil,
        e,
      ]),
    ).truthy() &&
    !mbagp(e).truthy() &&
    !d_featurep(e, q_d_nonscalar).truthy() &&
    !mrelationp(e).truthy() &&
    !d_member(e, symval(q_d_arrays)).truthy(),
  )
}

///|
/// Do noncontroversial simplifications on the hypergeometric function:
///
///     (a) hypergeometric([], [], x) --> exp(x),
///     (b) hypergeometric([a], [], x) --> 1 / (1 - x)^a,
///     (c) hypergeometric([a1,...], [b1, ...], 0) --> 1,
///     (d) hypergeometric([-n,...], [b1, ...], x) --> polynomial.
///     (d) sort and delete common parameters; for example
///         hypergeometric([p,b,a],[c,b],x) --> hypergeometric([a,p],[c],x).
///     (e) hypergeometric([0,a1, ... ], [b1, ...], x) --> 1.
///
/// The code uses (take '(mlist) a) instead of (cons '(mlist) a) because the
/// latter messes up tellsimp rules.
fn simp__pcthypergeometric(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 3 {
    wna_err(
      form,
      required_arg_count=int(3),
      pretty_name=mk(q_p_hypergeometric, [q_d_a, q_d_b, q_d_x]),
    )
    |> ignore
  }
  let mut a = nth(1, form)
  let mut b = nth(2, form)
  let mut x = nth(3, form)
  let bd = bind(q_d_domain, q_d_complex)
  defer unbind(bd)
  if !(d_listp(a).truthy() && d_listp(b).truthy()) {
    mtell(
      list1(
        Str("warning: The first two arguments to 'hypergeometric' must be lists.~%"),
      ),
    )
    |> ignore
    return eqtest(cons(list1(q_p_hypergeometric), list([a, b, x])), form)
  }
  a = mapcar(s => tsimpcheck(s, p__pctsimpflag), margs(a))
  b = mapcar(s => tsimpcheck(s, p__pctsimpflag), margs(b))
  x = tsimpcheck(x, p__pctsimpflag)

  // Delete common members of a and b. This code is taken from hyp.lisp.
  let l = zl_intersection(a, b)
  a = del(l, a)
  b = del(l, b)

  // Check for undefined cases
  let hg_type = classify_hypergeometric(a, b, x)
  let a_len = length(a)
  let b_len = length(b)

  // Sort a and b and reconvert to Maxima lists.
  a = sort_list(a, (p, q) => d_orderlessp(p, q).truthy())
  b = sort_list(b, (p, q) => d_orderlessp(p, q).truthy())
  a = simplify(cons(list1(q_mlist), a))
  b = simplify(cons(list1(q_mlist), b))

  // If constantp(x), apply rectform to x.
  if d_constantp(x).truthy() {
    x = d_rectform(x)
  }

  // Catch undefined cases and return a nounform.
  if eq(hg_type, q_undefined) ||
    member_if(s => !lenient_complex_p(s).truthy(), cdr(a)).truthy() ||
    member_if(s => !lenient_complex_p(s).truthy(), cdr(b)).truthy() ||
    !lenient_complex_p(x).truthy() {
    return eqtest(cons(list1(q_p_hypergeometric), list([a, b, x])), form)
  }

  // pFq([a1,...,ap], [b1,...,bq], 0) --> 1 + 0
  if zerop1(x).truthy() {
    return add2(Fix(1L), x)
  }

  // pFq([0,a1,...,ap], [b1,...,bq], x) --> 1
  if member_if(s => zerop1(s).truthy(), margs(a)).truthy() {
    return Fix(1L)
  }

  // Do hypergeometric([],[],x) --> exp(x).
  if a_len == 0 && b_len == 0 {
    let v = hypergeometric_0f0(x)
    if v.truthy() {
      return v
    }
  }

  // Do hypergeometric([a],[],x) --> 1 / (1-x)^a.
  if a_len == 1 && b_len == 0 {
    let v = hypergeometric_1f0(second(a), x)
    if v.truthy() {
      return v
    }
  }

  // Try reflection identity for 1F1.
  if a_len == 1 && b_len == 1 {
    let v = hypergeometric_1f1(second(a), second(b), x, hg_type)
    if v.truthy() {
      return v
    }
  }

  // For 2F1, value at 1--nothing else.
  if a_len == 2 && b_len == 1 {
    let v = hypergeometric_2f1(second(a), third(a), second(b), x)
    if v.truthy() {
      return v
    }
  }

  // Try numerical evaluation; return nil on failure. This should handle
  // IEEE float, IEEE complex float, bigfloat, and complex big float cases.
  let return_type = use_float_hypergeometric_numerical_eval(
    margs(a),
    margs(b),
    x,
  )
  if return_type.truthy() {
    let dig = hyp__ceiling_digits(
      if eq(return_type, q_float) {
        Fix(53L)
      } else {
        symval(q_fpprec)
      },
    )
    let v = hypergeometric_float_eval(margs(a), margs(b), x, dig, return_type)
    if v.truthy() {
      return v
    }
  }

  // Try rational number numerical evaluation. This should handle rational
  // and complex rational numerical evaluation.
  if use_rational_hypergeometric_numerical_eval(margs(a), margs(b), x).truthy() {
    return rational_hypergeometric_numerical_eval(margs(a), margs(b), x)
  }

  // Handle all other polynomial cases; this includes the case that x is a
  // Taylor polynomial centered at zero.
  let v = hypergeometric_poly_case(margs(a), margs(b), x)
  if v.truthy() {
    return v
  }

  // Return a nounform.
  eqtest(cons(list1(q_p_hypergeometric), list([a, b, x])), form)
}

///|
/// When x isn't a float, do 0F0([],[],x) --> exp(x).
fn hypergeometric_0f0(x : Value) -> Value raise {
  if use_float_hypergeometric_numerical_eval(Nil, Nil, x).truthy() {
    Nil
  } else {
    take(list1(q_mexpt), [q_d__pcte, x])
  }
}

///|
/// When a or x aren't floats, do 1F0([a],[],x) --> 1/(1-x)^a.
fn hypergeometric_1f0(a : Value, x : Value) -> Value raise {
  if use_float_hypergeometric_numerical_eval(list1(a), Nil, x).truthy() {
    Nil
  } else if onep(x).truthy() {
    if eq(t, mgrp(Fix(0L), a)) {
      Fix(0L)
    } else {
      Nil
    }
  } else {
    div(Fix(1L), take(list1(q_mexpt), [sub(Fix(1L), x), a]))
  }
}

///|
/// Apply the Kummer reflection identity when b-a is a negative integer and
/// we know that the hypergeometric function is not already known to be a
/// polynomial (that is a is not a negative integer) or when
/// (great (neg x) x); otherwise, return nil. This function doesn't do
/// floating point evaluation.
fn hypergeometric_1f1(
  a : Value,
  b : Value,
  x : Value,
  hg_type : Value,
) -> Value raise {
  if use_float_hypergeometric_numerical_eval(list1(a), list1(b), x).truthy() {
    Nil
  } else if (!eq(hg_type, q_polynomial) && great(neg(x), x).truthy()) ||
    (!eq(hg_type, q_polynomial) &&
    integerp(sub(b, a)) &&
    num_lt(sub(b, a), Fix(0L))) {
    mul2(
      take(list1(q_mexpt), [q_d__pcte, x]),
      take(list1(q_p_hypergeometric), [
        take(list1(q_mlist), [sub(b, a)]),
        take(list1(q_mlist), [b]),
        neg(x),
      ]),
    )
  } else {
    Nil
  }
}

///|
/// Convert x to a float; if float fails (say overflow), convert to a big
/// float.
fn safe_float(x : Value) -> Value raise {
  match errset(() => d_float(x)) {
    Some(v) => v
    None => d_bfloat(x)
  }
}

///|
let hyp__floatp_fn : Value = lfunc("floatp", args => lbool(floatp(arg(args, 0))))

///|
/// Coerce x to the number type of z.
fn number_coerce(x : Value, z : Value) -> Value raise {
  if complex_number_p(z, ntypep=q_d_bfloatp).truthy() {
    d_bfloat(x)
  } else if complex_number_p(z, ntypep=hyp__floatp_fn).truthy() {
    safe_float(x)
  } else {
    x
  }
}

///|
/// 2F1(a,b;c, x) -->  gamma(c) gamma(c - a - b) / (gamma(c-a) gamma (c-b))
/// (Chu-Vandermonde identity, A & S 15.1.20) provided real_part(c-a-b) > 0
/// and c # 0,-1,-2, ...
fn hypergeometric_2f1(a : Value, b : Value, c : Value, x : Value) -> Value raise {
  let z = sub(c, add2(a, b))
  if onep1(x).truthy() &&
    complex_number_p(z, ntypep=q_d_numberp).truthy() &&
    eq(t, mgrp(d_realpart(z), Fix(0L))) {
    number_coerce(
      div(
        mul2(take(list1(q_p_gamma), [c]), take(list1(q_p_gamma), [z])),
        mul2(
          take(list1(q_p_gamma), [sub(c, a)]),
          take(list1(q_p_gamma), [sub(c, b)]),
        ),
      ),
      x,
    )
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// (in-package #:bigfloat)
//
// For numerical evaluation of a general hypergeometric function, there
// aren't many alternatives to power series summation. Bigfloat functions
// receive bigfloat arguments and return bigfloat values.

///|
fn bf_0f0_numeric(x : Value) -> Value raise {
  bf_exp(x)
}

///|
fn bf_1f0_numeric(a : Value, x : Value) -> Value raise {
  bf_div(Fix(1L), bf_expt(bf_sub(Fix(1L), x), a))
}

///|
/// `(reduce #'* (mapcar #'(lambda (s) (+ s k)) l))` in the bigfloat package.
fn hyp__bf_shifted_product(l : Value, k : Value) -> Value raise {
  let terms = mapcar(s => bf_add(s, k), l)
  if terms is Nil {
    Fix(1L)
  } else {
    reduce((u, v) => bf_mul(u, v), terms)
  }
}

///|
/// This is DLMF: http://dlmf.nist.gov/15.15#E1 with zo = 1/2. It uses a
/// running error and it sums until three consecutive partial sums have a
/// modified relative difference that is bounded by the machine epsilon.
///
///   ff(a,b,c,x,n) := block([f, f0 : 1, f1 : 1- 2 * b / c,s : 1,k : 1,
///                           cf : a / (1-2/x), z],
///     b : c - 2 * b,
///     z : 1 - 2 / x,
///     while k <= n do (
///       s : s + cf * f1,
///       cf : cf * (a + k) / ((k + 1) * z),
///       f : (k * f0 + b * f1)/(k+c),
///       f0 : f1,
///       f1 : f,
///       k : k + 1),
///     s / (1-x/2)^a)$
fn bf_2f1_numeric_alt(
  a : Value,
  b : Value,
  c : Value,
  x : Value,
) -> (Value, Value) raise {
  let mut f : Value = Nil
  let mut f0 : Value = Fix(1L)
  let mut f1 = bf_sub(Fix(1L), bf_div(bf_mul(Fix(2L), b), c))
  let mut s : Value = Fix(1L)
  let mut ds : Value = Fix(1L)
  let mut k : Value = Fix(1L)
  let mut cf = bf_div(a, bf_sub(Fix(1L), bf_div(Fix(2L), x)))
  let mut se : Value = Fix(0L)
  let eps = bf_epsilon(x)
  let mut done = 0
  let b = bf_sub(c, bf_mul(Fix(2L), b))
  let z = bf_sub(Fix(1L), bf_div(Fix(2L), x))
  ignore(ds)
  while done < 3 {
    ds = bf_mul(cf, f1)
    s = bf_add(s, ds)
    done = if bf_lt(bf_abs(ds), bf_mul(eps, bf_max(Fix(1L), list1(bf_abs(s))))) {
      done + 1
    } else {
      0
    }
    se = bf_op_plus(list3(se, bf_abs(s), bf_abs(ds)))
    cf = bf_div(bf_mul(cf, bf_add(a, k)), bf_mul(bf_add(Fix(1L), k), z))
    f = bf_div(bf_add(bf_mul(k, f0), bf_mul(b, f1)), bf_add(k, c))
    f0 = f1
    f1 = f
    k = bf_add(k, Fix(1L))
  }
  (
    bf_div(s, bf_expt(bf_sub(Fix(1L), bf_div(x, Fix(2L))), a)),
    bf_mul(se, bf_epsilon(x)),
  )
}

///|
/// The general case of 2f1-numeric: transform with abramowitz_id and
/// evaluate with nfloat (binding multiple_value_return to true).
fn hyp__2f1_numeric_abramowitz(
  ma : Value,
  mb : Value,
  mc : Value,
  mx : Value,
  digits : Value,
  region0 : Value,
  d0 : Array[(Value, Value)],
) -> (Value, Value) raise {
  let bmv = bind(q_d_multiple_value_return, t)
  defer unbind(bmv)
  // It's really important to use the verb for here because that's what
  // abramowitz_id is looking for.
  let ff = list([
    list2(q_p_hypergeometric, q_simp),
    list3(list2(q_mlist, q_simp), ma, mb),
    list2(list2(q_mlist, q_simp), mc),
    q_z,
  ])
  let mut f : Value = Nil
  let mut region = region0
  let mut di = 0
  while di < d0.length() {
    f = if equal(region, Str("none")) {
      list3(list1(q_d_multiple_values), ff, t)
    } else {
      mfuncall(q_d_abramowitz_id, list2(ff, region))
    }
    if hyp__mnth(f, 2, q_d_second).truthy() {
      di = d0.length()
      f = d_first(f)
    } else {
      region = d0[di].0
      di += 1
    }
  }
  let (f1, f2) = nfloat(
    f,
    list2(list1(q_mlist), list3(list1(q_mequal), q_z, mx)),
    digits,
    symval(q_d_max_fpprec),
  )
  (bf_to(f1), bf_to(f2))
}

///|
/// hypergeometric([ma,mb],[mc],mx); prefix m means Maxima expression.
fn bf_2f1_numeric(
  ma : Value,
  mb : Value,
  mc : Value,
  mx : Value,
  digits : Value,
) -> (Value, Value) raise {
  let mut local_fpprec = digits
  let x = bf_to(mx)
  let d0 : Array[(Value, Value)] = [
    (Str("none"), bf_abs(x)), // region I, inside unit disk
    (
      Str("15.3.4"),
      if bf_eq(x, Fix(1L)) {
        Nil
      } else {
        bf_abs(bf_div(x, bf_sub(x, Fix(1L))))
      },
    ),
    (Str("15.3.6"), bf_abs(bf_sub(Fix(1L), x))),
    (
      Str("15.3.7"),
      if bf_zerop(x) {
        Nil
      } else {
        bf_abs(bf_div(Fix(1L), x))
      },
    ),
    (
      Str("15.3.8"),
      if bf_eq(x, Fix(1L)) {
        Nil
      } else {
        bf_abs(bf_div(Fix(1L), bf_sub(Fix(1L), x)))
      },
    ),
    (
      Str("15.3.9"),
      if bf_zerop(x) {
        Nil
      } else {
        bf_abs(bf_sub(Fix(1L), bf_div(Fix(1L), x)))
      },
    ),
  ]
  let d : Array[(Value, Value)] = d0.filter(s => s.1.truthy())
  // Sort d from least to greatest magnitude (stable).
  for i in 1..<d.length() {
    let mut j = i
    while j > 0 && bf_lt(d[j].1, d[j - 1].1) {
      let tmp = d[j]
      d[j] = d[j - 1]
      d[j - 1] = tmp
      j -= 1
    }
  }
  let region = d[0].0
  if bf_zerop(x) {
    // When x = 0, return 1.
    (Fix(1L), Nil)
  } else if bf_gt(d[0].1, Flo(0.9)) {
    // Use the alternative numerical method when |x| > 0.9; this happens
    // when x is near exp(+/- %i %pi / 3).
    let eps = bf_epsilon(bf_to(mx))
    let mut er : Value = Fix(1L)
    let mut f : Value = Fix(1L)
    while bf_gt(bf_abs(er), bf_mul(eps, bf_max(bf_abs(f), list1(Fix(1L))))) {
      hyp__bind_fpprec(local_fpprec, () => {
        let mlist0 = list1(list1(q_mlist))
        let mmax = symval(q_d_max_fpprec)
        let mma = nfloat(ma, mlist0, local_fpprec, mmax).0
        let mmb = nfloat(mb, mlist0, local_fpprec, mmax).0
        let mmc = nfloat(mc, mlist0, local_fpprec, mmax).0
        let mmx = nfloat(mx, mlist0, local_fpprec, mmax).0
        let (f1, er1) = bf_2f1_numeric_alt(
          bf_to(mma),
          bf_to(mmb),
          bf_to(mmc),
          bf_to(mmx),
        )
        f = f1
        er = er1
        local_fpprec = num_mul(Fix(2L), local_fpprec)
      })
    }
    (f, er)
  } else if equal(region, Str("none")) ||
    (integerp(ma) && num_le(ma, Fix(0L))) ||
    (integerp(mb) && num_le(mb, Fix(0L))) ||
    bf_lt(bf_abs(x), Flo(0.5)) {
    // ma or mb negative integers--that causes trouble for most of the A&S
    // 15.3.4--15.3.9 transformations--let's quickly dispatch
    // hypergeometric-float-eval; also dispatch hypergeometric-float-eval
    // when the transformation is "none" (with adjust-parameters false).
    bf_hypergeometric_float_eval(
      list2(ma, mb),
      list1(mc),
      mx,
      digits,
      adjust_params=Nil,
    )
  } else if integerp(ma) && integerp(mb) && integerp(mc) {
    // The case of a,b, and c integers causes trouble; let's dispatch hgfred
    // on it.
    let mut f = d_hgfred(
      take(list1(q_mlist), [ma, mb]),
      take(list1(q_mlist), [mc]),
      q_z,
    )
    f = d_horner(f, list1(q_z))
    let (f1, dd) = nfloat(
      f,
      list2(list1(q_mlist), list3(list1(q_mequal), q_z, mx)),
      digits,
      symval(q_d_max_fpprec),
    )
    (bf_bigfloat(f1), bf_bigfloat(dd))
  } else {
    hyp__2f1_numeric_abramowitz(ma, mb, mc, mx, digits, region, d)
  }
}

///|
/// Let a = (a1, a2, ..., am) and b = (b1, b2, ..., bn). Approximate
/// sum(c(k) x^k / k!,k,1,inf), where c(k + 1) / c(k) = (a1 + k) (a2 + k)
/// ... (am + k) / (b1 + k) (b2 + k) ... (bn + k).
fn bf_hypergeometric_by_series(
  a : Value,
  b : Value,
  x : Value,
) -> (Value, Value) raise {
  // es = running error for e and ez running error for z.
  let mut s : Value = Fix(0L)
  let mut s0 : Value = Fix(1L)
  let mut k : Value = Fix(0L)
  let mut z : Value = Fix(1L)
  let mut es : Value = Fix(0L)
  let mut ez : Value = Fix(1L)
  let stop : Value = Fix(20000L)
  let n = bf_mul(Fix(2L), bf_op_plus(list3(int(length(a)), int(length(b)), Fix(1L))))
  while bf_lt(k, stop) && !bf_eq(s, s0) {
    s = s0
    let p = hyp__bf_shifted_product(a, k) // p adds and p-1 multiplications
    let q = hyp__bf_shifted_product(b, k) // q adds and q-1 multiplications
    k = bf_add(k, Fix(1L))
    let r = bf_div(bf_mul(p, x), bf_mul(q, k))
    z = bf_mul(z, r)
    ez = bf_add(bf_mul(bf_abs(r), ez), bf_mul(bf_abs(z), n))
    s0 = bf_add(s, z)
    es = bf_op_plus(list3(es, ez, bf_abs(s0)))
  }
  if bf_ge(k, stop) {
    (Nil, Nil)
  } else {
    // estimate number of correct digits:
    let dig = bf_floor(
      bf_mul(
        bf_sub(
          bf_log(bf_max(bf_abs(s), list1(bf_epsilon(x)))),
          bf_log(bf_mul(es, bf_epsilon(x))),
        ),
        Flo(hyp__log10_2_single().to_double()),
      ),
    ).0
    (s, dig)
  }
}

///|
fn bf_hypergeometric_poly_case(a : Value, b : Value, x : Value) -> Value raise {
  let mut z : Value = Fix(1L)
  let mut s : Value = Fix(1L)
  let mut k : Value = Fix(0L)
  while !bf_zerop(z) {
    let p = hyp__bf_shifted_product(a, k)
    let q = hyp__bf_shifted_product(b, k)
    k = bf_add(k, Fix(1L))
    z = bf_div(bf_op_star(list3(p, x, z)), bf_mul(q, k))
    s = bf_add(z, s)
  }
  s
}

///|
/// This function numerically evaluates pFq([a1,...,ap], [b1,....bq], x),
/// where all the arguments are Maxima expressions, not bigfloat objects.
fn bf_hypergeometric_float_eval(
  ma : Value,
  mb : Value,
  mx : Value,
  digits : Value,
  adjust_params? : Value = t,
) -> (Value, Value) raise {
  let a_len = length(ma)
  let b_len = length(mb)
  let mut f : Value = Nil
  let mut local_fpprec = symval(q_d_fpprec)
  let mut d : Value = Nil
  let mut a = mapcar(s => bf_to(s), ma)
  let mut b = mapcar(s => bf_to(s), mb)
  let mut x = bf_to(mx)

  // Special case 0f0, 1f0, 2f1 for |x| > 1, and pfq for |x| > 1 and
  // p >= q + 1. For a general hypergeometric, I don't know how to
  // analytically continue, so in the last case, return false.
  //
  // In the general case, sum the hypergeometric series using a running
  // error, recursing on local-fpprec; bailout when local-fpprec exceeds
  // max_fpprec.
  if a_len == 0 && b_len == 0 {
    // special case 0f0
    (bf_0f0_numeric(x), digits)
  } else if a_len == 1 && b_len == 0 {
    // special case 1f0
    (bf_1f0_numeric(first(a), x), digits)
  } else if a_len == 1 &&
    integerp(first(a)) &&
    num_lt(first(a), Fix(0L)) &&
    b_len == 1 {
    // special case 1f1
    hyp__bind_fpprec(local_fpprec, () => bf_1f1_downward_recursion(
      first(a),
      first(b),
      x,
    ))
  } else if adjust_params.truthy() &&
    a_len == 1 &&
    b_len == 1 &&
    bf_lt(bf_realpart(x), Fix(0L)) {
    // Optionally do Kummer transformation. The adjust-params argument
    // prevents an infinite loop (transform --> untransform ...).
    let (f1, d1) = bf_hypergeometric_float_eval(
      list1(sub(car(mb), car(ma))),
      mb,
      neg(mx),
      digits,
      adjust_params=Nil,
    )
    (bf_mul(bf_exp(x), f1), d1)
  } else if a_len == 2 && b_len == 1 && adjust_params.truthy() {
    // analytic continuation for 2f1;
    bf_2f1_numeric(car(ma), cadr(ma), car(mb), mx, digits)
  } else if a_len < b_len + 1 ||
    bf_in_unit_circle_p(x).truthy() ||
    eq(q_polynomial, classify_hypergeometric(ma, mb, mx)) {
    // recurse on local-fpprec; bailout when local-fpprec exceeds
    // $max_fpprec.
    while (f is Nil || bf_lt(d, digits)) &&
      bf_lt(local_fpprec, symval(q_d_max_fpprec)) {
      hyp__bind_fpprec(local_fpprec, () => {
        let (f1, d1) = bf_hypergeometric_by_series(a, b, x)
        f = f1
        d = d1
        a = mapcar(s => bf_to(d_bfloat(s)), ma)
        b = mapcar(s => bf_to(d_bfloat(s)), mb)
        x = bf_to(d_bfloat(mx))
        local_fpprec = bf_mul(Fix(2L), local_fpprec)
      })
    }
    if f is Nil || bf_lt(d, digits) {
      mtell(list1(Str("Exceeded maximum allowed fpprec.~%"))) |> ignore
      (Nil, Nil)
    } else {
      (f, d)
    }
  } else {
    (Nil, Nil)
  }
}

///|
fn bf_in_unit_circle_p(x : Value) -> Value raise {
  lbool(bf_lt(bf_abs(x), Fix(1L)))
}

///|
/// Compute f11(a,b,x) using downward recursion (A&S 13.4.1). The first
/// argument must be a negative integer:
///
///    f <-- (k * fo + (2 * k + x) * fm1)/(b-k)
fn bf_1f1_downward_recursion(
  a : Value,
  b : Value,
  x : Value,
) -> (Value, Value) raise {
  let mut fo : Value = Fix(1L)
  let mut fm1 = bf_sub(Fix(1L), bf_div(x, b))
  let mut k : Int64 = -1L
  let mut efo : Value = Fix(0L)
  let mut efm1 : Value = Fix(0L)
  if eql(a, Fix(0L)) {
    (fo, Fix(0L))
  } else if eql(a, Fix(-1L)) {
    (fm1, Fix(0L))
  } else {
    let x = bf_sub(x, b)
    while bf_ge(Fix(k), a) {
      let kk : Value = Fix(k)
      let f = bf_div(
        bf_sub(bf_mul(kk, fo), bf_mul(bf_add(bf_mul(Fix(2L), kk), x), fm1)),
        bf_sub(b, kk),
      )
      let ef = bf_add(
        bf_div(
          bf_op_plus(
            list([
              bf_mul(kk, efo),
              bf_op_star(list1(bf_abs(bf_add(bf_mul(Fix(2L), kk), x)))),
              bf_add(efm1, bf_mul(Fix(2L), fm1)),
              bf_mul(kk, fo),
            ]),
          ),
          bf_abs(bf_sub(b, kk)),
        ),
        bf_mul(Fix(3L), bf_abs(f)),
      )
      fo = fm1
      efo = efm1
      fm1 = f
      efm1 = ef
      k = k - 1L
    }
    (fo, efo)
  }
}

// ---------------------------------------------------------------------------
// (in-package :maxima)

///|
fn float_or_bigfloat_p(x : Value) -> Value raise {
  if floatp(x) {
    t
  } else {
    d_bfloatp(x)
  }
}

///|
/// Return true iff it is possible to evaluate hypergeometric(a,b,x) using
/// (exact) rational arithmetic. Thus (1) x and every member of a and b
/// (Common Lisp lists) must be a $ratnump and (2) some member of a must be
/// an explicit negative integer.
fn use_rational_hypergeometric_numerical_eval(
  a : Value,
  b : Value,
  x : Value,
) -> Value raise {
  lbool(
    !symval(q_d_numer).truthy() &&
    complex_number_p(x, ntypep=q_d_ratnump).truthy() &&
    every(s => complex_number_p(s, ntypep=q_d_ratnump).truthy(), a) &&
    every(s => complex_number_p(s, ntypep=q_d_ratnump).truthy(), b) &&
    some(s => integerp(s) && num_lt(s, Fix(0L)), a),
  )
}

///|
/// Evaluate hypergeometric(a,b,x) using (exact) rational arithmetic. Here a
/// and b are Common Lisp lists. These are all polynomial cases, so we don't
/// need any analytic continuations.
fn rational_hypergeometric_numerical_eval(
  a : Value,
  b : Value,
  x : Value,
) -> Value raise {
  let a = mapcar(s => bf_to(s), a)
  let b = mapcar(s => bf_to(s), b)
  let x = bf_to(x)
  maxima_to(bf_hypergeometric_poly_case(a, b, x))
}

///|
/// Return float if hypergeometric(a,b,x) should evaluate to a double float
/// (real or complex); return bigfloat if it should evaluate to a bigfloat
/// (real or complex); otherwise return false.
///
/// When $numer is true, everybody must be a $numberp for numerical
/// evaluation; when numer is false, everybody must be a $numberp and
/// somebody must be a float.
fn use_float_hypergeometric_numerical_eval(
  a : Value,
  b : Value,
  x : Value,
) -> Value raise {
  if every(s => complex_number_p(s, ntypep=q_d_numberp).truthy(), a) &&
    every(s => complex_number_p(s, ntypep=q_d_numberp).truthy(), b) &&
    complex_number_p(x, ntypep=q_d_numberp).truthy() &&
    (symval(q_d_numer).truthy() ||
    !every(s => complex_number_p(s, ntypep=q_d_ratnump).truthy(), a) ||
    !every(s => complex_number_p(s, ntypep=q_d_ratnump).truthy(), b) ||
    !complex_number_p(x, ntypep=q_d_ratnump).truthy()) {
    // When everybody is a float or rational, the return type is float;
    // otherwise bigfloat.
    if every(
        s => complex_number_p(s, ntypep=q_float_or_rational_p).truthy(),
        a,
      ) &&
      every(
        s => complex_number_p(s, ntypep=q_float_or_rational_p).truthy(),
        b,
      ) &&
      complex_number_p(x, ntypep=q_float_or_rational_p).truthy() {
      q_float
    } else {
      q_bigfloat
    }
  } else {
    Nil
  }
}

///|
/// Evaluate pFq(a,b,x) using floating point arithmetic. Coerce the returned
/// value to the type described by return-type. When there is a double float
/// overflow, ignore-errors should return nil. After that, we'll try again
/// with a bigfloat.
fn hypergeometric_float_eval(
  a : Value,
  b : Value,
  z : Value,
  digits : Value,
  return_type : Value,
) -> Value raise {
  let (x, d) = hyp__ignore_errors2(() => bf_hypergeometric_float_eval(
    a, b, z, digits,
  ))
  if x is Nil && eq(return_type, q_float) {
    number_coerce(
      hypergeometric_float_eval(
        mapcar(s => d_bfloat(s), a),
        mapcar(s => d_bfloat(s), b),
        d_bfloat(z),
        digits,
        q_bigfloat,
      ),
      Flo(1.0),
    )
  } else if x is Nil || d is Nil {
    Nil
  } else if eq(return_type, q_float) {
    d_float(maxima_to(x))
  } else if eq(return_type, q_bigfloat) {
    d_bfloat(maxima_to(x))
  } else {
    // This should not happen.
    maxima_to(x)
  }
}

///|
fn hypergeometric_poly_case(a : Value, b : Value, x : Value) -> Value raise {
  let mut n : Value = Nil
  let mut z : Value = Fix(1L)
  let mut s : Value = Fix(1L)
  let mut cf : Value = Fix(1L)

  // Determine how many terms to sum
  if d_taylorp(x).truthy() &&
    eql(Fix(0L), hyp__mnth(d_first(d_taylorinfo(x)), 2, q_d_second)) &&
    integerp(hyp__mnth(d_first(d_taylorinfo(x)), 3, q_d_third)) {
    n = hyp__mnth(d_first(d_taylorinfo(x)), 3, q_d_third)
  } else if some(s => integerp(s) && num_le(s, Fix(0L)), a) {
    for ak in a.iter() {
      if integerp(ak) && num_lt(ak, Fix(0L)) {
        n = if n is Nil { ak } else { num_max(n, ak) }
      }
    }
    n = num_neg(n)
  } else {
    n = Nil
  }
  if d_ratp(x).truthy() {
    s = d_rat(Fix(1L), Nil)
    z = d_rat(Fix(1L), Nil)
  }

  // Expand to a polynomial when n is an integer and either
  //  (1) x and each member of a and b are complex numbers,
  //  (2) n < $expop or $expand_hypergeometric
  //  (3) x is a CRE expression.
  if integerp(n) &&
    (
      (complex_number_p(x, ntypep=q_d_numberp).truthy() &&
      every(s => complex_number_p(s, ntypep=q_d_numberp).truthy(), a) &&
      every(s => complex_number_p(s, ntypep=q_d_numberp).truthy(), b)) ||
      (symval(q_d_expand_hypergeometric).truthy() ||
      num_lt(n, symval(q_d_expop))) ||
      d_ratp(x).truthy()
    ) {
    let nn = to_int(n)
    for k in 0..<nn {
      let pl = mapcar(s => add2(s, int(k)), a)
      let p = if pl is Nil { muln_([]) } else { reduce((u, v) => mul2(u, v), pl) }
      let ql = mapcar(s => add2(s, int(k)), b)
      let q = if ql is Nil { muln_([]) } else { reduce((u, v) => mul2(u, v), ql) }

      // Maxima should (I think) return a rectangular form for complex
      // number multiplication and division. But it doesn't.
      cf = mul2(cf, div(p, mul2(q, int(k + 1))))
      if d_constantp(cf).truthy() {
        cf = d_rectform(cf)
      }
      z = mul2(z, x)
      s = add2(s, mul2(cf, z))
    }
    s
  } else {
    Nil
  }
}

///|
fn diff_hypergeometric(a : Value, b : Value, z : Value, x : Value) -> Value raise {
  if d_freeof(list2(x, a)).truthy() && d_freeof(list2(x, b)).truthy() {
    let a = margs(a)
    let b = margs(b)
    let p = if a is Nil { muln_([]) } else { reduce((u, v) => mul2(u, v), a) }
    let q = if b is Nil { muln_([]) } else { reduce((u, v) => mul2(u, v), b) }
    let a = simplify(cons(list1(q_mlist), mapcar(s => add2(Fix(1L), s), a)))
    let b = simplify(cons(list1(q_mlist), mapcar(s => add2(Fix(1L), s), b)))
    muln_([
      d_diff(list2(z, x)),
      p,
      div(Fix(1L), q),
      take(list1(q_p_hypergeometric), [a, b, z]),
    ])
  } else {
    merr(
      "Maxima does not know the derivatives of the hypergeometric functions with respect to the parameters",
      [],
    )
  }
}

///|
/// TeX hypergeometric([a],[b,c],x) as
/// $$F\left( \begin{bmatrix}a\\b\;\,c\end{bmatrix} ,x\right)$$
fn tex_hypergeometric(x : Value, l : Value, r : Value) -> Value raise {
  let wide_space : Value = Str(",\\;")
  let p = tex_list(margs(cadr(x)), Nil, Nil, wide_space)
  let q = tex_list(margs(caddr(x)), Nil, Nil, wide_space)
  let p = append(
    l,
    cons(
      Str("F\\left( \\left. \\begin{array}{c}"),
      append(
        p,
        cons(Str("\\\\"), append(q, list1(Str("\\end{array} \\right |,")))),
      ),
    ),
  )
  tex(fourth(x), p, cons(Str("\\right)"), r), q_mparen, q_mparen)
}

///|
/// Integral of hypergeometric(a,b,z) wrt z
///
/// Integrals and Series: Volume 3, More Special Functions
/// Prudnikov, A. P., Brychkov, Yu A., Gould, G. G., Marichev, O.I.
///
///   integrate(pFq((a_p);(b_q);c z), z)
///     = z (p+1)F(q+1)((a_p),1;(b_q),2;c z)                 1.16.1.2
///
///        product((b_q - 1))
///     =  ------------------ pFq((a_p)-1; (b_q)-1; c z)     1.16.1.3
///        product((a_p - 1))
fn hyp_integral_3(a : Value, b : Value, z : Value) -> Value raise {
  with_special(q_d_listarith, t, () => {
    let a_1 = add2(a, Fix(-1L))
    let b_1 = add2(b, Fix(-1L))
    let lb = margs(b_1)
    let prod_b_1 = if lb is Nil {
      muln_([])
    } else {
      reduce((u, v) => mul2(u, v), lb)
    }
    let la = margs(a_1)
    let prod_a_1 = if la is Nil {
      muln_([])
    } else {
      reduce((u, v) => mul2(u, v), la)
    }
    if eql(prod_a_1, Fix(0L)) {
      mul2(
        z,
        take(list1(q_p_hypergeometric), [
          append(a, list1(Fix(1L))),
          append(b, list1(Fix(2L))),
          z,
        ]),
      )
    } else {
      mul3(
        prod_b_1,
        inv(prod_a_1),
        take(list1(q_p_hypergeometric), [a_1, b_1, z]),
      )
    }
  })
}

///|
fn init_hypergeometric() -> Unit raise {
  putprop(
    q_d_max_fpprec,
    lfunc("max_fpprec-assign", args => {
      let b = arg(args, 1)
      if !(atom(b) && integerp(b)) {
        mtell(list1(Str("The value of `max_fpprec' must be an integer.~%")))
        |> ignore
        q_munbindp
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
  putprop(
    q_d_expand_hypergeometric,
    lfunc("expand_hypergeometric-assign", args => {
      let b = arg(args, 1)
      if !(eq(b, Nil) || eq(b, t)) {
        mtell(
          list1(
            Str(
              "The value of `expand_hypergeometric' must be either true or false.~%",
            ),
          ),
        )
        |> ignore
        q_munbindp
      } else {
        Nil
      }
    }),
    q_assign,
  )
  |> ignore
  putprop(q_d_multiple_values, q_simp_multiple_values, q_operators) |> ignore

  // We don't want realpart and imagpart to think that hypergeometric
  // functions are real valued. So declare hypergeometric to be complex.
  with_specials([(q_d_context, q_d_global), (q_context, q_d_global)], () => {
    meval(mk(q_d_declare, [q_p_hypergeometric, q_d_complex]))
  })
  |> ignore
  putprop(q_p_hypergeometric, q_conjugate_hypergeometric, q_conjugate_function)
  |> ignore
  putprop(q_p_hypergeometric, q_tex_hypergeometric, q_tex) |> ignore
  putprop(
    q_p_hypergeometric,
    list([list3(q_a, q_b, q_z), Nil, Nil, q_hyp_integral_3]),
    q_integral,
  )
  |> ignore
}
