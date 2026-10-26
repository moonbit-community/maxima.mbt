// Port of share/fourier_elim/fourier_elim.lisp (Barton Willis, 2007, 2008,
// 2021): Fourier elimination for systems of linear inequalities, and the
// standardization of (some) nonlinear inequalities.
//
// CL fourier_elim loads to_poly (for the macro OPAPPLY and the functions
// MAX-TO-ABS, MIN-TO-ABS and $ELIM). The two-line macro and the two
// one-line functions are used through private copies below; $elim is
// called through its function cell, so it is available exactly when
// to_poly has been loaded.

///|
/// (opapply op args) = (simplify (cons (list op) args)), from to_poly.lisp.
fn share_fourier_elim__opapply(op : Value, args : Value) -> Value raise {
  simplify(cons(list1(op), args))
}

///|
/// MAX-TO-ABS of to_poly.lisp.
fn share_fourier_elim__max_to_abs(e : Value) -> Value raise {
  reduce(
    (a, b) => div(
      add(list2(add(list2(a, b)), take(list1(q_mabs), [sub(a, b)]))),
      Fix(2L),
    ),
    e,
  )
}

///|
/// MIN-TO-ABS of to_poly.lisp.
fn share_fourier_elim__min_to_abs(e : Value) -> Value raise {
  reduce(
    (a, b) => div(
      sub(add(list2(a, b)), take(list1(q_mabs), [sub(a, b)])),
      Fix(2L),
    ),
    e,
  )
}

///|
/// `(bind-fpprec val body...)`
fn[T] share_fourier_elim__bind_fpprec(
  val : Value,
  f : () -> T raise,
) -> T raise {
  with_specials(
    [
      (q_fpprec, Nil),
      (q_ear_bigfloatzero, Nil),
      (q_ear_bigfloatone, Nil),
      (q_ear_bfhalf, Nil),
      (q_ear_bfmhalf, Nil),
    ],
    () => with_special(q_d_fpprec, fpprec1(Nil, val), f),
  )
}

///|
/// The pattern
///   (let ((save-context $context) (new-context (gensym)))
///     (unwind-protect (progn [($newcontext new-context)] body)
///       (if ($member new-context $contexts) ($killcontext new-context))
///       (setq $context save-context)))
fn share_fourier_elim__with_context(
  make_new : Bool,
  f : () -> Value raise,
) -> Value raise {
  let save_context = symval(q_d_context)
  let new_context = gensym()
  let cleanup = fn() raise {
    if d_member(new_context, symval(q_d_contexts)).truthy() {
      d_killcontext(list1(new_context)) |> ignore
    }
    set(q_d_context, save_context) |> ignore
  }
  let r = (fn() raise {
    if make_new {
      d_newcontext(list1(new_context)) |> ignore
    }
    f()
  })() catch {
    e => {
      cleanup()
      raise e
    }
  }
  cleanup()
  r
}

///|
fn share_fourier_elim__is_str(v : Value, ss : Array[String]) -> Bool {
  match v {
    Str(s) => ss.contains(s)
    _ => false
  }
}

///|
/// Maybe I should use csign instead of these functions...
fn number_sign(x : Value) -> Value raise {
  if integerp(x) || floatp(x) {
    if num_lt(x, Fix(0L)) {
      q_d_neg
    } else if num_eq(x, Fix(0L)) {
      q_d_zero
    } else if num_gt(x, Fix(0L)) {
      q_d_pos
    } else {
      Nil
    }
  } else if d_ratnump(x).truthy() {
    number_sign(d_num(x))
  } else if d_bfloatp(x).truthy() {
    number_sign(cadr(x))
  } else if eq(q_d_minf, x) {
    q_d_neg
  } else if eq(x, q_d_inf) ||
    eq(x, q_d__pctpi) ||
    eq(x, q_d__pcte) ||
    eq(x, q_d__pctphi) {
    q_d_pos
  } else if eq(x, q_d__pcti) || eq(x, q_d_infinity) {
    q_d_complex
  } else if d_constantp(x).truthy() {
    constant_expression_sign(x)
  } else {
    Nil
  }
}

///|
/// Evaluate with 25, 50, and 75 digits. Provided all three agree, and
/// |f3| > 2^-50, return the common sign.
fn constant_expression_sign(x : Value) -> Value raise {
  let f1 = share_fourier_elim__bind_fpprec(Fix(25L), () => d_bfloat(x))
  let f2 = share_fourier_elim__bind_fpprec(Fix(50L), () => d_bfloat(x))
  let f3 = share_fourier_elim__bind_fpprec(Fix(75L), () => d_bfloat(x))
  if d_bfloatp(f1).truthy() &&
    d_bfloatp(f2).truthy() &&
    d_bfloatp(f3).truthy() &&
    eq(number_sign(f1), number_sign(f2)) &&
    eq(number_sign(f2), number_sign(f3)) &&
    num_gt(car(last(f3)), Fix(-50L)) {
    number_sign(f1)
  } else {
    Nil
  }
}

///|
/// This isn't exactly the same as CARTESIAN-PRODUCT in src/nset.lisp.
fn fourier_elim_cartesian_product(b : Value) -> Value raise {
  if b is Nil {
    return Nil
  }
  let mut acc = mapcar(x => list1(x), car(b))
  for bi in cdr(b).iter() {
    let mut a : Value = Nil
    for bij in bi.iter() {
      let acc0 = acc
      a = append(a, mapcar(x => append(x, list1(bij)), acc0))
    }
    acc = a
  }
  acc
}

///|
fn expand_and_over_or(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    e
  } else if op_equalp(e, list1(q_mand)).truthy() {
    let mut e = mapcar(
      s => if op_equalp(s, list1(q_mor)).truthy() { margs(s) } else { list1(s) },
      margs(e),
    )
    e = fourier_elim_cartesian_product(e)
    e = mapcar(s => share_fourier_elim__opapply(q_mand, s), e)
    share_fourier_elim__opapply(q_mor, e)
  } else {
    share_fourier_elim__opapply(
      mop(e),
      mapcar(s => expand_and_over_or(s), margs(e)),
    )
  }
}

///|
fn make_positive_product(l : Value) -> Value raise {
  let n = length(l)
  let m = 1 << n
  let mut acc : Value = Nil
  for i in 0..<m {
    if logcount(int(i)) % 2 == 0 {
      let mut p : Value = Nil
      let mut k = 0
      for li in l.iter() {
        p = cons(
          if logbitp(k, int(i)) {
            fe_gt(Fix(0L), li, expand=Nil)
          } else {
            fe_gt(li, Fix(0L), expand=Nil)
          },
          p,
        )
        k += 1
      }
      p = share_fourier_elim__opapply(q_mand, p)
      acc = cons(p, acc)
    }
  }
  share_fourier_elim__opapply(q_mor, acc)
}

///|
fn in_real_domain(e : Value) -> Value raise {
  if eq(e, q_d__pcti) {
    Nil
  } else if d_mapatom(e).truthy() {
    t
  } else if op_equalp(
      e,
      list([
        q_mplus,
        q_mtimes,
        q_p_atan,
        q_p_cos,
        q_p_sin,
        q_p_cosh,
        q_p_sinh,
        q_p_asinh,
      ]),
    ).truthy() {
    share_fourier_elim__opapply(q_mand, mapcar(s => in_real_domain(s), margs(e)))
  } else if op_equalp(e, list2(q_p_acos, q_p_asin)).truthy() {
    let e = car(margs(e))
    share_fourier_elim__opapply(
      q_mand,
      list2(fe_gt_eq(e, Fix(-1L)), fe_gt_eq(Fix(1L), e)),
    )
  } else if op_equalp(e, list1(q_p_log)).truthy() {
    fe_gt(car(margs(e)), Fix(0L))
  } else if op_equalp(e, list1(q_p_acosh)).truthy() {
    fe_gt_eq(car(margs(e)), Fix(1L))
  } else if op_equalp(e, list1(q_mexpt)).truthy() {
    let x = car(margs(e))
    let n = cadr(margs(e))
    if share_fourier_elim__is_str(d_compare(n, Fix(0L)), ["<", "<="]) {
      take(list1(q_mand), [m_neq(x, Fix(0L)), in_real_domain(x), in_real_domain(n)])
    } else {
      take(list1(q_mand), [m_neq(x, Fix(0L)), in_real_domain(x), in_real_domain(n)])
    }
  } else {
    m_eq(e, take(list1(q_d_conjugate), [e]))
  }
}

///|
fn freeof_floats(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    lbool(!(floatp(e) || d_bfloatp(e).truthy()))
  } else {
    lbool(every(s => freeof_floats(s).truthy(), margs(ratdisrep(e))))
  }
}

///|
/// Splitify an expression; this does e -> ((e1, boolean) (e2, boolean), ...).
/// Examples:
///   x -->  ((x t)),
///   |x| --> ((-x, x < 0) (x, x >= 0)),
///   max(a,b) --> ((a, a > b) (b, b >= a)),
///   a + |b| --> ((a-b, b < 0) (a + b, b >= 0)).
fn d_splitify(e : Value) -> Value raise {
  cons(list1(q_mlist), mapcar(s => cons(list1(q_mlist), s), splitify(e)))
}

///|
fn splitify(e : Value) -> Value raise {
  if d_mapatom(e).truthy() {
    list1(list2(e, t))
  } else if op_equalp(e, list1(q_d_max)).truthy() {
    splitify(share_fourier_elim__max_to_abs(margs(e)))
  } else if op_equalp(e, list1(q_d_min)).truthy() {
    splitify(share_fourier_elim__min_to_abs(margs(e)))
  } else if op_equalp(e, list1(q_mabs)).truthy() {
    let e = car(margs(e))
    list2(list2(neg(e), fe_gt(Fix(0L), e)), list2(e, fe_gt_eq(e, Fix(0L))))
  } else if op_equalp(e, list1(q_mexpt)).truthy() {
    mapcar(
      s => list2(take(list1(q_mexpt), [car(s), caddr(e)]), cadr(s)),
      splitify(cadr(e)),
    )
  } else if op_equalp(e, list2(q_mplus, q_mtimes)).truthy() {
    let is_plus = op_equalp(e, list1(q_mplus)).truthy()
    let f = fn(a : Value, b : Value) raise {
      if is_plus {
        add(list2(a, b))
      } else {
        mult(a, b)
      }
    }
    let es = fourier_elim_cartesian_product(mapcar(s => splitify(s), margs(e)))
    let mut acc : Value = Nil
    for ek in es.iter() {
      acc = cons(
        reduce(
          (a, b) => list2(
            f(car(a), car(b)),
            take(list1(q_mand), [cadr(a), cadr(b)]),
          ),
          ek,
        ),
        acc,
      )
    }
    acc
  } else {
    list1(list2(e, t))
  }
}

///|
fn fe_gt(
  a : Value,
  b : Value,
  expand? : Value = Nil,
  use_splitify? : Value = t,
) -> Value raise {
  let mut a = d_ratdisrep(a)
  let mut b = d_ratdisrep(b)
  // This uses p / q > 0 == q^2 * (p / q) > 0 == p * q > 0. Skip the
  // p / q > 0 --> p * q > 0 transformation when z contains a floating
  // point number.
  let mut z = sub(a, b)
  z = if freeof_floats(z).truthy() {
    d_factor(mul2(d_num(z), d_denom(z)))
  } else {
    z
  }
  let sgn = compare_using_empty_context(a, b)
  let mmm = list3(q_mabs, q_d_min, q_d_max)
  if share_fourier_elim__is_str(sgn, [">"]) {
    t
  } else if share_fourier_elim__is_str(sgn, ["<", "<=", "="]) {
    Nil
  } else if op_equalp(a, list1(q_mabs)).truthy() &&
    d_freeof(append(mmm, list1(b))).truthy() {
    // First, |a| > b --> (b < 0) or (a > b, b >= 0) or (-a > b, b >= 0).
    a = car(margs(a))
    share_fourier_elim__opapply(
      q_mor,
      list3(
        share_fourier_elim__opapply(q_mand, list1(fe_gt(Fix(0L), b))),
        share_fourier_elim__opapply(
          q_mand,
          list2(fe_gt_eq(b, Fix(0L)), fe_gt(a, b)),
        ),
        share_fourier_elim__opapply(
          q_mand,
          list2(fe_gt_eq(b, Fix(0L)), fe_gt(neg(a), b)),
        ),
      ),
    )
  } else if op_equalp(b, list1(q_mabs)).truthy() &&
    d_freeof(append(mmm, list1(a))).truthy() {
    // Second, a > |b| == a > b and  a > -b.
    b = car(margs(b))
    share_fourier_elim__opapply(q_mand, list2(fe_gt(a, b), fe_gt(a, neg(b))))
  } else if op_equalp(a, list1(q_d_min)).truthy() &&
    d_freeof(append(mmm, list1(b))).truthy() {
    // Third, min(a1,a2,..., an) > b --> a1 > b and a2 > b and .. an > b.
    share_fourier_elim__opapply(q_mand, mapcar(s => fe_gt(s, b), margs(a)))
  } else if op_equalp(b, list1(q_d_max)).truthy() &&
    d_freeof(append(mmm, list1(a))).truthy() {
    // Fourth, a > max(b1,b2, ..., bn) --> a > b1 and ... and a > bn.
    share_fourier_elim__opapply(q_mand, mapcar(s => fe_gt(a, s), margs(b)))
  } else if op_equalp(z, list1(q_mexpt)).truthy() && integerp(caddr(z)) {
    // Do z^n > 0 --> z # 0  n even,  z > 0, n odd.
    if even(caddr(z)).truthy() {
      m_neq(cadr(z), Fix(0L))
    } else {
      fe_gt(cadr(z), Fix(0L))
    }
  } else if !d_mapatom(a).truthy() &&
    !d_mapatom(b).truthy() &&
    eq(mop(a), mop(b)) &&
    d_featurep(mop(a), q_d_increasing).truthy() {
    // Do f(a) > f(b), where f is increasing --> a > b.
    share_fourier_elim__opapply(
      q_mand,
      list3(
        fe_gt(car(margs(a)), car(margs(b))),
        in_real_domain(a),
        in_real_domain(b),
      ),
    )
  } else if !d_mapatom(a).truthy() &&
    !d_mapatom(b).truthy() &&
    eq(mop(a), mop(b)) &&
    d_featurep(mop(a), q_d_decreasing).truthy() {
    // Do f(a) > f(b), where f is decreasing --> a < b.
    fe_gt(car(margs(b)), car(margs(a)))
  } else if !d_mapatom(a).truthy() &&
    !d_mapatom(b).truthy() &&
    eq(mop(a), mop(b)) &&
    op_equalp(a, list1(q_mexpt)).truthy() &&
    eql(cadr(a), cadr(b)) &&
    share_fourier_elim__is_str(compare_using_empty_context(cadr(a), Fix(1L)), [
      ">",
    ]) {
    // Do a^x > a^y, where a > 1 --> x > y,
    fe_gt(caddr(a), caddr(b))
  } else if op_equalp(z, list1(q_mtimes)).truthy() && expand.truthy() {
    // Do a * b > 0 --> (a > 0, b > 0) or (a < 0, b < 0).
    make_positive_product(margs(z))
  } else if use_splitify.truthy() &&
    op_equalp(z, list([q_d_max, q_d_min, q_mabs, q_mtimes, q_mplus])).truthy() {
    // Finally, take care of the abs, max, and min cases that the previous
    // four cases miss.
    let z_split = splitify(z)
    let mut acc : Value = Nil
    for zk in z_split.iter() {
      acc = cons(
        cons(
          list1(q_mand),
          cons(fe_gt(car(zk), Fix(0L), expand=expand, use_splitify=Nil), cdr(zk)),
        ),
        acc,
      )
    }
    acc = cons(list1(q_mor), acc)
    simplifya(acc, Nil)
  } else {
    share_fourier_elim__opapply(q_mgreaterp, list2(z, Fix(0L)))
  }
}

///|
fn m_eq(a : Value, b : Value, use_splitify? : Value = t) -> Value raise {
  let mut z = sub(a, b)
  let sgn = compare_using_empty_context(a, b)
  z = if freeof_floats(z).truthy() { d_factor(z) } else { z }
  if share_fourier_elim__is_str(sgn, ["="]) {
    // If compare says a = b, return true.
    t
  } else if share_fourier_elim__is_str(sgn, ["<", ">", "#"]) {
    // If compare says a # b, return false.
    Nil
  } else if complex_number_p(a, ntypep=q_d_numberp).truthy() &&
    complex_number_p(b, ntypep=q_d_numberp).truthy() {
    // For complex numbers, look at the real and imaginary parts.
    take(list1(q_mand), [
      m_eq(d_realpart(a), d_realpart(b)),
      m_eq(d_imagpart(a), d_imagpart(b)),
    ])
  } else if op_equalp(z, list1(q_mexpt)).truthy() && mnump(caddr(z)).truthy() {
    // z^n = 0 --> false if n <= 0 else z = 0.
    let s = number_sign(caddr(z))
    if eq(s, q_d_neg) || eq(s, q_d_zero) {
      Nil
    } else {
      m_eq(cadr(z), Fix(0L))
    }
  } else if !d_mapatom(a).truthy() &&
    !d_mapatom(b).truthy() &&
    eq(mop(a), mop(b)) &&
    d_featurep(mop(a), q_d_one_to_one).truthy() {
    // f(a) = f(b), where f is one-to-one --> a = b.
    share_fourier_elim__opapply(
      q_mand,
      append(
        list2(in_real_domain(a), in_real_domain(b)),
        mapcar2((x, y) => m_eq(x, y), margs(a), margs(b)),
      ),
    )
  } else if op_equalp(z, list1(q_mtimes)).truthy() {
    // a * b  = 0 --> a = 0 or b = 0; also a / b --> a = 0 and b # 0.
    let nz = m_neq(d_ratdenom(z), Fix(0L))
    expand_and_over_or(
      take(list1(q_mand), [
        nz,
        share_fourier_elim__opapply(
          q_mor,
          mapcar(s => m_eq(s, Fix(0L)), margs(z)),
        ),
      ]),
    )
  } else if use_splitify.truthy() &&
    op_equalp(z, list([q_d_max, q_d_min, q_mabs, q_mtimes, q_mplus])).truthy() {
    let z_split = splitify(z)
    let mut acc : Value = Nil
    for zk in z_split.iter() {
      acc = cons(
        cons(list1(q_mand), cons(m_eq(car(zk), Fix(0L), use_splitify=Nil), cdr(zk))),
        acc,
      )
    }
    acc = cons(list1(q_mor), acc)
    expand_and_over_or(simplifya(acc, Nil))
  } else {
    take(list1(q_mequal), [z, Fix(0L)])
  }
}

///|
fn m_neq(a : Value, b : Value) -> Value raise {
  share_fourier_elim__with_context(false, () => {
    let sgn = mnqp(a, b)
    if eq(sgn, t) || sgn is Nil {
      sgn
    } else if eq(symval(q_d_domain), q_d_real) {
      opcons(q_mor, list2(fe_gt(a, b, expand=t), fe_gt(b, a, expand=t)))
    } else {
      take(list1(q_mnot), [m_eq(a, b)])
    }
  })
}

///|
fn fe_gt_eq(a : Value, b : Value) -> Value raise {
  let sgn = compare_using_empty_context(a, b)
  if share_fourier_elim__is_str(sgn, [">=", ">"]) {
    t
  } else if share_fourier_elim__is_str(sgn, ["<"]) {
    Nil
  } else {
    opcons(q_mor, list2(fe_gt(a, b, expand=t), m_eq(a, b)))
  }
}

///|
fn standardize_inequality(e : Value) -> Value raise {
  if op_equalp(e, list1(q_mand)).truthy() {
    share_fourier_elim__opapply(
      q_mand,
      mapcar(s => standardize_inequality(s), margs(e)),
    )
  } else if op_equalp(e, list1(q_mor)).truthy() {
    share_fourier_elim__opapply(
      q_mor,
      mapcar(s => standardize_inequality(s), margs(e)),
    )
  } else if mrelationp(e).truthy() || op_equalp(e, list1(q_d_equal)).truthy() {
    let a = cadr(e)
    let b = caddr(e)
    if op_equalp(e, list1(q_mlessp)).truthy() {
      fe_gt(b, a, expand=t)
    } else if op_equalp(e, list1(q_mleqp)).truthy() {
      opcons(q_mor, list2(fe_gt(b, a, expand=t), m_eq(a, b)))
    } else if op_equalp(e, list2(q_mequal, q_d_equal)).truthy() {
      m_eq(a, b)
    } else if op_equalp(e, list1(q_mgreaterp)).truthy() {
      fe_gt(a, b, expand=t)
    } else if op_equalp(e, list1(q_mgeqp)).truthy() {
      fe_gt_eq(a, b)
    } else if op_equalp(e, list1(q_mnotequal)).truthy() {
      m_neq(a, b)
    } else {
      e
    }
  } else {
    e
  }
}

///|
/// affine_p(p,vars) returns true iff p is an affine polynomial in vars,
/// that is, a polynomial in vars (a list) whose total degree in vars is no
/// greater than 1. (Stavros Macrakis.)
fn d_affine_p(p : Value, vl : Value) -> Value raise {
  let vl = require_list(vl, Str("affine_p"))
  with_specials([(q_d_ratfac, Nil), (q_d_ratprint, Nil)], () => {
    let rat = d_rat(p, Nil)
    // don't handle bags etc.; don't handle taylor series (even in other
    // vars)
    if !(eq(caar(rat), q_mrat) && memq(q_trunc, car(rat)) is Nil) {
      return Nil
    }
    // in affine poly, only numer can include vars
    let num = d_ratnumer(rat)
    let numvars = caddr(car(minimize_varlist(num)))
    // ... and denominator cannot depend on vars at all
    let den = d_ratdenom(rat)
    let denvars = caddr(car(minimize_varlist(den)))
    // everything in denvars must be freeof vl
    if !every(
        term => every(v_ => freeof(v_, term).truthy(), vl),
        denvars,
      ) {
      return Nil
    }
    // everything in numvars must be either in vl or freeof vl
    if !every(
        term => memalike(term, vl).truthy() ||
          every(v_ => freeof(v_, term).truthy(), vl),
        numvars,
      ) {
      return Nil
    }
    // there must be no terms of degree > 1: calculate p without terms of
    // degree > 1 (adding ($rat 0) performs the truncation), ignoring the
    // prevailing *ratweights.
    let truncnum = with_specials(
      [
        (q_d_ratwtlvl, Fix(1L)),
        (q_n_starratweights, mapcar(x => cons(x, Fix(1L)), vl)),
      ],
      () => add(list2(d_rat(Fix(0L), Nil), num)),
    )
    // subtract out: any terms of degree > 1?
    lbool(equal(Fix(0L), ratdisrep(sub(num, truncnum))))
  })
}

///|
fn linear_elimination(l : Value, v : Value) -> Value raise {
  with_specials(
    [
      (q_d_linsolve_params, Nil),
      (q_d_backsubst, t),
      (q_d_programmode, t),
      (q_d_linsolvewarn, Nil),
      (q_d_globalsolve, Nil),
    ],
    () => {
      let l = funcall(q_d_elim, [l, v])
      if d_member(Fix(1L), d_first(l)).truthy() {
        q_d_emptyset
      } else {
        let subs = d_linsolve(funcall(q_d_second, [l]), v)
        let mut vars = mapcar(s => d_lhs(s), margs(subs))
        vars = cons(list1(q_mlist), vars)
        let unsolved = cons(
          list1(q_mlist),
          mapcar(q => take(list1(q_mequal), [q, Fix(0L)]), cdr(d_first(l))),
        )
        simplifya(list4(list1(q_mlist), subs, unsolved, vars), t)
      }
    },
  )
}

///|
fn d_fourier_elim(l : Value, vars : Value) -> Value raise {
  with_specials(
    [(q_d_listconstvars, Nil), (q_d_ratprint, Nil), (q_d_domain, q_d_real)],
    () => {
      let mut eq_list : Value = Nil
      let mut pos_list : Value = Nil
      let mut other_list : Value = Nil
      // Check the arguments
      let mut l = if op_equalp(l, list2(q_mand, q_mlist)).truthy() {
        margs(l)
      } else {
        list1(l)
      }
      require_list_or_set(vars, Str("$fourier_elim")) |> ignore
      // Standardize each inequality and simplify. To simplify, apply
      // 'mand. After that, expand 'and' over 'or.'
      l = share_fourier_elim__opapply(
        q_mand,
        mapcar(s => standardize_inequality(s), l),
      )
      l = expand_and_over_or(l)
      if eq(t, l) {
        q_d_universalset
      } else if l is Nil {
        q_d_emptyset
      } else if op_equalp(l, list1(q_mor)).truthy() {
        let mut acc : Value = Nil
        for li in margs(l).iter() {
          acc = cons(d_fourier_elim(li, vars), acc)
        }
        acc = delete(q_d_emptyset, acc)
        if acc is Nil {
          q_d_emptyset
        } else if member(t, acc).truthy() {
          q_d_universalset
        } else {
          share_fourier_elim__opapply(q_mor, acc)
        }
      } else {
        l = if op_equalp(l, list1(q_mand)).truthy() {
          margs(l)
        } else {
          list1(l)
        }
        l = delete(t, l)
        // Push all non-affine expressions into other-list; push all
        // equalities into eq-list, push all > equalities into pos-list,
        // and push everything else into other-list.
        for li in l.iter() {
          if !d_affine_p(d_lhs(li), d_listofvars(li)).truthy() {
            other_list = cons(li, other_list)
          } else if op_equalp(li, list1(q_mequal)).truthy() {
            eq_list = cons(li, eq_list)
          } else if op_equalp(li, list1(q_mgreaterp)).truthy() {
            pos_list = cons(d_lhs(li), pos_list)
          } else {
            other_list = cons(li, other_list)
          }
        }
        // Using eq-list, eliminate as many variables as possible.
        eq_list = cons(list1(q_mlist), eq_list)
        pos_list = cons(list1(q_mlist), pos_list)
        other_list = cons(list1(q_mlist), other_list)
        eq_list = linear_elimination(eq_list, vars)
        if eq(q_d_emptyset, eq_list) {
          pos_list = q_d_emptyset
        } else {
          other_list = append(other_list, margs(funcall(q_d_second, [eq_list])))
          eq_list = d_first(eq_list)
          pos_list = d_substitute(eq_list, pos_list)
          other_list = d_substitute(eq_list, other_list)
        }
        if eq(pos_list, q_d_emptyset) {
          pos_list
        } else {
          pos_list = fourier_elim(margs(pos_list), margs(vars))
          if eq(pos_list, q_d_emptyset) {
            pos_list
          } else {
            d_append(list3(eq_list, pos_list, other_list))
          }
        }
      }
    },
  )
}

///|
/// Without the post-fourier-elim-simp, fourier_elim([0 < x, x<1, 0 < y,
/// y <1, x+y+z < 4, z > 0],[z,y,x]) gives y<min(1,4-x); since 0 < x < 1,
/// Maxima should be able to deduce that min(1,4-x) = 1. Each member of pos
/// is put into the fact database of a new context, then simplified.
fn post_fourier_elim_simp(pos : Value) -> Value raise {
  share_fourier_elim__with_context(true, () => {
    mapcar(s => mfuncall(q_d_assume, list1(s)), pos) |> ignore
    with_special(q_dosimp, t, () => {
      let pos = mapcar(s => simplifya(s, Nil), pos)
      remove_if(s => equal(t, standardize_inequality(s)), pos)
    })
  })
}

///|
fn fourier_elim(pos : Value, vars : Value) -> Value raise {
  let mut pos = pos
  let mut vars = vars
  let mut acc : Value = Nil
  while !eq(pos, q_d_emptyset) && car(pos).truthy() && vars is Cons(_) {
    let vi = car(vars)
    vars = cdr(vars)
    let w = fourier_elim_one_variable(pos, vi)
    acc = append(acc, car(w))
    pos = cadr(w)
  }
  if eq(q_d_emptyset, pos) {
    q_d_emptyset
  } else {
    pos = delete(t, mapcar(s => fe_gt(s, Fix(0L)), pos))
    if some(s => s is Nil, pos) {
      q_d_emptyset
    } else {
      share_fourier_elim__opapply(q_mlist, post_fourier_elim_simp(append(acc, pos)))
    }
  }
}

///|
/// (1) Delete all manifestly positive members of pos. (2) If pos has a
/// zero or negative member set pos to (-1). (3) Remove the extremal
/// members of pos (apply min).
fn simplify_fe_args(pos : Value) -> Value raise {
  if eq(pos, q_d_inf) || eq(pos, q_d_minf) {
    list1(pos)
  } else {
    share_fourier_elim__with_context(true, () => {
      let mut pos = remove_if(s => eq(q_d_pos, csign(s)), pos)
      if some(
          s => {
            let c = csign(s)
            eq(c, q_d_neg) || eq(c, q_d_nz) || eq(c, q_d_zero)
          },
          pos,
        ) {
        pos = list1(Fix(-1L))
      }
      pos = apply_min(pos)
      if op_equalp(pos, list1(q_d_min)).truthy() {
        margs(pos)
      } else {
        list1(pos)
      }
    })
  }
}

///|
/// Do Fourier elimination on a list l of inequalities with respect to the
/// indeterminate x. Each member of l is a polynomial p (with real
/// coefficients) meaning p > 0. Returns ((lb < x , x < ub), other), where
/// other lists the implied inequalities (each lower bound is less than each
/// upper bound) and the members of l that do not determine a bound on x.
fn fourier_elim_one_variable(
  pos : Value,
  x : Value,
  need_simp? : Value = t,
) -> Value raise {
  let mut pos = pos
  let mut acc : Value = Nil
  let mut lb : Value = Nil
  let mut ub : Value = Nil
  let mut bounds : Value = Nil
  if need_simp.truthy() {
    pos = simplify_fe_args(pos)
  }
  // Find the lower and upper bounds for x. Example: say 1 - x > 0. The
  // coefficient of x is negative, and solving 1 - x = 0 for x gives an
  // *upper* bound for x (that is x < 1).
  for li in pos.iter() {
    let cf = d_ratcoef(li, x)
    let sgn = number_sign(cf)
    if eq(sgn, q_d_neg) || eq(sgn, q_d_pos) {
      let sol = d_expand(div(sub(mul2(cf, x), li), cf))
      if eq(sgn, q_d_neg) {
        ub = cons(sol, ub)
      } else {
        lb = cons(sol, lb)
      }
    } else {
      acc = cons(li, acc)
    }
  }
  // Delete the non-extremal members of lb and ub
  lb = apply_max(lb)
  ub = apply_min(ub)
  let mut lb_args = if op_equalp(lb, list1(q_d_max)).truthy() {
    margs(lb)
  } else {
    list1(lb)
  }
  let mut ub_args = if op_equalp(ub, list1(q_d_min)).truthy() {
    margs(ub)
  } else {
    list1(ub)
  }
  lb_args = delete(q_d_minf, lb_args)
  ub_args = delete(q_d_inf, ub_args)
  // Require that each lower bound be smaller than each upper bound.
  acc = append(
    acc,
    mapcar(
      s => sub(cadr(s), car(s)),
      fourier_elim_cartesian_product(list2(lb_args, ub_args)),
    ),
  )
  // Return ((lb < x x < ub) acc).
  if !eq(q_d_inf, ub) {
    bounds = cons(opcons(q_mlessp, list2(x, ub)), bounds)
  }
  if !eq(q_d_minf, lb) {
    bounds = cons(opcons(q_mlessp, list2(lb, x)), bounds)
  }
  list2(
    bounds,
    if some(s => eql(Fix(0L), s) || s is Nil, acc) {
      q_d_emptyset
    } else {
      acc
    },
  )
}

///|
/// Apply max without looking at the current context.
fn apply_max(l : Value) -> Value raise {
  share_fourier_elim__with_context(true, () => {
    let l = mapcar(s => d_expand(s), l)
    share_fourier_elim__opapply(q_d_max, l)
  })
}

///|
/// Apply min without looking at the current context.
fn apply_min(l : Value) -> Value raise {
  share_fourier_elim__with_context(true, () => {
    let l = mapcar(s => d_expand(s), l)
    share_fourier_elim__opapply(q_d_min, l)
  })
}

///|
fn compare_using_empty_context(a : Value, b : Value) -> Value raise {
  share_fourier_elim__with_context(true, () => d_compare(a, b))
}

///|
fn init_share_fourier_elim() -> Unit raise {
  // (if (not ($get '$to_poly '$version)) ($load '$to_poly)): to_poly
  // provides $elim. When it cannot be loaded, fourier_elim still loads (its
  // other helpers from to_poly are private copies here) and $elim is
  // undefined.
  if !d_get(q_d_to_poly, q_d_version).truthy() {
    with_specials([(q_errcatch, t), (q_d_errormsg, Nil)], () => {
      errset(() => d_load(q_d_to_poly)) |> ignore
    })
  }
  mfuncall(q_d_declare, list2(q_d_one_to_one, q_d_feature)) |> ignore
  mfuncall(q_d_declare, list2(q_d_sinh, q_d_one_to_one)) |> ignore
  mfuncall(q_d_declare, list2(q_d_log, q_d_one_to_one)) |> ignore
  mfuncall(q_d_declare, list2(q_d_tanh, q_d_one_to_one)) |> ignore
  mfuncall(q_d_declare, list2(q_d_log, q_d_increasing)) |> ignore
}
