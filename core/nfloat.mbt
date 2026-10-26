// Port of src/nfloat.lisp: numerical evaluation of expressions with a
// running error (Barton Willis).

///|
/// `(bind-fpprec val body)` from float.lisp.
fn[T] nfloat__bind_fpprec(val : Value, f : () -> T raise) -> T raise {
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
/// `#.(/ (log 2.0) (log 10.0))` with double-float literals.
let nfloat__log10_2 : Double = 0.6931471805599453 / 2.302585092994046

// ---------------------------------------------------------------------------
// (in-package #:bigfloat)

///|
/// Each member of the CL list l is a two member list (running error form).
fn bf_running_error_plus(l : Value) -> Value raise {
  let mut acc : Value = Fix(0L)
  let mut err : Value = Fix(0L)
  for lk in l.iter() {
    acc = bf_add(acc, first(lk))
    err = bf_op_plus(list3(err, second(lk), bf_abs(acc)))
  }
  list2(acc, err)
}

///|
/// (%i20) ah * lh * (1 + eps);
/// (%o20) ah*(eps+1)*lh
/// (%i21) %-a*l;
/// (%o21) ah*(eps+1)*lh-a*l
/// (%i22) subst([a = ah-e,l = lh-w],%);
/// (%o22) ah*(eps+1)*lh-(ah-e)*(lh-w)
/// (%i23) expand(%);
/// (%o23) -e*w+ah*w+ah*eps*lh+e*lh
fn bf_running_error_prod(l : Value) -> Value raise {
  let mut acc : Value = Fix(1L)
  let mut err : Value = Fix(0L)
  for lk in l.iter() {
    let z = acc
    acc = bf_mul(acc, first(lk))
    err = bf_add(
      bf_mul(err, bf_abs(first(lk))),
      bf_mul(bf_abs(z), bf_abs(second(lk))),
    )
  }
  list2(acc, err)
}

///|
/// (%i1) (a+ae*eps)*(1+eps)/(b+be*eps)-a/b$
/// (%i2) expand(limit(%/eps,eps,0))$
/// (%i3) expand(ratsubst(Q,a/b,%))$
/// (%i4) map('abs,%)$
/// (%i5) facsum(%,abs(Q));
/// (%o5) ((abs(be)+abs(b))*abs(Q)+abs(ae))/abs(b)
fn bf_running_error_quotient(l : Value) -> Value raise {
  let a = first(l)
  let b = second(l)
  let s = bf_div(first(a), first(b))
  list2(
    s,
    bf_add(
      bf_mul(
        bf_abs(s),
        bf_add(Fix(1L), bf_abs(bf_div(second(b), first(b)))),
      ),
      bf_abs(bf_div(second(a), first(b))),
    ),
  )
}

///|
/// unary negation.
fn bf_running_error_negate(x : Value) -> Value raise {
  let x = first(x)
  list2(bf_neg(first(x)), second(x))
}

///|
/// (x+ex)^(n+en) = en*x^n*log(x)+x^n+ex*n*x^(n-1) + ...
fn bf_running_error_expt(l : Value) -> Value raise {
  let x0 = first(l)
  let n0 = second(l)
  let ex = second(x0)
  let en = second(n0)
  let x = first(x0)
  let n = first(n0)
  let s = bf_expt(x, n)
  list2(
    s,
    bf_add(
      if bf_zerop(en) {
        Fix(0L)
      } else {
        bf_abs(bf_op_star(list3(s, en, bf_log(x))))
      },
      bf_abs(bf_op_star(list3(n, bf_expt(x, bf_sub(n, Fix(1L))), ex))),
    ),
  )
}

///|
/// sqrt(x + ex) = sqrt(x) + ex / (2 * sqrt(x)) + ...
fn bf_running_error_sqrt(x : Value) -> Value raise {
  let x = first(x)
  let s = bf_sqrt(first(x))
  list2(s, bf_abs(bf_div(second(x), bf_mul(Fix(2L), s))))
}

///|
/// log(x + ex) = log(x) + ex / x + ...
fn bf_running_error_log(x : Value) -> Value raise {
  let x = first(x)
  list2(bf_log(first(x)), bf_abs(bf_div(second(x), first(x))))
}

///|
fn bf_psi0(x : Value) -> Value raise {
  bf_bigfloat(
    d_rectform(
      mfuncall(q_d_bfpsi0, list2(d_bfloat(maxima_to(x)), symval(q_d_fpprec))),
    ),
  )
}

///|
fn bf_gamma(x : Value) -> Value raise {
  bf_bigfloat(d_bfloat(take(list1(q_p_gamma), [maxima_to(x)])))
}

///|
/// gamma(x + ex) = gamma(x) + ex * gamma(x) * psi[0](x) + ..
fn bf_running_error_gamma(x : Value) -> Value raise {
  let x = first(x)
  let s = bf_gamma(first(x))
  list2(s, bf_abs(bf_op_star(list3(s, second(x), bf_psi0(first(x))))))
}

///|
fn bf_running_error_hypergeometric(
  a : Value,
  b : Value,
  x : Value,
  subs : Value,
  bits : Value,
) -> Value raise {
  // To do this correctly, we'd need the partial derivatives of the
  // hypergeometric functions with respect the the parameters. Ouch!
  let mut a = mapcar(s => car(bf_running_error_eval(s, subs, bits)), margs(a))
  let mut b = mapcar(s => car(bf_running_error_eval(s, subs, bits)), margs(b))
  let mut x = car(bf_running_error_eval(x, subs, bits))
  if bf_lt(bf_abs(x), Flo(0.99)) {
    let (f, d) = bf_hypergeometric_by_series(a, b, x)
    list2(
      f,
      bf_div(bf_mul(bf_abs(f), bf_expt(Fix(10L), bf_neg(d))), bf_epsilon(x)),
    )
  } else {
    let dig = bf_ceiling(bf_mul(bits, Flo(nfloat__log10_2))).0
    a = mapcar(s => maxima_to(s), a)
    b = mapcar(s => maxima_to(s), b)
    x = maxima_to(x)
    let (f, d) = bf_hypergeometric_float_eval(a, b, x, dig, adjust_params=t)
    list2(f, bf_mul(bf_abs(f), bf_expt(Fix(10L), bf_neg(d))))
  }
}

///|
/// The substitution list `((mlist) ((mequal) v lo))`.
fn nfloat__subst1(v : Value, lo : Value) -> Value {
  list2(list1(q_mlist), list3(list1(q_mequal), v, lo))
}

///|
fn bf_running_error_sum(l : Value, subs : Value, bits : Value) -> Value raise {
  let sumand = first(l)
  let v = second(l)
  let mut lo = third(l)
  let hi = fourth(l)
  let mut acc : Value = Fix(0L)
  let mut err : Value = Fix(0L)
  if integerp(lo) && integerp(hi) {
    while bf_le(lo, hi) {
      let mut q = d_sublis(nfloat__subst1(v, lo), sumand)
      q = simplify(q)
      let x = bf_running_error_eval(q, subs, bits)
      lo = bf_add(lo, Fix(1L))
      acc = bf_add(acc, first(x))
      err = bf_op_plus(list3(err, second(x), bf_abs(acc)))
    }
    list2(acc, err)
  } else {
    throw_tag(q_nfloat_nounform_return, q_return_nounform)
  }
}

///|
fn bf_running_error_product(
  l : Value,
  subs : Value,
  bits : Value,
) -> Value raise {
  let prodand = first(l) // a sum has a summand, so a product has a ...
  let v = second(l)
  let mut lo = third(l)
  let hi = fourth(l)
  let mut acc : Value = Fix(1L)
  let mut err : Value = Fix(0L)
  if integerp(lo) && integerp(hi) {
    while bf_le(lo, hi) {
      let mut x = d_sublis(nfloat__subst1(v, lo), prodand)
      x = simplify(x)
      x = bf_running_error_eval(x, subs, bits)
      lo = bf_add(lo, Fix(1L))
      err = bf_add(
        bf_mul(err, bf_abs(first(x))),
        bf_mul(bf_abs(acc), second(x)),
      )
      acc = bf_mul(acc, first(x))
      err = bf_add(err, bf_abs(acc))
    }
    list2(acc, err)
  } else {
    throw_tag(q_nfloat_nounform_return, q_return_nounform)
  }
}

///|
fn bf_running_error_abs(l : Value) -> Value raise {
  let l = first(l)
  list2(bf_abs(first(l)), second(l))
}

///|
fn bf_running_error_conjugate(l : Value) -> Value raise {
  let l = first(l)
  list2(bf_conjugate(first(l)), second(l))
}

///|
/// untested!!!!!
fn bf_running_error_factorial(l : Value) -> Value raise {
  let l = first(l)
  if integerp(l) {
    list2(take(list1(q_mfactorial), [l]), Fix(0L))
  } else {
    bf_running_error_gamma(list1(list2(bf_add(Fix(1L), first(l)), second(l))))
  }
}

///|
fn bf_running_error_atan2(l : Value) -> Value raise {
  let y = first(l)
  let x = second(l)
  let d = bf_div(
    Fix(1L),
    bf_add(bf_mul(first(x), first(x)), bf_mul(first(y), first(y))),
  )
  list2(
    bf_atan(first(y), b=first(x)),
    bf_mul(
      bf_add(
        bf_mul(bf_abs(second(y)), bf_abs(first(x))),
        bf_mul(bf_abs(second(x)), bf_abs(first(y))),
      ),
      d,
    ),
  )
}

///|
fn bf_running_error_realpart(l : Value) -> Value raise {
  let l = first(l)
  list2(bf_realpart(first(l)), second(l))
}

///|
fn bf_running_error_imagpart(l : Value) -> Value raise {
  let l = first(l)
  list2(bf_imagpart(first(l)), second(l))
}

///|
/// The predicate `(lambda (s) (or (maxima::$ratnump s) (maxima::$numberp s)))`.
let nfloat__ratnum_or_number_fn : Value = lfunc("nfloat-number-p", args => {
  let s = arg(args, 0)
  let v = d_ratnump(s)
  if v.truthy() {
    v
  } else {
    d_numberp(s)
  }
})

///|
fn bf_running_error_eval(e : Value, subs : Value, bits : Value) -> Value raise {
  if eq(e, q_d__pcti) {
    let e = bf_to(
      if num_gt(bits, Fix(53L)) {
        d_bfloat(Fix(1L))
      } else {
        d_float(Fix(1L))
      },
    )
    return list2(bf_to(Fix(0L), imag=e), bf_abs(e))
  }
  if complex_number_p(e, ntypep=nfloat__ratnum_or_number_fn).truthy() {
    let e = bf_to(
      if num_gt(bits, Fix(53L)) {
        d_bfloat(e)
      } else {
        d_float(e)
      },
    )
    return list2(e, bf_abs(e))
  }

  // Check sysconst before $numer: the $numer value of a system constant
  // such as %pi is only a double-float.
  if atom(e) && get(e, q_sysconst).truthy() {
    return bf_running_error_eval(d_bfloat(e), list1(list1(q_mlist)), bits)
  }
  if atom(e) && mget(e, q_d_numer).truthy() {
    return bf_running_error_eval(mget(e, q_d_numer), subs, bits)
  }
  if atom(e) {
    let e = d_sublis(subs, e)
    return if complex_number_p(e, ntypep=q_bigfloat_or_number_p).truthy() {
      bf_running_error_eval(e, Nil, bits)
    } else {
      throw_tag(q_nfloat_nounform_return, q_return_nounform)
    }
  }

  // Return a nounform for expressions (arrays, CRE expressions) that don't
  // appear to be Maxima expressions of the form ((op) a1 a2 ...).
  if !(consp(e) && consp(car(e))) {
    return throw_tag(q_nfloat_nounform_return, q_return_nounform)
  }

  // Special case exp(x) (more efficient & accurate than sending this
  // through mexpt).
  if eq(q_mexpt, caar(e)) && eq(second(e), q_d__pcte) {
    let e = bf_running_error_eval(third(e), subs, bits)
    let z = bf_exp(first(e))
    return list2(z, bf_abs(bf_mul(second(e), z)))
  }

  // Special case x^n, where n is an integer. For this case, we do not want
  // to convert the integer to a float. This prevents some, but not all,
  // semi-spurious nonzero imaginary parts for (negative real)^integer.
  if eq(q_mexpt, caar(e)) && integerp(third(e)) {
    return bf_running_error_expt(
      list2(
        bf_running_error_eval(second(e), subs, bits),
        list2(third(e), Fix(0L)),
      ),
    )
  }

  // main function dispatch.
  let f = gethash(mop(e), symval(q_ear_running_error_op))
  if f.truthy() {
    let e = mapcar(s => bf_running_error_eval(s, subs, bits), margs(e))
    return funcall(f, [e])
  }

  // f(x + ex) = f(x) + ex * f'(x) + ... Functions without bigfloat
  // evaluation, for example the Bessel functions, need to be excluded.
  // For now, this code rejects functions of two or more variables.
  if get(caar(e), q_grad).truthy() &&
    cdr(margs(e)) is Nil &&
    (gethash(caar(e), symval(q_ear_big_float_op)).truthy() ||
    trigp(caar(e)).truthy() ||
    arcp(caar(e)).truthy()) {
    let x = bf_running_error_eval(cadr(e), subs, bits)
    let f = take(list1(caar(e)), [maxima_to(first(x))])
    let mut df = get(caar(e), q_grad)
    df = d_rectform(d_substitute(maxima_to(first(x)), caar(df), expr=cadr(df)))
    df = bf_to(df)
    return list2(bf_to(f), bf_mul(second(x), bf_abs(df)))
  }

  // special case hypergeometric
  if eq(caar(e), q_p_hypergeometric) {
    return bf_running_error_hypergeometric(
      second(e),
      third(e),
      fourth(e),
      subs,
      bits,
    )
  }

  // special case sum.
  if eq(caar(e), q_p_sum) || eq(caar(e), q_d_sum) {
    return bf_running_error_sum(cdr(e), subs, bits)
  }

  // special case product
  if eq(caar(e), q_d_product) || eq(caar(e), q_p_product) {
    return bf_running_error_product(cdr(e), subs, bits)
  }

  // special case assignment
  if eq(caar(e), q_msetq) {
    let x = bf_running_error_eval(caddr(e), subs, bits)
    mset(cadr(e), maxima_to(car(x))) |> ignore
    return x
  }

  // Yes, via nformat, this can happen. Try, for example,
  // nfloat('(a,b),[a=3,b=7]).
  if eq(caar(e), q_mprogn) {
    let mut q : Value = Nil
    for ek in cdr(e).iter() {
      q = bf_running_error_eval(ek, subs, bits)
    }
    return q
  }
  throw_tag(q_nfloat_nounform_return, q_return_nounform)
}

///|
/// d * eps is a upper bound for how much e differs from its true value,
/// where eps is the machine epsilon.
///
/// First (log = natural log)
///
///    log10(x) = log(x) / log(10) and log2(x) = log(x) / log(2).
/// So
///    log10(x) = log2(x) * (log(2) / log(10)).
///
/// Second
///     -log10(abs(d * eps / e)) = log10(abs(e)) - log10(abs(d)) - log10(eps),
///                        = (log2(abs(e)) - log2(abs(d)) - log2(eps)) * (log(2) / log(10).
///
/// For log2 we use the binary exponent of the number. Common Lisp gives
/// (decode-float 0.0) --> 0.0 0 1.0, by the way.
fn bf_log10_relative_error(d : Value, e : Value) -> Value raise {
  let mut d = d
  let mut e = e
  if rationalp(d) {
    d = bf_bigfloat(d_bfloat(maxima_to(d)))
  }
  if rationalp(e) {
    e = bf_bigfloat(d_bfloat(maxima_to(e)))
  }
  let ee = bf_decode_float(bf_abs(e)).1
  let de = bf_decode_float(bf_abs(d)).1
  let epse = bf_decode_float(bf_epsilon(bf_abs(d))).1
  bf_floor(bf_mul(bf_sub(ee, bf_add(de, epse)), Flo(nfloat__log10_2))).0
}

///|
fn bf_not_done(
  err : Value,
  f : Value,
  eps : Value,
  machine_eps : Value,
) -> Value raise {
  lbool(
    bf_gt(
      bf_mul(machine_eps, err),
      bf_mul(eps, bf_max(bf_abs(f), list1(Fix(1L)))),
    ),
  )
}

// ---------------------------------------------------------------------------
// (in-package :maxima)

///|
fn nfloat(
  e : Value,
  subs : Value,
  digits : Value,
  max_digits : Value,
) -> (Value, Value) raise {
  if mbagp(e).truthy() || mrelationp(e).truthy() || d_setp(e).truthy() {
    return (
      simplify(
        cons(
          list1(caar(e)),
          mapcar(s => nfloat(s, subs, digits, max_digits).0, margs(e)),
        ),
      ),
      Nil,
    )
  }
  let mut z = list2(Nil, Nil)
  let dig = digits
  let mut digits = digits
  let mut machine_epsilon : Value = Nil
  let mut second_value : Value = Nil
  let primary = catch_tag(q_nfloat_nounform_return, () => {
    let e = nformat(e)
    let mut eps = expt(Fix(10L), num_neg(digits))
    eps = num_div(eps, num_sub(Fix(1L), eps))
    while (
        first(z) is Nil ||
        bf_not_done(second(z), first(z), eps, machine_epsilon).truthy()
      ) &&
      num_lt(digits, max_digits) {
      nfloat__bind_fpprec(digits, () => {
        z = bf_running_error_eval(e, subs, symval(q_fpprec))
        machine_epsilon = if !second(z).truthy() {
          Nil
        } else if integerp(second(z)) {
          Fix(0L)
        } else {
          bf_epsilon(second(z))
        }
        digits = num_mul(Fix(2L), digits)
      })
    }
    if first(z) is Nil ||
      bf_not_done(second(z), first(z), eps, machine_epsilon).truthy() {
      merr("Unable to evaluate to requested number of digits", [])
    } else {
      nfloat__bind_fpprec(dig, () => {
        let v1 = maxima_to(first(z))
        let v2 = maxima_to(second(z))
        second_value = v2
        v1
      })
    }
  })
  (primary, second_value)
}

///|
fn simp_nfloat(x : Value, yy : Value, z : Value) -> Value raise {
  ignore(yy)
  let mut x = cdr(x) // remove ($nfloat)
  let e = if x.truthy() {
    let v = car(x)
    x = cdr(x)
    simpcheck(v, z)
  } else {
    wna_err(q_d_nfloat)
  }
  let subs = if x.truthy() {
    let v = car(x)
    x = cdr(x)
    simpcheck(v, z)
  } else {
    take(list1(q_mlist), [])
  }
  let digits = if x.truthy() {
    let v = car(x)
    x = cdr(x)
    simpcheck(v, z)
  } else {
    symval(q_d_fpprec)
  }
  let max_digits = if x.truthy() {
    let v = car(x)
    x = cdr(x)
    simpcheck(v, z)
  } else {
    symval(q_d_max_fpprec)
  }
  let nounform = () => list([list2(q_d_nfloat, q_simp), e, subs, digits, max_digits])
  if d_listp(subs).truthy() &&
    every(
      s => mequalp(s).truthy() &&
        symbolp(d_lhs(s)) &&
        complex_number_p(d_rhs(s), ntypep=q_mnump).truthy(),
      cdr(subs),
    ) {
    if mbagp(e).truthy() || mrelationp(e).truthy() || d_setp(e).truthy() {
      simplify(
        cons(
          list1(caar(e)),
          mapcar(
            s => take(list1(q_d_nfloat), [s, subs, digits, max_digits]),
            margs(e),
          ),
        ),
      )
    } else {
      let f = nfloat(e, subs, digits, max_digits).0
      if complex_number_p(f, ntypep=q_bigfloat_or_number_p).truthy() {
        f
      } else {
        nounform()
      }
    }
  } else {
    nounform()
  }
}

///|
fn init_nfloat() -> Unit raise {
  // For a similar hashtable mechanism, see trig.lisp.
  defvar_init(q_ear_running_error_op, make_hash_table(kind=Eql))
  let tbl = symval(q_ear_running_error_op)
  sethash(q_mplus, tbl, q_bf_running_error_plus) |> ignore
  sethash(q_mtimes, tbl, q_bf_running_error_prod) |> ignore
  sethash(q_mquotient, tbl, q_bf_running_error_quotient) |> ignore
  sethash(q_mminus, tbl, q_bf_running_error_negate) |> ignore
  sethash(q_mexpt, tbl, q_bf_running_error_expt) |> ignore
  sethash(q_p_sqrt, tbl, q_bf_running_error_sqrt) |> ignore
  sethash(q_p_log, tbl, q_bf_running_error_log) |> ignore
  sethash(q_p_gamma, tbl, q_bf_running_error_gamma) |> ignore
  sethash(q_mabs, tbl, q_bf_running_error_abs) |> ignore
  sethash(q_d_cabs, tbl, q_bf_running_error_abs) |> ignore
  sethash(q_d_conjugate, tbl, q_bf_running_error_conjugate) |> ignore
  sethash(q_mfactorial, tbl, q_bf_running_error_factorial) |> ignore
  sethash(q_p_atan2, tbl, q_bf_running_error_atan2) |> ignore
  sethash(q_d_realpart, tbl, q_bf_running_error_realpart) |> ignore
  sethash(q_d_imagpart, tbl, q_bf_running_error_imagpart) |> ignore
  putprop(q_d_nfloat, q_simp_nfloat, q_operators) |> ignore
}
