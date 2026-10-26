// Port of src/conjugate.lisp: the conjugate function.

///|
fn conjugate__nounform(x : Value) -> Value {
  list2(list2(q_d_conjugate, q_simp), x)
}

///|
fn conjugate__conj(x : Value) -> Value raise {
  take(list1(q_d_conjugate), [x])
}

///|
fn tex_conjugate(x : Value, l : Value, r : Value) -> Value raise {
  // Punt to TeX output for MEXPT, but defeat the special case for powers of
  // trig functions by supplying an expression which has a different
  // operator (namely CONJUGATE-SUPERSCRIPT-STAR) instead of MEXPT.
  tex_mexpt(mk(q_conjugate_superscript_star, [second(x), Str("\\ast")]), l, r)
}

///|
/// Return true iff Maxima can prove that z is not on the negative real axis.
fn off_negative_real_axisp(z : Value) -> Value raise {
  let z = trisplit(z)
  lbool(eql(t, mnqp(cdr(z), int(0))) || eql(t, mgqp(car(z), int(0))))
}

///|
fn on_negative_real_axisp(z : Value) -> Value raise {
  let z = trisplit(z)
  lbool(eql(t, meqp(cdr(z), int(0))) && eql(t, mgrp(int(0), car(z))))
}

///|
fn off_negative_one_to_onep(z : Value) -> Value raise {
  let z = trisplit(z)
  lbool(
    eq(t, mnqp(cdr(z), int(0))) ||
    eq(t, mgrp(car(z), int(1))) ||
    eq(t, mgrp(int(-1), car(z))),
  )
}

///|
fn in_domain_of_asin(z : Value) -> Value raise {
  let z = trisplit(z)
  let x = car(z)
  let y = cdr(z)
  lbool(
    eq(t, mnqp(y, int(0))) ||
    (eq(t, mgrp(x, int(-1))) && eq(t, mgrp(int(1), x))),
  )
}

///|
/// Return T iff Maxima can prove that Z is off the segment of the imaginary
/// axis that runs from -%i to %i, excluding zero itself.
fn in_domain_of_acot(z : Value) -> Value raise {
  let z = trisplit(z)
  let x = car(z)
  let y = cdr(z)
  lbool(
    eq(t, mnqp(x, int(0))) ||
    eq(t, meqp(y, int(0))) ||
    eq(t, mgrp(y, int(1))) ||
    eq(t, mgrp(int(-1), y)),
  )
}

///|
/// Return T iff Maxima can prove that Z is off the branch cut
/// (-infinity, 1] of acosh.
fn in_domain_of_acosh(z : Value) -> Value raise {
  let z = trisplit(z)
  lbool(eq(t, mnqp(cdr(z), int(0))) || eq(t, mgrp(car(z), int(1))))
}

///|
/// Return T iff Maxima can prove that Z is off the branch cuts
/// (-infinity, 0] and [1, infinity) of asech.
fn in_domain_of_asech(z : Value) -> Value raise {
  let z = trisplit(z)
  let x = car(z)
  let y = cdr(z)
  lbool(
    eq(t, mnqp(y, int(0))) ||
    (eq(t, mgrp(x, int(0))) && eq(t, mgrp(int(1), x))),
  )
}

///|
/// Return conjugate(log(x)). Actually, x is a lisp list (x).
fn conjugate_log(x : Value) -> Value raise {
  let x = car(x)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_log), [conjugate__conj(x)])
  } else if on_negative_real_axisp(x).truthy() {
    add2(take(list1(q_p_log), [neg(x)]), muln_([int(-1), q_d__pcti, q_d__pctpi]))
  } else {
    conjugate__nounform(take(list1(q_p_log), [x]))
  }
}

///|
/// Return conjugate(plog(x)); again, x is the CL list (x).
fn conjugate_plog(x : Value) -> Value raise {
  let x = car(x)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_plog), [conjugate__conj(x)])
  } else if on_negative_real_axisp(x).truthy() {
    add2(take(list1(q_p_plog), [neg(x)]), muln_([int(-1), q_d__pcti, q_d__pctpi]))
  } else {
    conjugate__nounform(take(list1(q_p_plog), [x]))
  }
}

///|
/// Return conjugate(x^p), where e = (x, p).
fn conjugate_mexpt(e : Value) -> Value raise {
  let x = first(e)
  let p = second(e)
  if maxima_integerp(p).truthy() || off_negative_real_axisp(x).truthy() {
    power(conjugate__conj(x), conjugate__conj(p))
  } else if odd_root_exponent_p(p).truthy() &&
    eq(t, meqp(cdr(trisplit(x)), int(0))) {
    // The real root of a real X, see ODD-ROOT-EXPONENT-P.
    power(x, p)
  } else {
    conjugate__nounform(power(x, p))
  }
}

///|
fn conjugate_sum(e : Value) -> Value raise {
  if d_featurep(third(e), q_d_real).truthy() &&
    d_featurep(fourth(e), q_d_real).truthy() {
    take(list1(q_p_sum), [
      conjugate__conj(first(e)),
      second(e),
      third(e),
      fourth(e),
    ])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_sum), e), t))
  }
}

///|
fn conjugate_product(e : Value) -> Value raise {
  if d_featurep(third(e), q_d_real).truthy() &&
    d_featurep(fourth(e), q_d_real).truthy() {
    take(list1(q_p_product), [
      conjugate__conj(first(e)),
      second(e),
      third(e),
      fourth(e),
    ])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_product), e), t))
  }
}

///|
fn conjugate_asin(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_asin(x).truthy() {
    take(list1(q_p_asin), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_asin), [x]))
  }
}

///|
fn conjugate_acos(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_asin(x).truthy() {
    take(list1(q_p_acos), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_acos), [x]))
  }
}

///|
fn conjugate_acsc(x : Value) -> Value raise {
  let x = car(x)
  if off_negative_one_to_onep(x).truthy() {
    take(list1(q_p_acsc), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_acsc), [x]))
  }
}

///|
fn conjugate_asec(x : Value) -> Value raise {
  let x = car(x)
  if off_negative_one_to_onep(x).truthy() {
    take(list1(q_p_asec), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_asec), [x]))
  }
}

///|
fn conjugate_atan(x : Value) -> Value raise {
  let x = car(x)
  let xx = mul2(q_d__pcti, x)
  if in_domain_of_asin(xx).truthy() {
    take(list1(q_p_atan), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_atan), [x]))
  }
}

///|
/// atanh and asin are entire on the same set.
fn conjugate_atanh(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_asin(x).truthy() {
    take(list1(q_p_atanh), [conjugate__conj(x)])
  } else {
    conjugate__nounform(take(list1(q_p_atanh), [x]))
  }
}

///|
fn conjugate_acot(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_acot(x).truthy() {
    ftake(q_p_acot, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(take(list1(q_p_acot), [x]))
  }
}

///|
fn conjugate_acsch(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_acot(x).truthy() {
    ftake(q_p_acsch, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(ftake(q_p_acsch, [x]))
  }
}

///|
fn conjugate_asinh(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_asin(mul2(q_d__pcti, x)).truthy() {
    ftake(q_p_asinh, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(ftake(q_p_asinh, [x]))
  }
}

///|
fn conjugate_acoth(x : Value) -> Value raise {
  let x = car(x)
  if off_negative_one_to_onep(x).truthy() {
    ftake(q_p_acoth, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(ftake(q_p_acoth, [x]))
  }
}

///|
fn conjugate_acosh(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_acosh(x).truthy() {
    ftake(q_p_acosh, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(ftake(q_p_acosh, [x]))
  }
}

///|
fn conjugate_asech(x : Value) -> Value raise {
  let x = car(x)
  if in_domain_of_asech(x).truthy() {
    ftake(q_p_asech, [ftake(q_d_conjugate, [x])])
  } else {
    conjugate__nounform(ftake(q_p_asech, [x]))
  }
}

///|
/// Integer order Bessel functions are entire; thus they commute with the
/// conjugate (Schwartz reflection principle). Non-integer order Bessel
/// functions are not analytic along the negative real axis.
fn conjugate_bessel_j(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if d_featurep(n, q_d_integer).truthy() || off_negative_real_axisp(x).truthy() {
    take(list1(q_p_bessel_j), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_bessel_j), z), t))
  }
}

///|
fn conjugate_bessel_y(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_bessel_y), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_bessel_y), z), t))
  }
}

///|
fn conjugate_bessel_i(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if d_featurep(n, q_d_integer).truthy() || off_negative_real_axisp(x).truthy() {
    take(list1(q_p_bessel_i), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_bessel_i), z), t))
  }
}

///|
fn conjugate_bessel_k(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_bessel_k), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_bessel_k), z), t))
  }
}

///|
fn conjugate_hankel_1(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_hankel_2), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_hankel_1), z), t))
  }
}

///|
fn conjugate_hankel_2(z : Value) -> Value raise {
  let n = first(z)
  let x = second(z)
  if off_negative_real_axisp(x).truthy() {
    take(list1(q_p_hankel_1), [conjugate__conj(n), conjugate__conj(x)])
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_hankel_2), z), t))
  }
}

///|
fn conjugate_log_gamma(z : Value) -> Value raise {
  let z = first(z)
  if off_negative_real_axisp(z).truthy() {
    take(list1(q_p_log_gamma), [conjugate__conj(z)])
  } else {
    conjugate__nounform(take(list1(q_p_log_gamma), [z]))
  }
}

///|
/// For z in C \ [1,infinity) and n in {1,2,3,...}, replace
/// conjugate(li[n](z)) by li[n](conjugate(z)). For all other cases, return
/// a conjugate nounform.
fn conjugate_li(z : Value) -> Value raise {
  let n = first(z)
  let zz = risplit(second(z))
  if d_featurep(n, q_d_integer).truthy() &&
    eq(t, mgrp(n, int(0))) &&
    (eq(t, mnqp(cdr(zz), int(0))) || eq(t, mgrp(int(1), car(zz)))) {
    subftake(q_d_li, list1(n), list1(ftake(q_d_conjugate, [second(z)])))
  } else {
    list2(list2(q_d_conjugate, q_simp), subftake(q_d_li, list1(n), list1(second(z))))
  }
}

///|
fn conjugate_psi(z : Value) -> Value raise {
  let s = conjugate__conj(first(z))
  let x = conjugate__conj(second(z))
  take(list1(q_mqapply), [cons(list2(q_d_psi, q_array), list1(s)), x])
}

///|
/// When all derivative variables & orders are real, commute the derivative
/// with the conjugate.
fn conjugate_derivative(z : Value) -> Value raise {
  if every(x => manifestly_real_p(x).truthy(), cdr(z)) {
    let z = cons(conjugate__conj(car(z)), cdr(z))
    simplifya(cons(list1(q_p_derivative), z), t)
  } else {
    conjugate__nounform(simplifya(cons(list1(q_p_derivative), z), t))
  }
}

///|
/// The function manifestly-real-p makes some effort to determine if its
/// input is real valued.
fn manifestly_real_p(e : Value) -> Value raise {
  with_special(q_d_inflag, t, () => {
    let v = d_numberp(e)
    if v.truthy() {
      return v
    }
    if d_mapatom(e).truthy() &&
      !manifestly_pure_imaginary_p(e).truthy() &&
      !manifestly_complex_p(e).truthy() &&
      !manifestly_nonreal_p(e).truthy() {
      return t
    }
    if consp(e) && consp(car(e)) {
      let r = get(caar(e), q_real_valued)
      if r.truthy() {
        return r
      }
    }
    if d_subvarp(e).truthy() {
      return manifestly_real_p(d_op(e))
    }
    Nil
  })
}

///|
/// The function manifestly-pure-imaginary-p makes some effort to determine
/// if its input is a multiple of %i.
fn manifestly_pure_imaginary_p(e : Value) -> Value raise {
  with_special(q_d_inflag, t, () => {
    if d_mapatom(e).truthy() &&
      (
        eq(e, q_d__pcti) ||
        (
          symbolp(e) &&
          kindp(e, q_d_imaginary).truthy() &&
          !d_nonscalarp(e).truthy()
        ) ||
        (d_subvarp(e).truthy() && manifestly_pure_imaginary_p(d_op(e)).truthy())
      ) {
      return t
    }
    // For now, let's use $csign on constant expressions only.
    lbool(
      d_constantp(e).truthy() &&
      !eq(q_d_und, e) &&
      !eq(q_d_ind, e) &&
      eq(q_d_imaginary, d_csign(e)),
    )
  })
}

///|
/// Don't use (kindp e '$complex)!
fn manifestly_complex_p(e : Value) -> Value raise {
  with_special(q_d_inflag, t, () => lbool(
    (symbolp(e) && decl_complexp(e).truthy() && !d_nonscalarp(e).truthy()) ||
    eq(e, q_d_infinity) ||
    (
      d_subvarp(e).truthy() &&
      manifestly_complex_p(d_op(e)).truthy() &&
      !d_nonscalarp(e).truthy()
    ),
  ))
}

///|
fn manifestly_nonreal_p(e : Value) -> Value raise {
  if symbolp(e) {
    let m = member(e, list([q_d_und, q_d_ind, t, Nil]))
    if m.truthy() {
      return m
    }
    d_nonscalarp(e)
  } else {
    Nil
  }
}

///|
fn simp_conjugate(e : Value, f : Value, z : Value) -> Value raise {
  ignore(f)
  oneargcheck(e) |> ignore
  let e = simpcheck(cadr(e), z) // simp and disrep if necessary
  if complexp(e) {
    // never happens, but might someday.
    return conjugate(e)
  }
  if manifestly_real_p(e).truthy() {
    return e
  }
  if manifestly_pure_imaginary_p(e).truthy() {
    return mul2(int(-1), e)
  }
  if manifestly_nonreal_p(e).truthy() || d_mapatom(e).truthy() {
    return conjugate__nounform(e)
  }
  if op_equalp(e, list1(q_d_conjugate)).truthy() {
    return car(margs(e))
  }
  let op = mop(e)
  if symbolp(op) && get(op, q_real_valued).truthy() {
    return e
  }
  if symbolp(op) && get(op, q_commutes_with_conjugate).truthy() {
    return simplify(cons(list1(op), mapcar(s => conjugate__conj(s), margs(e))))
  }
  // non-subscripted functions (operator doesn't have the specsimp property)
  let f1 = if symbolp(op) && !get(op, q_specsimp).truthy() {
    get(op, q_conjugate_function)
  } else {
    Nil
  }
  if f1.truthy() {
    return funcall(f1, [margs(e)])
  }
  // subscripted functions (operator has the specsimp property)
  let f2 = if d_subvarp(op).truthy() && get(caar(op), q_specsimp).truthy() {
    get(caar(op), q_conjugate_function)
  } else {
    Nil
  }
  if f2.truthy() {
    return funcall(f2, [append(margs(op), margs(e))])
  }
  conjugate__nounform(e)
}

///|
fn init_conjugate() -> Unit raise {
  d_put(q_d_conjugate, int(1), q_d_version) |> ignore
  set(q_d_props, remove(q_d_conjugate, symval(q_d_props))) |> ignore
  setf_get(q_conjugate_superscript_star, q_tex_lbp, tex_lbp(q_mexpt)) |> ignore
  setf_get(q_conjugate_superscript_star, q_tex_rbp, tex_rbp(q_mexpt)) |> ignore
  putprop(q_d_conjugate, q_tex_conjugate, q_tex) |> ignore
  putprop(q_d_conjugate, int(121), q_tex_lbp) |> ignore
  putprop(q_d_conjugate, int(120), q_tex_rbp) |> ignore
  putprop(q_d_conjugate, q_simp_conjugate, q_operators) |> ignore
  putprop(
    q_d_conjugate,
    lread("(mlist $matrix mequal $set mnotequal %transpose)"),
    q_distribute_u_over,
  )
  |> ignore
  with_specials([(q_d_context, q_d_global), (q_context, q_d_global)], () => {
    meval(lread("(($declare) $conjugate $complex)")) |> ignore
    set(q_d_props, remove(q_d_conjugate, symval(q_d_props)))
  })
  |> ignore
  for name in [
    "mplus", "mtimes", "%signum", "%cosh", "%sinh", "%tanh", "%sech", "%csch",
    "%coth", "%cos", "%sin", "%tan", "%sec", "%csc", "%cot", "%atan2", "%jacobi_cn",
    "%jacobi_sn", "%jacobi_dn", "%gamma", "$pochhammer", "$max", "$min",
  ] {
    setf_get(sym(name), q_commutes_with_conjugate, t) |> ignore
  }
  for pair in [
    ("%log", "conjugate-log"),
    ("%plog", "conjugate-plog"),
    ("mexpt", "conjugate-mexpt"),
    ("%asin", "conjugate-asin"),
    ("%acos", "conjugate-acos"),
    ("%atan", "conjugate-atan"),
    ("%atanh", "conjugate-atanh"),
    ("%asec", "conjugate-asec"),
    ("%acsc", "conjugate-acsc"),
    ("%acot", "conjugate-acot"),
    ("%asinh", "conjugate-asinh"),
    ("%acosh", "conjugate-acosh"),
    ("%asech", "conjugate-asech"),
    ("%acsch", "conjugate-acsch"),
    ("%acoth", "conjugate-acoth"),
    ("%bessel_j", "conjugate-bessel-j"),
    ("%bessel_y", "conjugate-bessel-y"),
    ("%bessel_i", "conjugate-bessel-i"),
    ("%bessel_k", "conjugate-bessel-k"),
    ("%hankel_1", "conjugate-hankel-1"),
    ("%hankel_2", "conjugate-hankel-2"),
    ("%log_gamma", "conjugate-log-gamma"),
    ("$li", "conjugate-li"),
    ("$psi", "conjugate-psi"),
    ("%sum", "conjugate-sum"),
    ("%product", "conjugate-product"),
  ] {
    setf_get(sym(pair.0), q_conjugate_function, sym(pair.1)) |> ignore
  }
  setf_get(q_p_derivative, q_conjugate_function, q_conjugate_derivative)
  |> ignore
  for name in [
    "%imagpart", "mabs", "%realpart", "%carg", "$ceiling", "$floor", "$mod", "$unit_step",
    "$charfun",
  ] {
    setf_get(sym(name), q_real_valued, t) |> ignore
  }
}
