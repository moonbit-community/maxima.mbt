// Port of share/orthopoly/orthopoly.lisp: orthogonal polynomials
// (Abramowitz & Stegun, chapter 22), pochhammer, unit_step and the
// spherical Bessel/Hankel functions.

///|
let share_orthopoly__pi : Value = Flo(3.141592653589793)

///|
fn share_orthopoly__eps() -> Value {
  symval(q_n_plusflonum_epsilon_plus)
}

///|
/// `(* 4 a b +flonum-epsilon+)` (or `(* 4 a +flonum-epsilon+ b)`) as SBCL
/// compiles it: the constant factors are multiplied first, then the others
/// from left to right.
fn share_orthopoly__sbcl_mul4(a : Value, b : Value) -> Value raise {
  num_mul(num_mul(num_mul(Fix(4L), share_orthopoly__eps()), a), b)
}

///|
/// `(if (oddp n) a b)` for an integer `n`.
fn share_orthopoly__oddp(n : Value) -> Bool raise {
  oddp(n)
}

///|
/// Build a form from a Lisp-syntax template, replacing the placeholder
/// symbols in `binds` (like backquote with commas).
fn share_orthopoly__tmpl(s : String, binds : Array[(String, Value)]) -> Value raise {
  let t = lread(s)
  let syms = binds.map(b => (sym(b.0), b.1))
  fn go_(x : Value) -> Value {
    match x {
      Cons({ car, cdr }) => cons(go_(car), go_(cdr))
      Sym(_) => {
        for b in syms {
          if eq(x, b.0) {
            return b.1
          }
        }
        x
      }
      _ => x
    }
  }

  go_(t)
}

///|
fn maxima_to_lisp_complex_float(a : Value) -> Value raise {
  with_special(q_d_ratprint, Nil, () => {
    let b = d_rectform(a)
    let br = d_float(d_realpart(b))
    let bi = d_float(d_imagpart(b))
    if numberp(br) && numberp(bi) {
      if num_eq(bi, Fix(0L)) {
        lfloat(br)
      } else {
        complex(lfloat(br), i=lfloat(bi))
      }
    } else {
      a
    }
  })
}

///|
fn xcomplexp(a : Value) -> Value raise {
  lbool(
    floatp(a) ||
    (complexp(a) && (floatp(realpart(a)) || floatp(imagpart(a)))),
  )
}

///|
fn lisp_complex_to_maxima(x : Value) -> Value raise {
  if complexp(x) {
    add2(realpart(x), mul2(q_d__pcti, imagpart(x)))
  } else {
    x
  }
}

///|
fn orthopoly_return_handler(d : Value, f : Value, e : Value) -> Value raise {
  if floatp(f) || complexp(f) {
    let df = maxima_to_lisp_complex_float(d)
    let f = lisp_complex_to_maxima(
      if numberp(df) {
        num_mul(df, f)
      } else {
        mul2(d, f)
      },
    )
    let ef = if numberp(df) && numberp(e) {
      num_abs(num_mul(df, e))
    } else {
      Nil
    }
    if symval(q_d_orthopoly_returns_intervals).truthy() && floatp(ef) {
      mk_simp(q_d_interval, [f, ef])
    } else {
      f
    }
  } else {
    mul2(d, f)
  }
}

///|
fn simp_unk(x : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  ignore(z)
  merr(
    "Maxima doesn't know the derivative of ~:M with respect the ~:M argument",
    [nth(2, x), nth(1, x)],
  )
}

///|
fn simp_unit_step(a : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  oneargcheck(a) |> ignore
  let y = simpcheck(cadr(a), z)
  let s = csign(y)
  if eq(s, q_d_nz) || eq(s, q_d_zero) || eq(s, q_d_neg) {
    Fix(0L)
  } else if eq(s, q_d_pos) {
    Fix(1L)
  } else {
    mk_simp(q_d_unit_step, [y])
  }
}

///|
fn d_intervalp(a : Value) -> Value raise {
  lbool(consp(a) && consp(car(a)) && eq(caar(a), q_d_interval))
}

///|
fn interval_mult(x : Value, a : Value, dx? : Value = Nil) -> Value raise {
  let dx : Value = if dx is Nil { Fix(0L) } else { dx }
  if d_intervalp(a).truthy() && !d_intervalp(x).truthy() {
    let mut p = nth(1, a)
    let mut q = nth(2, a)
    let mut x = x
    if floatp(p) || floatp(q) {
      x = d_float(d_rectform(x))
    }
    p = d_expand(mult(x, p))
    q = d_expand(mult(x, add2(q, simplify(mk(q_mabs, [mul2(p, dx)])))))
    q = simplify(mk(q_mabs, [q]))
    mk_simp(q_d_interval, [p, q])
  } else {
    mult(x, a)
  }
}

///|
fn tex_sub_and_super_scripted_function(
  fn_ : Value,
  sub : Value,
  b1 : Value,
  sup : Value,
  b2 : Value,
  i : Value,
  x : Value,
  l : Value,
  r : Value,
) -> Value raise {
  let x = cdr(x)
  let mut s1 = if b1.truthy() { list1(Str("\\left(")) } else { Nil }
  let mut s2 = if b1.truthy() { list1(Str("\\right)")) } else { Nil }
  let mut lo : Value = Nil
  for k in sub.iter() {
    lo = cons(nth(to_int(k), x), lo)
  }
  lo = if lo.truthy() { tex_list(nreverse(lo), s1, s2, Str(",")) } else { Nil }
  s1 = if b2.truthy() { list1(Str("\\left(")) } else { Nil }
  s2 = if b2.truthy() { list1(Str("\\right)")) } else { Nil }
  let mut hi : Value = Nil
  for k in sup.iter() {
    hi = cons(nth(to_int(k), x), hi)
  }
  hi = if hi.truthy() { tex_list(nreverse(hi), s1, s2, Str(",")) } else { Nil }
  append_n([
    l,
    list1(fn_),
    if lo.truthy() {
      append(list1(Str("_{")), append(lo, list1(Str("}"))))
    } else {
      Nil
    },
    if hi.truthy() {
      append(list1(Str("^{")), append(hi, list1(Str("}"))))
    } else {
      Nil
    },
    tex_list(
      nthcdr(to_int(i), x),
      list1(Str("\\left(")),
      list1(Str("\\right)")),
      Str(","),
    ),
    r,
  ])
}

///|
fn dimension_sub_and_super_scripted_function(
  fn_ : Value,
  sub : Value,
  sup : Value,
  b2 : Value,
  k : Value,
  x : Value,
) -> Value raise {
  let mut lo : Value = Nil
  for i in sub.iter() {
    lo = cons(nth(to_int(i), x), lo)
  }
  lo = nreverse(lo)
  let mut hi : Value = Nil
  for i in sup.iter() {
    hi = cons(nth(to_int(i), x), hi)
  }
  hi = nreverse(hi)
  let head = list3(fn_, q_simp, q_array)
  let form = if hi is Nil {
    cons(head, lo)
  } else if b2.truthy() {
    list3(list1(q_mexpt), cons(head, lo), cons(list1(q_mprogn), hi))
  } else {
    cons(list1(q_mexpt), cons(cons(head, lo), hi))
  }
  cons(list2(form, q_simp), nthcdr(to_int(k), x))
}

///|
fn use_float(a : Value) -> Value raise {
  let mut float_found = false
  let mut okay = true
  for x in a.iter() {
    let x = d_rectform(x)
    let xr = d_realpart(x)
    let xi = d_imagpart(x)
    float_found = float_found ||
      floatp(xr) ||
      floatp(xi) ||
      d_bfloatp(xr).truthy() ||
      d_bfloatp(xi).truthy()
    okay = floatp(d_float(xr)) && floatp(d_float(xi))
    if !okay {
      break
    }
  }
  lbool(okay && float_found)
}

///|
fn d_hypergeo11(a : Value, b : Value, x : Value, n : Value) -> (Value, Value) raise {
  if like(x, Fix(0L)).truthy() {
    (Fix(1L), Nil)
  } else if integerp(n) && num_gt(n, Fix(-1L)) {
    if like(a, num_neg(n)).truthy() && use_float(list([b, x])).truthy() {
      hypergeo11_float(
        num_neg(n),
        maxima_to_lisp_complex_float(b),
        maxima_to_lisp_complex_float(x),
      )
    } else {
      let mut sum : Value = Fix(1L)
      let mut cf : Value = Fix(1L)
      let nn = to_int(n)
      for i in 0..<nn {
        cf = div(
          muln_([cf, add2(int(i), a), x]),
          mul2(add2(int(i), b), int(1 + i)),
        )
        sum = add2(cf, sum)
      }
      (sum, Nil)
    }
  } else {
    let index = gensumindex()
    (
      simplify(
        list([
          list1(q_p_sum),
          muln_([
            inv(take(list1(q_mfactorial), [index])),
            take(list1(q_d_pochhammer), [a, index]),
            inv(take(list1(q_d_pochhammer), [b, index])),
            power(x, index),
          ]),
          index,
          Fix(0L),
          n,
        ]),
      ),
      Nil,
    )
  }
}

///|
fn d_hypergeo21(
  a : Value,
  b : Value,
  c : Value,
  x : Value,
  n : Value,
) -> (Value, Value) raise {
  if like(x, Fix(0L)).truthy() {
    (Fix(1L), Nil)
  } else if integerp(n) && num_gt(n, Fix(-1L)) {
    if like(a, num_neg(n)).truthy() && use_float(list([b, c, x])).truthy() {
      hypergeo21_float(
        num_neg(n),
        maxima_to_lisp_complex_float(b),
        maxima_to_lisp_complex_float(c),
        maxima_to_lisp_complex_float(x),
      )
    } else {
      let mut sum : Value = Fix(1L)
      let mut cf : Value = Fix(1L)
      let nn = to_int(n)
      for i in 0..<nn {
        cf = div(
          muln_([cf, add2(int(i), a), add2(int(i), b), x]),
          mul2(int(1 + i), add2(int(i), c)),
        )
        sum = add2(cf, sum)
      }
      (sum, Nil)
    }
  } else {
    let index = gensumindex()
    (
      simplify(
        list([
          list1(q_p_sum),
          muln_([
            take(list1(q_d_pochhammer), [a, index]),
            take(list1(q_d_pochhammer), [b, index]),
            inv(take(list1(q_d_pochhammer), [c, index])),
            inv(take(list1(q_mfactorial), [index])),
            power(x, index),
          ]),
          index,
          Fix(0L),
          n,
        ]),
      ),
      Nil,
    )
  }
}

///|
fn d_pochhammer(x : Value, n : Value) -> Value raise {
  take(list1(q_d_pochhammer), [x, n])
}

///|
/// Numerical evaluation of pochhammer using the bigfloat package.
fn bf_pochhammer(x : Value, n : Value) -> Value raise {
  let mut acc : Value = Fix(1L)
  if bf_lt(n, Fix(0L)) {
    bf_div(Fix(1L), bf_pochhammer(bf_add(x, n), bf_neg(n)))
  } else {
    let mut k : Value = Fix(0L)
    while num_lt(k, n) {
      acc = bf_mul(acc, bf_add(k, x))
      k = num_add(k, Fix(1L))
    }
    acc
  }
}

///|
fn simp_pochhammer(e : Value, y : Value, z : Value) -> Value raise {
  ignore(y)
  twoargcheck(e) |> ignore
  let return_a_rat = d_ratp(second(e))
  let mut x = simplifya(specrepcheck(second(e)), z)
  let mut n = simplifya(specrepcheck(third(e)), z)
  if d_taylorp(second(e)).truthy() || d_taylorp(third(e)).truthy() {
    x = simplifya(second(e), z)
    n = simplifya(third(e), z)
    d_taylor(
      div(take(list1(q_p_gamma), [add2(x, n)]), take(list1(q_p_gamma), [x])),
      Nil,
    )
  } else if eql(n, Fix(0L)) {
    Fix(1L)
  } else if eql(x, Fix(1L)) {
    // pochhammer(1,n) = n!
    take(list1(q_mfactorial), [n])
  } else if integerp(n) && complex_number_p(x, ntypep=q_d_numberp).truthy() {
    // pure numeric evaluation--use numeric package.
    maxima_to(bf_pochhammer(bf_to(x), bf_to(n)))
  } else if integerp(mul2(Fix(2L), n)) &&
    integerp(mul2(Fix(2L), x)) &&
    num_gt(mul2(Fix(2L), n), Fix(0L)) &&
    num_gt(mul2(Fix(2L), x), Fix(0L)) {
    div(take(list1(q_p_gamma), [add2(x, n)]), take(list1(q_p_gamma), [x]))
  } else if great(neg(n), n).truthy() {
    // pochhammer(x,n) = 1/pochhammer(x+n,-n).
    div(Fix(1L), take(list1(q_d_pochhammer), [add2(x, n), neg(n)]))
  } else if integerp(n) &&
    (
      num_lt(num_abs(n), symval(q_d_expop)) ||
      num_lt(num_abs(n), symval(q_d_pochhammer_max_index))
    ) {
    if num_lt(n, Fix(0L)) {
      div(Fix(1L), take(list1(q_d_pochhammer), [add2(x, n), neg(n)]))
    } else {
      let mut acc : Value = Fix(1L)
      if num_lt(num_abs(n), symval(q_d_expop)) || return_a_rat.truthy() {
        acc = d_rat(acc, Nil)
        x = d_rat(x, Nil)
      }
      let mut k : Value = Fix(0L)
      while num_lt(k, n) {
        acc = mul2(acc, add2(k, x))
        k = num_add(k, Fix(1L))
      }
      if return_a_rat.truthy() {
        acc
      } else {
        d_ratdisrep(acc)
      }
    }
  } else {
    mk_simp(q_d_pochhammer, [x, n])
  }
}

///|
fn tex_pochhammer(x : Value, l : Value, r : Value) -> Value raise {
  let x = mapcar(s => tex(s, Nil, Nil, Nil, Nil), cdr(x))
  append_n([
    l,
    list1(Str("\\left(")),
    nth(0, x),
    list1(Str("\\right)_{")),
    nth(1, x),
    list1(Str("}")),
    r,
  ])
}

///|
fn dimension_pochhammer(form : Value, result : Value) -> Value raise {
  let form = list2(
    list3(list2(list1(q_mprogn), nth(1, form)), q_simp, q_array),
    nth(2, form),
  )
  dimension_array(form, result)
}

///|
fn pochhammer_quotient(a : Value, b : Value, x : Value, n : Value) -> Value raise {
  if mminusp(n).truthy() {
    pochhammer_quotient(b, a, x, neg(n))
  } else if integerp(n) && use_float(list([a, b, x])).truthy() {
    let mut acc : Value = Flo(1.0)
    let a = maxima_to_lisp_complex_float(a)
    let b = maxima_to_lisp_complex_float(b)
    let mut i : Value = Fix(0L)
    while num_lt(i, n) {
      acc = num_mul(acc, num_div(num_add(i, a), num_add(i, b)))
      i = num_add(i, Fix(1L))
    }
    lisp_float_to_maxima_float(acc)
  } else {
    div(d_pochhammer(a, n), d_pochhammer(b, n))
  }
}

///|
fn use_hypergeo(n : Value, x : Value) -> Value raise {
  ignore(x)
  if integerp(n) && num_gt(n, Fix(-1L)) {
    t
  } else {
    d_featurep(n, q_d_integer)
  }
}

///|
fn d_jacobi_p(n : Value, a : Value, b : Value, x : Value) -> Value raise {
  if integerp(a) &&
    integerp(n) &&
    num_le(num_neg(n), a) &&
    num_lt(a, Fix(0L)) {
    // For (- n) <= a < 0, avoid problems with (a + k) in denominator of
    // unsimplified expression.
    let a_gensym = gensym(prefix="a")
    d_ratsimp(
      d_substitute(a, a_gensym, expr=d_ratsimp(jacobi_p_1(n, a_gensym, b, x), Nil)),
      Nil,
    )
  } else {
    jacobi_p_1(n, a, b, x)
  }
}

///|
fn jacobi_p_1(n : Value, a : Value, b : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let d = pochhammer_quotient(add2(a, Fix(1L)), Fix(1L), x, n)
    let (f, e) = d_hypergeo21(
      mul2(Fix(-1L), n),
      addn_([n, a, b, Fix(1L)]),
      add2(a, Fix(1L)),
      div(add2(Fix(1L), mul2(Fix(-1L), x)), Fix(2L)),
      n,
    )
    let e = if e.truthy() {
      num_add(
        e,
        share_orthopoly__sbcl_mul4(n, num_abs(f)),
      )
    } else {
      Nil
    }
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_jacobi_p, [n, a, b, x])
  }
}

///|
fn tex_jacobi_poly(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("P"),
    list1(Fix(0L)),
    Nil,
    list2(Fix(1L), Fix(2L)),
    t,
    Fix(3L),
    x,
    l,
    r,
  )
}

///|
fn dimension_jacobi_p(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$p")),
      list1(Fix(1L)),
      list2(Fix(2L), Fix(3L)),
      t,
      Fix(4L),
      form,
    ),
    result,
  )
}

///|
fn d_ultraspherical(n : Value, a : Value, x : Value) -> Value raise {
  // The 2F1 form (A&S 22.5.46) has denominator parameter c = a + 1/2. For a
  // in {-1/2, -3/2, ..., -(2*n-1)/2} the factor (a + 1/2 + k) vanishes in a
  // denominator of the unsimplified expression; evaluate with a gensym in
  // place of a so the removable singularity cancels, then substitute a back.
  let c = add2(a, div(Fix(1L), Fix(2L)))
  if integerp(n) &&
    integerp(c) &&
    num_le(num_sub(Fix(1L), n), c) &&
    num_le(c, Fix(0L)) {
    let a_gensym = gensym(prefix="a")
    d_ratsimp(
      d_substitute(a, a_gensym, expr=d_ratsimp(ultraspherical_1(n, a_gensym, x), Nil)),
      Nil,
    )
  } else {
    ultraspherical_1(n, a, x)
  }
}

///|
fn ultraspherical_1(n : Value, a : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let d = pochhammer_quotient(mul2(Fix(2L), a), Fix(1L), x, n)
    let (f, e) = d_hypergeo21(
      mul2(Fix(-1L), n),
      add2(n, mul2(Fix(2L), a)),
      add2(a, div(Fix(1L), Fix(2L))),
      div(add2(Fix(1L), mul2(Fix(-1L), x)), Fix(2L)),
      n,
    )
    let e = if e.truthy() {
      num_add(
        e,
        share_orthopoly__sbcl_mul4(n, num_abs(f)),
      )
    } else {
      Nil
    }
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_ultraspherical, [n, a, x])
  }
}

///|
fn tex_ultraspherical(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("C"),
    list1(Fix(0L)),
    Nil,
    list1(Fix(1L)),
    t,
    Fix(2L),
    x,
    l,
    r,
  )
}

///|
fn dimension_ultraspherical(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$c")),
      list1(Fix(1L)),
      list1(Fix(2L)),
      t,
      Fix(3L),
      form,
    ),
    result,
  )
}

///|
fn d_chebyshev_t(n : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let (f, e) = d_hypergeo21(
      mul2(Fix(-1L), n),
      n,
      rat(Fix(1L), Fix(2L)),
      div(add2(Fix(1L), mul2(Fix(-1L), x)), Fix(2L)),
      n,
    )
    orthopoly_return_handler(Fix(1L), f, e)
  } else {
    mk_simp(q_d_chebyshev_t, [n, x])
  }
}

///|
fn share_orthopoly__tex1(name : String, x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str(name),
    list1(Fix(0L)),
    Nil,
    Nil,
    Nil,
    Fix(1L),
    x,
    l,
    r,
  )
}

///|
fn share_orthopoly__dim1(name : String, form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case(name)),
      list1(Fix(1L)),
      Nil,
      Nil,
      Fix(2L),
      form,
    ),
    result,
  )
}

///|
fn tex_chebyshev_t(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("T", x, l, r)
}

///|
fn dimension_chebyshev_t(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$t", form, result)
}

///|
/// See A & S 22.5.48, page 779.
fn d_chebyshev_u(n : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let d = add2(Fix(1L), n)
    let (f, e) = d_hypergeo21(
      mul2(Fix(-1L), n),
      add2(Fix(2L), n),
      rat(Fix(3L), Fix(2L)),
      div(add2(Fix(1L), mul2(Fix(-1L), x)), Fix(2L)),
      n,
    )
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_chebyshev_u, [n, x])
  }
}

///|
fn tex_chebyshev_u(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("U", x, l, r)
}

///|
fn dimension_chebyshev_u(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$u", form, result)
}

///|
/// See A&S 8.2.1 page 333 and 22.5.35 page 779.  We evaluate the legendre
/// polynomials as jacobi_p(n,0,0,x).
fn d_legendre_p(n : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    if integerp(n) && num_lt(n, Fix(0L)) {
      d_legendre_p(num_sub(num_abs(n), Fix(1L)), x)
    } else {
      d_jacobi_p(n, Fix(0L), Fix(0L), x)
    }
  } else {
    mk_simp(q_d_legendre_p, [n, x])
  }
}

///|
fn tex_legendre_p(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("P", x, l, r)
}

///|
fn dimension_legendre_p(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$p", form, result)
}

///|
fn d_legendre_q(n : Value, x : Value) -> Value raise {
  if integerp(n) && num_gt(n, Fix(-1L)) {
    d_assoc_legendre_q(n, Fix(0L), x)
  } else {
    mk_simp(q_d_legendre_q, [n, x])
  }
}

///|
fn tex_legendre_q(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("Q", x, l, r)
}

///|
fn dimension_legendre_q(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$q", form, result)
}

///|
fn share_orthopoly__sgn(odd : Bool, a : Int) -> Value {
  if odd {
    int(a)
  } else {
    int(-a)
  }
}

///|
/// Return assoc_legendre(0,m,x).
fn q0m(m : Value, x : Value) -> Value raise {
  if num_lt(m, Fix(0L)) {
    merr("function q0m called with negative order. File a bug report", [])
  } else if num_eq(m, Fix(0L)) {
    div(
      simplify(mk(q_p_log, [div(add2(Fix(1L), x), sub(Fix(1L), x))])),
      Fix(2L),
    )
  } else {
    let odd = share_orthopoly__oddp(m)
    muln_([
      factorial(num_sub(m, Fix(1L))),
      mk_simp(q_rat, [Fix(1L), Fix(2L)]),
      share_orthopoly__sgn(odd, -1),
      power(sub(Fix(1L), mult(x, x)), div(m, Fix(2L))),
      add2(
        mul2(share_orthopoly__sgn(odd, 1), power(add2(Fix(1L), x), neg(m))),
        power(sub(Fix(1L), x), neg(m)),
      ),
    ])
  }
}

///|
/// Return assoc_legendre(1,m,x).
fn q1m(m : Value, x : Value) -> Value raise {
  if num_lt(m, Fix(0L)) {
    merr("function q1m called with negative order. File a bug report", [])
  } else if num_eq(m, Fix(0L)) {
    sub(mul2(x, q0m(Fix(0L), x)), Fix(1L))
  } else if num_eq(m, Fix(1L)) {
    muln_([
      Fix(-1L),
      power(sub(Fix(1L), mult(x, x)), mk_simp(q_rat, [Fix(1L), Fix(2L)])),
      sub(q0m(Fix(0L), x), div(x, sub(mul2(x, x), Fix(1L)))),
    ])
  } else {
    let odd = share_orthopoly__oddp(m)
    muln_([
      share_orthopoly__sgn(odd, -1),
      power(sub(Fix(1L), mult(x, x)), div(m, Fix(2L))),
      add2(
        muln_([
          factorial(num_sub(m, Fix(2L))),
          mk_simp(q_rat, [Fix(1L), Fix(2L)]),
          share_orthopoly__sgn(odd, -1),
          sub(
            power(add2(x, Fix(1L)), sub(Fix(1L), m)),
            power(sub(x, Fix(1L)), sub(Fix(1L), m)),
          ),
        ]),
        muln_([
          factorial(num_sub(m, Fix(1L))),
          mk_simp(q_rat, [Fix(1L), Fix(2L)]),
          share_orthopoly__sgn(odd, -1),
          add2(power(add2(x, Fix(1L)), neg(m)), power(sub(x, Fix(1L)), neg(m))),
        ]),
      ),
    ])
  }
}

///|
/// Return assoc_legendre_q(n,n,x).  After the loop,
/// q = int(1/(1-t^2)^(n+1),t,0,x).
fn assoc_legendre_q_nn(n : Value, x : Value) -> Value raise {
  let z = sub(Fix(1L), mul2(x, x))
  let mut i : Value = Fix(1L)
  let mut q = div(
    simplify(mk(q_p_log, [div(add2(Fix(1L), x), sub(Fix(1L), x))])),
    Fix(2L),
  )
  while num_le(i, n) {
    q = add2(
      mul2(sub(Fix(1L), mk(q_rat, [Fix(1L), num_mul(Fix(2L), i)])), q),
      div(x, muln_([Fix(2L), i, power(z, i)])),
    )
    i = num_add(i, Fix(1L))
  }
  muln_([expt(Fix(-2L), n), factorial(n), power(z, div(n, Fix(2L))), q])
}

///|
/// Use degree recursion to find the assoc_legendre_q function.
/// See A&S 8.5.3. For negative order, see A&S 8.2.6.
fn d_assoc_legendre_q(n : Value, m : Value, x : Value) -> Value raise {
  if integerp(n) &&
    num_gt(n, Fix(-1L)) &&
    integerp(m) &&
    num_le(num_abs(m), n) {
    if num_lt(m, Fix(0L)) {
      mul2(
        div(factorial(num_add(n, m)), factorial(num_sub(n, m))),
        d_assoc_legendre_q(n, num_neg(m), x),
      )
    } else {
      let mut x = x
      if !(floatp(x) || d_bfloatp(x).truthy()) {
        x = d_rat(x, Nil)
      }
      let mut q0 = q0m(m, x)
      let mut q1 = if num_eq(n, Fix(0L)) { q0 } else { q1m(m, x) }
      let mut i : Value = Fix(2L)
      let use_rat = d_ratp(x).truthy() || floatp(x) || d_bfloatp(x).truthy()
      while num_le(i, n) {
        let q = if num_eq(i, m) {
          assoc_legendre_q_nn(i, x)
        } else {
          div(
            sub(
              muln_([num_sub(num_mul(Fix(2L), i), Fix(1L)), x, q1]),
              mul2(num_add(num_add(i, Fix(-1L)), m), q0),
            ),
            num_sub(i, m),
          )
        }
        q0 = q1
        q1 = q
        i = num_add(i, Fix(1L))
      }
      if use_rat {
        q1
      } else {
        d_ratsimp(q1, Nil)
      }
    }
  } else {
    mk_simp(q_d_assoc_legendre_q, [n, m, x])
  }
}

///|
fn tex_assoc_legendre_q(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("Q"),
    list1(Fix(0L)),
    Nil,
    list1(Fix(1L)),
    Nil,
    Fix(2L),
    x,
    l,
    r,
  )
}

///|
fn dimension_assoc_legendre_q(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$q")),
      list1(Fix(1L)),
      list1(Fix(2L)),
      Nil,
      Fix(3L),
      form,
    ),
    result,
  )
}

///|
/// See A & S 22.5.37 page 779, A & S 8.6.6 (second equation) page 334, and
/// A & S 8.2.5 page 333.  For n < 0, see A&S 8.2.1 page 333.
fn d_assoc_legendre_p(n : Value, m : Value, x : Value) -> Value raise {
  let mut f : Value = Nil
  let mut d : Value = Nil
  let mut dx = 0
  if integerp(n) && integerp(m) {
    if num_lt(n, Fix(0L)) {
      f = d_assoc_legendre_p(num_sub(num_abs(n), Fix(1L)), m, x)
      d = Fix(1L)
      dx = 1
    } else if num_gt(num_abs(m), n) {
      f = Fix(0L)
      d = Fix(1L)
    } else if num_lt(m, Fix(0L)) {
      f = d_assoc_legendre_p(n, neg(m), x)
      // A factor (-1)^m gives the expected results for odd negative m.
      d = mul2(
        power(Fix(-1L), m),
        div(factorial(num_add(n, m)), factorial(num_sub(n, m))),
      )
      dx = 1
    } else {
      if eql(m, Fix(0L)) {
        d = Fix(1L)
      } else {
        d = simplify(
          mk(q_p_genfact, [
            num_sub(num_mul(Fix(2L), m), Fix(1L)),
            num_sub(m, Fix(1L)),
            Fix(2L),
          ]),
        )
        d = mul2(d, if oddp(m) { Fix(-1L) } else { Fix(1L) })
        d = mul2(d, power(sub(Fix(1L), mul2(x, x)), div(m, Fix(2L))))
      }
      dx = 4
      f = d_ultraspherical(
        num_sub(n, m),
        add2(m, rat(Fix(1L), Fix(2L))),
        x,
      )
    }
  } else {
    d = Fix(1L)
    f = mk_simp(q_d_assoc_legendre_p, [n, m, x])
  }
  interval_mult(d, f, dx=num_mul(share_orthopoly__eps(), int(dx)))
}

///|
fn tex_assoc_legendre_p(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("P"),
    list1(Fix(0L)),
    Nil,
    list1(Fix(1L)),
    Nil,
    Fix(2L),
    x,
    l,
    r,
  )
}

///|
fn dimension_assoc_legendre_p(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$p")),
      list1(Fix(1L)),
      list1(Fix(2L)),
      Nil,
      Fix(3L),
      form,
    ),
    result,
  )
}

///|
/// See A&S 22.5.55 and 22.5.56, page 780.
fn d_hermite(n : Value, x : Value) -> Value raise {
  if integerp(n) {
    let mut f : Value = Nil
    let mut d : Value = Nil
    let mut e : Value = Nil
    let mut n = n
    if d_evenp(n).truthy() {
      n = num_div(n, Fix(2L))
      let (f1, e1) = d_hypergeo11(
        num_neg(n),
        rat(Fix(1L), Fix(2L)),
        mul2(x, x),
        n,
      )
      f = f1
      e = e1
      d = muln_([
        if oddp(n) { Fix(-1L) } else { Fix(1L) },
        factorial(num_mul(Fix(2L), n)),
        div(Fix(1L), factorial(n)),
      ])
    } else if d_oddp(n).truthy() {
      n = num_div(num_sub(n, Fix(1L)), Fix(2L))
      let (f1, e1) = d_hypergeo11(
        num_neg(n),
        rat(Fix(3L), Fix(2L)),
        mul2(x, x),
        n,
      )
      f = f1
      e = e1
      d = muln_([
        if oddp(n) { Fix(-1L) } else { Fix(1L) },
        factorial(num_add(Fix(1L), num_mul(Fix(2L), n))),
        Fix(2L),
        x,
        div(Fix(1L), factorial(n)),
      ])
    }
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_hermite, [n, x])
  }
}

///|
fn tex_hermite(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("H", x, l, r)
}

///|
fn dimension_hermite(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$h", form, result)
}

///|
/// See A & S 22.5.54, page 780.
fn d_gen_laguerre(n : Value, a : Value, x : Value) -> Value raise {
  if integerp(a) &&
    integerp(n) &&
    num_le(num_neg(n), a) &&
    num_lt(a, Fix(0L)) {
    let a_gensym = gensym(prefix="a")
    d_ratsimp(
      d_substitute(a, a_gensym, expr=d_ratsimp(gen_laguerre_1(n, a_gensym, x), Nil)),
      Nil,
    )
  } else {
    gen_laguerre_1(n, a, x)
  }
}

///|
fn gen_laguerre_1(n : Value, a : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let d = pochhammer_quotient(add2(a, Fix(1L)), Fix(1L), x, n)
    let (f, e) = d_hypergeo11(mul2(Fix(-1L), n), add2(Fix(1L), a), x, n)
    let e = if e.truthy() {
      num_add(
        e,
        share_orthopoly__sbcl_mul4(num_abs(f), n),
      )
    } else {
      Nil
    }
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_gen_laguerre, [n, a, x])
  }
}

///|
fn tex_gen_laguerre(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("L"),
    list1(Fix(0L)),
    Nil,
    list1(Fix(1L)),
    t,
    Fix(2L),
    x,
    l,
    r,
  )
}

///|
fn dimension_gen_laguerre(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$l")),
      list1(Fix(1L)),
      list1(Fix(2L)),
      t,
      Fix(3L),
      form,
    ),
    result,
  )
}

///|
/// See A & S 22.5.16, page 778.
fn d_laguerre(n : Value, x : Value) -> Value raise {
  if use_hypergeo(n, x).truthy() {
    let (f, e) = d_hypergeo11(mul2(Fix(-1L), n), Fix(1L), x, n)
    orthopoly_return_handler(Fix(1L), f, e)
  } else {
    mk_simp(q_d_laguerre, [n, x])
  }
}

///|
fn tex_laguerre(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("L", x, l, r)
}

///|
fn dimension_laguerre(form : Value, result : Value) -> Value raise {
  share_orthopoly__dim1("$l", form, result)
}

///|
fn d_spherical_hankel1(n : Value, x : Value) -> Value raise {
  if integerp(n) && num_lt(n, Fix(0L)) {
    let d = mul2(q_d__pcti, if oddp(n) { Fix(1L) } else { Fix(-1L) })
    // The recursive call returns a single value, so e is nil.
    let f = d_spherical_hankel1(add2(Fix(-1L), mul2(Fix(-1L), n)), x)
    orthopoly_return_handler(d, f, Nil)
  } else if use_hypergeo(n, x).truthy() {
    let (f, e) = d_hypergeo11(
      mul2(Fix(-1L), n),
      mul2(Fix(-2L), n),
      muln_([Fix(-2L), q_d__pcti, x]),
      n,
    )
    let d = muln_([
      q_d__pcti,
      if num_eq(Fix(0L), n) {
        Fix(1L)
      } else {
        simplify(
          mk(q_p_genfact, [
            add2(mul2(Fix(2L), n), Fix(-1L)),
            add2(n, rat(Fix(-1L), Fix(2L))),
            Fix(2L),
          ]),
        )
      },
      power(q_d__pcte, mul2(q_d__pcti, x)),
      div(Fix(-1L), power(x, add2(Fix(1L), n))),
    ])
    orthopoly_return_handler(d, f, e)
  } else {
    mk_simp(q_d_spherical_hankel1, [n, x])
  }
}

///|
fn tex_spherical_hankel_1(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("h^{(1)}", x, l, r)
}

///|
fn dimension_spherical_hankel_1(form : Value, result : Value) -> Value raise {
  let form1 = list3(
    list1(q_mexpt),
    list2(list3(sym(invert_case("$h")), q_simp, q_array), nth(1, form)),
    list1(Fix(1L)),
  )
  dimension_function(list2(list2(form1, q_simp), nth(2, form)), result)
}

///|
/// See A & S 10.1.36.
fn d_spherical_hankel2(n : Value, x : Value) -> Value raise {
  if integerp(n) {
    let x = mul2(
      x,
      power(
        q_d__pcte,
        muln_([q_d__pcti, q_d__pctpi, add2(mul2(Fix(2L), n), Fix(1L))]),
      ),
    )
    let f = d_spherical_hankel1(n, x)
    if oddp(n) {
      interval_mult(Fix(-1L), f)
    } else {
      f
    }
  } else {
    mk_simp(q_d_spherical_hankel2, [n, x])
  }
}

///|
fn tex_spherical_hankel_2(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("h^{(2)}", x, l, r)
}

///|
fn dimension_spherical_hankel_2(form : Value, result : Value) -> Value raise {
  let form1 = list3(
    list1(q_mexpt),
    list2(list3(sym(invert_case("$h")), q_simp, q_array), nth(1, form)),
    list1(Fix(2L)),
  )
  dimension_function(list2(list2(form1, q_simp), nth(2, form)), result)
}

///|
/// See A&S 10.1.8 and 10.1.9 page 437.
fn p__fun(n : Value, x : Value) -> Value raise {
  let mut s : Value = Fix(1L)
  let mut w : Value = Fix(1L)
  let n1 = floor1(num_div(n, Fix(2L)))
  let x2 = mul2(x, x)
  let mut m : Value = Fix(0L)
  while num_lt(m, n1) {
    let m2 = num_mul(Fix(2L), m)
    let num = num_prod([
      Fix(-1L),
      num_add(num_add(n, m2), Fix(2L)),
      num_add(num_add(n, m2), Fix(1L)),
      num_sub(n, m2),
      num_sub(n, num_add(m2, Fix(1L))),
    ])
    let den = num_prod([
      Fix(4L),
      num_add(m2, Fix(1L)),
      num_add(m2, Fix(2L)),
    ])
    w = div(mul2(w, div(num, den)), x2)
    s = add2(s, w)
    m = num_add(m, Fix(1L))
  }
  s
}

///|
fn q__fun(n : Value, x : Value) -> Value raise {
  let mut s : Value = if num_eq(Fix(0L), n) { Fix(0L) } else { Fix(1L) }
  let mut w : Value = Fix(1L)
  let x2 = mul2(x, x)
  let n1 = floor1(num_div(num_sub(n, Fix(1L)), Fix(2L)))
  let mut m : Value = Fix(0L)
  while num_lt(m, n1) {
    let m2 = num_mul(Fix(2L), m)
    let num = num_prod([
      Fix(-1L),
      num_add(num_add(n, m2), Fix(3L)),
      num_add(num_add(n, m2), Fix(2L)),
      num_sub(n, num_add(m2, Fix(1L))),
      num_sub(n, num_add(m2, Fix(2L))),
    ])
    let den = num_prod([
      Fix(4L),
      num_add(m2, Fix(3L)),
      num_add(m2, Fix(2L)),
    ])
    w = div(mul2(w, div(num, den)), x2)
    s = add2(s, w)
    m = num_add(m, Fix(1L))
  }
  div(muln_([n, num_add(n, Fix(1L)), s]), mul2(Fix(2L), x))
}

///|
/// Shared float branch of spherical_bessel_j/y: d0 is the sign factor used
/// when the real part of x is negative.
fn share_orthopoly__sph_float(
  n : Value,
  x : Value,
  odd_sign : Value,
  even_sign : Value,
  bessel : Value,
) -> Value raise {
  let mut d : Value = Fix(1L)
  let mut x = d_rectform(d_float(x))
  let xr = d_realpart(x)
  let xi = d_imagpart(x)
  let mut z = complex(xr, i=xi)
  if num_lt(xr, Flo(0.0)) {
    d = if oddp(n) { odd_sign } else { even_sign }
    x = mul2(Fix(-1L), x)
    z = num_mul(Fix(-1L), z)
  }
  let n = num_add(Flo(0.5), d_float(n))
  d = num_mul(d, lsqrt(num_div(share_orthopoly__pi, num_mul(Fix(2L), z))))
  d = lisp_float_to_maxima_float(d)
  d_expand(mul2(d_rectform(d), funcall(bessel, [n, x])))
}

///|
/// See A&S 10.1.8 page 437 and A&S 10.1.15 page 439; for the analytic
/// continuation, A&S 10.1.34.
fn d_spherical_bessel_j(n : Value, x : Value) -> Value raise {
  if eq(q_d_zero, csign(d_ratdisrep(x))) &&
    (integerp(n) || d_featurep(n, q_d_integer).truthy()) {
    mk(q_p_kron_delta, [Fix(0L), n])
  } else if use_float(list1(x)).truthy() && integerp(n) {
    share_orthopoly__sph_float(n, x, Fix(-1L), Fix(1L), q_d_bessel_j)
  } else if integerp(n) && num_gt(n, Fix(-1L)) {
    let xt = sub(x, div(mul2(n, q_d__pctpi), Fix(2L)))
    div(
      add2(
        mul2(p__fun(n, x), simplify(mk(q_p_sin, [xt]))),
        mul2(q__fun(n, x), simplify(mk(q_p_cos, [xt]))),
      ),
      x,
    )
  } else if integerp(n) {
    mul2(
      if oddp(n) { Fix(-1L) } else { Fix(1L) },
      d_spherical_bessel_y(num_neg(num_add(n, Fix(1L))), x),
    )
  } else {
    mk_simp(q_d_spherical_bessel_j, [n, x])
  }
}

///|
fn tex_spherical_bessel_j(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("j^{(2)}", x, l, r)
}

///|
fn dimension_spherical_bessel_j(form : Value, result : Value) -> Value raise {
  let form1 = list2(list3(sym(invert_case("$j")), q_simp, q_array), nth(1, form))
  dimension_function(list2(list2(form1, q_simp), nth(2, form)), result)
}

///|
/// For analytic continuation, see A&S 10.1.35.
fn d_spherical_bessel_y(n : Value, x : Value) -> Value raise {
  if use_float(list1(x)).truthy() && integerp(n) {
    share_orthopoly__sph_float(n, x, Fix(1L), Fix(-1L), q_d_bessel_y)
  } else if integerp(n) && num_gt(n, Fix(-1L)) {
    let xt = add2(x, div(mul2(n, q_d__pctpi), Fix(2L)))
    mul2(
      if oddp(n) { Fix(1L) } else { Fix(-1L) },
      div(
        sub(
          mul2(p__fun(n, x), simplify(mk(q_p_cos, [xt]))),
          mul2(q__fun(n, x), simplify(mk(q_p_sin, [xt]))),
        ),
        x,
      ),
    )
  } else if integerp(n) {
    mul2(
      if oddp(n) { Fix(1L) } else { Fix(-1L) },
      d_spherical_bessel_j(num_neg(num_add(n, Fix(1L))), x),
    )
  } else {
    mk_simp(q_d_spherical_bessel_y, [n, x])
  }
}

///|
fn tex_spherical_bessel_y(x : Value, l : Value, r : Value) -> Value raise {
  share_orthopoly__tex1("y^{(2)}", x, l, r)
}

///|
fn dimension_spherical_bessel_y(form : Value, result : Value) -> Value raise {
  let form1 = list2(list3(sym(invert_case("$y")), q_simp, q_array), nth(1, form))
  dimension_function(list2(list2(form1, q_simp), nth(2, form)), result)
}

///|
/// Compute P_n^m(cos(theta)).  See Merzbacher, 9.59 page 184 and 9.64 page
/// 185, and A & S 22.5.37 page 779.  The factors (1 - cos^2(x))^(m/2) are
/// written as sin^m(x) rather than |sin(x)|^m.
fn assoc_leg_cos(n : Value, m : Value, x : Value) -> Value raise {
  interval_mult(
    if num_eq(m, Fix(0L)) {
      Fix(1L)
    } else {
      mul2(
        take(list1(q_p_genfact), [
          sub(mul2(Fix(2L), m), Fix(1L)),
          sub(m, div(Fix(1L), Fix(2L))),
          Fix(2L),
        ]),
        power(take(list1(q_p_sin), [x]), m),
      )
    },
    d_ultraspherical(
      sub(n, m),
      add2(m, div(Fix(1L), Fix(2L))),
      take(list1(q_p_cos), [x]),
    ),
  )
}

///|
fn d_spherical_harmonic(n : Value, m : Value, th : Value, p : Value) -> Value raise {
  if integerp(n) && integerp(m) && num_gt(n, Fix(-1L)) {
    if num_gt(num_abs(m), n) {
      Fix(0L)
    } else if num_lt(m, Fix(0L)) {
      interval_mult(
        if oddp(m) { Fix(-1L) } else { Fix(1L) },
        d_spherical_harmonic(n, num_neg(m), th, mul2(Fix(-1L), p)),
      )
    } else {
      interval_mult(
        mul2(
          d_exp(muln_([q_d__pcti, m, p])),
          power(
            div(
              num_mul(
                num_add(num_mul(Fix(2L), n), Fix(1L)),
                factorial(num_sub(n, m)),
              ),
              mul2(q_d__pctpi, num_mul(Fix(4L), factorial(num_add(n, m)))),
            ),
            mk(q_rat, [Fix(1L), Fix(2L)]),
          ),
        ),
        assoc_leg_cos(n, m, th),
      )
    }
  } else {
    mk_simp(q_d_spherical_harmonic, [n, m, th, p])
  }
}

///|
fn tex_spherical_harmonic(x : Value, l : Value, r : Value) -> Value raise {
  tex_sub_and_super_scripted_function(
    Str("Y"),
    list1(Fix(0L)),
    Nil,
    list1(Fix(1L)),
    Nil,
    Fix(2L),
    x,
    l,
    r,
  )
}

///|
fn dimension_spherical_harmonic(form : Value, result : Value) -> Value raise {
  dimension_function(
    dimension_sub_and_super_scripted_function(
      sym(invert_case("$y")),
      list1(Fix(1L)),
      list1(Fix(2L)),
      Nil,
      Fix(3L),
      form,
    ),
    result,
  )
}

///|
fn maxima_float_to_lisp_float(y : Value) -> Value raise {
  let x = d_rectform(y)
  let xr = d_realpart(x)
  let xi = d_imagpart(x)
  if floatp(xr) || floatp(xi) {
    let xr = lfloat(xr)
    let xi = lfloat(xi)
    if num_eq(Flo(0.0), xi) {
      xr
    } else {
      complex(xr, i=xi)
    }
  } else {
    y
  }
}

///|
fn lisp_float_to_maxima_float(x : Value) -> Value raise {
  if complexp(x) {
    add2(realpart(x), mul2(q_d__pcti, imagpart(x)))
  } else {
    x
  }
}

///|
fn hypergeo11_float(n : Value, b : Value, x : Value) -> (Value, Value) raise {
  let size = to_int(num_sub(Fix(1L), n))
  let as_ : Array[Value] = Array::make(size, Flo(0.0))
  let bs : Array[Value] = Array::make(size, Flo(0.0))
  let fs : Array[Value] = Array::make(size, Flo(0.0))
  let mut f0 : Value = Flo(1.0)
  let mut fm1 : Value = Flo(0.0)
  let x = num_sub(b, x)
  let n = to_int(num_neg(n))
  let mut i = 0
  while i < n {
    fs[i] = f0
    let dk = num_add(b, int(i))
    let ak = num_div(num_add(int(2 * i), x), dk)
    let bk = num_div(int(-i), dk)
    let f = num_add(num_mul(ak, f0), num_mul(bk, fm1))
    as_[i] = ak
    bs[i] = bk
    fm1 = f0
    f0 = f
    i += 1
  }
  fs[i] = f0
  i = 1
  let mut err : Value = Flo(1.0)
  let mut u0 : Value = Flo(1.0)
  let mut um1 : Value = Flo(0.0)
  while i < n {
    let k = n - i
    let u = num_add(num_mul(as_[k], u0), num_mul(bs[k + 1], um1))
    um1 = u0
    u0 = u
    err = num_add(err, num_abs(num_mul(u0, fs[k])))
    i += 1
  }
  (f0, num_mul(num_mul(Fix(12L), share_orthopoly__eps()), err))
}

///|
fn hypergeo21_float(n : Value, b : Value, c : Value, x : Value) -> (Value, Value) raise {
  let size = to_int(num_sub(Fix(1L), n))
  let as_ : Array[Value] = Array::make(size, Flo(0.0))
  let bs : Array[Value] = Array::make(size, Flo(0.0))
  let fs : Array[Value] = Array::make(size, Flo(0.0))
  let mut f0 : Value = Flo(1.0)
  let mut fm1 : Value = Flo(0.0)
  let n = to_int(num_neg(n))
  let mut i = 0
  while i < n {
    fs[i] = f0
    let dk = num_add(c, int(i))
    let ak = num_div(
      num_add(
        num_add(int(2 * i), c),
        num_neg(num_mul(x, num_add(b, int(i)))),
      ),
      dk,
    )
    let bk = num_div(num_mul(int(i), num_sub(x, Fix(1L))), dk)
    let f = num_add(num_mul(ak, f0), num_mul(bk, fm1))
    as_[i] = ak
    bs[i] = bk
    fm1 = f0
    f0 = f
    i += 1
  }
  fs[i] = f0
  i = 1
  let mut err : Value = Flo(1.0)
  let mut u0 : Value = Flo(1.0)
  let mut um1 : Value = Flo(0.0)
  while i < n {
    let k = n - i
    let u = num_add(num_mul(as_[k], u0), num_mul(bs[k + 1], um1))
    um1 = u0
    u0 = u
    i += 1
    err = num_add(err, num_abs(num_mul(fs[k], u0)))
  }
  (f0, num_mul(num_mul(Fix(12L), share_orthopoly__eps()), err))
}

///|
fn check_arg_length(fn_ : Value, n : Value, m : Value) -> Value raise {
  if !num_eq(n, m) {
    merr("Function ~:M needs ~:M arguments, instead it received ~:M", [
      fn_, n, m,
    ])
  } else {
    Nil
  }
}

///|
fn share_orthopoly__nargs(arg : Value) -> Value {
  int(length(arg) - 1)
}

///|
fn d_orthopoly_recur(fn_ : Value, arg : Value) -> Value raise {
  if !d_listp(arg).truthy() {
    merr("The second argument to orthopoly_recur must be a list", []) |> ignore
  }
  if eq(fn_, q_d_jacobi_p) {
    check_arg_length(fn_, Fix(4L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) (($jacobi_p) ((mplus) 1 pn) pa pb px) ((mtimes) ((rat) 1 2) ((mexpt) ((mplus) 1 pn) -1) ((mexpt) ((mplus) 1 pa pb pn) -1) ((mexpt) ((mplus) pa pb ((mtimes) 2 pn)) -1) ((mplus) ((mtimes) -2 ((mplus) pa pn) ((mplus) pb pn) ((mplus) 2 pa pb ((mtimes) 2 pn)) (($jacobi_p) ((mplus) -1 pn) pa pb px)) ((mtimes) (($jacobi_p) pn pa pb px) ((mplus) ((mtimes) ((mplus) ((mexpt) pa 2) ((mtimes) -1 ((mexpt) pb 2))) ((mplus) 1 pa pb ((mtimes) 2 pn))) ((mtimes) ((mplus) pa pb ((mtimes) 2 pn)) ((mplus) 1 pa pb ((mtimes) 2 pn)) ((mplus) 2 pa pb ((mtimes) 2 pn)) px))))))",
        [
          ("pn", nth(1, arg)),
          ("pa", nth(2, arg)),
          ("pb", nth(3, arg)),
          ("px", nth(4, arg)),
        ],
      ),
    )
  } else if eq(fn_, q_d_ultraspherical) {
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) (($ultraspherical) ((mplus) 1 pn) pa px) ((mtimes) ((mexpt) ((mplus) 1 pn) -1) ((mplus) ((mtimes) -1 ((mplus) -1 ((mtimes) 2 pa) pn) (($ultraspherical) ((mplus) -1 pn) pa px)) ((mtimes) 2 ((mplus) pa pn) (($ultraspherical) pn pa px) px))))",
        [("pn", nth(1, arg)), ("pa", nth(2, arg)), ("px", nth(3, arg))],
      ),
    )
  } else if eq(fn_, q_d_chebyshev_t) || eq(fn_, q_d_chebyshev_u) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) ((pfn) ((mplus) 1 pn) px) ((mplus) ((mtimes) -1 ((pfn) ((mplus) -1 pn) px)) ((mtimes) 2 ((pfn) pn px) px)))",
        [("pfn", fn_), ("pn", nth(1, arg)), ("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_legendre_p) || eq(fn_, q_d_legendre_q) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    let n = nth(1, arg)
    let x = nth(2, arg)
    let z = if eq(fn_, q_d_legendre_q) {
      mk(q_mtimes, [Fix(-1L), mk(q_p_kron_delta, [n, Fix(0L)])])
    } else {
      Fix(0L)
    }
    simplify(
      share_orthopoly__tmpl(
        "((mequal) ((pfn) ((mplus) 1 pn) px) ((mplus) ((mtimes) ((mexpt) ((mplus) 1 pn) -1) ((mplus) ((mtimes) ((mtimes) -1 pn) ((pfn) ((mplus) -1 pn) px)) ((mtimes) ((mplus) 1 ((mtimes) 2 pn)) ((pfn) pn px) px))) pz))",
        [("pfn", fn_), ("pn", n), ("px", x), ("pz", z)],
      ),
    )
  } else if eq(fn_, q_d_assoc_legendre_p) || eq(fn_, q_d_assoc_legendre_q) {
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) ((pfn) ((mplus) 1 pn) pm px) ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 pm) pn) -1) ((mplus) ((mtimes) ((mplus) ((mtimes) -1 pm) ((mtimes) -1 pn)) ((pfn) ((mplus) -1 pn) pm px)) ((mtimes) ((mplus) 1 ((mtimes) 2 pn)) ((pfn) pn pm px) px))))",
        [
          ("pfn", fn_),
          ("pn", nth(1, arg)),
          ("pm", nth(2, arg)),
          ("px", nth(3, arg)),
        ],
      ),
    )
  } else if eq(fn_, q_d_laguerre) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) (($laguerre) ((mplus) 1 pn) px) ((mtimes) ((mexpt) ((mplus) 1 pn) -1) ((mplus) ((mtimes) -1 pn (($laguerre) ((mplus) -1 pn) px)) ((mtimes) (($laguerre) pn px) ((mplus) 1 ((mtimes) 2 pn) ((mtimes) -1 px))))))",
        [("pn", nth(1, arg)), ("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_gen_laguerre) {
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) (($gen_laguerre) ((mplus) 1 pn) pa px) ((mtimes) ((mexpt) ((mplus) 1 pn) -1) ((mplus) ((mtimes) -1 ((mplus) pa pn) (($gen_laguerre) ((mplus) -1 pn) pa px)) ((mtimes) (($gen_laguerre) pn pa px) ((mplus) 1 pa ((mtimes) 2 pn) ((mtimes) -1 px))))))",
        [("pn", nth(1, arg)), ("pa", nth(2, arg)), ("px", nth(3, arg))],
      ),
    )
  } else if eq(fn_, q_d_hermite) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) (($hermite) ((mplus) 1 pn) px) ((mplus) ((mtimes) -2 pn (($hermite) ((mplus) -1 pn) px)) ((mtimes) 2 (($hermite) pn px) px)))",
        [("pn", nth(1, arg)), ("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_spherical_bessel_j) ||
    eq(fn_, q_d_spherical_bessel_y) ||
    eq(fn_, q_d_spherical_hankel1) ||
    eq(fn_, q_d_spherical_hankel2) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mequal) ((pfn) ((mplus) 1 pn) px) ((mplus) ((mtimes) -1 ((pfn) ((mplus) -1 pn) px)) ((mtimes) ((pfn) pn px) ((mexpt) px -1)) ((mtimes) 2 pn ((pfn) pn px) ((mexpt) px -1))))",
        [("pfn", fn_), ("pn", nth(1, arg)), ("px", nth(2, arg))],
      ),
    )
  } else {
    merr("A recursion relation for ~:M isn't known to Maxima", [fn_])
  }
}

///|
/// See A & S Table 22.2, page 774.
fn d_orthopoly_weight(fn_ : Value, arg : Value) -> Value raise {
  if !d_listp(arg).truthy() {
    merr("The second argument to orthopoly_weight must be a list", []) |> ignore
  }
  let v = car(last(arg))
  if !(d_symbolp(v).truthy() || d_subvarp(v).truthy()) {
    merr(
      "The last element of the second argument to orthopoly_weight must\nbe a symbol or a subscripted symbol, instead found ~:M",
      [v],
    )
    |> ignore
  }
  if !every(s => d_freeof(list2(car(last(arg)), s)).truthy(), butlast(cdr(arg))) {
    merr(
      "Only the last element of ~:M may depend on the integration\nvariable ~:M",
      [arg, car(last(arg))],
    )
    |> ignore
  }
  if eq(fn_, q_d_jacobi_p) {
    check_arg_length(fn_, Fix(4L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) -1 px)) pa) ((mexpt) ((mplus) 1 px) pb)) -1 1)",
        [("pa", nth(2, arg)), ("pb", nth(3, arg)), ("px", nth(4, arg))],
      ),
    )
  } else if eq(fn_, q_d_ultraspherical) {
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) px 2))) ((mplus) ((rat) -1 2) pa)) -1 1)",
        [("pa", nth(2, arg)), ("px", nth(3, arg))],
      ),
    )
  } else if eq(fn_, q_d_chebyshev_t) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) px 2))) ((rat) -1 2)) -1 1)",
        [("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_chebyshev_u) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) px 2))) ((rat) 1 2)) -1 1)",
        [("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_legendre_p) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    list([list1(q_mlist), Fix(1L), Fix(-1L), Fix(1L)])
  } else if eq(fn_, q_d_assoc_legendre_p) {
    // This is for a fixed order.  There is also an orthogonality condition
    // for fixed degree with weight function 1/(1-x^2); see A & S 8.14.11
    // and 8.14.12.
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    list([list1(q_mlist), Fix(1L), Fix(-1L), Fix(1L)])
  } else if eq(fn_, q_d_laguerre) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mexpt) $%e ((mtimes) -1 px)) 0 $inf)",
        [("px", nth(2, arg))],
      ),
    )
  } else if eq(fn_, q_d_gen_laguerre) {
    check_arg_length(fn_, Fix(3L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mtimes) ((mexpt) px pa) ((mexpt) $%e ((mtimes) -1 px))) 0 $inf)",
        [("pa", nth(2, arg)), ("px", nth(3, arg))],
      ),
    )
  } else if eq(fn_, q_d_hermite) {
    check_arg_length(fn_, Fix(2L), share_orthopoly__nargs(arg)) |> ignore
    simplify(
      share_orthopoly__tmpl(
        "((mlist) ((mexpt) $%e ((mtimes) -1 ((mexpt) px 2))) ((mtimes) -1 $inf) $inf)",
        [("px", nth(2, arg))],
      ),
    )
  } else {
    merr("A weight for ~:M isn't known to Maxima", [fn_])
  }
}

///|
fn share_orthopoly__grad(f : Value, s : String) -> Unit raise {
  putprop(f, lread(s), q_grad) |> ignore
}

///|
fn init_share_orthopoly() -> Unit raise {
  d_put(q_d_orthopoly, Flo(1.0), q_d_version) |> ignore
  putprop(q_unk, q_simp_unk, q_operators) |> ignore
  putprop(q_d_unit_step, Str("\\Theta"), q_texword) |> ignore
  // This disallows noninteger assignments to $pochhammer_max_index.
  setf_get(
    q_d_pochhammer_max_index,
    q_assign,
    lfunc("pochhammer_max_index-assign", args => {
      let b = args[1]
      if !(atom(b) && integerp(b)) {
        mtell(
          list1(Str("The value of `pochhammer_max_index' must be an integer.~%")),
        )
        |> ignore
        q_munbindp
      } else {
        Nil
      }
    }),
  )
  |> ignore
  share_orthopoly__grad(
    q_d_pochhammer,
    "((x n) ((mtimes) (($pochhammer) x n) ((mplus) ((mtimes) -1 ((mqapply) (($psi array) 0) x)) ((mqapply) (($psi array) 0) ((mplus) n x)))) ((mtimes) (($pochhammer) x n) ((mqapply) (($psi array) 0) ((mplus) n x))))",
  )
  putprop(q_d_pochhammer, q_tex_pochhammer, q_tex) |> ignore
  setf_get(q_d_pochhammer, q_dimension, q_dimension_pochhammer) |> ignore
  share_orthopoly__grad(
    q_d_jacobi_p,
    "((n a b x) ((unk) first jacobi_p) ((unk) second jacobi_p) ((unk) third jacobi_p) ((mtimes) ((mexpt) ((mplus) a b ((mtimes) 2 n)) -1) ((mplus) ((mtimes) 2 (($unit_step) n) ((mplus) a n) ((mplus) b n) (($jacobi_p) ((mplus) -1 n) a b x)) ((mtimes) n (($jacobi_p) n a b x) ((mplus) a ((mtimes) -1 b) ((mtimes) ((mplus) ((mtimes) -1 a) ((mtimes) -1 b) ((mtimes) -2 n)) x)))) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))",
  )
  putprop(q_d_jacobi_p, q_tex_jacobi_poly, q_tex) |> ignore
  setf_get(q_d_jacobi_p, q_dimension, q_dimension_jacobi_p) |> ignore
  share_orthopoly__grad(
    q_d_ultraspherical,
    "((n a x) ((unk) first ultraspherical) ((unk) second ultrapsherical) ((mtimes) ((mplus) ((mtimes) (($unit_step) n) ((mplus) -1 ((mtimes) 2 a) n) (($ultraspherical) ((mplus) -1 n) a x)) ((mtimes) -1 n (($ultraspherical) n a x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))",
  )
  putprop(q_d_ultraspherical, q_tex_ultraspherical, q_tex) |> ignore
  setf_get(q_d_ultraspherical, q_dimension, q_dimension_ultraspherical)
  |> ignore
  share_orthopoly__grad(
    q_d_chebyshev_t,
    "((n x) ((unk) first chebyshev_t) ((mtimes) ((mplus) ((mtimes) n (($chebyshev_t) ((mplus) -1 n) x)) ((mtimes) -1 n (($chebyshev_t) n x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))",
  )
  putprop(q_d_chebyshev_t, q_tex_chebyshev_t, q_tex) |> ignore
  setf_get(q_d_chebyshev_t, q_dimension, q_dimension_chebyshev_t) |> ignore
  share_orthopoly__grad(
    q_d_chebyshev_u,
    "((n x) ((unk) first chebyshev_u) ((mtimes) ((mplus) ((mtimes) (($unit_step) n) ((mplus) 1 n) (($chebyshev_u) ((mplus) -1 n) x)) ((mtimes) -1 n (($chebyshev_u) n x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))",
  )
  putprop(q_d_chebyshev_u, q_tex_chebyshev_u, q_tex) |> ignore
  setf_get(q_d_chebyshev_u, q_dimension, q_dimension_chebyshev_u) |> ignore
  share_orthopoly__grad(
    q_d_legendre_p,
    "((n x) ((unk) first legendre_p) ((mtimes) ((mplus) ((mtimes) n (($legendre_p) ((mplus) -1 n) x)) ((mtimes) -1 n (($legendre_p) n x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1)))",
  )
  putprop(q_d_legendre_p, q_tex_legendre_p, q_tex) |> ignore
  setf_get(q_d_legendre_p, q_dimension, q_dimension_legendre_p) |> ignore
  share_orthopoly__grad(
    q_d_legendre_q,
    "((n x) ((unk) first legendre_p) ((mplus) ((mtimes) -1 ((%kron_delta) 0 n) ((mexpt) ((mplus) -1 ((mexpt) x 2)) -1)) ((mtimes) ((mplus) ((mtimes) n (($legendre_q) ((mplus) -1 n) x)) ((mtimes) -1 n (($legendre_q) n x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1))))",
  )
  putprop(q_d_legendre_q, q_tex_legendre_q, q_tex) |> ignore
  setf_get(q_d_legendre_q, q_dimension, q_dimension_legendre_q) |> ignore
  // See G & R, 8.733, page 1005 first equation.
  share_orthopoly__grad(
    q_d_assoc_legendre_q,
    "((n m x) ((unk) first assoc_legendre_q) ((unk) second assoc_legendre_q) ((mplus) ((mtimes) ((mplus) ((mtimes) -1 ((mplus) 1 ((mtimes) -1 m) n) (($assoc_legendre_q) ((mplus) 1 n) m x)) ((mtimes) ((mplus) 1 n) (($assoc_legendre_q) n m x) x)) ((mexpt) ((mplus) 1 ((mtimes) -1 ((mexpt) x 2))) -1))))",
  )
  putprop(q_d_assoc_legendre_q, q_tex_assoc_legendre_q, q_tex) |> ignore
  setf_get(q_d_assoc_legendre_q, q_dimension, q_dimension_assoc_legendre_q)
  |> ignore
  // For the derivative of the associated legendre p function, see
  // A & S 8.5.4 page 334.
  share_orthopoly__grad(
    q_d_assoc_legendre_p,
    "((n m x) ((unk) first assoc_legendre_p) ((unk) second assoc_legendre_p) ((mtimes simp) ((mplus simp) ((mtimes simp) -1 ((mplus simp) m n) (($unit_step) n) (($assoc_legendre_p simp) ((mplus simp) -1 n) m x)) ((mtimes simp) n (($assoc_legendre_p simp) n m x) x)) ((mexpt simp) ((mplus simp) -1 ((mexpt simp) x 2)) -1)))",
  )
  putprop(q_d_assoc_legendre_p, q_tex_assoc_legendre_p, q_tex) |> ignore
  setf_get(q_d_assoc_legendre_p, q_dimension, q_dimension_assoc_legendre_p)
  |> ignore
  share_orthopoly__grad(
    q_d_hermite,
    "((n x) ((unk) first hermite) ((mtimes) 2 n (($hermite) ((mplus) -1 n) x)))",
  )
  putprop(q_d_hermite, q_tex_hermite, q_tex) |> ignore
  setf_get(q_d_hermite, q_dimension, q_dimension_hermite) |> ignore
  share_orthopoly__grad(
    q_d_gen_laguerre,
    "((n a x) ((unk) first gen_laguerre) ((unk) second gen_laguerre) ((mtimes) ((mplus) ((mtimes) -1 ((mplus) a n) (($unit_step) n) (($gen_laguerre) ((mplus) -1 n) a x)) ((mtimes) n (($gen_laguerre) n a x))) ((mexpt) x -1)))",
  )
  putprop(q_d_gen_laguerre, q_tex_gen_laguerre, q_tex) |> ignore
  setf_get(q_d_gen_laguerre, q_dimension, q_dimension_gen_laguerre) |> ignore
  share_orthopoly__grad(
    q_d_laguerre,
    "((n x) ((unk) first laguerre) ((mtimes) ((mplus) ((mtimes) -1 n (($laguerre) ((mplus) -1 n) x)) ((mtimes) n (($laguerre) n x))) ((mexpt) x -1)))",
  )
  putprop(q_d_laguerre, q_tex_laguerre, q_tex) |> ignore
  setf_get(q_d_laguerre, q_dimension, q_dimension_laguerre) |> ignore
  share_orthopoly__grad(
    q_d_spherical_hankel1,
    "((n x) ((unk) first spherical_hankel1) ((mplus simp) (($spherical_hankel1) ((mplus) -1 n) x) ((mtimes simp) -1 ((mplus) 1 n) (($spherical_hankel1) n x) ((mexpt) x -1))))",
  )
  putprop(q_d_spherical_hankel1, q_tex_spherical_hankel_1, q_tex) |> ignore
  setf_get(q_d_spherical_hankel1, q_dimension, q_dimension_spherical_hankel_1)
  |> ignore
  share_orthopoly__grad(
    q_d_spherical_hankel2,
    "((n x) ((unk) first spherical_hankel2) ((mplus simp) (($spherical_hankel2) ((mplus) -1 n) x) ((mtimes simp) -1 ((mplus) 1 n) (($spherical_hankel2) n x) ((mexpt) x -1))))",
  )
  putprop(q_d_spherical_hankel2, q_tex_spherical_hankel_2, q_tex) |> ignore
  setf_get(q_d_spherical_hankel2, q_dimension, q_dimension_spherical_hankel_2)
  |> ignore
  share_orthopoly__grad(
    q_d_spherical_bessel_j,
    "((n x) ((unk) first spherical_bessel_j) ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) 2 n)) -1) ((mplus) ((mtimes) n (($spherical_bessel_j) ((mplus) -1 n) x)) ((mtimes) -1 ((mplus) 1 n) (($spherical_bessel_j) ((mplus) 1 n) x)))))",
  )
  putprop(q_d_spherical_bessel_j, q_tex_spherical_bessel_j, q_tex) |> ignore
  setf_get(q_d_spherical_bessel_j, q_dimension, q_dimension_spherical_bessel_j)
  |> ignore
  share_orthopoly__grad(
    q_d_spherical_bessel_y,
    "((n x) ((unk) first spherical_bessel_y) ((mtimes) ((mexpt) ((mplus) 1 ((mtimes) 2 n)) -1) ((mplus) ((mtimes) n (($spherical_bessel_y) ((mplus) -1 n) x)) ((mtimes) -1 ((mplus) 1 n) (($spherical_bessel_y) ((mplus) 1 n) x)))))",
  )
  putprop(q_d_spherical_bessel_y, q_tex_spherical_bessel_y, q_tex) |> ignore
  setf_get(q_d_spherical_bessel_y, q_dimension, q_dimension_spherical_bessel_y)
  |> ignore
  putprop(q_d_spherical_harmonic, q_tex_spherical_harmonic, q_tex) |> ignore
  setf_get(q_d_spherical_harmonic, q_dimension, q_dimension_spherical_harmonic)
  |> ignore
  share_orthopoly__grad(
    q_d_spherical_harmonic,
    "((n m theta phi) ((unk) first spherical_harmonic) ((unk) second spherical_harmonic) ((mplus) ((mtimes) ((rat) -1 2) ((mexpt) ((mtimes) ((mplus) ((mtimes) -1 m) n) ((mplus) 1 m n)) ((rat) 1 2)) (($spherical_harmonic) n ((mplus) 1 m) theta phi) ((mexpt) $%e ((mtimes) -1 $%i phi))) ((mtimes) ((rat) 1 2) ((mexpt) ((mtimes) ((mplus) 1 ((mtimes) -1 m) n) ((mplus) m n)) ((rat) 1 2)) (($spherical_harmonic) n ((mplus) -1 m) theta phi) ((mexpt) $%e ((mtimes) $%i phi)))) ((mtimes) $%i m (($spherical_harmonic) n m theta phi)))",
  )
}
