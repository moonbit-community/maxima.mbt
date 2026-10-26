// Port of src/asum.lisp: polynomial predicates, factorials, sums and
// products, and the linear operator machinery (additive, multiplicative,
// outative, evenfun, oddfun, commutative, antisymmetric, nary,
// lassociative, rassociative, define_opproperty).

// polynomial predicates and other such things

///|
fn poly_q(exp_ : Value, var_ : Value) -> Value raise {
  if atom(exp_) {
    return t
  }
  let f = free(exp_, var_)
  if f.truthy() {
    f
  } else if eq(caar(exp_), q_mtimes) || eq(caar(exp_), q_mplus) {
    for x in cdr(exp_).iter() {
      if poly_q(x, var_) is Nil {
        return Nil
      }
    }
    t
  } else if eq(caar(exp_), q_mexpt) &&
    integerp(caddr(exp_)) &&
    num_gt(caddr(exp_), Fix(0L)) {
    poly_q(cadr(exp_), var_)
  } else {
    Nil
  }
}

///|
fn smono(x : Value, var_ : Value) -> Value raise {
  smonogen(x, var_, t)
}

///|
fn smonop(x : Value, var_ : Value) -> Value raise {
  smonogen(x, var_, Nil)
}

///|
/// FL indicates whether to return *A *N
fn smonogen(x : Value, var_ : Value, fl : Value) -> Value raise {
  if free(x, var_).truthy() {
    if fl.truthy() {
      set(q_n_starn, Fix(0L)) |> ignore
      set(q_n_stara, x) |> ignore
    }
    t
  } else if atom(x) {
    if fl.truthy() {
      set(q_n_starn, set(q_n_stara, Fix(1L))) |> ignore
    }
    t
  } else if listp(car(x)) && eq(caar(x), q_mtimes) {
    let mut a = list1(Fix(1L))
    let mut n = list1(Fix(0L))
    for f in cdr(x).iter() {
      let ok = with_specials([(q_n_stara, Nil), (q_n_starn, Nil)], fn() raise {
        if smonogen(f, var_, fl).truthy() {
          if fl.truthy() {
            a = cons(symval(q_n_stara), a)
            n = cons(symval(q_n_starn), n)
          }
          true
        } else {
          false
        }
      })
      if !ok {
        return Nil
      }
    }
    if fl.truthy() {
      set(q_n_starn, addn(n, Nil)) |> ignore
      set(q_n_stara, muln(a, Nil)) |> ignore
    }
    t
  } else if listp(car(x)) && eq(caar(x), q_mexpt) {
    if free(caddr(x), var_).truthy() && eq(cadr(x), var_) {
      if fl.truthy() {
        set(q_n_starn, caddr(x)) |> ignore
        set(q_n_stara, Fix(1L)) |> ignore
      }
      t
    } else {
      Nil
    }
  } else {
    Nil
  }
}

// factorial stuff

///|
fn gfact(n : Value, p_m : Value, i : Value) -> Value raise {
  if minusp(p_m) {
    improper_arg_err(p_m, q_d_genfact)
  } else if num_eq(p_m, Fix(0L)) {
    Fix(1L)
  } else {
    let mut n = n
    let mut m = p_m
    let mut ans = n
    while true {
      if num_eq(m, Fix(1L)) {
        return ans
      }
      n = sub_star(n, i)
      m = one_minus(m)
      ans = mul2_star(ans, n)
    }
    ans
  }
}

///|
/// k(n,m) = n*(n-m)*(n-2*m)*...
fn asum__k(n : Value, m : Value) -> Value raise {
  if num_le(n, m) {
    n
  } else {
    let m2 = num_mul(Fix(2L), m)
    num_mul(asum__k(n, m2), asum__k(num_sub(n, m), m2))
  }
}

///|
/// From Richard Fateman's paper, "Comments on Factorial Programs".
/// (k n 1) is n!; this is much faster than the naive product.
fn factorial(n : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else {
    asum__k(n, Fix(1L))
  }
}

///|
fn simpfact(x : Value, y : Value, z : Value) -> Value raise {
  oneargcheck(x) |> ignore
  let y = simpcheck(cadr(x), z)
  ignore(y)
  if mnump(y).truthy() &&
    eq(d_sign(y), q_d_neg) &&
    zerop1(sub(simplify(list2(list1(q_p_truncate), y)), y)).truthy() {
    // Negative integer or a real representation of a negative integer.
    merr("factorial: factorial of negative integer ~:M not defined.", [y])
  } else if floatp(y) ||
    d_bfloatp(y).truthy() ||
    (
      !integerp(y) &&
      ratnump(y) is Nil &&
      (
        (
          complex_number_p(y, ntypep=q_float_or_rational_p).truthy() &&
          (
            symval(q_d_numer).truthy() ||
            floatp(d_realpart(y)) ||
            floatp(d_imagpart(y))
          )
        ) ||
        (
          complex_number_p(y, ntypep=q_bigfloat_or_number_p).truthy() &&
          (
            symval(q_d_numer).truthy() ||
            d_bfloatp(d_realpart(y)).truthy() ||
            d_bfloatp(d_imagpart(y)).truthy()
          )
        )
      )
    ) ||
    (symval(q_makef) is Nil && ratnump(y).truthy() && equal(caddr(y), Fix(2L))) {
    // Numerically evaluate for real or complex argument in float or
    // bigfloat precision using the Gamma function
    simplify(list2(list1(q_p_gamma), add2(Fix(1L), y)))
  } else if eq(y, q_d_inf) {
    q_d_inf
  } else if symval(q_d_factorial_expand).truthy() &&
    mplusp(y).truthy() &&
    integerp(cadr(y)) {
    // factorial(n+m) and m integer. Expand.
    let mut m = cadr(y)
    let n = simplify(cons(list1(q_mplus), cddr(y)))
    if num_ge(m, Fix(0L)) {
      mul2(
        simplify(list3(list1(q_d_pochhammer), add2(n, Fix(1L)), m)),
        simplify(list2(list1(q_mfactorial), n)),
      )
    } else {
      m = num_neg(m)
      div(
        mul2(power(Fix(-1L), m), simplify(list2(list1(q_mfactorial), n))),
        // We factor to get the ordering (n-1)*(n-2)*...
        d_factor(simplify(list3(list1(q_d_pochhammer), mul2(Fix(-1L), n), m))),
      )
    }
  } else if !fixnump(y) || !num_gt(y, Fix(-1L)) {
    eqtest(list2(list1(q_mfactorial), y), x)
  } else if minusp(symval(q_d_factlim)) || !num_gt(y, symval(q_d_factlim)) {
    factorial(y)
  } else {
    eqtest(list2(list1(q_mfactorial), y), x)
  }
}

///|
let asum__lit_kc_half : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 4) ((mexpt simp) $%pi ((rat simp) -1 2)) ((mexpt simp) ((%gamma simp) ((rat simp) 1 4)) 2))",
)

///|
let asum__lit_kc_a1 : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 4) ((mplus simp) 2 ((mexpt simp) 3 ((rat simp) 1 2))))",
)

///|
let asum__lit_kc_a2 : Value = try! lread(
  "((mplus simp) ((rat simp) 1 2) ((mtimes simp) ((rat simp) 1 4) ((mexpt simp) 3 ((rat simp) 1 2))))",
)

///|
let asum__lit_kc_a3 : Value = try! lread(
  "((mexpt simp) ((mplus simp) 8 ((mtimes simp) -4 ((mexpt simp) 3 ((rat simp) 1 2)))) -1)",
)

///|
let asum__lit_kc_a : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 4) ((mexpt simp) 3 ((rat simp) 1 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3)))",
)

///|
let asum__lit_kc_b1 : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 4) ((mplus simp) 2 ((mtimes simp) -1 ((mexpt simp) 3 ((rat simp) 1 2)))))",
)

///|
let asum__lit_kc_b2 : Value = try! lread(
  "((mplus simp) ((rat simp) 1 2) ((mtimes simp) ((rat simp) -1 4) ((mexpt simp) 3 ((rat simp) 1 2))))",
)

///|
let asum__lit_kc_b3 : Value = try! lread(
  "((mexpt simp) ((mplus simp) 8 ((mtimes simp) 4 ((mexpt simp) 3 ((rat simp) 1 2)))) -1)",
)

///|
let asum__lit_kc_b : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 4) ((mexpt simp) 3 ((rat simp) -1 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3)))",
)

///|
let asum__lit_kc_c1 : Value = try! lread(
  "((mtimes simp) ((mplus simp) 3 ((mtimes simp) -2 ((mexpt simp) 2 ((rat simp) 1 2)))) ((mexpt simp) ((mplus simp) 3 ((mtimes simp) 2 ((mexpt simp) 2 ((rat simp) 1 2)))) -1))",
)

///|
let asum__lit_kc_c2 : Value = try! lread(
  "((mplus simp) 17 ((mtimes simp) -12 ((mexpt simp) 2 ((rat simp) 1 2))))",
)

///|
let asum__lit_kc_c3 : Value = try! lread(
  "((mtimes simp) -1 ((mplus simp) -3 ((mtimes simp) 2 ((mexpt simp) 2 ((rat simp) 1 2)))) ((mexpt simp) ((mplus simp) 3 ((mtimes simp) 2 ((mexpt simp) 2 ((rat simp) 1 2)))) -1))",
)

///|
let asum__lit_kc_c : Value = try! lread(
  "((mtimes simp) ((rat simp) 1 8) ((mexpt simp) 2 ((rat simp) -1 2)) ((mplus simp) 1 ((mexpt simp) 2 ((rat simp) 1 2))) ((mexpt simp) $%pi ((rat simp) -1 2)) ((mexpt simp) ((%gamma simp) ((rat simp) 1 4)) 2))",
)

///|
let asum__lit_ec_half : Value = try! lread(
  "((mplus simp) ((mtimes simp) ((mexpt simp) $%pi ((rat simp) 3 2)) ((mexpt simp) ((%gamma simp irreducible) ((rat simp) 1 4)) -2)) ((mtimes simp) ((rat simp) 1 8) ((mexpt simp) $%pi ((rat simp) -1 2)) ((mexpt simp) ((%gamma simp) ((rat simp) 1 4)) 2)))",
)

///|
let asum__lit_ec_b : Value = try! lread(
  "((mplus simp) ((mtimes simp) ((mexpt simp) 3 ((rat simp) -1 4)) ((mexpt simp) $%pi ((rat simp) 3 2)) ((mexpt simp) ((%gamma simp) ((rat simp) 1 6)) -1) ((mexpt simp) ((%gamma simp) ((rat simp) 1 3)) -1)) ((mtimes simp) ((rat simp) 1 8) ((mexpt simp) 3 ((rat simp) -3 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3))) ((mtimes simp) ((rat simp) 1 8) ((mexpt simp) 3 ((rat simp) -1 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3))))",
)

///|
let asum__lit_ec_a : Value = try! lread(
  "((mplus simp) ((mtimes simp) 3 ((mexpt simp) 3 ((rat simp) -3 4)) ((mexpt simp) $%pi ((rat simp) 3 2)) ((mexpt simp) ((%gamma simp) ((rat simp) 1 6)) -1) ((mexpt simp) ((%gamma simp) ((rat simp) 1 3)) -1)) ((mtimes simp) ((rat simp) 3 8) ((mexpt simp) 3 ((rat simp) -3 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3))) ((mtimes simp) ((rat simp) -1 8) ((mexpt simp) 3 ((rat simp) -1 4)) ((mexpt simp) $%pi ((rat simp) -1 2)) ((%gamma simp) ((rat simp) 1 6)) ((%gamma simp) ((rat simp) 1 3))))",
)

///|
let asum__lit_half : Value = try! lread("((rat simp) 1 2)")

///|
fn makegamma1(e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_mfactorial) {
    list2(list1(q_p_gamma), list3(list1(q_mplus), Fix(1L), makegamma1(cadr(e))))
    // Begin code copied from orthopoly/orthopoly-init.lisp
    // Do pochhammer(x,n) ==> gamma(x+n)/gamma(x),
    // but not if x is a negative integer or zero.
  } else if eq(caar(e), q_d_pochhammer) {
    let x = makegamma1(nth(1, e))
    let n = makegamma1(nth(2, e))
    if integerp(x) && num_le(x, Fix(0L)) {
      e
    } else {
      div(take(list1(q_p_gamma), [add2(x, n)]), take(list1(q_p_gamma), [x]))
    }
    // (gamma(x/z+1)*z^floor(y))/gamma(x/z-floor(y)+1)
  } else if eq(caar(e), q_p_genfact) {
    let x = makegamma1(nth(1, e))
    let mut y = makegamma1(nth(2, e))
    let z = makegamma1(nth(3, e))
    y = take(list1(q_d_floor), [y])
    div(
      mul2(take(list1(q_p_gamma), [add2(div(x, z), Fix(1L))]), power(z, y)),
      take(list1(q_p_gamma), [sub(add2(div(x, z), Fix(1L)), y)]),
    )
    // End code copied from orthopoly/orthopoly-init.lisp
    // Double factorial
  } else if eq(caar(e), q_p_double_factorial) {
    let x = makegamma1(nth(1, e))
    muln_([
      power(
        div(Fix(2L), q_d__pctpi),
        mul2(
          div(Fix(1L), Fix(4L)),
          sub(Fix(1L), simplify(list2(list1(q_p_cos), mul2(q_d__pctpi, x)))),
        ),
      ),
      power(Fix(2L), div(x, Fix(2L))),
      simplify(list2(list1(q_p_gamma), add2(Fix(1L), div(x, Fix(2L))))),
    ])
  } else if eq(caar(e), q_p_elliptic_kc) {
    // Complete elliptic integral of the first kind
    let a = cadr(e)
    if alike1(a, asum__lit_half).truthy() {
      // K(1/2) = gamma(1/4)/4/sqrt(pi)
      asum__lit_kc_half
    } else if alike1(a, asum__lit_kc_a1).truthy() ||
      alike1(a, asum__lit_kc_a2).truthy() ||
      alike1(a, asum__lit_kc_a3).truthy() {
      // K((2+sqrt(3)/4))
      asum__lit_kc_a
    } else if alike1(a, asum__lit_kc_b1).truthy() ||
      alike1(a, asum__lit_kc_b2).truthy() ||
      like(a, asum__lit_kc_b3).truthy() {
      // K((2-sqrt(3))/4)
      asum__lit_kc_b
    } else if alike1(a, asum__lit_kc_c1).truthy() ||
      alike1(a, asum__lit_kc_c2).truthy() ||
      alike1(a, asum__lit_kc_c3).truthy() {
      asum__lit_kc_c
    } else {
      // Give up
      e
    }
  } else if eq(caar(e), q_p_elliptic_ec) {
    // Complete elliptic integral of the second kind
    let a = cadr(e)
    if alike1(a, asum__lit_half).truthy() {
      // 2*E(1/2) - K(1/2) = 2*%pi^(3/2)*gamma(1/4)^(-2)
      asum__lit_ec_half
    } else if alike1(a, asum__lit_kc_b1).truthy() ||
      alike1(a, asum__lit_kc_b2).truthy() {
      // E((2-sqrt(3))/4)
      //
      // %pi/4/sqrt(3) = K*(E-(sqrt(3)+1)/2/sqrt(3)*K)
      asum__lit_ec_b
    } else if alike1(a, asum__lit_kc_a1).truthy() ||
      alike1(a, asum__lit_kc_a2).truthy() {
      // E((2+sqrt(3))/4)
      //
      // %pi*sqrt(3)/4 = K1*(E1-(sqrt(3)-1)/2/sqrt(3)*K1)
      asum__lit_ec_a
    } else {
      e
    }
  } else {
    recur_apply(lfunc("makegamma1", args => makegamma1(arg(args, 0))), e)
  }
}

///|
fn simp__pctgenfact(
  form : Value,
  y : Value,
  p__pctsimpflag : Value,
) -> Value raise {
  ignore(y)
  if length(cdr(form)) != 3 {
    wna_err(
      form,
      required_arg_count=Fix(3L),
      pretty_name=list4(list1(q_p_genfact), q_d_x, q_d_y, q_d_z),
    )
    |> ignore
  }
  let x = simpcheck(nth(1, form), p__pctsimpflag)
  let y = simpcheck(nth(2, form), p__pctsimpflag)
  let z = simpcheck(nth(3, form), p__pctsimpflag)
  let a = x
  let b = take(list1(q_d_floor), [y])
  let c = z
  if fixnump(a) && fixnump(b) && fixnump(c) {
    if num_gt(a, Fix(-1L)) &&
      num_gt(b, Fix(-1L)) &&
      (num_le(c, a) || num_eq(b, Fix(0L))) &&
      num_le(b, num_div(a, c)) {
      gfact(a, b, c)
    } else {
      merr("genfact: generalized factorial not defined for given arguments.", [])
    }
  } else {
    // Give up, we want to return a result with args that are different
    // from the original.  In particular, we want the floor of y if y was
    // real number.  Otherwise, we leave it.
    let args = list3(
      a,
      if !atom(b) && eq(caar(b), q_d_floor) {
        cadr(b)
      } else {
        b
      },
      c,
    )
    eqtest(cons(list1(q_p_genfact), args), form)
  }
}

// sum begins

///|
fn sum_arg(sum : Value) -> Value raise {
  cadr(sum)
}

///|
fn sum_index(sum : Value) -> Value raise {
  caddr(sum)
}

///|
fn sum_lower(sum : Value) -> Value raise {
  cadddr(sum)
}

///|
fn sum_upper(sum : Value) -> Value raise {
  cadr(cdddr(sum))
}

///|
/// `(mbinding (vars vals) body)`
fn asum__mbinding(
  vars : Value,
  vals : Value,
  f : () -> Value raise,
) -> Value raise {
  let mut win = false
  defer (if win { munbind(vars) |> ignore })
  mbind(vars, vals, Nil) |> ignore
  win = true
  f()
}

///|
fn d_sum(l : Value) -> Value raise {
  arg_count_check(Fix(4L), l) |> ignore
  let l = cdr(l)
  dosum(
    car(l),
    cadr(l),
    meval(caddr(l)),
    meval(cadddr(l)),
    t,
    evaluate_summand=t,
  )
}

///|
fn d_lsum(l : Value) -> Value raise {
  arg_count_check(Fix(3L), l) |> ignore
  let l = cdr(l)
  let form = car(l)
  let ind = cadr(l)
  let lis = meval(caddr(l))
  let mut ans : Value = Fix(0L)
  if !symbolp(ind) {
    merr("lsum: second argument must be a variable; found ~M", [ind]) |> ignore
  }
  if d_listp(lis).truthy() {
    let lind = cons(ind, Nil)
    for v in cdr(lis).iter() {
      let w = cons(v, Nil)
      ans = add2_star(ans, asum__mbinding(lind, w, () => meval(form)))
    }
    ans
  } else {
    list4(list1(q_p_lsum), form, ind, lis)
  }
}

///|
fn simpsum(x : Value, y : Value, z : Value) -> Value raise {
  let y = with_special(q_d_ratsimpexpons, t, () => {
    maybe_simplifya(sum_arg(x), z)
  })
  ignore(y)
  simpsum1(
    y,
    sum_index(x),
    maybe_simplifya(sum_lower(x), z),
    maybe_simplifya(sum_upper(x), z),
  )
}

///|
/// This function was SIMPSUM1 until the sum/product code was revised Nov
/// 2005.  The revised code punts back to this function since this code
/// knows some simplifications not handled by the revised code.
fn simpsum1_save(
  exp_ : Value,
  i : Value,
  lo : Value,
  hi : Value,
) -> Value raise {
  if !symbolp(i) {
    merr("sum: index must be a symbol; found ~M", [i])
  } else if equal(lo, hi) {
    asum__mbinding(list1(i), list1(hi), () => meval(exp_))
  } else if atom(exp_) &&
    !eq(exp_, i) &&
    getl(q_p_sum, list2(q_d_outative, q_d_linear)).truthy() {
    freesum(exp_, lo, hi, Fix(1L))
  } else if symval(q_d_simpsum) is Nil {
    list5_(get(q_p_sum, q_msimpind), exp_, i, lo, hi)
  } else if (
      eq(lo, q_d_minf) ||
      alike1(lo, list3(list2(q_mtimes, q_simp), Fix(-1L), q_d_inf)).truthy()
    ) &&
    equal(hi, q_d_inf) {
    let pos_part = simpsum2(exp_, i, Fix(0L), q_d_inf)
    let neg_part = simpsum2(
      maxima_substitute(mul_star(list2(Fix(-1L), i)), i, exp_),
      i,
      Fix(1L),
      q_d_inf,
    )
    if eq(neg_part, q_d_und) || eq(pos_part, q_d_und) {
      q_d_und
    } else if eq(pos_part, q_d_inf) {
      if eq(neg_part, q_d_minf) {
        q_d_und
      } else {
        q_d_inf
      }
    } else if eq(pos_part, q_d_minf) {
      if eq(neg_part, q_d_inf) {
        q_d_und
      } else {
        q_d_minf
      }
    } else if eq(neg_part, q_d_inf) || eq(neg_part, q_d_minf) {
      neg_part
    } else {
      add2_star(neg_part, pos_part)
    }
  } else if eq(lo, q_d_minf) ||
    alike1(lo, list3(list2(q_mtimes, q_simp), Fix(-1L), q_d_inf)).truthy() {
    simpsum2(
      maxima_substitute(mul_star(list2(Fix(-1L), i)), i, exp_),
      i,
      mul_star(list2(Fix(-1L), hi)),
      q_d_inf,
    )
  } else {
    simpsum2(exp_, i, lo, hi)
  }
}

// DOSUM, MEVALSUMARG, DO%SUM -- general principles
//
//  - evaluate the summand/productand
//  - substitute a gensym for the index variable and make assertions (via
//    assume) about the gensym index
//  - return 0/1 for empty sum/product. sumhack/prodhack are ignored
//  - distribute sum/product over mbags when listarith = true

///|
fn dosum(
  expr : Value,
  ind : Value,
  low : Value,
  hi : Value,
  sump : Value,
  evaluate_summand~ : Value = t,
) -> Value raise {
  let mut expr = expr
  let low = ratdisrep(low)
  let hi = ratdisrep(hi) // UGH, GAG WITH ME A SPOON
  if !symbolp(ind) {
    merr("~:M: index must be a symbol; found ~M", [
      if sump.truthy() {
        q_d_sum
      } else {
        q_d_product
      },
      ind,
    ])
    |> ignore
  }
  let b = bind(q_n_stari, Nil)
  defer unbind(b)
  let lind = cons(ind, Nil)
  let mut hl = mfuncall(q_d_floor, list1(sub_star(hi, low)))
  if !fixnump(hl) {
    if evaluate_summand.truthy() {
      expr = mevalsumarg(expr, ind, low, hi)
    }
    return cons(
      list1(if sump.truthy() { q_p_sum } else { q_p_product }),
      list4(expr, ind, low, hi),
    )
  } else if num_lt(hl, Fix(0L)) {
    return if sump.truthy() { Fix(0L) } else { Fix(1L) }
  }
  set(q_n_stari, low) |> ignore
  let l_stari = list1(symval(q_n_stari))
  let mut u : Value = if sump.truthy() { Fix(0L) } else { Fix(1L) }
  while true {
    let term = resimplify(
      {
        let foo = asum__mbinding(lind, l_stari, () => meval(expr))
        subst_if_not_freeof(symval(q_n_stari), ind, foo)
      },
    )
    u = if sump.truthy() { add2(u, term) } else { mul2(u, term) }
    if zerop(hl) {
      return u
    }
    hl = one_minus(hl)
    set(q_n_stari, car(rplaca(l_stari, add2_star(symval(q_n_stari), Fix(1L)))))
    |> ignore
  }
  u
}

///|
fn subst_if_not_freeof(x : Value, y : Value, expr : Value) -> Value raise {
  if d_freeof(list2(y, expr)).truthy() {
    // suppressing substitution here avoids substituting for local
    // variables recognize by freeof, e.g., formal argument of lambda.
    expr
  } else {
    with_special(q_d_simp, Nil, () => maxima_substitute(x, y, expr))
  }
}

///|
fn mevalsumarg(
  expr : Value,
  ind : Value,
  low : Value,
  hi : Value,
) -> Value raise {
  // The value of this test is not used.
  with_special(q_d_prederror, Nil, () => mevalp(list3(list1(q_mlessp), hi, low)))
  |> ignore
  let gensym_ind = gensym()
  if apparently_integer(low).truthy() {
    meval(list3(list1(q_d_declare), gensym_ind, q_d_integer)) |> ignore
  }
  assume(list3(list1(q_mgeqp), gensym_ind, low)) |> ignore
  if !eq(hi, q_d_inf) {
    assume(list3(list1(q_mgeqp), hi, gensym_ind)) |> ignore
  }
  with_special(q_msump, t, fn() raise {
    let mut summand = if !atom(expr) &&
      get(caar(expr), q_mevalsumarg_macro).truthy() {
      funcall(get(caar(expr), q_mevalsumarg_macro), [expr])
    } else {
      expr
    }
    summand = with_special(q_d_simp, Nil, () => {
      d_substitute(gensym_ind, ind, expr=summand)
    })
    let mut foo = asum__mbinding(list1(gensym_ind), list1(gensym_ind), () => {
      resimplify(meval(summand))
    })
    // At this point we do not switch off simplification to preserve the
    // achieved simplification of the summand (DK 02/2010).
    foo = with_special(q_d_simp, t, () => {
      d_substitute(ind, gensym_ind, expr=foo)
    })
    if !eq(hi, q_d_inf) {
      forget(list3(list1(q_mgeqp), hi, gensym_ind)) |> ignore
    }
    forget(list3(list1(q_mgeqp), gensym_ind, low)) |> ignore
    if apparently_integer(low).truthy() {
      meval(list3(list1(q_d_remove), gensym_ind, q_d_integer)) |> ignore
    }
    foo
  })
}

///|
fn apparently_integer(x : Value) -> Value raise {
  let v = d_integerp(x)
  if v.truthy() {
    v
  } else {
    d_featurep(x, q_d_integer)
  }
}

///|
fn do_pctsum(l : Value, op : Value) -> Value raise {
  if length(l) != 4 {
    wna_err(op) |> ignore
  }
  let mut ind = cadr(l)
  if mquotep(ind).truthy() {
    ind = cadr(ind)
  }
  if !symbolp(ind) {
    merr("~:M: index must be a symbol; found ~M", [op, ind]) |> ignore
  }
  let low = caddr(l)
  let hi = cadddr(l)
  let a = mevalsumarg(car(l), ind, low, hi)
  let b = meval(caddr(l))
  let c = meval(cadddr(l))
  list4(a, ind, b, c)
}

///|
/// `(with-new-context (context) ...)`
fn asum__with_new_context(f : () -> Value raise) -> Value raise {
  let my_context = gensym(prefix="$ctxt")
  mfuncall(q_d_supcontext, list2(my_context, symval(q_context))) |> ignore
  defer {
    let _ = d_killcontext(list1(my_context)) catch { _ => nil }
  }
  f()
}

///|
fn asum__is_sgn_nonpos(sgn : Value) -> Bool {
  eq(sgn, q_d_neg) || eq(sgn, q_d_zero) || eq(sgn, q_d_nz)
}

///|
fn simpsum1(e : Value, k : Value, lo : Value, hi : Value) -> Value raise {
  asum__with_new_context(fn() raise {
    with_special(q_d_prederror, Nil, fn() raise {
      let i = gensym()
      let lo = d_ratdisrep(lo)
      let hi = d_ratdisrep(hi)
      let n = d_limit(list1(add2(Fix(1L), sub(hi, lo))))
      // N is the number of terms. $SIGN errors out on a complex value, and
      // the count is complex whenever a bound is. $CSIGN answers complex
      // instead, which falls through to the noun form below.
      let mut sgn = d_csign(n)
      if !eq(t, csign(lo)) {
        mfuncall(q_d_assume, list1(list3(list1(q_mgeqp), i, lo))) |> ignore
      }
      if !eq(t, csign(hi)) {
        mfuncall(q_d_assume, list1(list3(list1(q_mgeqp), hi, i))) |> ignore
      }
      let mut ex = subst(i, k, e)
      ex = subst(i, k, ex) // Why substitute again?
      let mut acc = if eq(n, q_d_inf) && d_freeof(list2(i, ex)).truthy() {
        sgn = csign(ex)
        if eq(sgn, q_d_pos) {
          q_d_inf
        } else if eq(sgn, q_d_neg) {
          q_d_minf
        } else if eq(sgn, q_d_zero) {
          Fix(0L)
        } else {
          list5_(list2(q_p_sum, q_simp), ex, i, lo, hi)
        }
      } else if mbagp(e).truthy() && symval(q_d_listarith).truthy() {
        simplifya(
          cons(
            list1(caar(e)),
            mapcar(s => mfuncall(q_d_sum, list4(s, k, lo, hi)), margs(e)),
          ),
          t,
        )
      } else if asum__is_sgn_nonpos(sgn) {
        Fix(0L)
      } else if like(ex, Fix(0L)).truthy() {
        Fix(0L)
      } else if d_freeof(list2(i, ex)).truthy() {
        mult(n, ex)
      } else if integerp(n) && eq(sgn, q_d_pos) && symval(q_d_simpsum).truthy() {
        let mut acc : Value = Fix(0L)
        let mut j : Value = Fix(0L)
        while num_lt(j, n) {
          acc = add2(acc, resimplify(subst(add2(j, lo), i, ex)))
          j = one_plus(j)
        }
        acc
      } else {
        list5_(list2(q_p_sum, q_simp), subst(k, i, ex), k, lo, hi)
      }
      acc = subst(k, i, acc)
      // If expression is still a summation, punt to previous
      // simplification code.
      if symval(q_d_simpsum).truthy() && op_equalp(acc, q_p_sum).truthy() {
        let args = cdr(acc)
        acc = simpsum1_save(
          first(args),
          second(args),
          third(args),
          fourth(args),
        )
      }
      // If the expression is no longer a %sum, resimplify.  Ordering of
      // expressions may change due to the gensym -> index substitution.
      if op_equalp(acc, q_p_sum) is Nil {
        acc = resimplify(acc)
      }
      acc
    })
  })
}

///|
fn simpprod1(e : Value, k : Value, lo : Value, hi : Value) -> Value raise {
  asum__with_new_context(fn() raise {
    with_special(q_d_prederror, Nil, fn() raise {
      let i = gensym()
      let lo = d_ratdisrep(lo)
      let hi = d_ratdisrep(hi)
      let n = d_limit(list1(add2(Fix(1L), sub(hi, lo))))
      // N is the number of terms. $SIGN errors out on a complex value, and
      // the count is complex whenever a bound is. $CSIGN answers complex
      // instead, which falls through to the noun form below.
      let sgn = d_csign(n)
      if !eq(t, csign(lo)) {
        mfuncall(q_d_assume, list1(list3(list1(q_mgeqp), i, lo))) |> ignore
      }
      if !eq(t, csign(hi)) {
        mfuncall(q_d_assume, list1(list3(list1(q_mgeqp), hi, i))) |> ignore
      }
      let mut ex = subst(i, k, e)
      ex = subst(i, k, ex) // Why substitute again?
      let mut acc : Value = if like(ex, Fix(1L)).truthy() {
        Fix(1L)
      } else if eq(n, q_d_inf) && d_freeof(list2(i, ex)).truthy() {
        let ex_mag = mfuncall(q_d_cabs, list1(ex))
        let mut realp_ = mfuncall(q_d_imagpart, list1(ex))
        realp_ = mevalp(list3(list1(q_mequal), Fix(0L), realp_))
        if eq(t, mevalp(list3(list1(q_mlessp), ex_mag, Fix(1L)))) {
          Fix(0L)
        } else if eq(realp_, t) &&
          eq(t, mevalp(list3(list1(q_mgreaterp), ex, Fix(1L)))) {
          q_d_inf
        } else if eq(t, mevalp(list3(list1(q_mgreaterp), ex_mag, Fix(1L)))) {
          q_d_infinity
        } else if eq(t, mevalp(list3(list1(q_mequal), Fix(1L), ex_mag))) {
          q_d_und
        } else {
          list5_(list2(q_p_product, q_simp), e, k, lo, hi)
        }
      } else if asum__is_sgn_nonpos(sgn) {
        Fix(1L)
      } else if mbagp(e).truthy() && symval(q_d_listarith).truthy() {
        simplifya(
          cons(
            list1(caar(e)),
            mapcar(s => mfuncall(q_d_product, list4(s, k, lo, hi)), margs(e)),
          ),
          t,
        )
      } else if d_freeof(list2(i, ex)).truthy() {
        power(ex, n)
      } else if integerp(n) &&
        eq(sgn, q_d_pos) &&
        symval(q_d_simpproduct).truthy() {
        let mut acc : Value = Fix(1L)
        let mut j : Value = Fix(0L)
        while num_lt(j, n) {
          acc = mult(acc, resimplify(subst(add2(j, lo), i, ex)))
          j = one_plus(j)
        }
        acc
      } else {
        list5_(list2(q_p_product, q_simp), subst(k, i, ex), k, lo, hi)
      }
      // Hmm, this is curious... don't call existing product
      // simplifications if index range is infinite -- what's up with that??
      if symval(q_d_simpproduct).truthy() &&
        op_equalp(acc, q_p_product).truthy() &&
        like(n, q_d_inf) is Nil {
        let args = cdr(acc)
        acc = simpprod1_save(
          first(args),
          second(args),
          third(args),
          fourth(args),
        )
      }
      acc = subst(k, i, acc)
      // If the expression is no longer a %product, resimplify.  Ordering of
      // expressions may change due to the gensym -> index substitution.
      if op_equalp(acc, q_p_product) is Nil {
        acc = resimplify(acc)
      }
      acc
    })
  })
}

///|
/// This function was SIMPPROD1 until the sum/product code was revised Nov
/// 2005.  The revised code punts back to this function since this code
/// knows some simplifications not handled by the revised code.
fn simpprod1_save(
  exp_ : Value,
  i : Value,
  lo : Value,
  hi : Value,
) -> Value raise {
  let mut hi = hi
  if !symbolp(i) {
    return merr("product: index must be a symbol; found ~M", [i])
  }
  if alike1(lo, hi).truthy() {
    let valist = list1(i)
    return asum__mbinding(valist, list1(hi), () => meval(exp_))
  }
  let u = sub_star(hi, lo)
  if eq(d_sign(u), q_d_neg) {
    if eq(d_sign(add2(u, Fix(1L))), q_d_zero) {
      Fix(1L)
    } else {
      merr("product: lower bound ~M greater than upper bound ~M", [lo, hi])
    }
  } else if atom(exp_) {
    if !eq(exp_, i) {
      power_star(
        exp_,
        list4(list1(q_mplus), hi, Fix(1L), list3(list1(q_mtimes), Fix(-1L), lo)),
      )
    } else {
      let lot = asksign(lo)
      if equal(lot, q_d_zero) {
        Fix(0L)
      } else if eq(lot, q_d_positive) {
        div_star(
          list2(list1(q_mfactorial), hi),
          list2(list1(q_mfactorial), list3(list1(q_mplus), lo, Fix(-1L))),
        )
      } else {
        let a = list2(list1(q_mfactorial), list2(list1(q_mabs), lo))
        let ahi = asksign(hi)
        let b : Value = if eq(ahi, q_d_zero) || eq(ahi, q_d_positive) {
          Fix(0L)
        } else {
          let r = power_star(Fix(-1L), addn_star([hi, lo, Fix(1L)]))
          hi = list2(list1(q_mabs), hi)
          r
        }
        muln_star([a, b, list2(list1(q_mfactorial), hi)])
      }
    }
  } else {
    list5_(list2(q_p_product, q_simp), exp_, i, lo, hi)
  }
}

// multiplication of sums

///|
fn gensumindex() -> Value raise {
  let gi = symval(q_d_genindex)
  let base = if symbolp(gi) { symbol_name(gi) } else { prin1_to_string(gi) }
  if symval(q_d_gensumnum).truthy() {
    let n = set(q_d_gensumnum, one_plus(symval(q_d_gensumnum)))
    sym(base + prin1_to_string(n))
  } else {
    sym(base)
  }
}

///|
fn sumtimes(x : Value, y : Value) -> Value raise {
  if x is Nil {
    y
  } else if y is Nil {
    x
  } else if (numberp(x) && zerop(x)) || (numberp(y) && zerop(y)) {
    Fix(0L)
  } else if atom(x) || !eq(caar(x), q_p_sum) {
    sumultin(x, y)
  } else if atom(y) || !eq(caar(y), q_p_sum) {
    sumultin(y, x)
  } else {
    let mut u = x
    let mut v = y
    if great(sum_arg(x), sum_arg(y)).truthy() {
      u = y
      v = x
    }
    let i = {
      let ind = gensumindex()
      u = subst(ind, sum_index(u), u)
      ind
    }
    let j = {
      let ind = gensumindex()
      v = subst(ind, sum_index(v), v)
      ind
    }
    if symval(q_d_cauchysum).truthy() &&
      eq(sum_upper(u), q_d_inf) &&
      eq(sum_upper(v), q_d_inf) {
      let inner = list5_(
        list1(q_p_sum),
        sumtimes(
          maxima_substitute(j, i, sum_arg(u)),
          maxima_substitute(sub_star(i, j), j, sum_arg(v)),
        ),
        j,
        sum_lower(u),
        sub_star(i, sum_lower(v)),
      )
      list5_(
        list1(q_p_sum),
        inner,
        i,
        addn_star([sum_lower(u), sum_lower(v)]),
        q_d_inf,
      )
    } else {
      let inner = list5_(
        list1(q_p_sum),
        sumtimes(sum_arg(u), sum_arg(v)),
        j,
        sum_lower(v),
        sum_upper(v),
      )
      list5_(list1(q_p_sum), inner, i, sum_lower(u), sum_upper(u))
    }
  }
}

///|
/// Multiplies x into a sum adjusting indices.
fn sumultin(x : Value, s : Value) -> Value raise {
  if atom(s) || !eq(caar(s), q_p_sum) {
    mul2_star(x, s)
  } else if free(x, sum_index(s)).truthy() {
    cons(car(s), cons(sumultin(x, sum_arg(s)), cddr(s)))
  } else {
    let ind = gensumindex()
    cons(
      car(s),
      cons(
        sumultin(x, subst(ind, sum_index(s), sum_arg(s))),
        cons(ind, cdddr(s)),
      ),
    )
  }
}

// addition of sums

///|
fn sumpls(sum : Value, out : Value) -> Value raise {
  let mut sum = sum
  if out is Nil {
    return cons(sum, Nil)
  }
  let l = cons(Nil, out)
  let mut out = l
  while true {
    // a
    if cdr(out) is Nil {
      return cons(sum, cdr(l))
    }
    let o = cadr(out)
    if !atom(o) &&
      consp(car(o)) &&
      eq(caar(o), q_p_sum) &&
      alike1(sum_arg(o), sum_arg(sum)).truthy() &&
      alike1(sum_index(o), sum_index(sum)).truthy() {
      if onediff(sum_upper(o), sum_lower(sum)).truthy() {
        sum = list5_(
          car(sum),
          sum_arg(sum),
          sum_index(sum),
          sum_lower(o),
          sum_upper(sum),
        )
        rplacd(out, cddr(out)) |> ignore
        continue
      } else if onediff(sum_upper(sum), sum_lower(o)).truthy() {
        sum = list5_(
          car(sum),
          sum_arg(sum),
          sum_index(sum),
          sum_lower(sum),
          sum_upper(o),
        )
        rplacd(out, cddr(out)) |> ignore
        continue
      }
    }
    out = cdr(out)
  }
  Nil
}

///|
fn onediff(x : Value, y : Value) -> Value raise {
  lbool(equal(Fix(1L), sub_star(y, x)))
}

///|
fn freesum(e : Value, b : Value, a : Value, q : Value) -> Value raise {
  muln_star([e, q, sub_star(add2_star(a, Fix(1L)), b)])
}

// linear operator stuff

///|
fn oper_apply(e : Value, z : Value) -> Value raise {
  let ol = symval(q_opers_list)
  if ol is Nil {
    let w = get(caar(e), q_operators)
    if w.truthy() {
      funcall(w, [e, Fix(1L), z])
    } else {
      simpargs(e, z)
    }
  } else if get(caar(e), caar(ol)).truthy() {
    let fun = cdar(ol)
    with_special(q_opers_list, cdr(ol), () => funcall(fun, [e, z]))
  } else {
    with_special(q_opers_list, cdr(ol), () => oper_apply(e, z))
  }
}

///|
/// Define an operator simplification, the same as antisymmetric,
/// commutative, linear, etc.  Here OP = operator name, FN = function of 1
/// argument to carry out operator-specific simplification.
/// 1. push operator name onto OPERS
/// 2. update $OPPROPERTIES
/// 3. push operator name and glue code onto *OPERS-LIST
/// 4. declare operator name as a feature, so declare(..., <op>) is
///    recognized
fn d_define_opproperty(op : Value, fn_ : Value) -> Value raise {
  if !symbolp(op) {
    merr("define_opproperty: first argument must be a symbol; found: ~M", [op])
    |> ignore
  }
  if !(symbolp(fn_) || (consp(fn_) && eq(caar(fn_), q_lambda))) {
    merr(
      "define_opproperty: second argument must be a symbol or lambda expression; found: ~M",
      [fn_],
    )
    |> ignore
  }
  set(q_opers, cons(op, symval(q_opers))) |> ignore
  set(q_d_opproperties, cons(list2(q_mlist, q_simp), reverse(symval(q_opers))))
  |> ignore
  let fn_glue = if symbolp(fn_) {
    lfunc("opproperty-glue", fn(args) raise {
      let e = arg(args, 0)
      let z = arg(args, 1)
      if fboundp(fn_) || mget(fn_, q_mexpr).truthy() {
        let e1 = with_special(q_d_simp, Nil, () => mfuncall(fn_, list1(e)))
        if d_mapatom(e1).truthy() {
          e1
        } else {
          oper_apply(e1, Nil)
        }
      } else {
        list2(
          list1(fn_),
          with_special(q_n_staropers_list, cdr(symval(q_n_staropers_list)), () => {
            oper_apply(e, z)
          }),
        )
      }
    })
  } else {
    lfunc("opproperty-glue", fn(args) raise {
      let e = arg(args, 0)
      let e1 = with_special(q_d_simp, Nil, () => mfuncall(fn_, list1(e)))
      if d_mapatom(e1).truthy() {
        e1
      } else {
        oper_apply(e1, Nil)
      }
    })
  }
  set(q_n_staropers_list, cons(cons(op, fn_glue), symval(q_n_staropers_list)))
  |> ignore
  mfuncall(q_d_declare, list2(op, q_d_feature))
}

///|
/// z = t means args already simplified.
fn linearize1(e : Value, z : Value) -> Value raise {
  linearize2(cons(car(e), mapcar(q => simpcheck(q, z), cdr(e))), Nil)
}

///|
fn opident(op : Value) -> Value raise {
  if eq(op, q_mplus) {
    Fix(0L)
  } else if eq(op, q_mtimes) {
    Fix(1L)
  } else {
    Nil
  }
}

///|
/// removes constantp stuff
fn rem_const(e : Value) -> Value raise {
  let mut a = list1(opident(caar(e)))
  let mut b = list1(opident(caar(e)))
  for x in cdr(e).iter() {
    if d_constantp(x).truthy() {
      a = cons(x, a)
    } else {
      b = cons(x, b)
    }
  }
  cons(
    simplifya(cons(list1(caar(e)), a), Nil),
    simplifya(cons(list1(caar(e)), b), Nil),
  )
}

///|
fn asum__partition_or_rem_const(e : Value) -> Value raise {
  if cddr(e).truthy() && (atom(caddr(e)) || d_subvarp(caddr(e)).truthy()) {
    partition(cadr(e), caddr(e), Fix(1L))
  } else {
    rem_const(cadr(e))
  }
}

///|
fn linearize2(e : Value, times : Value) -> Value raise {
  let c = linearconst(e)
  if c.truthy() {
    c
  } else if atom(cadr(e)) {
    oper_apply(e, t)
  } else if eq(caar(cadr(e)), q_mplus) {
    addn(
      mapcar(q => linearize2(cons(car(e), cons(q, cddr(e))), Nil), cdr(cadr(e))),
      t,
    )
  } else if eq(caar(cadr(e)), q_mtimes) && times is Nil {
    let z = asum__partition_or_rem_const(e)
    let w = linearize2(cons(car(e), cons(simplifya(cdr(z), t), cddr(e))), t)
    linearize3(w, e, car(z))
  } else {
    oper_apply(e, t)
  }
}

///|
fn linearconst(e : Value) -> Value raise {
  if mnump(cadr(e)).truthy() ||
    constant(cadr(e)).truthy() ||
    (
      cddr(e).truthy() &&
      (atom(caddr(e)) || memq(q_array, cdar(caddr(e))).truthy()) &&
      free(cadr(e), caddr(e)).truthy()
    ) {
    if zerop1(cadr(e)).truthy() ||
      (
        (eq(caar(e), q_p_sum) || eq(caar(e), q_p_integrate)) &&
        length(e) == 5 &&
        (
          eq(cadddr(e), q_d_minf) ||
          eq(car(cddddr(e)), q_d_inf) ||
          eq(car(cddddr(e)), q_d_infinity)
        ) &&
        eq(d_asksign(cadr(e)), q_d_zero)
      ) {
      Fix(0L)
    } else {
      let w = oper_apply(cons(car(e), cons(Fix(1L), cddr(e))), t)
      linearize3(w, e, cadr(e))
    }
  } else {
    Nil
  }
}

///|
fn asum__outative_or_linear(op : Value) -> Bool raise {
  getl(op, list2(q_d_outative, q_d_linear)).truthy()
}

///|
fn linearize3(w : Value, e : Value, x : Value) -> Value raise {
  if (eq(w, q_d_inf) || eq(w, q_d_minf) || eq(w, q_d_infinity)) &&
    numberp(x) &&
    zerop(x) {
    merr("LINEARIZE3: undefined form 0*inf: ~M", [e]) |> ignore
  }
  let w = mul2(simplifya(x, t), w)
  let w1 : Value = if atom(w) || asum__outative_or_linear(caar(w)) {
    Fix(1L)
  } else if eq(caar(w), q_mtimes) {
    let mut w1 = cons(list1(q_mtimes), Nil)
    for w2 in cdr(w).iter() {
      if atom(w2) || !asum__outative_or_linear(caar(w2)) {
        w1 = cons(w2, w1)
      }
    }
    nreverse(w1)
  } else {
    w
  }
  if !atom(w1) && (among(q_d_inf, w1).truthy() || among(q_d_minf, w1).truthy()) {
    infsimp(w)
  } else {
    w
  }
}

///|
fn rem_opers_p(p : Value) -> Value raise {
  let ol = symval(q_opers_list)
  if eq(caar(ol), p) {
    set(q_opers_list, cdr(p))
  } else {
    let mut l = ol
    while l.truthy() {
      if eq(caar(cdr(l)), p) {
        return rplacd(l, cddr(l))
      }
      l = cdr(l)
    }
    Nil
  }
}

///|
fn additive(e : Value, z : Value) -> Value raise {
  if get(caar(e), q_d_outative).truthy() {
    // Really a linearize!
    set(q_opers_list, copy_list(symval(q_opers_list))) |> ignore
    rem_opers_p(q_d_outative) |> ignore
    linearize1(e, z)
  } else if mplusp(cadr(e)).truthy() {
    addn(
      mapcar(
        q => {
          with_special(q_opers_list, symval(q_n_staropers_list), () => {
            oper_apply(cons(car(e), cons(q, cddr(e))), z)
          })
        },
        cdr(cadr(e)),
      ),
      z,
    )
  } else {
    oper_apply(e, z)
  }
}

///|
fn multiplicative(e : Value, z : Value) -> Value raise {
  if mtimesp(cadr(e)).truthy() {
    muln(
      mapcar(
        q => {
          with_special(q_opers_list, symval(q_n_staropers_list), () => {
            oper_apply(cons(car(e), cons(q, cddr(e))), z)
          })
        },
        cdr(cadr(e)),
      ),
      z,
    )
  } else {
    oper_apply(e, z)
  }
}

///|
fn outative(e : Value, z : Value) -> Value raise {
  let e = cons(car(e), mapcar(q => simpcheck(q, z), cdr(e)))
  if get(caar(e), q_d_additive).truthy() {
    set(q_opers_list, copy_list(symval(q_opers_list))) |> ignore
    rem_opers_p(q_d_additive) |> ignore
    return linearize1(e, t)
  }
  let c = linearconst(e)
  if c.truthy() {
    c
  } else if mtimesp(cadr(e)).truthy() {
    let u = asum__partition_or_rem_const(e)
    let w = oper_apply(cons(car(e), cons(simplifya(cdr(u), t), cddr(e))), t)
    linearize3(w, e, car(u))
  } else {
    oper_apply(e, t)
  }
}

///|
fn evenfun(e : Value, z : Value) -> Value raise {
  if cdr(e) is Nil || cddr(e).truthy() {
    merr("Function declared 'even' takes exactly one argument; found ~M", [e])
    |> ignore
  }
  let arg_ = simpcheck(cadr(e), z)
  oper_apply(
    list2(car(e), if mminusp(arg_).truthy() { neg(arg_) } else { arg_ }),
    t,
  )
}

///|
fn oddfun(e : Value, z : Value) -> Value raise {
  if cdr(e) is Nil || cddr(e).truthy() {
    merr("Function declared 'odd' takes exactly one argument; found ~M", [e])
    |> ignore
  }
  let arg_ = simpcheck(cadr(e), z)
  if mminusp(arg_).truthy() {
    neg(oper_apply(list2(car(e), neg(arg_)), t))
  } else {
    oper_apply(list2(car(e), arg_), t)
  }
}

///|
fn commutative1(e : Value, z : Value) -> Value raise {
  oper_apply(
    cons(
      car(e),
      reverse(
        sort_list(mapcar(q => simpcheck(q, z), cdr(e)), (a, b) => {
          great(a, b).truthy()
        }),
      ),
    ),
    t,
  )
}

///|
fn antisym(e : Value, z : Value) -> Value raise {
  let mut e = e
  if symval(q_d_dotscrules).truthy() && mnctimesp(e).truthy() {
    e = with_special(q_d_dotexptsimp, Nil, () => simpnct(e, Fix(1L), Nil))
  }
  if d_atom(e).truthy() {
    e
  } else {
    antisym1(e, z)
  }
}

///|
fn antisym1(e : Value, z : Value) -> Value raise {
  let mut antisym_sign : Value = Nil
  let mut l = mapcar(q => simpcheck(q, z), cdr(e))
  if !eq(caar(e), q_mnctimes) || freel(l, q_mnctimes).truthy() {
    let (l1, s1) = bbsort1(l)
    l = l1
    antisym_sign = s1
  }
  if equal(l, Fix(0L)) {
    Fix(0L)
  } else {
    let e = oper_apply(cons(car(e), l), t)
    if antisym_sign is Nil {
      e
    } else {
      neg(e)
    }
  }
}

///|
fn bbsort1(l : Value) -> (Value, Value) raise {
  let mut l = l
  let mut antisym_sign : Value = Nil
  if l is Nil || cdr(l) is Nil {
    return (l, antisym_sign)
  }
  let sl = list2(Nil, car(l))
  while true {
    // loop
    l = cdr(l)
    if l is Nil {
      return (nreverse(cdr(sl)), antisym_sign)
    }
    let mut sl1 = sl
    while true {
      // loop1
      if cdr(sl1) is Nil {
        rplacd(sl1, cons(car(l), Nil)) |> ignore
        break
      } else if alike1(car(l), cadr(sl1)).truthy() {
        return (Fix(0L), Nil)
      } else if great(car(l), cadr(sl1)).truthy() {
        rplacd(sl1, cons(car(l), cdr(sl1))) |> ignore
        break
      } else {
        antisym_sign = lbool(antisym_sign is Nil)
        sl1 = cdr(sl1)
      }
    }
  }
  (l, antisym_sign)
}

///|
fn nary1(e : Value, z : Value) -> Value raise {
  oper_apply(nary2(e, z), z)
}

///|
fn nary2(e : Value, z : Value) -> Value raise {
  let mut ans : Value = Nil
  let mut some_change = false
  for x in cdr(e).iter() {
    ans = if !atom(x) && eq(caar(x), caar(e)) {
      some_change = true
      nconc(reverse(cdr(x)), ans)
    } else {
      cons(x, ans)
    }
  }
  if some_change {
    nary2(cons(car(e), nreverse(ans)), z)
  } else {
    simpargs(e, z)
  }
}

///|
fn lassociative(e : Value, z : Value) -> Value raise {
  let ans0 = oper_apply(cons(car(e), total_nary(e)), z)
  let ans = if consp(ans0) { cdr(ans0) } else { Nil }
  if cddr(ans) is Nil || !eq(caar(ans0), caar(e)) {
    ans0
  } else {
    let mut newans = list3(car(ans0), car(ans), cadr(ans))
    let mut ans = cddr(ans)
    while ans.truthy() {
      newans = list3(car(ans0), newans, car(ans))
      ans = cdr(ans)
    }
    newans
  }
}

///|
fn rassociative(e : Value, z : Value) -> Value raise {
  let ans0 = oper_apply(cons(car(e), total_nary(e)), z)
  let mut ans = if consp(ans0) { cdr(ans0) } else { Nil }
  if cddr(ans) is Nil || !eq(caar(ans0), caar(e)) {
    ans0
  } else {
    ans = nreverse(ans)
    let mut newans = list3(car(ans0), cadr(ans), car(ans))
    let mut ans = cddr(ans)
    while ans.truthy() {
      newans = list3(car(ans0), car(ans), newans)
      ans = cdr(ans)
    }
    newans
  }
}

///|
fn total_nary(e : Value) -> Value raise {
  let mut ans : Value = Nil
  for x in cdr(e).iter() {
    ans = if !atom(x) && eq(caar(x), caar(e)) {
      nconc(reverse(total_nary(x)), ans)
    } else {
      cons(x, ans)
    }
  }
  nreverse(ans)
}

///|
fn asum__push_oper(name : Value, fun : Value) -> Unit {
  set(q_opers, cons(name, symval(q_opers))) |> ignore
  set(q_n_staropers_list, cons(cons(name, fun), symval(q_n_staropers_list)))
  |> ignore
}

///|
fn init_asum() -> Unit raise {
  defvar_init(
    q_d_opproperties,
    cons(
      list2(q_mlist, q_simp),
      list([
        q_d_linear, q_d_additive, q_d_multiplicative, q_d_outative, q_d_evenfun,
        q_d_oddfun, q_d_commutative, q_d_symmetric, q_d_antisymmetric, q_d_nary,
        q_d_lassociative, q_d_rassociative,
      ]),
    ),
  )
  putprop(q_d_opproperties, q_neverset, q_assign) |> ignore
  let recips = [
    q_p_cot, q_p_tan, q_p_csc, q_p_sin, q_p_sec, q_p_cos, q_p_coth, q_p_tanh, q_p_csch,
    q_p_sinh, q_p_sech, q_p_cosh,
  ]
  let mut i = 0
  while i + 1 < recips.length() {
    putprop(recips[i], recips[i + 1], q_recip) |> ignore
    putprop(recips[i + 1], recips[i], q_recip) |> ignore
    i += 2
  }
  // Factorial has mirror symmetry
  putprop(q_mfactorial, t, q_commutes_with_conjugate) |> ignore
  asum__push_oper(q_d_additive, q_additive)
  asum__push_oper(q_d_multiplicative, q_multiplicative)
  asum__push_oper(q_d_outative, q_outative)
  putprop(q_p_sum, t, q_d_outative) |> ignore
  putprop(q_p_sum, t, q_opers) |> ignore
  putprop(q_p_integrate, t, q_d_outative) |> ignore
  putprop(q_p_integrate, t, q_opers) |> ignore
  putprop(q_p_limit, t, q_d_outative) |> ignore
  putprop(q_p_limit, t, q_opers) |> ignore
  asum__push_oper(q_d_evenfun, q_evenfun)
  asum__push_oper(q_d_oddfun, q_oddfun)
  asum__push_oper(q_d_commutative, q_commutative1)
  asum__push_oper(q_d_symmetric, q_commutative1)
  asum__push_oper(q_d_antisymmetric, q_antisym)
  asum__push_oper(q_d_nary, q_nary1)
  asum__push_oper(q_d_lassociative, q_lassociative)
  asum__push_oper(q_d_rassociative, q_rassociative)
}
