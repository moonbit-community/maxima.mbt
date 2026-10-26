// Port of src/sin.lisp (part 3): extension of the integrator for more
// integrals with power functions (the m2-exp-type patterns,
// INTEGRATE-EXP-SPECIAL) and FACSUM-EXPONENT.

// ---------------------------------------------------------------------------
// Recognizers.

///|
/// Recognize (a^(c*(z^r)^p+d)^v
fn m2_exp_type_1a(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mexpt) ((mexpt) (a freevar02 @var2) ((mplus) ((coeffpp) (d freevar2 @var2)) ((coefft) (c freevar02 @var2) ((mexpt) ((mexpt) (z varp2 @var2) (r freevar02 @var2)) (p freevar2 @var2))))) (v freevar2 @var2))",
      var2,
    ),
  )
}

///|
/// Recognize z^v*a^(b*z^r+d)
fn m2_exp_type_2(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (v freevar02 @var2)) ((mexpt) (a freevar02 @var2) ((mplus) ((coeffpp) (d freevar2 @var2)) ((coefft) (b freevar02 @var2) ((mexpt) (z varp2 @var2) (r freevar02 @var2))))))",
      var2,
    ),
  )
}

///|
/// Recognize z^v*%e^(a*z^r+b)^u
fn m2_exp_type_2_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (v freevar02 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (b freevar2 @var2)) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) (r freevar02 @var2))))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize (a*z+b)^p*%e^(c*z+d)
fn m2_exp_type_3(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) ((mplus) ((coefft) (a freevar02 @var2) (z varp2 @var2)) ((coeffpp) (b freevar2 @var2))) (p freevar02 @var2)) ((mexpt) $%e ((mplus) ((coefft) (c freevar02 @var2) (z varp2 @var2)) ((coeffpp) (d freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize d^(a*z^2+b/z^2+c)
fn m2_exp_type_4(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mexpt) (d freevar02 @var2) ((mplus) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) 2)) ((coefft) (b freevar02 @var2) ((mexpt) (z varp2 @var2) -2)) ((coeffpp) (c freevar2 @var2))))",
      var2,
    ),
  )
}

///|
/// Recognize z^(2*n)*d^(a*z^2+b/z^2+c)
fn m2_exp_type_4_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar02 @var2)) ((mexpt) (d freevar02 @var2) ((mplus) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) 2)) ((coefft) (b freevar02 @var2) ((mexpt) (z varp2 @var2) -2)) ((coeffpp) (c freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*d^(a*z^2+b*z+c)
fn m2_exp_type_5(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) (d freevar02 @var2) ((mplus) ((coeffpt) (a freevar2 @var2) ((mexpt) (z varp2 @var2) 2)) ((coeffpt) (b freevar2 @var2) (z varp2 @var2)) ((coeffpp) (c freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*(%e^(a*z^2+b*z+c))^u
fn m2_exp_type_5_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar02 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (c freevar2 @var2)) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) 2)) ((coefft) (b freevar02 @var2) (z varp2 @var2)))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*d^(a*sqrt(z)+b*z+c)
fn m2_exp_type_6(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar02 @var2)) ((mexpt) (d freevar02 @var2) ((mplus) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coefft) (b freevar02 @var2) (z varp2 @var2)) ((coeffpp) (c freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*(%e^(a*sqrt(z)+b*z+c))^u
fn m2_exp_type_6_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar02 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (c freevar2 @var2)) ((coefft) (a freevar02 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coefft) (b freevar02 @var2) (z varp2 @var2)))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*a^(b*z^r+e)*h^(c*z^r+g)
fn m2_exp_type_7(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) (a freevar02 @var2) ((mplus) ((coefft) (b freevar02 @var2) ((mexpt) (z varp2 @var2) (r freevar02 @var2))) ((coeffpp) (e freevar2 @var2)))) ((mexpt) (h freevar02 @var2) ((mplus) ((coefft) (c freevar02 @var2) ((mexpt) (z varp2 @var2) (r1 freevar02 @var2))) ((coeffpp) (g freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^v*(%e^(b*z^r+e))^q*(%e^(c*z^r+g))^u
fn m2_exp_type_7_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (v freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (e freevar2 @var2)) ((coefft) (b freevar02 @var2) ((mexpt) (z varp2 @var2) (r freevar02 @var2))))) (q freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (g freevar2 @var2)) ((coefft) (c freevar02 @var2) ((mexpt) (z varp2 @var2) (r1 freevar02 @var2))))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z)+f*z+g)
fn m2_exp_type_8(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (a freevar02 @var2) ((mplus) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)) ((coeffpp) (e freevar2 @var2)))) ((mexpt) (h freevar02 @var2) ((mplus) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)) ((coeffpp) (g freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize (%e^(b*sqrt(z)+d*z+e))^u*(%e^(c*sqrt(z)+f*z+g))^v
fn m2_exp_type_8_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (e freevar2 @var2)) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)))) (u freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (g freevar2 @var2)) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)))) (v freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize (%e^(b*z^r+e))^u*(%e^(c*z^r+g))^v
fn m2_exp_type_8_2(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (e freevar2 @var2)) ((coefft) (b freevar2 @var2) ((mexpt) (z varp2 @var2) (r freevar02 @var2))))) (u freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (g freevar2 @var2)) ((coefft) (c freevar2 @var2) ((mexpt) (z varp2 @var2) (r1 freevar02 @var2))))) (v freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*a^(b*z^2+d*z+e)*h^(c*z^2+f*z+g)
fn m2_exp_type_9(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) (a freevar02 @var2) ((mplus) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) 2)) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)) ((coeffpp) (e freevar2 @var2)))) ((mexpt) (h freevar02 @var2) ((mplus) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) 2)) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)) ((coeffpp) (g freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*(%e^(b*z^2+d*z+e))^q*(%e^(c*z^2+f*z+g))^u
fn m2_exp_type_9_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (e freevar2 @var2)) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) 2)) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)))) (q freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (g freevar2 @var2)) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) 2)) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z+)f*z+g)
fn m2_exp_type_10(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) (a freevar02 @var2) ((mplus) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)) ((coeffpp) (e freevar2 @var2)))) ((mexpt) (h freevar02 @var2) ((mplus) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)) ((coeffpp) (g freevar2 @var2)))))",
      var2,
    ),
  )
}

///|
/// Recognize z^n*(%e^(b*sqrt(z)+d*z+e))^q*(%e^(c*sqrt(z)+f*z+g))^u
fn m2_exp_type_10_1(expr : Value, var2 : Value) -> Value raise {
  m2(
    expr,
    sin__pv(
      "((mtimes) ((mexpt) (z varp2 @var2) (n freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (e freevar2 @var2)) ((coeffpt) (b freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (d freevar2 @var2) (z varp2 @var2)))) (q freevar2 @var2)) ((mexpt) ((mexpt) $%e ((mplus) ((coeffpp) (g freevar2 @var2)) ((coeffpt) (c freevar2 @var2) ((mexpt) (z varp2 @var2) ((rat) 1 2))) ((coeffpt) (f freevar2 @var2) (z varp2 @var2)))) (u freevar2 @var2)))",
      var2,
    ),
  )
}

///|
/// The variables of a SCHATCHEN-COND clause are all bound (non-nil) in W.
fn sin__sc_bound(w : Value, vars : Array[Value]) -> Bool raise {
  if w is Nil {
    return false
  }
  for v in vars {
    if !cdras(v, w).truthy() {
      return false
    }
  }
  true
}

///|
/// `($log x)`
fn sin__lg(x : Value) -> Value raise {
  ftake(q_p_log, [x])
}

///|
fn sin__dbg(fmt : String, w : Value) -> Unit raise {
  if sin__debug() {
    format(t, fmt, [w]) |> ignore
  }
}

///|
fn integrate_exp_special(expr : Value, var2 : Value) -> Value raise {
  // First factor the expression.
  let expr = d_factor(expr)
  // Remove constant factors.
  let w0 = partition(expr, var2, Fix(1L))
  let const_ = car(w0)
  let expr = cdr(w0)
  let e_ = q_d__pcte
  let half = () => div(Fix(1L), Fix(2L))
  let gi = list1(q_p_gamma_incomplete)
  let mut w : Value = Nil

  // Type 1a: (a^(c*(z^r)^p+d)^v
  w = m2_exp_type_1a(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_c, q_d, q_r, q_p, q_v]) {
    let a = sin__as(q_a, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let r = sin__as(q_r, w)
    let p = sin__as(q_p, w)
    let v = sin__as(q_v, w)
    sin__dbg("~&Type 1a: (a^(c*(z^r)^p+d)^v : w = ~A~%", w)
    return muln_([
      Fix(-1L),
      const_,
      // 1/(p*r*(a^(c*v*(var2^r)^p)))
      inv(muln_([p, r, power(a, muln_([c, v, power(power(var2, r), p)]))])),
      var2,
      // (a^(d+c*(var2^r)^p))^v
      power(power(a, add2(d, mul2(c, power(power(var2, r), p)))), v),
      // gamma_h_incomplete(1/(p*r), -c*v*(var2^r)^p*log(a))
      take(gi, [
        inv(mul2(p, r)),
        muln_([
          Fix(-1L),
          c,
          v,
          power(power(var2, r), p),
          take(list1(q_p_log), [a]),
        ]),
      ]),
      // (-c*v*(var2^r)^p*log(a))^(-1/(p*r))
      power(
        muln_([
          Fix(-1L),
          c,
          v,
          power(power(var2, r), p),
          take(list1(q_p_log), [a]),
        ]),
        div(Fix(-1L), mul2(p, r)),
      ),
    ])
  }

  // Type 2: z^v*a^(b*z^r+d)
  w = m2_exp_type_2(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_d, q_v, q_r]) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let d = sin__as(q_d, w)
    let v = sin__as(q_v, w)
    let r = sin__as(q_r, w)
    sin__dbg("~&Type 2: z^v*a^(b*z^r+d) : w = ~A~%", w)
    return muln_([
      const_,
      div(Fix(-1L), r),
      power(a, d),
      power(var2, add2(v, Fix(1L))),
      ftake(q_p_gamma_incomplete, [
        div(add2(v, Fix(1L)), r),
        muln_([Fix(-1L), b, power(var2, r), sin__lg(a)]),
      ]),
      power(
        muln_([Fix(-1L), b, power(var2, r), sin__lg(a)]),
        mul2(Fix(-1L), div(add2(v, Fix(1L)), r)),
      ),
    ])
  }

  // Type 2-1: z^v*(%e^(a*z^r+b))^u
  w = m2_exp_type_2_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_v, q_r, q_u]) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let v = sin__as(q_v, w)
    let r = sin__as(q_r, w)
    let u = sin__as(q_u, w)
    sin__dbg("~&Type 2-1: z^v*(%e^(a*z^r+b))^u : w = ~A~%", w)
    return muln_([
      const_,
      Fix(-1L),
      inv(r),
      power(e_, muln_([Fix(-1L), a, u, power(var2, r)])),
      power(power(e_, add2(mul2(a, power(var2, r)), b)), u),
      power(var2, add2(v, Fix(1L))),
      power(
        muln_([Fix(-1L), a, u, power(var2, r)]),
        div(mul2(Fix(-1L), add2(v, Fix(1L))), r),
      ),
      take(gi, [
        div(add2(v, Fix(1L)), r),
        muln_([Fix(-1L), a, u, power(var2, r)]),
      ]),
    ])
  }

  // Type 3: (a*z+b)^p*%e^(c*z+d)
  w = m2_exp_type_3(expand_base_of_exp(facsum_exponent(expr, var2), var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_p]) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let p = sin__as(q_p, w)
    sin__dbg("~&Type 3: (a*z+b)^p*%e^(c*z+d) : w = ~A~%", w)
    return muln_([
      const_,
      div(Fix(-1L), a),
      power(e_, sub(d, div(mul2(b, c), a))),
      power(add2(b, mul2(a, var2)), add2(p, Fix(1L))),
      ftake(q_p_expintegral_e, [
        mul2(Fix(-1L), p),
        muln_([div(Fix(-1L), a), c, add2(b, mul2(a, var2))]),
      ]),
    ])
  }

  // Type 4: d^(a*z^2+b/z^2+c)
  w = m2_exp_type_4(expr, var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d]) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    // Do not simplify erfc(-x) !
    return with_special(q_d_trigsign, Nil, () => {
      sin__dbg("~&Type 4: d^(a*z^2+b/z^2+c) : w = ~A~%", w)
      let sa = () => power(muln_([Fix(-1L), a, sin__lg(d)]), half())
      let sb = () => power(muln_([Fix(-1L), b, sin__lg(d)]), half())
      mul3(
        const_,
        div(Fix(1L), mul2(Fix(4L), sa())),
        muln_([
          power(d, c),
          power(q_d__pctpi, half()),
          power(e_, muln_([Fix(-2L), sa(), sb()])),
          add2(
            ftake(q_p_erfc, [add2(div(sb(), var2), muln_([Fix(-1L), var2, sa()]))]),
            muln_([
              Fix(-1L),
              power(e_, muln_([Fix(4L), sa(), sb()])),
              ftake(q_p_erfc, [add2(mul2(var2, sa()), div(sb(), var2))]),
            ]),
          ),
        ]),
      )
    })
  }

  // Type 4-1: z^(2*n)*d^(a*z^2+b/z^2+c)
  w = m2_exp_type_4_1(expr, var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_n]) &&
    poseven(cdras(q_n, w)).truthy() { // only for n a positive, even integer
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let n = sin__as(q_n, w)
    // Do not simplify erfc(-x) !
    return with_special(q_d_trigsign, Nil, () => {
      let original_a = a
      let a = gensym()
      sin__dbg("~&Type 4-1: z^(2*n)*d^(a*z^2+b/z^2+c) : w = ~A~%", w)
      let n = div(n, Fix(2L))
      let sa = () => power(muln_([Fix(-1L), a, sin__lg(d)]), half())
      let sb = () => power(muln_([Fix(-1L), b, sin__lg(d)]), half())
      maxima_substitute(
        original_a,
        a,
        muln_([
          const_,
          div(Fix(1L), Fix(4L)),
          power(d, c),
          power(q_d__pctpi, half()),
          d_diff(
            list([
              div(
                mul2(
                  power(sin__lg(d), mul2(Fix(-1L), n)),
                  sub(
                    mul2(
                      power(e_, muln_([Fix(-2L), sa(), sb()])),
                      ftake(q_p_erfc, [
                        add2(div(sb(), var2), muln_([Fix(-1L), var2, sa()])),
                      ]),
                    ),
                    mul2(
                      power(e_, muln_([Fix(2L), sa(), sb()])),
                      ftake(q_p_erfc, [add2(mul2(var2, sa()), div(sb(), var2))]),
                    ),
                  ),
                ),
                sa(),
              ),
              a,
              n,
            ]),
          ),
        ]),
      )
    })
  }

  // Type 5: z^n*d^(a*z^2+b*z+c)
  w = m2_exp_type_5(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let n = sin__as(q_n, w)
    sin__dbg("~&Type 5: z^n*d^(a*z^2+b*z+c) : w = ~A~%", w)
    let f1 = div(Fix(-1L), mul2(Fix(2L), power(mul2(a, sin__lg(d)), half())))
    let f2a = power(d, sub(c, div(mul2(b, b), mul2(Fix(4L), a))))
    let index = gensumindex()
    let f2b = with_special(q_d_simpsum, t, () => {
      let bz = () => add2(b, mul3(Fix(2L), a, var2))
      mfuncall(
        q_d_sum,
        list([
          muln_([
            power(Fix(2L), sub(index, n)),
            ftake(q_p_binomial, [n, index]),
            ftake(q_p_gamma_incomplete, [
              div(add2(index, Fix(1L)), Fix(2L)),
              mul3(
                div(Fix(-1L), mul2(Fix(4L), a)),
                power(bz(), Fix(2L)),
                sin__lg(d),
              ),
            ]),
            power(mul2(a, sin__lg(d)), mul2(Fix(-1L), add2(n, half()))),
            power(mul3(Fix(-1L), b, sin__lg(d)), sub(n, index)),
            power(mul2(bz(), sin__lg(d)), add2(index, Fix(1L))),
            power(
              mul3(div(Fix(-1L), a), power(bz(), Fix(2L)), sin__lg(d)),
              mul2(div(Fix(-1L), Fix(2L)), add2(index, Fix(1L))),
            ),
          ]),
          index,
          Fix(0L),
          n,
        ]),
      )
    })
    return mul3(const_, f1, mul2(f2a, f2b))
  }

  // Type 5-1: z^n*(%e^(a*z^2+b*z+c))^u
  w = m2_exp_type_5_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_u, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let u = sin__as(q_u, w)
    let n = sin__as(q_n, w)
    sin__dbg("~&Type 5-1: z^n*(%e^(a*z^2+b*z+c))^u : w = ~A~%", w)
    let f1 = div(Fix(-1L), Fix(2L))
    let f2 = power(
      e_,
      add2(
        mul2(Fix(-1L), div(mul3(b, b, u), mul2(Fix(4L), a))),
        mul3(Fix(-1L), u, add2(mul3(a, var2, var2), mul2(b, var2))),
      ),
    )
    let f3 = power(a, mul2(Fix(-1L), add2(n, Fix(1L))))
    let f4 = power(
      power(e_, addn_([mul3(a, var2, var2), mul2(b, var2), c])),
      u,
    )
    let index = gensumindex()
    let f5 = with_special(q_d_simpsum, t, () => {
      let bz = () => add2(b, mul3(Fix(2L), a, var2))
      dosum(
        muln_([
          power(Fix(2L), sub(index, n)),
          power(mul2(Fix(-1L), b), sub(n, index)),
          power(bz(), add2(index, Fix(1L))),
          power(
            div(mul3(Fix(-1L), u, power(bz(), Fix(2L))), a),
            mul2(div(Fix(-1L), Fix(2L)), add2(index, Fix(1L))),
          ),
          take(list1(q_p_binomial), [n, index]),
          take(gi, [
            div(add2(index, Fix(1L)), Fix(2L)),
            div(mul3(Fix(-1L), u, power(bz(), Fix(2L))), mul2(Fix(4L), a)),
          ]),
        ]),
        index,
        Fix(0L),
        n,
        t,
      )
    })
    return muln_([const_, f1, f2, f3, f4, f5])
  }

  // Type 6: z^n*d^(a*sqrt(z)+b*z+c)
  w = m2_exp_type_6(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let n = sin__as(q_n, w)
    sin__dbg("~&Type 6: z^n*d^(a*sqrt(z)+b*z+c) : w = ~A~%", w)
    let f1 = power(Fix(2L), mul2(Fix(-1L), add2(mul2(Fix(2L), n), Fix(1L))))
    let f2 = power(d, sub(c, div(mul2(a, a), mul2(Fix(4L), b))))
    let f3 = power(mul2(b, sin__lg(d)), mul2(Fix(-2L), add2(n, Fix(1L))))
    let index1 = gensumindex()
    let index2 = gensumindex()
    let f4 = with_special(q_d_simpsum, t, () => {
      let ab = () => add2(a, mul3(Fix(2L), b, power(var2, half())))
      mfuncall(
        q_d_sum,
        list([
          mfuncall(
            q_d_sum,
            list([
              muln_([
                power(Fix(-1L), sub(index1, index2)),
                power(Fix(4L), index1),
                ftake(q_p_binomial, [index1, index2]),
                ftake(q_p_binomial, [n, index1]),
                sin__lg(d),
                power(
                  mul2(a, sin__lg(d)),
                  sub(mul2(Fix(2L), n), add2(index1, index2)),
                ),
                power(mul2(ab(), sin__lg(d)), add2(index1, index2)),
                power(
                  mul3(div(Fix(-1L), b), power(ab(), Fix(2L)), sin__lg(d)),
                  mul2(
                    div(Fix(-1L), Fix(2L)),
                    addn_([index1, index2, Fix(1L)]),
                  ),
                ),
                add2(
                  muln_([
                    Fix(2L),
                    b,
                    power(
                      mul3(div(Fix(-1L), b), power(ab(), Fix(2L)), sin__lg(d)),
                      half(),
                    ),
                    ftake(q_p_gamma_incomplete, [
                      div(addn_([index1, index2, Fix(2L)]), Fix(2L)),
                      mul3(
                        div(Fix(-1L), mul2(Fix(4L), b)),
                        power(ab(), Fix(2L)),
                        sin__lg(d),
                      ),
                    ]),
                  ]),
                  muln_([
                    a,
                    ab(),
                    sin__lg(d),
                    ftake(q_p_gamma_incomplete, [
                      div(addn_([index1, index2, Fix(1L)]), Fix(2L)),
                      mul3(
                        div(Fix(-1L), mul2(Fix(4L), b)),
                        power(ab(), Fix(2L)),
                        sin__lg(d),
                      ),
                    ]),
                  ]),
                ),
              ]),
              index2,
              Fix(0L),
              index1,
            ]),
          ),
          index1,
          Fix(0L),
          n,
        ]),
      )
    })
    return muln_([const_, f1, f2, f3, f4])
  }

  // Type 6-1: z^n*(%e^(a*sqrt(z)+b*z+c))^u
  w = m2_exp_type_6_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_u, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let u = sin__as(q_u, w)
    let n = sin__as(q_n, w)
    sin__dbg("~&Type 6-1: z^n*(%e^(a*sqrt(z)+b*z+c))^u : w = ~A~%", w)
    let f1 = power(Fix(2L), mul2(Fix(-1L), add2(mul2(Fix(2L), n), Fix(1L))))
    let f2 = power(
      e_,
      add2(
        div(muln_([Fix(-1L), u, a, a]), mul2(Fix(4L), b)),
        mul3(
          Fix(-1L),
          u,
          add2(mul2(a, power(var2, half())), mul2(b, var2)),
        ),
      ),
    )
    let f3 = power(b, mul2(Fix(-2L), add2(n, Fix(1L))))
    let f4 = power(
      power(e_, addn_([mul2(a, power(var2, half())), mul2(b, var2), c])),
      u,
    )
    let index1 = gensumindex()
    let index2 = gensumindex()
    let f5 = with_special(q_d_simpsum, t, () => {
      let ab = () => add2(a, mul3(Fix(2L), b, power(var2, half())))
      dosum(
        dosum(
          muln_([
            power(Fix(-1L), sub(index1, index2)),
            power(Fix(4L), index1),
            power(a, addn_([neg(index2), neg(index1), mul2(Fix(2L), n)])),
            power(ab(), add2(index1, index2)),
            power(
              div(mul3(Fix(-1L), u, power(ab(), Fix(2L))), b),
              mul2(div(Fix(-1L), Fix(2L)), addn_([index1, index2, Fix(1L)])),
            ),
            take(list1(q_p_binomial), [index1, index2]),
            take(list1(q_p_binomial), [n, index1]),
            add2(
              mul3(
                a,
                ab(),
                take(gi, [
                  div(addn_([index1, index2, Fix(1L)]), Fix(2L)),
                  div(
                    mul3(Fix(-1L), u, power(ab(), Fix(2L))),
                    mul2(Fix(4L), b),
                  ),
                ]),
              ),
              muln_([
                inv(u),
                power(div(mul3(Fix(-1L), u, power(ab(), Fix(2L))), b), half()),
                mul2(Fix(2L), b),
                take(gi, [
                  div(addn_([index1, index2, Fix(2L)]), Fix(2L)),
                  div(
                    mul3(Fix(-1L), u, power(ab(), Fix(2L))),
                    mul2(Fix(4L), b),
                  ),
                ]),
              ]),
            ),
          ]),
          index2,
          Fix(0L),
          index1,
          t,
        ),
        index1,
        Fix(0L),
        n,
        t,
      )
    })
    return muln_([const_, f1, f2, f3, f4, f5])
  }

  // Type 7: z^n*a^(b*z^r+e)*h^(c*z^r+g)
  w = m2_exp_type_7(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_e, q_g, q_h, q_r, q_n]) &&
    eq(d_sign(sub(cdras(q_r, w), cdras(q_r1, w))), q_d_zero) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let e = sin__as(q_e, w)
    let g = sin__as(q_g, w)
    let h = sin__as(q_h, w)
    let r = sin__as(q_r, w)
    let n = sin__as(q_n, w)
    sin__dbg("~&Type 7: z^n*a^(b*z^r+e)*h^(c*z^r+g) : w = ~A~%", w)
    let n = add2(n, Fix(1L))
    return muln_([
      const_,
      power(var2, n),
      div(Fix(-1L), r),
      power(a, e),
      power(h, g),
      power(
        mul3(
          Fix(-1L),
          power(var2, r),
          add2(mul2(b, sin__lg(a)), mul2(c, sin__lg(h))),
        ),
        div(mul2(Fix(-1L), n), r),
      ),
      ftake(q_p_gamma_incomplete, [
        div(n, r),
        mul3(
          Fix(-1L),
          power(var2, r),
          add2(mul2(b, sin__lg(a)), mul2(c, sin__lg(h))),
        ),
      ]),
    ])
  }

  // Type 7-1: z^v*(%e^(b*z^r+e))^q*(%e^(c*z^r+g))^u
  w = m2_exp_type_7_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_b, q_c, q_e, q_g, q_r, q_v, q_q, q_u]) &&
    eq(d_sign(sub(cdras(q_r, w), cdras(q_r1, w))), q_d_zero) {
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let e = sin__as(q_e, w)
    let g = sin__as(q_g, w)
    let r = sin__as(q_r, w)
    let v = sin__as(q_v, w)
    let q = sin__as(q_q, w)
    let u = sin__as(q_u, w)
    sin__dbg(
      "~&Type 7-1: z^v*(%e^(b*z^r+e))^q*(%e^(c*z^r+g))^u : w = ~A~%",
      w,
    )
    let bc = () => add2(mul2(b, q), mul2(c, u))
    return muln_([
      const_,
      div(Fix(-1L), r),
      power(e_, mul3(Fix(-1L), power(var2, r), bc())),
      power(power(e_, add2(e, mul2(b, power(var2, r)))), q),
      power(power(e_, add2(g, mul2(c, power(var2, r)))), u),
      power(var2, add2(v, Fix(1L))),
      power(
        mul3(Fix(-1L), power(var2, r), bc()),
        div(mul2(Fix(-1L), add2(v, Fix(1L))), r),
      ),
      take(gi, [
        div(add2(v, Fix(1L)), r),
        mul3(Fix(-1L), power(var2, r), bc()),
      ]),
    ])
  }

  // Type 8: a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z)+f*z+g)
  w = m2_exp_type_8(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h]) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let h = sin__as(q_h, w)
    if sin__debug() {
      format(t, "~&Type 8: a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z)+f*z+g)", [])
      |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let dl = () => add2(mul2(d, sin__lg(a)), mul2(f, sin__lg(h)))
    let bl = () => add2(mul2(b, sin__lg(a)), mul2(c, sin__lg(h)))
    return muln_([
      const_,
      div(Fix(1L), Fix(2L)),
      power(a, e),
      power(h, g),
      add2(
        muln_([
          Fix(2L),
          power(a, add2(mul2(b, power(var2, half())), mul2(d, var2))),
          power(h, add2(mul2(c, power(var2, half())), mul2(f, var2))),
          div(Fix(1L), dl()),
        ]),
        muln_([
          Fix(-1L),
          power(q_d__pctpi, half()),
          power(
            e_,
            mul2(
              Fix(-1L),
              div(power(bl(), Fix(2L)), mul2(Fix(4L), dl())),
            ),
          ),
          ftake(q_p_erfi, [
            div(
              addn_([
                mul2(b, sin__lg(a)),
                mul2(c, sin__lg(h)),
                mul3(Fix(2L), power(var2, half()), dl()),
              ]),
              mul2(Fix(2L), power(dl(), half())),
            ),
          ]),
          bl(),
          power(dl(), div(Fix(-3L), Fix(2L))),
        ]),
      ),
    ])
  }

  // Type 8-1: (%e^(b*sqrt(z)+d*z+e))^u*(%e^(c*sqrt(z)+f*z+g))^v
  w = m2_exp_type_8_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_b, q_c, q_d, q_e, q_f, q_g, q_u, q_v]) {
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let u = sin__as(q_u, w)
    let v = sin__as(q_v, w)
    if sin__debug() {
      format(
        t,
        "~&Type 8-1: (%e^(b*sqrt(z)+d*z+e))^u*(%e^(c*sqrt(z)+f*z+g))^v",
        [],
      )
      |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let du = () => add2(mul2(d, u), mul2(f, v))
    let sq = () => power(var2, half())
    let x = () => addn_([
      mul2(b, u),
      muln_([Fix(2L), d, u, sq()]),
      mul2(v, add2(c, mul3(Fix(2L), f, sq()))),
    ])
    return muln_([
      const_,
      div(Fix(1L), Fix(2L)),
      power(du(), div(Fix(-3L), Fix(2L))),
      muln_([
        power(
          e_,
          mul3(Fix(-1L), power(x(), Fix(2L)), inv(mul2(Fix(4L), du()))),
        ),
        power(power(e_, addn_([mul2(b, sq()), e, mul2(d, var2)])), u),
        power(power(e_, addn_([mul2(c, sq()), g, mul2(f, var2)])), v),
        add2(
          mul3(
            Fix(2L),
            power(e_, mul2(power(x(), Fix(2L)), inv(mul2(Fix(4L), du())))),
            power(du(), half()),
          ),
          muln_([
            Fix(-1L),
            power(q_d__pctpi, half()),
            add2(mul2(b, u), mul2(c, v)),
            take(list1(q_p_erfi), [
              div(
                addn_([
                  mul2(b, u),
                  muln_([Fix(2L), d, u, sq()]),
                  mul2(c, v),
                  muln_([Fix(2L), f, v, sq()]),
                ]),
                mul2(Fix(2L), power(du(), half())),
              ),
            ]),
          ]),
        ),
      ]),
    ])
  }

  // Type 8-2: (%e^(b*z^r+e))^u*(%e^(c*z^r+g))^v
  w = m2_exp_type_8_2(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_b, q_c, q_e, q_g, q_r, q_u, q_v]) &&
    eq(d_sign(sub(cdras(q_r, w), cdras(q_r1, w))), q_d_zero) {
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let e = sin__as(q_e, w)
    let g = sin__as(q_g, w)
    let r = sin__as(q_r, w)
    let u = sin__as(q_u, w)
    let v = sin__as(q_v, w)
    if sin__debug() {
      format(t, "~&Type 8-2: (%e^(b*z^r+e))^u*(%e^(c*z^r+g))^v", []) |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let bu = () => add2(mul2(b, u), mul2(c, v))
    return muln_([
      const_,
      Fix(-1L),
      inv(r),
      power(e_, mul3(Fix(-1L), power(var2, r), bu())),
      power(power(e_, add2(power(var2, r), e)), u),
      power(power(e_, add2(power(var2, r), g)), v),
      var2,
      power(mul3(Fix(-1L), power(var2, r), bu()), div(Fix(-1L), r)),
      take(gi, [div(Fix(1L), r), mul3(Fix(-1L), power(var2, r), bu())]),
    ])
  }

  // Type 9: z^n*a^(b*z^2+d*z+e)*h^(c*z^2+f*z+g)
  w = m2_exp_type_9(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) &&
    (
      !eq(d_sign(cdras(q_b, w)), q_d_zero) ||
      !eq(d_sign(cdras(q_c, w)), q_d_zero)
    ) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let h = sin__as(q_h, w)
    let n = sin__as(q_n, w)
    if sin__debug() {
      format(t, "~&Type 9: z^n*a^(b*z^2+d*z+e)*h^(c*z^2+f*z+g)", []) |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let dl = () => add2(mul2(d, sin__lg(a)), mul2(f, sin__lg(h)))
    let bl = () => add2(mul2(b, sin__lg(a)), mul2(c, sin__lg(h)))
    let zz = () => add2(
      mul2(add2(d, mul3(Fix(2L), b, var2)), sin__lg(a)),
      mul2(add2(f, mul3(Fix(2L), c, var2)), sin__lg(h)),
    )
    let f1 = div(Fix(-1L), Fix(2L))
    let f2 = power(a, e)
    let f3 = power(h, g)
    let f4 = power(e_, div(power(dl(), Fix(2L)), mul2(Fix(-4L), bl())))
    let f5 = power(bl(), mul2(Fix(-1L), add2(n, Fix(1L))))
    let index = gensumindex()
    let f6 = with_special(q_d_simpsum, t, () => mfuncall(
      q_d_sum,
      list([
        muln_([
          power(Fix(2L), sub(index, n)),
          ftake(q_p_binomial, [n, index]),
          power(
            add2(
              mul3(Fix(-1L), d, sin__lg(a)),
              mul3(Fix(-1L), f, sin__lg(h)),
            ),
            sub(n, index),
          ),
          power(zz(), add2(index, Fix(1L))),
          power(
            mul2(Fix(-1L), div(power(zz(), Fix(2L)), bl())),
            div(add2(index, Fix(1L)), Fix(-2L)),
          ),
          ftake(q_p_gamma_incomplete, [
            div(add2(index, Fix(1L)), Fix(2L)),
            mul2(Fix(-1L), div(power(zz(), Fix(2L)), mul2(Fix(4L), bl()))),
          ]),
        ]),
        index,
        Fix(0L),
        n,
      ]),
    ))
    return muln_([const_, f1, f2, f3, f4, f5, f6])
  }

  // Type 9-1: z^n*(%e^(b*z^2+d*z+e))^q*(%e^(c*z^2+f*z+g))^u
  w = m2_exp_type_9_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_b, q_c, q_d, q_e, q_f, q_g, q_q, q_u, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) &&
    (
      !eq(d_sign(cdras(q_b, w)), q_d_zero) ||
      !eq(d_sign(cdras(q_c, w)), q_d_zero)
    ) {
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let q = sin__as(q_q, w)
    let u = sin__as(q_u, w)
    let n = sin__as(q_n, w)
    if sin__debug() {
      format(
        t,
        "~&Type 9-1: z^n*(%e^(b*z^2+d*z+e))^q*(%e^(c*z^2+f*z+g))^u",
        [],
      )
      |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let bq = () => add2(mul2(b, q), mul2(c, u))
    let dq = () => add2(mul2(d, q), mul2(f, u))
    let f1 = div(Fix(-1L), Fix(2L))
    let f2 = power(bq(), div(Fix(-1L), Fix(2L)))
    let f3 = power(
      e_,
      add2(
        div(power(dq(), Fix(2L)), mul2(Fix(-4L), bq())),
        mul3(
          Fix(-1L),
          var2,
          addn_([mul2(d, q), mul3(b, q, var2), mul2(f, u), mul3(c, u, var2)]),
        ),
      ),
    )
    let f4 = power(power(e_, add2(e, mul2(var2, add2(d, mul2(b, var2))))), q)
    let f5 = power(power(e_, add2(g, mul2(var2, add2(f, mul2(c, var2))))), u)
    let index = gensumindex()
    let f6 = with_special(q_d_simpsum, t, () => dosum(
      muln_([
        power(Fix(2L), sub(index, n)),
        power(bq(), neg(add2(n, div(Fix(1L), Fix(2L))))),
        power(add2(neg(mul2(d, q)), neg(mul2(f, u))), sub(n, index)),
        power(
          addn_([mul2(d, q), mul2(f, u), mul3(Fix(2L), var2, bq())]),
          add2(index, Fix(1L)),
        ),
        power(
          div(
            power(
              addn_([mul2(d, q), mul2(f, u), mul3(Fix(2L), bq(), var2)]),
              Fix(2L),
            ),
            neg(bq()),
          ),
          mul2(div(Fix(-1L), Fix(2L)), add2(index, Fix(1L))),
        ),
        take(list1(q_p_binomial), [n, index]),
        take(gi, [
          div(add2(index, Fix(1L)), Fix(2L)),
          div(
            power(
              addn_([mul2(d, q), mul2(f, u), mul3(Fix(2L), bq(), var2)]),
              Fix(2L),
            ),
            mul2(Fix(-4L), bq()),
          ),
        ]),
      ]),
      index,
      Fix(0L),
      n,
      t,
    ))
    return muln_([const_, f1, f2, f3, f4, f5, f6])
  }

  // Type 10: z^n*a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z)+f*z+g)
  w = m2_exp_type_10(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) &&
    (
      !eq(d_sign(cdras(q_b, w)), q_d_zero) ||
      !eq(d_sign(cdras(q_c, w)), q_d_zero)
    ) {
    let a = sin__as(q_a, w)
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let h = sin__as(q_h, w)
    let n = sin__as(q_n, w)
    if sin__debug() {
      format(t, "~&Type 10: z^n*a^(b*sqrt(z)+d*z+e)*h^(c*sqrt(z)+f*z+g)", [])
      |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let dl = () => add2(mul2(d, sin__lg(a)), mul2(f, sin__lg(h)))
    let bl = () => add2(mul2(b, sin__lg(a)), mul2(c, sin__lg(h)))
    let yy = () => addn_([
      mul2(b, sin__lg(a)),
      mul2(c, sin__lg(h)),
      mul3(Fix(2L), power(var2, half()), dl()),
    ])
    let f1 = power(Fix(2L), add2(mul2(Fix(-2L), n), Fix(-1L)))
    let f2 = power(a, e)
    let f3 = power(h, g)
    let f4 = power(e_, div(power(bl(), Fix(2L)), mul2(Fix(-4L), dl())))
    let f5 = power(dl(), mul2(Fix(-2L), add2(n, Fix(1L))))
    let index1 = gensumindex()
    let index2 = gensumindex()
    let f6 = with_special(q_d_simpsum, t, () => dosum(
      dosum(
        muln_([
          power(Fix(-1L), sub(index1, index2)),
          power(Fix(4L), index1),
          ftake(q_p_binomial, [index1, index2]),
          ftake(q_p_binomial, [n, index1]),
          power(bl(), sub(mul2(Fix(2L), n), add2(index1, index2))),
          power(yy(), add2(index1, index2)),
          power(
            mul2(Fix(-1L), div(power(yy(), Fix(2L)), dl())),
            mul2(div(Fix(-1L), Fix(2L)), addn_([index1, index2, Fix(1L)])),
          ),
          add2(
            mul3(
              ftake(q_p_gamma_incomplete, [
                mul2(div(Fix(1L), Fix(2L)), addn_([index1, index2, Fix(1L)])),
                mul2(div(Fix(-1L), Fix(4L)), div(power(yy(), Fix(2L)), dl())),
              ]),
              bl(),
              yy(),
            ),
            muln_([
              Fix(2L),
              ftake(q_p_gamma_incomplete, [
                mul2(div(Fix(1L), Fix(2L)), addn_([index1, index2, Fix(2L)])),
                mul2(div(Fix(-1L), Fix(4L)), div(power(yy(), Fix(2L)), dl())),
              ]),
              dl(),
              power(mul2(Fix(-1L), div(power(yy(), Fix(2L)), dl())), half()),
            ]),
          ),
        ]),
        index2,
        Fix(0L),
        index1,
        t,
      ),
      index1,
      Fix(0L),
      n,
      t,
    ))
    return muln_([const_, f1, f2, f3, f4, f5, f6])
  }

  // Type 10-1: z^n*(%e^(b*sqrt(z)+d*z+e))^q*(%e^(c*sqrt(z)+f*z+g))^u
  w = m2_exp_type_10_1(facsum_exponent(expr, var2), var2)
  if sin__sc_bound(w, [q_b, q_c, q_d, q_e, q_f, q_g, q_q, q_u, q_n]) &&
    maxima_integerp(cdras(q_n, w)).truthy() &&
    eq(d_sign(cdras(q_n, w)), q_d_pos) &&
    (
      !eq(d_sign(cdras(q_b, w)), q_d_zero) ||
      !eq(d_sign(cdras(q_c, w)), q_d_zero)
    ) {
    let b = sin__as(q_b, w)
    let c = sin__as(q_c, w)
    let d = sin__as(q_d, w)
    let e = sin__as(q_e, w)
    let f = sin__as(q_f, w)
    let g = sin__as(q_g, w)
    let q = sin__as(q_q, w)
    let u = sin__as(q_u, w)
    let n = sin__as(q_n, w)
    let bq_cu = add2(mul2(b, q), mul2(c, u))
    let dq_fu = add2(mul2(d, q), mul2(f, u))
    if sin__debug() {
      format(
        t,
        "~&Type 10-1: z^n*(%e^(b*sqrt(z)+d*z+e))^q*(%e^(c*sqrt(z)+f*z+g))^u",
        [],
      )
      |> ignore
      format(t, "~&   : w = ~A~%", [w]) |> ignore
    }
    let sq = () => power(var2, half())
    let f1 = power(Fix(2L), mul2(Fix(-1L), add2(mul2(Fix(2L), n), Fix(1L))))
    let f2 = power(
      e_,
      addn_([
        div(mul2(Fix(-1L), power(bq_cu, Fix(2L))), mul2(Fix(4L), dq_fu)),
        muln_([Fix(-1L), d, var2, q]),
        muln_([Fix(-1L), b, sq(), q]),
        muln_([Fix(-1L), f, var2, u]),
        muln_([Fix(-1L), c, sq(), u]),
      ]),
    )
    let f3 = power(power(e_, addn_([mul2(b, sq()), mul2(d, var2), e])), q)
    let f4 = power(power(e_, addn_([mul2(c, sq()), mul2(f, var2), g])), u)
    let f5 = power(dq_fu, mul2(Fix(-2L), add2(n, Fix(1L))))
    let index1 = gensumindex()
    let index2 = gensumindex()
    let f6 = with_special(q_d_simpsum, t, () => {
      let s2 = () => add2(bq_cu, mul3(Fix(2L), sq(), dq_fu))
      dosum(
        dosum(
          muln_([
            power(Fix(-1L), sub(index1, index2)),
            power(Fix(4L), index1),
            power(bq_cu, addn_([neg(index1), neg(index2), mul2(Fix(2L), n)])),
            power(s2(), add2(index1, index2)),
            power(
              div(power(s2(), Fix(2L)), mul2(Fix(-1L), dq_fu)),
              mul2(div(Fix(-1L), Fix(2L)), addn_([index1, index2, Fix(1L)])),
            ),
            take(list1(q_p_binomial), [index1, index2]),
            take(list1(q_p_binomial), [n, index1]),
            add2(
              mul3(
                bq_cu,
                s2(),
                take(gi, [
                  mul2(div(Fix(1L), Fix(2L)), addn_([index1, index2, Fix(1L)])),
                  div(
                    power(
                      addn_([mul2(b, q), mul2(c, u), mul3(Fix(2L), sq(), dq_fu)]),
                      Fix(2L),
                    ),
                    mul2(Fix(-4L), dq_fu),
                  ),
                ]),
              ),
              muln_([
                Fix(2L),
                power(div(power(s2(), Fix(2L)), mul2(Fix(-1L), dq_fu)), half()),
                dq_fu,
                take(gi, [
                  mul2(div(Fix(1L), Fix(2L)), addn_([index1, index2, Fix(2L)])),
                  div(power(s2(), Fix(2L)), mul2(Fix(-4L), dq_fu)),
                ]),
              ]),
            ),
          ]),
          index2,
          Fix(0L),
          index1,
          t,
        ),
        index1,
        Fix(0L),
        n,
        t,
      )
    })
    return muln_([const_, f1, f2, f3, f4, f5, f6])
  }
  Nil
}

// ---------------------------------------------------------------------------
// Do a facsum for the exponent of power functions.
// This is necessary to integrate all general forms. The pattern matcher is
// not powerful enough to do the job.

///|
fn facsum_exponent(expr : Value, var2 : Value) -> Value raise {
  // Make sure that expr has the form ((mtimes) factor1 factor2 ...)
  let expr = if !mtimesp(expr).truthy() { mk(q_mtimes, [expr]) } else { expr }
  let mut result : Value = Nil
  for l in cdr(expr).iter() {
    if mexptp(l).truthy() {
      // Found an power function. Factor the exponent with facsum.
      let fac = mfuncall(q_d_facsum, list([caddr(l), var2]))
      let (num, den) = with_specials(
        [(q_d_exptdispflag, t), (q_d_pfeformat, Nil), (q_d__pctedispflag, Nil)],
        () => num_denom_split(fac),
      )
      result = cons(
        cons(
          list1(q_mexpt),
          cons(cadr(l), if equal(Fix(1L), den) {
            list1(num)
          } else {
            list1(d_multthru(inv(den), e2=num))
          }),
        ),
        result,
      )
    } else {
      // Nothing to do.
      result = cons(l, result)
    }
  }
  cons(list1(q_mtimes), result)
}
