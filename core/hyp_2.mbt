// Port of src/hyp.lisp, part 2: Legendre function cases of 2F1, the
// Gauss transformations, the trig/log cases, and the confluent
// hypergeometric function 1F1.

///|
/// Is F(a, b; c; z) is Legendre function?
///
/// Lemma 29 (see ref) says F(a, b; c; z) can be reduced to a Legendre
/// function if two of the numbers 1-c, +/-(a-b), and +/- (c-a-b) are equal
/// to each other or one of them equals +/- 1/2.
///
/// This routine checks for each of the possibilities.
fn legfun(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  let n1_c = sub(Fix(1L), c)
  let a_b = sub(a, b)
  let c_a_b = sub(sub(c, a), b)
  let inv2 = inv(Fix(2L))
  if alike1(a_b, inv2).truthy() {
    // a-b = 1/2
    if hyp__trace() {
      hyp__fmt("Legendre a-b = 1/2~%", [])
    }
    gered1(list2(a, b), list1(c), q_legf24, arg)
  } else if alike1(a_b, mul2(Fix(-1L), inv2)).truthy() {
    // a-b = -1/2
    //
    // For example F(a,a+1/2;c;x)
    if hyp__trace() {
      hyp__fmt("Legendre a-b = -1/2~%", [])
    }
    legf24(list2(a, b), list1(c), arg)
  } else if alike1(c_a_b, hyp__rat(1, 2)).truthy() {
    // c-a-b = 1/2
    // For example F(a,b;a+b+1/2;z)
    if hyp__trace() {
      hyp__fmt("Legendre c-a-b = 1/2~%", [])
    }
    legf20(list2(a, b), list1(c), arg)
  } else if alike1(c_a_b, hyp__rat(3, 2)).truthy() &&
    !alike1(c, Fix(1L)).truthy() &&
    !alike1(a, hyp__mhalf()).truthy() &&
    !alike1(b, hyp__mhalf()).truthy() {
    // c-a-b = 3/2 e.g. F(a,b;a+b+3/2;z) Reduce to F(a,b;a+b+1/2) and use
    // A&S 15.2.6. But if c = 1, we don't want to reduce c to 0! Problem:
    // The derivative of assoc_legendre_p introduces a unit_step function
    // and the result looks very complicated. And this doesn't work if
    // a+1/2 or b+1/2 is zero, so skip that too.
    if hyp__trace() {
      hyp__fmt("Legendre c-a-b = 3/2~%", [])
      mformat(list([t, Str("   : a = ~A~%"), a])) |> ignore
      mformat(list([t, Str("   : b = ~A~%"), b])) |> ignore
      mformat(list([t, Str("   : c = ~A~%"), c])) |> ignore
    }
    let psey = gensym()
    maxima_substitute(
      arg,
      psey,
      muln_([
        power(sub(Fix(1L), psey), hyp__rat(3, 2)),
        addn_([a, b, hyp__rat(1, 2)]),
        inv(add2(b, hyp__rat(1, 2))),
        inv(add2(a, hyp__rat(1, 2))),
        hyp__diff(
          mul2(
            power(sub(Fix(1L), psey), hyp__rat(-1, 2)),
            hgfsimp(
              list2(a, b),
              list1(addn_([a, b, hyp__rat(1, 2)])),
              psey,
            ),
          ),
          psey,
          Fix(1L),
        ),
      ]),
    )
  } else if alike1(c_a_b, hyp__rat(-1, 2)).truthy() {
    // c-a-b = -1/2, e.g. F(a,b; a+b-1/2; z)
    // This case is reduce to F(a,b; a+b+1/2; z) with
    //    F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a,c-b;c;z)
    if hyp__trace() {
      hyp__fmt("Legendre c-a-b = -1/2~%", [])
    }
    gered1(list2(a, b), list1(c), q_legf20, arg)
  } else if alike1(n1_c, a_b).truthy() {
    // 1-c = a-b, F(a,b; b-a+1; z)
    if hyp__trace() {
      hyp__fmt("Legendre 1-c = a-b~%", [])
    }
    gered1(list2(a, b), list1(c), q_legf16, arg)
  } else if alike1(n1_c, mul2(Fix(-1L), a_b)).truthy() {
    // 1-c = b-a, e.g. F(a,b; a-b+1; z)
    if hyp__trace() {
      hyp__fmt("Legendre 1-c = b-a~%", [])
    }
    legf16(list2(a, b), list1(c), arg)
  } else if alike1(n1_c, c_a_b).truthy() {
    // 1-c = c-a-b, e.g. F(a,b; (a+b+1)/2; z)
    if hyp__trace() {
      hyp__fmt("Legendre 1-c = c-a-b~%", [])
    }
    gered1(list2(a, b), list1(c), q_legf14, arg)
  } else if alike1(n1_c, mul2(Fix(-1L), c_a_b)).truthy() {
    // 1-c = a+b-c
    //
    // For example F(a,1-a;c;x)
    if hyp__trace() {
      hyp__fmt("Legendre 1-c = a+b-c~%", [])
    }
    legf14(list2(a, b), list1(c), arg)
  } else if alike1(a_b, mul2(Fix(-1L), c_a_b)).truthy() {
    // a-b = a+b-c, e.g. F(a,b;2*b;z)
    if hyp__trace() {
      hyp__fmt("Legendre a-b = a+b-c~%", [])
    }
    legf36(list2(a, b), list1(c), arg)
  } else if alike1(n1_c, inv2).truthy() ||
    alike1(n1_c, mul2(Fix(-1L), inv2)).truthy() {
    // 1-c = 1/2 or 1-c = -1/2
    // For example F(a,b;1/2;z) or F(a,b;3/2;z)
    if hyp__trace() {
      hyp__fmt("Legendre |1-c| = 1/2~%", [])
    }
    // At this point it does not make sense to call legpol. For this case
    // a special algorithm is needed. At this time we return nil.
    Nil
  } else if alike1(a_b, c_a_b).truthy() {
    // a-b = c-a-b
    if hyp__trace() {
      hyp__fmt("Legendre a-b = c-a-b~%", [])
    }
    q_legendre_funct_to_be_discovered
  } else {
    Nil
  }
}

// The following legf<n> functions correspond to formulas in Higher
// Transcendental Functions. See the chapter on Legendre functions, in
// particular the table on page 124ff,

///|
/// Handle the case c-a-b = 1/2
///
/// Formula 20:
///
/// P(n,m,z) = 2^m*(z^2-1)^(-m/2)/gamma(1-m)*F(1/2+n/2-m/2, -n/2-m/2; 1-m; 1-z^2)
///
/// See also A&S 15.4.12 and 15.4.13.
///
/// F(a,b;c;w) = 2^(c-1)*gamma(c)*(-w)^((1-c)/2)*P(c-2*b-1,1-c,sqrt(1-w))
fn legf20(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  // F(a,b;a+b+1/2;x)
  with_special(q_d_radexpand, Nil, () => {
    let b = cadr(arg_l1)
    let c = car(arg_l2)
    let a = sub(sub(c, b), hyp__rat(1, 2))
    let m = sub(Fix(1L), c)
    let n = mul2(Fix(-1L), addn_([b, b, m]))
    // m = 1 - c
    // n = -(2*b+1-c) = c - 1 - 2*b
    // A&S 15.4.13
    //
    // F(a,b;a+b+1/2;x) = 2^(a+b-1/2)*gamma(a+b+1/2)*x^((1/2-a-b)/2)
    //                     *assoc_legendre_p(a-b-1/2,1/2-a-b,sqrt(1-x))
    // This formula is correct for all arguments x.
    muln_([
      power(Fix(2L), addn_([a, b, hyp__rat(-1, 2)])),
      take(list1(q_p_gamma), [addn_([a, b, hyp__rat(1, 2)])]),
      power(arg, div(sub(hyp__rat(1, 2), add2(a, b)), Fix(2L))),
      legen(n, m, power(sub(Fix(1L), arg), hyp__rat(1, 2)), q_d_p),
    ])
  })
}

///|
/// Handle the case a-b = -1/2.
///
/// Formula 24:
///
/// P(n,m,z) = 2^m*(z^2-1)^(-m/2)*z^(n+m)/gamma(1-m)*F(-n/2-m/2,1/2-n/2-m/2;1-m;1-1/z^2)
///
/// See also A&S 15.4.10 and 15.4.11.
fn legf24(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  with_special(q_d_radexpand, Nil, () => {
    let a = car(arg_l1)
    let c = car(arg_l2)
    let m = sub(Fix(1L), c)
    let n = sub(add2(a, a), c)
    let z = inv(power(sub(Fix(1L), arg), inv(Fix(2L))))
    // A&S 15.4.10, 15.4.11
    if eq(asksign(arg), q_d_negative) {
      // A&S 15.4.11
      //
      // F(a,a+1/2;c;x) = 2^(c-1)*gamma(c)(-x)^(1/2-c/2)*(1-x)^(c/2-a-1/2)
      //                   *assoc_legendre_p(2*a-c,1-c,1/sqrt(1-x))
      muln_([
        inv(power(Fix(2L), m)),
        gm(sub(Fix(1L), m)),
        power(mul2(Fix(-1L), arg), div(m, Fix(2L))),
        power(sub(Fix(1L), arg), sub(div(m, Fix(-2L)), a)),
        legen(n, m, z, q_d_p),
      ])
    } else {
      muln_([
        inv(power(Fix(2L), m)),
        gm(sub(Fix(1L), m)),
        power(arg, div(m, Fix(2L))),
        power(sub(Fix(1L), arg), sub(div(m, Fix(-2L)), a)),
        legen(n, m, z, q_d_p),
      ])
    }
  })
}

///|
/// Handle 1-c = a-b
///
/// Formula 16:
///
/// P(n,m,z) = 2^(-n)*(z+1)^(m/2+n)*(z-1)^(-m/2)/gamma(1-m)*F(-n,-n-m;1-m;(z-1)/(z+1))
///
/// See also A&S 15.4.14 and 15.4.15.
///
/// F(a,b;c;w) = gamma(c)*w^(1/2-c/2)*(1-w)^(-a)*P(-a,1-c,(1+w)/(1-w));
///
/// FIXME:  We don't correctly handle the branch cut here!
fn legf16(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  with_special(q_d_radexpand, Nil, () => {
    let a = car(arg_l1)
    let c = car(arg_l2)
    // m = 1-c = b-a
    let m = sub(Fix(1L), c)
    // n = -b
    // m = b - a, so b = a + m
    let b = add2(a, m)
    let n = mul2(Fix(-1L), b)
    let z = div(add2(Fix(1L), arg), sub(Fix(1L), arg))
    if hyp__trace() {
      hyp__fmt("a, c = ~A ~A~%", [a, c])
      hyp__fmt("b = ~A~%", [b])
    }
    // A&S 15.4.14, 15.4.15
    if eq(asksign(arg), q_d_negative) {
      // A&S 15.4.15
      //
      // F(a,b;a-b+1,x) = gamma(a-b+1)*(1-x)^(-b)*(-x)^(b/2-a/2)
      //                   * assoc_legendre_p(-b,b-a,(1+x)/(1-x))
      //
      // for x < 0
      muln_([
        take(list1(q_p_gamma), [c]),
        power(sub(Fix(1L), arg), mul2(Fix(-1L), b)),
        power(mul2(Fix(-1L), arg), div(m, Fix(2L))),
        legen(n, m, z, q_d_p),
      ])
    } else {
      muln_([
        take(list1(q_p_gamma), [c]),
        power(sub(Fix(1L), arg), mul2(Fix(-1L), b)),
        power(arg, div(m, Fix(2L))),
        legen(n, m, z, q_d_p),
      ])
    }
  })
}

///|
/// Handle the case 1-c = a+b-c.
///
/// Formula 14:
///
/// P(n,m,z) = (z+1)^(m/2)*(z-1)^(-m/2)/gamma(1-m)*F(-n,1+n;1-m;(1-z)/2)
///
/// See also A&S 8.1.2, 15.4.16, 15.4.17
///
/// F(a,b;c;w) = gamma(c)*(-w)^(1/2-c/2)*(1-w)^(c/2-1/2)*P(-a,1-c,1-2*w)
fn legf14(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  // Set $radexpand to NIL, because we don't want (-z)^x getting expanded
  // to (-1)^x*z^x because that's wrong for this.
  with_special(q_d_radexpand, Nil, () => {
    let a = first(arg_l1)
    let b = second(arg_l1)
    let c = first(arg_l2)
    let m = sub(Fix(1L), c)
    let n = mul2(Fix(-1L), a)
    let z = sub(Fix(1L), mul2(Fix(2L), arg))
    if hyp__trace() {
      hyp__fmt("~&legf14~%", [])
    }
    // A&S 15.4.16, 15.4.17
    if !alike1(add2(a, b), Fix(1L)).truthy() {
      // I think 15.4.16 and 15.4.17 require the form F(a,1-a;c;x). That
      // is, a+b = 1. If we don't have it exit now.
      Nil
    } else if eq(asksign(arg), q_d_positive) &&
      eq(asksign(sub(Fix(1L), arg)), q_d_positive) {
      if hyp__trace() {
        hyp__fmt(" A&S 15.4.17~%", [])
      }
      // A&S 15.4.17
      //
      // F(a,1-a;c;x) = gamma(c)*x^(1/2-c/2)*(1-x)^(c/2-1/2)*
      //                 assoc_legendre_p(-a,1-c,1-2*x)
      //
      // for 0 < x < 1
      muln_([
        gm(c),
        power(arg, div(sub(Fix(1L), c), Fix(2L))),
        power(sub(Fix(1L), arg), div(sub(c, Fix(1L)), Fix(2L))),
        legen(n, m, z, q_d_p),
      ])
    } else {
      // A&S 15.4.16
      //
      // F(a,1-a;c;z) = gamma(c)*(-z)^(1/2-c/2)*(1-z)^(c/2-1/2)*
      //                 assoc_legendre_p(-a,1-c,1-2*z)
      if hyp__trace() {
        hyp__fmt(" A&S 15.4.17~%", [])
      }
      muln_([
        gm(c),
        power(mul2(Fix(-1L), arg), div(sub(Fix(1L), c), Fix(2L))),
        power(sub(Fix(1L), arg), div(sub(c, Fix(1L)), Fix(2L))),
        legen(n, m, z, q_d_p),
      ])
    }
  })
}

///|
/// Handle a-b = a+b-c
///
/// Formula 36:
///
/// exp(-%i*m*%pi)*Q(n,m,z) =
///     2^n*gamma(1+n)*gamma(1+n+m)*(z+1)^(m/2-n-1)*(z-1)^(-m/2)/gamma(2+2*n)
///     * hgfred([1+n-m,1+n],[2+2*n],2/(1+z))
///
/// Let a = 1+n-m, b = 1+n, c = 2+2*n.  then n = b-1 and m = b - a.
fn legf36(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  ignore(arg_l2)
  let a = car(arg_l1)
  let b = cadr(arg_l1)
  let n = sub(b, Fix(1L))
  let m = sub(b, a)
  let z = sub(div(Fix(2L), arg), Fix(1L))
  muln_([
    inv(power(Fix(2L), n)),
    inv(gm(add2(Fix(1L), n))),
    inv(gm(addn_([Fix(1L), n, m]))),
    inv(
      power(
        add2(z, Fix(1L)),
        addn_([div(m, Fix(2L)), mul2(Fix(-1L), n), Fix(-1L)]),
      ),
    ),
    inv(power(sub(z, Fix(1L)), div(m, Fix(-2L)))),
    gm(addn_([Fix(2L), n, n])),
    power(q_d__pcte, muln_([Fix(-1L), q_d__pcti, m, q_d__pctpi])),
    legen(n, m, z, q_d_q),
  ])
}

///|
fn legen(n : Value, m : Value, x : Value, pq : Value) -> Value raise {
  // A&S 8.2.1: P(-n-1,m,z) = P(n,m,z)
  let n = if hyp__sign_negnz(n) || // negative sign or
    mminusp(n).truthy() { // negative form like -n-1
    mul2(Fix(-1L), add2(Fix(1L), n))
  } else {
    n
  }
  if equal(m, Fix(0L)) {
    list3(
      if eq(pq, q_d_q) {
        list2(q_d_legendre_q, q_simp)
      } else {
        list2(q_d_legendre_p, q_simp)
      },
      n,
      x,
    )
  } else {
    list4(
      if eq(pq, q_d_q) {
        list2(q_d_assoc_legendre_q, q_simp)
      } else {
        list2(q_d_assoc_legendre_p, q_simp)
      },
      n,
      m,
      x,
    )
  }
}

///|
fn legpol_core(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  // I think for this to be correct, we need a to be a negative integer.
  if !(eq(q_d_yes, ask_integerp(a)) && eq(asksign(a), q_d_negative)) {
    return Nil
  }
  let l = vfvp(div(add2(b, a), Fix(2L)), arg)
  let v = cdr(assoc_equal(q_v, l))
  // v is (a+b)/2
  if alike1(v, hyp__rat(1, 2)).truthy() && alike1(c, Fix(1L)).truthy() {
    // A&S 22.5.49:
    // P(n,x) = F(-n,n+1;1;(1-x)/2)
    legenpol(mul2(Fix(-1L), a), sub(Fix(1L), mul2(Fix(2L), arg)))
  } else if alike1(c, hyp__rat(1, 2)).truthy() &&
    alike1(add2(b, a), hyp__rat(1, 2)).truthy() {
    // c = 1/2, a+b = 1/2
    //
    // A&S 22.5.52
    // P(2*n,x) = (-1)^n*(2*n)!/2^(2*n)/(n!)^2*F(-n,n+1/2;1/2;x^2)
    //
    // F(-n,n+1/2;1/2;x^2) = P(2*n,x)*(-1)^n*(n!)^2/(2*n)!*2^(2*n)
    let n = mul2(Fix(-1L), a)
    muln_([
      power(Fix(-1L), n),
      power(gm(add2(n, Fix(1L))), Fix(2L)),
      inv(gm(add2(Fix(1L), mul2(Fix(2L), n)))),
      power(Fix(2L), mul2(Fix(2L), n)),
      legenpol(mul2(Fix(2L), n), power(arg, div(Fix(1L), Fix(2L)))),
    ])
  } else if alike1(c, hyp__rat(3, 2)).truthy() &&
    alike1(add2(b, a), hyp__rat(3, 2)).truthy() {
    // c = 3/2, a+b = 3/2
    //
    // A&S 22.5.53
    // P(2*n+1,x) = (-1)^n*(2*n+1)!/2^(2*n)/(n!)^2*F(-n,n+3/2;3/2;x^2)*x
    //
    // F(-n,n+3/2;3/2;x^2) = P(2*n+1,x)*(-1)^n*(n!)^2/(2*n+1)!*2^(2*n)/x
    let n = mul2(Fix(-1L), a)
    muln_([
      power(Fix(-1L), n),
      power(gm(add2(Fix(1L), n)), Fix(2L)),
      inv(gm(add2(Fix(2L), mul2(Fix(2L), n)))),
      power(Fix(2L), mul2(Fix(2L), n)),
      legenpol(
        add2(Fix(1L), mul2(Fix(2L), n)),
        power(arg, div(Fix(1L), Fix(2L))),
      ),
      inv(power(arg, div(Fix(1L), Fix(2L)))),
    ])
  } else if zerp(sub(b, a)).truthy() && zerp(sub(c, add2(a, b))).truthy() {
    // a = b, c = a + b
    //
    // A&S 22.5.50
    // P(n,x) = binomial(2*n,n)*((x-1)/2)^n*F(-n,-n;-2*n;2/(1-x))
    //
    // F(-n,-n;-2*n;x) = P(n,1-2/x)/binomial(2*n,n)(-1/x)^(-n)
    muln_([
      power(gm(add2(Fix(1L), mul2(Fix(-1L), a))), Fix(2L)),
      inv(gm(add2(Fix(1L), mul2(Fix(-2L), a)))),
      power(mul2(Fix(-1L), arg), mul2(Fix(-1L), a)),
      legenpol(mul2(Fix(-1L), a), add2(Fix(1L), div(Fix(-2L), arg))),
    ])
  } else if alike1(sub(a, b), hyp__rat(1, 2)).truthy() &&
    alike1(sub(c, mul2(Fix(2L), b)), hyp__rat(1, 2)).truthy() {
    // a - b = 1/2, c - 2*b = 1/2
    //
    // A&S 22.5.51
    // P(n,x) = binomial(2*n,n)*(x/2)^n*F(-n/2,(1-n)/2;1/2-n;1/x^2)
    //
    // F(-n/2,(1-n)/2;1/2-n,1/x^2) = P(n,x)/binomial(2*n,n)*(x/2)^(-n)
    muln_([
      power(gm(add2(Fix(1L), mul2(Fix(-2L), b))), Fix(2L)),
      inv(gm(add2(Fix(1L), mul2(Fix(-4L), b)))),
      power(
        mul2(Fix(2L), power(arg, div(Fix(1L), Fix(2L)))),
        mul2(Fix(-2L), b),
      ),
      legenpol(mul2(Fix(-2L), b), power(arg, div(Fix(-1L), Fix(2L)))),
    ])
  } else if alike1(sub(b, a), hyp__rat(1, 2)).truthy() &&
    alike1(sub(c, mul2(Fix(2L), a)), hyp__rat(1, 2)).truthy() {
    // b - a = 1/2, c + 2*a = 1/2
    //
    // A&S 22.5.51
    // P(n,x) = binomial(2*n,n)*(x/2)^n*F(-n/2,(1-n)/2;1/2-n;1/x^2)
    //
    // F(-n/2,(1-n)/2;1/2-n,1/x^2) = P(n,x)/binomial(2*n,n)*(x/2)^(-n)
    muln_([
      power(gm(add2(Fix(1L), mul2(Fix(-2L), a))), Fix(2L)),
      inv(gm(add2(Fix(1L), mul2(Fix(-4L), a)))),
      power(
        mul2(Fix(2L), power(arg, div(Fix(1L), Fix(2L)))),
        mul2(Fix(-2L), a),
      ),
      legenpol(mul2(Fix(-2L), a), power(arg, div(Fix(-1L), Fix(2L)))),
    ])
  } else {
    Nil
  }
}

///|
/// See A&S 15.3.3:
///
/// F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a,c-b;c;z)
fn gered1(
  arg_l1 : Value,
  arg_l2 : Value,
  simpflg : Value,
  arg : Value,
) -> Value raise {
  let a = first(arg_l1)
  let b = second(arg_l1)
  let c = first(arg_l2)
  mul2(
    power(
      sub(Fix(1L), arg),
      addn_([c, mul2(Fix(-1L), a), mul2(Fix(-1L), b)]),
    ),
    funcall(simpflg, [list2(sub(c, a), sub(c, b)), arg_l2, arg]),
  )
}

///|
/// See A&S 15.3.4
///
/// F(a,b;c;z) = (1-z)^(-a)*F(a,c-b;c;z/(z-1))
fn gered2(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  mul2(
    power(sub(Fix(1L), arg), mul2(Fix(-1L), a)),
    hgfsimp(
      list2(a, sub(c, b)),
      list1(c),
      div(arg, sub(arg, Fix(1L))),
    ),
  )
}

///|
/// See A&S 15.3.9:
///
/// F(a,b;c;z) = A*z^(-a)*F(a,a-c+1;a+b-c+1;1-1/z)
///              + B*(1-z)^(c-a-b)*z^(a-c)*F(c-a,1-a;c-a-b+1,1-1/z)
///
/// where A = gamma(c)*gamma(c-a-b)/gamma(c-a)/gamma(c-b)
///       B = gamma(c)*gamma(a+b-c)/gamma(a)/gamma(b)
fn geredf(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  with_special(q_d_gamma_expand, t, () => add2(
    div(
      muln_([
        take(list1(q_p_gamma), [c]),
        take(list1(q_p_gamma), [
          addn_([c, mul2(Fix(-1L), a), mul2(Fix(-1L), b)]),
        ]),
        power(arg, mul2(Fix(-1L), a)),
        d_hgfred(
          mk(q_mlist, [a, addn_([a, Fix(1L), mul2(Fix(-1L), c)])]),
          mk(q_mlist, [addn_([a, b, mul2(Fix(-1L), c), Fix(1L)])]),
          sub(Fix(1L), div(Fix(1L), arg)),
        ),
      ]),
      mul2(
        take(list1(q_p_gamma), [sub(c, a)]),
        take(list1(q_p_gamma), [sub(c, b)]),
      ),
    ),
    div(
      muln_([
        take(list1(q_p_gamma), [c]),
        take(list1(q_p_gamma), [addn_([a, b, mul2(Fix(-1L), c)])]),
        power(
          sub(Fix(1L), arg),
          addn_([c, mul2(Fix(-1L), a), mul2(Fix(-1L), b)]),
        ),
        power(arg, sub(a, c)),
        d_hgfred(
          mk(q_mlist, [sub(c, a), sub(Fix(1L), a)]),
          mk(q_mlist, [
            addn_([c, mul2(Fix(-1L), a), mul2(Fix(-1L), b), Fix(1L)]),
          ]),
          sub(Fix(1L), div(Fix(1L), arg)),
        ),
      ]),
      mul2(take(list1(q_p_gamma), [a]), take(list1(q_p_gamma), [b])),
    ),
  ))
}

///|
fn trig_log(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  if equal(simplifya(car(arg_l2), Nil), hyp__rat(3, 2)) {
    // c = 3/2
    if hyp__trace() {
      hyp__fmt("  trig-log:  Test c=3/2~%", [])
    }
    trig_log_3(arg_l1, arg_l2, arg)
  } else if equal(simplifya(car(arg_l2), Nil), hyp__rat(1, 2)) {
    // c = 1/2
    if hyp__trace() {
      hyp__fmt("  trig-log:  Test c=1/2~%", [])
    }
    trig_log_1(arg_l1, arg_l2, arg)
  } else {
    Nil
  }
}

///|
fn trig_log_3(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  if (equal(car(arg_l1), Fix(1L)) || equal(cadr(arg_l1), Fix(1L))) &&
    (
      equal(car(arg_l1), div(Fix(1L), Fix(2L))) ||
      equal(cadr(arg_l1), div(Fix(1L), Fix(2L)))
    ) {
    // (a = 1 or b = 1) and (a = 1/2 or b = 1/2)
    if hyp__trace() {
      hyp__fmt("   Case a or b is 1 and the other is 1/2~%", [])
    }
    trig_log_3_exec(arg_l1, arg_l2, arg)
  } else if equal(car(arg_l1), cadr(arg_l1)) &&
    (
      equal(Fix(1L), car(arg_l1)) ||
      equal(div(Fix(1L), Fix(2L)), car(arg_l1))
    ) {
    // a = b and (a = 1 or a = 1/2)
    if hyp__trace() {
      hyp__fmt("   Case a=b and a is 1 or 1/2~%", [])
    }
    trig_log_3a_exec(arg_l1, arg_l2, arg)
  } else if equal(add2(car(arg_l1), cadr(arg_l1)), Fix(1L)) ||
    equal(add2(car(arg_l1), cadr(arg_l1)), Fix(2L)) {
    // a + b = 1 or a + b = 2
    if hyp__trace() {
      hyp__fmt("   Case a+b is 1 or 2~%", [])
    }
    trig_sin(arg_l1, arg_l2, arg)
  } else if equal(sub(car(arg_l1), cadr(arg_l1)), div(Fix(1L), Fix(2L))) ||
    equal(sub(cadr(arg_l1), car(arg_l1)), div(Fix(1L), Fix(2L))) {
    // a - b = 1/2 or b - a = 1/2
    if hyp__trace() {
      hyp__fmt("   Case a-b=1/2 or b-a=1/2~%", [])
    }
    trig_3(arg_l1, arg_l2, arg)
  } else {
    Nil
  }
}

///|
fn trig_3(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  ignore(arg_l2)
  // A&S 15.1.10
  //
  // F(a,a+1/2,3/2,z^2) =
  // ((1+z)^(1-2*a) - (1-z)^(1-2*a))/2/z/(1-2*a)
  with_special(q_d_radexpand, q_d_all, () => {
    let a = sub(
      Fix(1L),
      sub(add2(car(arg_l1), cadr(arg_l1)), div(Fix(1L), Fix(2L))),
    )
    let z = power(arg, div(Fix(1L), Fix(2L)))
    muln_([
      inv(z),
      inv(Fix(2L)),
      inv(a),
      sub(power(add2(Fix(1L), z), a), power(sub(Fix(1L), z), a)),
    ])
  })
}

///|
fn trig_sin(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  ignore(arg_l2)
  // A&S 15.1.15, 15.1.16
  let a = first(arg_l1)
  let b = second(arg_l1)
  // I think it's ok to convert sqrt(z^2) to z here, so $radexpand is $all.
  with_special(q_d_radexpand, q_d_all, () => if equal(add2(a, b), Fix(1L)) {
    // A&S 15.1.15
    //
    // F(a,1-a;3/2;sin(z)^2) =
    //
    // sin((2*a-1)*z)/(2*a-1)/sin(z)
    mul2(
      inv(mul2(mul2(Fix(-1L), sub(a, b)), msin(masin(msqrt(arg))))),
      msin(mul2(mul2(Fix(-1L), sub(a, b)), masin(msqrt(arg)))),
    )
  } else if equal(add2(a, b), Fix(2L)) {
    // A&S 15.1.16
    //
    // F(a, 2-a; 3/2; sin(z)^2) =
    //
    // sin((2*a-2)*z)/(a-1)/sin(2*z)
    let z1 = masin(msqrt(arg))
    let a1 = mul2(Fix(-1L), sub(a, b))
    mul2(msin(mul2(z1, a1)), inv(muln_([a1, msin(z1), mcos(z1)])))
  } else {
    Nil
  })
}

///|
/// Generates atan if arg positive else log
fn trig_log_3_exec(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  ignore(arg_l1)
  ignore(arg_l2)
  // See A&S 15.1.4 and 15.1.5
  //
  // F(a,b;3/2;z) where a = 1/2 and b = 1 (or vice versa).

  // I think it's ok to convert sqrt(z^2) to z here, so $radexpand is $all.
  with_special(q_d_radexpand, q_d_all, () => if equal(
      checksigntm(arg),
      q_d_positive,
    ) {
    // A&S 15.1.4
    //
    // F(1/2,1;3/2,z^2) =
    //
    // log((1+z)/(1-z))/z/2
    //
    // This is the same as atanh(z)/z.
    let z = power(arg, div(Fix(1L), Fix(2L)))
    muln_([
      power(z, Fix(-1L)),
      inv(Fix(2L)),
      mlog(div(add2(Fix(1L), z), sub(Fix(1L), z))),
    ])
  } else if equal(checksigntm(arg), q_d_negative) {
    // A&S 15.1.5
    //
    // F(1/2,1;3/2,z^2) =
    // atan(z)/z
    let z = power(mul2(Fix(-1L), arg), div(Fix(1L), Fix(2L)))
    mul2(power(z, Fix(-1L)), matan(z))
  } else {
    Nil
  })
}

///|
fn trig_log_3a_exec(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  // See A&S 15.1.6 and 15.1.7
  //
  // F(a,b;3/2,z) where a = b and a = 1/2 or a = 1.

  // I think it's ok to convert sqrt(z^2) to z here, so $radexpand is $all.
  let a = first(arg_l1)
  with_special(q_d_radexpand, q_d_all, () => if equal(
      checksigntm(arg),
      q_d_positive,
    ) {
    // A&S 15.1.6
    //
    // F(1/2,1/2; 3/2; z^2) = sqrt(1-z^2)*F(1,1;3/2;z^2) =
    // asin(z)/z
    let z = power(arg, div(Fix(1L), Fix(2L)))
    if equal(a, Fix(1L)) {
      div(
        trig_log_3a_exec(
          list2(div(Fix(1L), Fix(2L)), div(Fix(1L), Fix(2L))),
          arg_l2,
          arg,
        ),
        power(sub(Fix(1L), power(z, Fix(2L))), div(Fix(1L), Fix(2L))),
      )
    } else {
      div(masin(z), z)
    }
  } else if equal(checksigntm(arg), q_d_negative) {
    // A&S 15.1.7
    //
    // F(1/2,1/2; 3/2; -z^2) = sqrt(1+z^2)*F(1,1,3/2; -z^2) =
    // log(z + sqrt(1+z^2))/z
    let z = power(mul2(Fix(-1L), arg), div(Fix(1L), Fix(2L)))
    let n1_plusz_hat2 = add2(Fix(1L), power(z, Fix(2L)))
    if equal(a, Fix(1L)) {
      div(
        trig_log_3a_exec(
          list2(div(Fix(1L), Fix(2L)), div(Fix(1L), Fix(2L))),
          arg_l2,
          arg,
        ),
        power(n1_plusz_hat2, div(Fix(1L), Fix(2L))),
      )
    } else {
      div(
        mlog(add2(z, power(n1_plusz_hat2, div(Fix(1L), Fix(2L))))),
        z,
      )
    }
  } else {
    Nil
  })
}

///|
/// 2F1's with C = 1/2
fn trig_log_1(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  ignore(arg_l2)
  // 15.1.17, 11, 18, 12, 9, and 19

  // I think it's ok to convert sqrt(z^2) to z here, so $radexpand is $all.
  with_specials([(q_d_radexpand, q_d_all), (q_d_exponentialize, Nil)], () => {
    let a = car(arg_l1)
    let mut b = cadr(arg_l1)
    if eq0(add2(a, b)) {
      // F(-a,a;1/2,z)
      if equal(checksigntm(arg), q_d_positive) {
        // A&S 15.1.17:
        // F(-a,a;1/2;sin(z)^2) = cos(2*a*z)
        trig_log_1_pos(a, arg)
      } else if equal(checksigntm(arg), q_d_negative) {
        // A&X 15.1.11:
        // F(-a,a;1/2;-z^2) = 1/2*((sqrt(1+z^2)+z)^(2*a)
        //                         +(sqrt(1+z^2)-z)^(2*a))
        trig_log_1_neg(a, b, arg)
      } else {
        Nil
      }
    } else if equal(add2(a, b), Fix(1L)) {
      // F(a,1-a;1/2,z)
      if equal(checksigntm(arg), q_d_positive) {
        // A&S 15.1.18:
        // F(a,1-a;1/2;sin(z)^2) = cos((2*a-1)*z)/cos(z)
        let z = masin(msqrt(arg))
        div(mcos(mul2(sub(a, b), z)), mcos(z))
      } else if equal(checksigntm(arg), q_d_negative) {
        // A&S 15.1.12
        // F(a,1-a;1/2;-z^2) = 1/2*(1+z^2)^(-1/2)*
        //                     {[(sqrt(1+z^2)+z]^(2*a-1)
        //                       +[sqrt(1+z^2)-z]^(2*a-1)}
        let x = msqrt(sub(Fix(1L), arg))
        let f2 = inv(x)
        let z = msqrt(neg(arg))
        b = sub(a, b)
        muln_([
          hyp__half(),
          f2,
          add2(power(add2(x, z), b), power(sub(x, z), b)),
        ])
      } else {
        Nil
      }
    } else if n_eq1_sl_sl2(hyp_mabs(sub(b, a))).truthy() {
      // F(a, a+1/2; 1/2; z)
      if equal(checksigntm(arg), q_d_positive) {
        // A&S 15.1.9
        // F(a,1/2+a;1/2;z^2) = ((1+z)^(-2*a)+(1-z)^(-2*a))/2
        let z = msqrt(arg)
        let base1 = add2(Fix(1L), z)
        b = sub(hyp__half(), add2(a, b))
        mul2(hyp__half(), add2(power(base1, b), power(sub(Fix(1L), z), b)))
      } else if equal(checksigntm(arg), q_d_negative) {
        // A&S 15.1.19
        // F(a,1/2+a;1/2;-tan(z)^2) = cos(z)^(2*a)*cos(2*a*z)
        let z = matan(msqrt(neg(arg)))
        let base1 = mcos(z)
        b = addn_([a, b, hyp__mhalf()])
        mul2(power(base1, b), mcos(mul2(b, z)))
      } else {
        Nil
      }
    } else {
      Nil
    }
  })
}

///|
fn trig_log_1_pos(a : Value, z : Value) -> Value raise {
  // I think it's ok to convert sqrt(z^2) to z here, so $radexpand is $all.
  with_special(q_d_radexpand, q_d_all, () => mcos(
    muln_([Fix(2L), a, masin(msqrt(z))]),
  ))
}

///|
fn trig_log_1_neg(a : Value, b : Value, v : Value) -> Value raise {
  // Look to see a is of the form m*s+c where m and c are numbers. If m is
  // positive, swap a and b. Basically we want F(-a,a;1/2;-z^2) =
  // F(a,-a;1/2;-z^2), as they should be.
  with_special(q_d_radexpand, q_d_all, () => {
    let match_ = m_stars_plusc(a)
    let m = cdras(q_m, match_)
    let s = cdras(q_s, match_)
    let b = if s.truthy() {
      if m.truthy() && eq(checksigntm(m), q_d_positive) {
        a
      } else {
        b
      }
    } else if eq(checksigntm(a), q_d_negative) {
      b
    } else {
      a
    }
    let x = msqrt(sub(Fix(1L), v))
    let z = msqrt(neg(v))
    let b = mul2(Fix(2L), b)
    mul2(hyp__half(), add2(power(add2(x, z), b), power(sub(x, z), b)))
  })
}

///|
let hyp__m_star_s_plus_c_pat : Value = try! lread(
  "((mplus) ((coeffpt) (m $numberp) (s nonnump)) ((coeffpp) (c $numberp)))",
)

///|
/// Pattern match for m*s+c where a is a number, x is symbolic, and c is a
/// number.
fn m_stars_plusc(exp_ : Value) -> Value raise {
  m2(exp_, hyp__m_star_s_plus_c_pat)
}

///|
/// Confluent hypergeometric function.
///
/// F(a;c;z)
fn confl(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a = car(arg_l1)
  let c = car(arg_l2)
  let a_c = sub(a, c)
  if zerop1(arg).truthy() {
    // F(a;c;0) = 1
    return add2(Fix(1L), arg)
  }
  if equal(Fix(1L), c) && !integerp(a) && !integerp(add2(a, a)) {
    // Do not handle an integer or an half integral value
    // F(a;1;z) = laguerre(-a,z)
    return lagpol(neg(a), Fix(0L), arg)
  }
  if maxima_integerp(a).truthy() &&
    memq(d_sign(a), list2(q_d_neg, q_nz)).truthy() {
    // F(-n; c; z) and n a positive integer
    return n1f1polys(list1(c), a, arg)
  }
  if alike1(c, add2(a, a)).truthy() {
    // F(a;2a;z)
    // A&S 13.6.6
    //
    // F(n+1;2*n+1;2*z) =
    // gamma(3/2+n)*exp(z)*(z/2)^(-n-1/2)*bessel_i(n+1/2,z).
    //
    // So
    //
    // F(n,2*n,z) =
    // gamma(n+1/2)*exp(z/2)*(z/4)^(-n-3/2)*bessel_i(n-1/2,z/2);
    //
    // If n is a negative integer, we use laguerre polynomial.
    return if maxima_integerp(a).truthy() && eq(asksign(a), q_d_negative) {
      // We have already checked a negative integer. This algorithm is now
      // present in 1f1polys and at this place never called.
      let n = neg(a)
      muln_([
        power(Fix(-1L), n),
        inv(take(list1(q_p_binomial), [add2(n, n), n])),
        lagpol(n, sub(c, Fix(1L)), arg),
      ])
    } else {
      let z = div(arg, Fix(2L))
      mul2(
        power(q_d__pcte, z),
        bestrig(add2(a, hyp__rat(1, 2)), div(mul2(z, z), Fix(4L))),
      )
    }
  }
  let n = sub(add2(a, a), c)
  if integerp(n) && plusp(n) && !integerp(a) && !integerp(add2(a, a)) {
    // F(a,2*a-n,z) and a not an integer or a half integral value
    if hyp__debug() {
      hyp__fmt("~&Case 1F1(a,2*a-n,x):", [])
      hyp__fmt("~&   ; a = ~A~%", [a])
      hyp__fmt("~&   ; c = ~A~%", [c])
      hyp__fmt("~&   : n = ~A~%", [n])
    }
    let index = gensym()
    return sratsimp(
      muln_([
        take(list1(q_p_gamma), [sub(a, add2(n, hyp__rat(1, 2)))]),
        power(div(arg, Fix(4L)), sub(add2(hyp__rat(1, 2), n), a)),
        power(q_d__pcte, div(arg, Fix(2L))),
        dosum(
          muln_([
            power(Fix(-1L), index),
            take(list1(q_d_pochhammer), [num_neg(n), index]),
            take(list1(q_d_pochhammer), [
              addn_([a, a, num_mul(Fix(-2L), n), Fix(-1L)]),
              index,
            ]),
            addn_([a, index, num_neg(n), hyp__rat(-1, 2)]),
            inv(take(list1(q_d_pochhammer), [sub(add2(a, a), n), index])),
            inv(take(list1(q_mfactorial), [index])),
            take(list1(q_p_bessel_i), [
              addn_([a, index, num_neg(n), hyp__rat(-1, 2)]),
              div(arg, Fix(2L)),
            ]),
          ]),
          index,
          Fix(0L),
          n,
          t,
        ),
      ]),
    )
  }
  let n = sub(c, add2(a, a))
  if integerp(n) && plusp(n) && !integerp(a) && !integerp(add2(a, a)) {
    // F(a,2*a+n,z) and a not an integer or a half integral value
    if hyp__debug() {
      hyp__fmt("~&Case 1F1(a,2*a+n,x):", [])
      hyp__fmt("~&   ; a = ~A~%", [a])
      hyp__fmt("~&   ; c = ~A~%", [c])
      hyp__fmt("~&   : n = ~A~%", [n])
    }
    let index = gensym()
    return sratsimp(
      muln_([
        take(list1(q_p_gamma), [sub(a, hyp__rat(1, 2))]),
        power(div(arg, Fix(4L)), sub(hyp__rat(1, 2), a)),
        power(q_d__pcte, div(arg, Fix(2L))),
        dosum(
          muln_([
            take(list1(q_d_pochhammer), [num_neg(n), index]),
            take(list1(q_d_pochhammer), [addn_([a, a, Fix(-1L)]), index]),
            addn_([a, index, hyp__rat(-1, 2)]),
            inv(take(list1(q_d_pochhammer), [addn_([a, a, n]), index])),
            inv(take(list1(q_mfactorial), [index])),
            take(list1(q_p_bessel_i), [
              addn_([a, index, hyp__rat(-1, 2)]),
              div(arg, Fix(2L)),
            ]),
          ]),
          index,
          Fix(0L),
          n,
          t,
        ),
      ]),
    )
  }
  let n = sub(a, hyp__rat(1, 2))
  if integerp(n) && num_ge(n, Fix(0L)) && integerp(c) && plusp(c) {
    let m = c
    return with_specials([(q_d_simpsum, t), (q_d_bessel_reduce, t)], () => {
      if hyp__debug() {
        hyp__fmt("~&Case 1F1(n+1/2,m,x):", [])
        hyp__fmt("~&   ; a = ~A~%", [a])
        hyp__fmt("~&   ; c = ~A~%", [c])
        hyp__fmt("~&   : n = ~A~%", [n])
        hyp__fmt("~&   : m = ~A~%", [m])
      }
      sratsimp(
        muln_([
          power(Fix(2L), num_sub(Fix(1L), m)),
          power(q_d__pcte, div(arg, Fix(2L))),
          factorial(num_sub(m, Fix(1L))),
          factorial(n),
          inv(
            take(list1(q_d_pochhammer), [
              hyp__rat(1, 2),
              num_sub(m, Fix(1L)),
            ]),
          ),
          inv(take(list1(q_d_pochhammer), [hyp__rat(1, 2), n])),
          {
            let index1 = gensumindex()
            dosum(
              muln_([
                power(Fix(2L), neg(index1)),
                power(neg(arg), index1),
                inv(take(list1(q_mfactorial), [index1])),
                mfuncall(
                  q_d_gen_laguerre,
                  list3(
                    sub(n, index1),
                    sub(index1, hyp__rat(1, 2)),
                    neg(arg),
                  ),
                ),
                {
                  let index2 = gensumindex()
                  dosum(
                    muln_([
                      power(Fix(-1L), index2),
                      power(Fix(2L), neg(index2)),
                      take(list1(q_p_binomial), [
                        addn_([index1, m, Fix(-1L)]),
                        index2,
                      ]),
                      {
                        let index3 = gensumindex()
                        dosum(
                          mul2(
                            take(list1(q_p_binomial), [index2, index3]),
                            take(list1(q_p_bessel_i), [
                              sub(index2, mul2(Fix(2L), index3)),
                              div(arg, Fix(2L)),
                            ]),
                          ),
                          index3,
                          Fix(0L),
                          index2,
                          t,
                        )
                      },
                    ]),
                    index2,
                    Fix(0L),
                    addn_([index1, m, Fix(-1L)]),
                    t,
                  )
                },
              ]),
              index1,
              Fix(0L),
              n,
              t,
            )
          },
        ]),
      )
    })
  }
  let n = sub(a, hyp__rat(1, 2))
  if integerp(n) && num_lt(n, Fix(0L)) && integerp(c) && plusp(c) {
    let n = num_neg(n)
    let m = c
    return with_specials([(q_d_simpsum, t), (q_d_bessel_reduce, t)], () => {
      if hyp__debug() {
        hyp__fmt("~&Case 1F1(1/2-n,m,x):", [])
        hyp__fmt("~&   ; a = ~A~%", [a])
        hyp__fmt("~&   ; c = ~A~%", [c])
        hyp__fmt("~&   : n = ~A~%", [n])
        hyp__fmt("~&   : m = ~A~%", [m])
      }
      sratsimp(
        muln_([
          power(Fix(-1L), n),
          power(Fix(2L), num_sub(Fix(1L), m)),
          power(q_d__pcte, div(arg, Fix(2L))),
          factorial(num_sub(m, Fix(1L))),
          inv(
            take(list1(q_d_pochhammer), [
              hyp__rat(1, 2),
              num_sub(m, Fix(1L)),
            ]),
          ),
          inv(take(list1(q_d_pochhammer), [sub(m, hyp__rat(1, 2)), n])),
          {
            let index1 = gensumindex()
            dosum(
              muln_([
                power(Fix(2L), neg(index1)),
                power(arg, index1),
                take(list1(q_p_binomial), [n, index1]),
                take(list1(q_d_pochhammer), [
                  sub(hyp__rat(3, 2), num_add(m, n)),
                  sub(n, index1),
                ]),
                {
                  let index2 = gensumindex()
                  dosum(
                    muln_([
                      power(hyp__rat(-1, 2), index2),
                      take(list1(q_p_binomial), [
                        addn_([index1, m, Fix(-1L)]),
                        index2,
                      ]),
                      {
                        let index3 = gensumindex()
                        dosum(
                          mul2(
                            take(list1(q_p_binomial), [index2, index3]),
                            take(list1(q_p_bessel_i), [
                              sub(index2, mul2(Fix(2L), index3)),
                              div(arg, Fix(2L)),
                            ]),
                          ),
                          index3,
                          Fix(0L),
                          index2,
                          t,
                        )
                      },
                    ]),
                    index2,
                    Fix(0L),
                    addn_([index1, m, Fix(-1L)]),
                    t,
                  )
                },
              ]),
              index1,
              Fix(0L),
              n,
              t,
            )
          },
        ]),
      )
    })
  }
  if !hyp_integerp(a_c).truthy() {
    if hyp_integerp(a).truthy() {
      kummer(arg_l1, arg_l2, arg)
    } else if symval(q_d_prefer_whittaker).truthy() {
      // A&S 15.1.32:
      //
      // %m[k,u](z) = exp(-z/2)*z^(u+1/2)*M(1/2+u-k,1+2*u,z)
      //
      // So
      //
      // M(a,c,z) = exp(z/2)*z^(-c/2)*%m[c/2-a,c/2-1/2](z)
      //
      // But if we apply Kummer's transformation, we can also derive the
      // expression
      //
      // %m[k,u](z) = exp(z/2)*z^(u+1/2)*M(1/2+u+k,1+2*u,-z)
      //
      // or
      //
      // M(a,c,z) = exp(-z/2)*(-z)^(-c/2)*%m[a-c/2,c/2-1/2](-z)
      //
      // For Laplace transforms it might be more beneficial to return this
      // second form instead.
      let m = div(sub(c, Fix(1L)), Fix(2L))
      let k = addn_([hyp__rat(1, 2), m, mul2(Fix(-1L), a)])
      muln_([
        power(arg, mul2(Fix(-1L), add2(hyp__rat(1, 2), m))),
        power(q_d__pcte, div(arg, Fix(2L))),
        whitfun(k, m, arg),
      ])
    } else {
      fpqform(arg_l1, arg_l2, arg)
    }
  } else if minusp(a_c) {
    sratsimp(erfgammared(a, c, arg))
  } else {
    kummer(arg_l1, arg_l2, arg)
  }
}
