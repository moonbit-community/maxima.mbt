// Port of src/hyp.lisp, part 3: erf and incomplete gamma reductions of
// 1F1, splitting pFq, the step4 algorithm and the A&S 15.2.x
// differentiation formulas, and the atanh cases of 2F1.

///|
/// A&S 13.6.19:
/// M(1/2,3/2,-z^2) =  sqrt(%pi)*erf(z)/2/sqrt(z)
///
/// So M(1/2,3/2,z) = sqrt(%pi)*erf(sqrt(-z))/2/sqrt(-z)
///                 = sqrt(%pi)*erf(%i*sqrt(z))/2/(%i*sqrt(z))
fn hyprederf(x : Value) -> Value raise {
  let x = mul2(q_d__pcti, power(x, hyp__rat(1, 2)))
  muln_([
    power(q_d__pctpi, hyp__rat(1, 2)),
    hyp__rat(1, 2),
    inv(x),
    take(list1(q_p_erf), [x]),
  ])
}

///|
/// M(a,c,z), where a-c is a negative integer.
fn erfgammared(a : Value, c : Value, z : Value) -> Value raise {
  if nump(a).truthy() && nump(c).truthy() {
    erfgamnumred(a, c, z)
  } else {
    gammareds(a, c, z)
  }
}

///|
/// M(a,c,z) where a-c is a negative integer.
fn gammareds(a : Value, c : Value, z : Value) -> Value raise {
  let diff = sub(c, a)
  if eql(diff, Fix(1L)) {
    // We have M(a,a+1,z).
    hypredincgm(a, z)
  } else if eql(a, Fix(1L)) {
    // We have M(1,a,z)
    // Apply Kummer's transformation to get the form M(a-1,a,z)
    //
    // (I don't think we ever get here, but just in case, we leave it.)
    kummer(list1(a), list1(c), z)
  } else {
    // We have M(a, a+n, z)
    //
    // A&S 13.4.3 says
    // (1+a-b)*M(a,b,z) - a*M(a+1,b,z)+(b-1)*M(a,b-1,z) = 0
    //
    // So
    //
    // M(a,b,z) = [a*M(a+1,b,z) - (b-1)*M(a,b-1,z)]/(1+a-b);
    //
    // Thus, the difference between b and a is reduced, until b-a=1,
    // which we handle above.
    mul2(
      sub(
        mul2(a, gammareds(add2(Fix(1L), a), c, z)),
        mul2(sub(c, Fix(1L)), gammareds(a, sub(c, Fix(1L)), z)),
      ),
      inv(sub(add2(Fix(1L), a), c)),
    )
  }
}

///|
/// A&S 6.5.12:
/// gamma_incomplete_lower(a,x) = x^a/a*M(a,1+a,-x)
///                  = x^a/a*exp(-x)*M(1,1+a,x)
///
/// M(a,1+a,x) = a*(-x)^(-a)*gamma_incomplete_lower(a,-x)
fn hypredincgm(a : Value, z : Value) -> Value raise {
  let mz = mul2(Fix(-1L), z)
  if !symval(q_d_prefer_gamma_incomplete).truthy() {
    muln_([
      a,
      power(mz, mul2(Fix(-1L), a)),
      take(list1(q_p_gamma_incomplete_lower), [a, mz]),
    ])
  } else {
    muln_([
      a,
      power(mz, mul2(Fix(-1L), a)),
      sub(
        take(list1(q_p_gamma), [a]),
        take(list1(q_p_gamma_u_incomplete), [a, mz]),
      ),
    ])
  }
}

///|
/// M(a,c,z), when a and c are numbers, and a-c is a negative integer
fn erfgamnumred(a : Value, c : Value, z : Value) -> Value raise {
  if hyp_integerp(sub(c, hyp__rat(1, 2))).truthy() {
    erfred(a, c, z)
  } else {
    gammareds(a, c, z)
  }
}

///|
/// M(a,c,z) when a and c are numbers and c-1/2 is an integer and a-c is a
/// negative integer. Thus, we have M(p+1/2, q+1/2,z)
fn erfred(a : Value, c : Value, z : Value) -> Value raise {
  let n = sub(a, hyp__rat(1, 2))
  let m = sub(c, hyp__rat(3, 2))
  // a = n + 1/2
  // c = m + 3/2
  // a - c < 0 so n - m - 1 < 0
  if !(num_gt(n, m) || minusp(n)) {
    // 0 <= n <= m
    thno33(n, m, z)
  } else if minusp(n) && minusp(m) {
    // n < 0 and m < 0
    thno35(mul2(Fix(-1L), n), mul2(Fix(-1L), m), z)
  } else if minusp(n) && plusp(m) {
    // n < 0 and m > 0
    thno34(mul2(Fix(-1L), n), m, z)
  } else {
    // n = 0 or m = 0
    gammareds(add2(n, hyp__rat(1, 2)), add2(m, hyp__rat(3, 2)), z)
  }
}

///|
/// Compute M(n+1/2, m+3/2, z) with 0 <= n <= m.
///
/// Method:
///
///   Since n <= m, apply the differentiation formula:
///
///     diff(M(1/2,m-n+3/2,z),z,n) = poch(1/2,n)/poch(m-n+3/2,n)*M(n+1/2,m+3/2,z)
///
///   Apply Kummer's transformation:
///
///     M(1/2,m-n+3/2,z) = exp(z)*M(m-n+1,m-n+3/2,z)
///
///   Apply the differentiation formula again:
///
///     diff(M(1,3/2,z),z,m-n) = poch(1,m-n)/poch(3/2,m-n)*M(m-n+1,m-n+3/2,z)
fn thno33(n : Value, m : Value, x : Value) -> Value raise {
  // M(n+1/2,m+3/2,z) = diff(M(1/2,m-n+3/2,z),z,n)*poch(m-n+3/2,n)/poch(1/2,n)
  // M(1/2,m-n+3/2,z) = exp(z)*M(m-n+1,m-n+3/2,-z)
  // M(m-n+1,m-n+3/2,z) = diff(M(1,3/2,z),z,m-n)*poch(3/2,m-n)/poch(1,m-n)
  // diff(M(1,3/2,z),z,m-n) = (-1)^(m-n)*diff(M(1,3/2,-z),z,m-n)
  // M(1,3/2,-z) = exp(-z)*M(1/2,3/2,z)
  let yannis = gensym()
  let m_n = sub(m, n)
  // poch(m-n+3/2,n)/poch(1/2,n)
  let factor1 = div(
    take(list1(q_d_pochhammer), [add2(m_n, hyp__rat(3, 2)), n]),
    take(list1(q_d_pochhammer), [hyp__rat(1, 2), n]),
  )
  // poch(3/2,m-n)/poch(1,m-n)
  let factor2 = div(
    take(list1(q_d_pochhammer), [hyp__rat(3, 2), m_n]),
    take(list1(q_d_pochhammer), [Fix(1L), m_n]),
  )
  // M(1,3/2,-z) = exp(-z)*M(1/2,3/2,z)
  let hgferf = mul2(
    power(q_d__pcte, mul2(Fix(-1L), yannis)),
    hyprederf(yannis),
  )
  // diff(M(1,3/2,z),z,m-n)
  let diff1 = meval(mk(q_d_diff, [hgferf, yannis, m_n]))
  // exp(z)*M(m-n+1,m-n+3/2,-z)
  let kummer = mul2(power(q_d__pcte, yannis), diff1)
  // diff(M(1/2,m-n+3/2,z),z,n)
  let diff2 = meval(mk(q_d_diff, [kummer, yannis, n]))
  // Multiply all the terms together.
  sratsimp(
    muln_([
      power(Fix(-1L), m_n),
      factor1,
      factor2,
      maxima_substitute(x, yannis, diff2),
    ]),
  )
}

///|
/// M(n+1/2,m+3/2,z), with n < 0 and m > 0
///
/// Let's write it more explicitly as M(-n+1/2,m+3/2,z) with n > 0 and
/// m > 0.
///
/// First, use Kummer's transformation to get
///
///    M(-n+1/2,m+3/2,z) = exp(z)*M(m+n+1,m+3/2,-z)
///
/// We also have
///
///    diff(z^(n+m)*M(m+1,m+3/2,z),z,n) = poch(m+1,n)*z^m*M(m+n+1,m+3/2,z)
///
/// And finally
///
///    diff(M(1,3/2,z),z,m) = poch(1,m)/poch(3/2,m)*M(m+1,m+3/2,z)
///
/// Thus, we can compute M(-n+1/2,m+3/2,z) from M(1,3/2,z).
fn thno34(n : Value, m : Value, x : Value) -> Value raise {
  let yannis = gensym()
  sratsimp(
    maxima_substitute(
      x,
      yannis,
      muln_([
        power(Fix(-1L), m),
        div(
          mul2(
            take(list1(q_d_pochhammer), [hyp__rat(3, 2), m]),
            power(q_d__pcte, yannis),
          ),
          muln_([
            take(list1(q_d_pochhammer), [Fix(1L), m]),
            take(list1(q_d_pochhammer), [one_plus(m), n]),
            power(yannis, m),
          ]),
        ),
        meval(
          mk(q_d_diff, [
            mul2(
              power(yannis, num_add(m, n)),
              meval(
                mk(q_d_diff, [
                  mul2(
                    power(q_d__pcte, mul2(Fix(-1L), yannis)),
                    hyprederf(yannis),
                  ),
                  yannis,
                  m,
                ]),
              ),
            ),
            yannis,
            n,
          ]),
        ),
      ]),
    ),
  )
}

///|
/// M(n+1/2,m+3/2,z), with n < 0 and m < 0
///
/// Write it more explicitly as M(-n+1/2,-m+3/2,z) with n > 0 and m > 0.
///
/// We know that
///
///    diff(sqrt(z)*M(-n+1/2,3/2,z),z,m) = poch(3/2-m,m)*M(-n+1/2,-m+3/2,z).
///
/// Apply Kummer's transformation:
///
///    M(-n+1/2,3/2,z) = exp(z) * M(n+1,3/2,-z)
///
/// Finally
///
///    diff(z^n*M(1,3/2,z),z,n) = n!*M(n+1,3/2,z)
///
/// So we can express M(-n+1/2,-m+3/2,z) in terms of M(1,3/2,z).
fn thno35(n : Value, m : Value, x : Value) -> Value raise {
  let yannis = gensym()
  sratsimp(
    maxima_substitute(
      x,
      yannis,
      mul2(
        div(
          power(yannis, sub(m, hyp__rat(1, 2))),
          muln_([
            power(Fix(-1L), num_mul(Fix(-1L), m)),
            take(list1(q_d_pochhammer), [Fix(1L), n]),
            take(list1(q_d_pochhammer), [hyp__rat(-1, 2), m]),
          ]),
        ),
        meval(
          mk(q_d_diff, [
            muln_([
              power(yannis, hyp__rat(1, 2)),
              power(q_d__pcte, yannis),
              meval(
                mk(q_d_diff, [
                  muln_([
                    power(q_d__pcte, mul2(Fix(-1L), yannis)),
                    power(yannis, n),
                    hyprederf(yannis),
                  ]),
                  yannis,
                  n,
                ]),
              ),
            ]),
            yannis,
            m,
          ]),
        ),
      ),
    ),
  )
}

///|
/// Pochhammer symbol. fctrl(a,n) = a*(a+1)*(a+2)*...*(a+n-1).
///
/// N must be a positive integer!
fn fctrl(a : Value, n : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else if equal(n, Fix(1L)) {
    a
  } else {
    mul2(add2(a, one_minus(n)), fctrl(a, one_minus(n)))
  }
}

///|
/// Check to see if EXP is free of ARG.
fn vfvp(exp_ : Value, arg : Value) -> Value raise {
  m2(exp_, list3(q_v, q_freevar2, arg))
}

///|
fn fpqform(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  list([
    list1(q_mqapply),
    list([
      list3(q_d__pctf, q_simp, q_array),
      int(length(arg_l1)),
      int(length(arg_l2)),
    ]),
    cons(list2(q_mlist, q_simp), arg_l1),
    cons(list2(q_mlist, q_simp), arg_l2),
    arg,
  ])
}

///|
/// Consider pFq([a_k]; [c_j]; z). If a_k = c_j + m for some k and j and
/// m >= 0, we can express pFq in terms of (p-1)F(q-1):
///
///                 n
/// F(a+n,b;c;z) = sum z^k/poch(a,k)*binomial(n,k)*poch(b,k)*F(b+k;;z)
///                k=0
fn splitpfq(l : Value, arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a1 = first(l)
  let k = second(l)
  let mut result : Value = Fix(0L)
  let mut prodnum : Value = Fix(1L)
  let mut proden : Value = Fix(1L)
  let b1 = sub(a1, k)
  let mut prod_b : Value = Fix(1L)
  let mut arg_l1 = hyp__delete1_equal(a1, arg_l1)
  let mut arg_l2 = hyp__delete1_equal(b1, arg_l2)
  let mut count : Value = Fix(0L)
  while num_le(count, k) {
    if hyp__trace() {
      hyp__fmt("splitpfg term:~%", [])
      maxima_display(
        muln_([
          combin(k, count),
          div(prodnum, proden),
          inv(prod_b),
          power(arg, count),
        ]),
      )
      |> ignore
      mtell(
        list([
          Str("F(~:M, ~:M)~%"),
          cons(list1(q_mlist), arg_l1),
          cons(list1(q_mlist), arg_l2),
        ]),
      )
      |> ignore
    }
    result = add2(
      result,
      muln_([
        combin(k, count),
        div(prodnum, proden),
        inv(prod_b),
        power(arg, count),
        hgfsimp(arg_l1, arg_l2, arg),
      ]),
    )
    prod_b = mul2(prod_b, add2(b1, count))
    prodnum = mul2(prodnum, mull(arg_l1))
    proden = mul2(proden, mull(arg_l2))
    arg_l1 = incr1(arg_l1)
    arg_l2 = incr1(arg_l2)
    count = num_add(count, Fix(1L))
  }
  result
}

///|
/// binomial(k,count)
fn combin(k : Value, count : Value) -> Value raise {
  div(
    factorial(k),
    mul2(factorial(count), factorial(sub(k, count))),
  )
}

///|
let hyp__algii_pat : Value = try! lread(
  "((mtimes) ((coefft) (m $numberp)) ((coefft) (s nonnump)))",
)

///|
/// We have something like F(s+m,-s+n;c;z)
/// Rewrite it like F(a'+d,-a';c;z) where a'=s-n=-b and d=m+n.
fn algii(a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut b = b
  let sym_ = cdras(q_f, s_plusc(a))
  let sign = cdras(q_m, m2(sym_, hyp__algii_pat))
  if sign.truthy() && minusp(sign) {
    let tmp = a
    a = b
    b = tmp
  }
  list3(Nil, mul2(Fix(-1L), b), add2(a, b))
}

///|
/// Algor. 2F1-RL from thesis:step 4:dispatch on a+m,-a+n,1/2+l cases
fn step4(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  // F(a,b;c;z) where a+b is an integer and c+1/2 is an integer. If a and
  // b are not integers themselves, we can derive the result from
  // F(a1,-a1;1/2;z). However, if a and b are integers, we can't use that
  // because F(a1,-a1;1/2;z) is a polynomial. We need to derive the result
  // from F(1,1;3/2;z).
  if hyp_integerp(a).truthy() && hyp_integerp(b).truthy() {
    step4_int(a, b, c, arg)
  } else {
    step4_a(a, b, c, arg)
  }
}

///|
fn step4_a(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  let alglist = algii(a, b)
  let aprime = cadr(alglist)
  let m = caddr(alglist)
  let n = sub(c, inv(Fix(2L)))
  with_specials(
    [
      (q_d_ratsimpexpons, symval(q_d_true)),
      (q_d_ratprint, symval(q_d_false)),
    ],
    () => if hyp_integerp(add2(aprime, inv(Fix(2L)))).truthy() {
      // At this point, we have F(a'+m,-a';1/2+n;z) where m and n are
      // integers.
      //
      // Ok. We have a problem if aprime + 1/2 is an integer. We can't
      // always use the algorithm below because we have F(1/2,-1/2;1/2;z)
      // which is 1F0(-1/2;;z) so the derivation isn't quite right. Also,
      // sometimes we'll end up with a division by zero.
      //
      // Thus, We need to do something else. So, use A&S 15.3.3 to change
      // the problem:
      //
      // F(a,b;c;z) = (1-z)^(c-a-b)*F(c-a, c-b; c; z)
      //
      // which is
      //
      // F('a+m,-a';1/2+n;z) = (1-z)^(1/2+n-m)*F(1/2+n-a'-m,1/2+n+a';1/2+n;z)
      //
      // Recall that a' + 1/2 is an integer. Thus we have
      // F(<int>,<int>,1/2+n;z), which we know how to handle in step4-int.
      gered1(list2(a, b), list1(c), q_hgfsimp, arg)
    } else {
      // Ok, this uses F(a,-a;1/2;z). Since there are 2 possible
      // representations (A&S 15.1.11 and 15.1.17), we check the sign of
      // the arg (as done in trig-log-1) to select which form we want to
      // use.
      let newf = if equal(checksigntm(arg), q_d_positive) {
        trig_log_1_pos(aprime, q_ell)
      } else if equal(checksigntm(arg), q_d_negative) {
        trig_log_1_neg(mul2(Fix(-1L), aprime), aprime, q_ell)
      } else {
        Nil
      }
      subst(arg, q_ell, algiii(newf, m, n, aprime))
    },
  )
}

// F(a,b;c;z), where a and b are (positive) integers and c = 1/2+l. This
// can be computed from F(1,1;3/2;z).
//
// We start from F(1,1;3/2;z). Use A&S 15.2.3, differentiating m times to
// get F(m,1;3/2;z). Swap a and b to get F(m,1;3/2;z) = F(1,m;3/2;z) and use
// A&S 15.2.3 again to get F(n,m;3/2;z) by differentiating n times.
// Finally, if L < 0, use A&S 15.2.4. Otherwise use A&S 15.2.6.

///|
/// Transform F(a,b;c;z) to F(a+n,b;c;z), given F(a,b;c;z)
fn as_15_dot2_dot3(
  a : Value,
  bb : Value,
  cx : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  ignore(bb)
  ignore(cx)
  hyp__assert_nonneg(n)
  // A&S 15.2.3:
  // F(a+n,b;c;z) = z^(1-a)/poch(a,n)*diff(z^(a+n-1)*fun,z,n)
  muln_([
    inv(factf(a, n)),
    power(arg, sub(Fix(1L), a)),
    hyp__diff(mul2(power(arg, sub(add2(a, n), Fix(1L))), fun), arg, n),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a,b;c-n;z), given F(a,b;c;z)
fn as_15_dot2_dot4(
  axax : Value,
  bb : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  ignore(axax)
  ignore(bb)
  hyp__assert_nonneg(n)
  // A&S 15.2.4
  // F(a,b;c-n;z) = 1/poch(c-n,n)/z^(c-n-1)*diff(z^(c-1)*fun,z,n)
  muln_([
    inv(factf(sub(c, n), n)),
    inv(power(arg, sub(sub(c, n), Fix(1L)))),
    hyp__diff(mul2(power(arg, sub(c, Fix(1L))), fun), arg, n),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a-n,b;c;z), given F(a,b;c;z)
fn as_15_dot2_dot5(
  a : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.5
  // F(a-n,b;c;z) = 1/poch(c-a,n)*z^(1+a-c)*(1-z)^(c+n-a-b)
  //                 *diff(z^(c-a+n-1)*(1-z)^(a+b-c)*F(a,b;c;z),z,n)
  hyp__assert_nonneg(n)
  muln_([
    inv(factf(sub(c, a), n)),
    power(arg, sub(add2(a, Fix(1L)), c)),
    power(sub(Fix(1L), arg), sub(add2(c, n), add2(a, b))),
    hyp__diff(
      muln_([
        power(arg, sub(add2(c, n), add2(a, Fix(1L)))),
        power(sub(Fix(1L), arg), sub(add2(a, b), c)),
        fun,
      ]),
      arg,
      n,
    ),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a,b;c+n;z), given F(a,b;c;z)
fn as_15_dot2_dot6(
  a : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.6
  // F(a,b;c+n;z) = poch(c,n)/poch(c-a,n)/poch(c-b,n)*(1-z)^(c+n-a-b)
  //                 *diff((1-z)^(a+b-c)*fun,z,n)
  hyp__assert_nonneg(n)
  muln_([
    factf(c, n),
    inv(factf(sub(c, a), n)),
    inv(factf(sub(c, b), n)),
    inv(power(sub(Fix(1L), arg), sub(add2(a, b), add2(c, n)))),
    hyp__diff(mul2(power(sub(Fix(1L), arg), sub(add2(a, b), c)), fun), arg, n),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a+n, b; c+n; z)
fn as_15_dot2_dot7(
  a : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.7
  // F(a+n,b;c+n;z) = (-1)^n*poch(c,n)/poch(a,n)/poch(c-b,n)*(1-z)^(1-a)
  //                    *diff((1-z)^(a+n-1)*fun, z, n)
  hyp__assert_nonneg(n)
  muln_([
    power(Fix(-1L), n),
    factf(c, n),
    inv(factf(a, n)),
    inv(factf(sub(c, b), n)),
    power(sub(Fix(1L), arg), sub(Fix(1L), a)),
    hyp__diff(
      mul2(power(sub(Fix(1L), arg), sub(add2(a, n), Fix(1L))), fun),
      arg,
      n,
    ),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a-n, b; c-n; z)
fn as_15_dot2_dot8(
  axax : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.8
  //  F(a-n,b;c-n;z) = 1/poch(c-n,n)/(z^(c-n-1)*(1-z)^(b-c))
  //                    *diff(z^(c-1)*(1-z^(b-c+n)*fun, z, n))
  ignore(axax)
  hyp__assert_nonneg(n)
  muln_([
    inv(factf(sub(c, n), n)),
    inv(
      mul2(
        power(arg, sub(sub(c, n), Fix(1L))),
        power(sub(Fix(1L), arg), sub(b, c)),
      ),
    ),
    hyp__diff(
      muln_([
        power(arg, sub(c, Fix(1L))),
        power(sub(Fix(1L), arg), add2(sub(b, c), n)),
        fun,
      ]),
      arg,
      n,
    ),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a+n,b+n;c+n;z)
fn as_15_dot2_dot2(
  a : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.2
  // F(a+n,b+n; c+n;z) = poch(c,n)/poch(a,n)/poch(b,n)
  //                      *diff(fun, z, n)
  hyp__assert_nonneg(n)
  muln_([
    factf(c, n),
    inv(factf(a, n)),
    inv(factf(b, n)),
    hyp__diff(fun, arg, n),
  ])
}

///|
/// Transform F(a,b;c;z) to F(a-n,b-n;c-n;z)
fn as_15_dot2_dot9(
  a : Value,
  b : Value,
  c : Value,
  n : Value,
  arg : Value,
  fun : Value,
) -> Value raise {
  // A&S 15.2.9
  // F(a-n,b-n; c-n;z) = 1/poch(c-n,n)/(z^(c-n-1)*(1-z)^(a+b-c-n))
  //                      *diff(z^(c-1)*(1-z)^(a+b-c)*fun, z, n)
  hyp__assert_nonneg(n)
  muln_([
    inv(factf(sub(c, n), n)),
    inv(
      mul2(
        power(arg, sub(sub(c, n), Fix(1L))),
        power(sub(Fix(1L), arg), sub(add2(a, b), add2(c, n))),
      ),
    ),
    hyp__diff(
      muln_([
        power(arg, sub(c, Fix(1L))),
        power(sub(Fix(1L), arg), sub(add2(a, b), c)),
        fun,
      ]),
      arg,
      n,
    ),
  ])
}

///|
fn step4_int(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  if num_gt(a, b) {
    return step4_int(b, a, c, arg)
  }
  let s = gensym(prefix="step4-arg-")
  let m = one_minus(a)
  let n = one_minus(b)
  let ell = sub(c, hyp__3half())
  let mut res = if eq(checksigntm(arg), q_d_negative) {
    // F(1,1;3/2;z) =
    // -%i*log(%i*sqrt(zn)+sqrt(1-zn))/(sqrt(1-zn)*sqrt(zn))
    // for z < 0
    let root1_z = power(sub(Fix(1L), s), inv(Fix(2L)))
    let rootz = power(s, inv(Fix(2L)))
    muln_([
      Fix(-1L),
      q_d__pcti,
      mlog(add2(mul2(q_d__pcti, rootz), root1_z)),
      inv(root1_z),
      inv(rootz),
    ])
  } else {
    // F(1,1;3/2;z) = asin(sqrt(zp))/(sqrt(1-zp)*sqrt(zp))
    // for z > 0
    let root1_z = power(sub(Fix(1L), s), inv(Fix(2L)))
    let rootz = power(s, inv(Fix(2L)))
    muln_([masin(rootz), inv(root1_z), inv(rootz)])
  }
  // Start with res = F(1,1;3/2;z). Compute F(m,1;3/2;z)
  res = as_15_dot2_dot3(Fix(1L), Fix(1L), hyp__3half(), m, s, res)
  // We now have res = C*F(m,1;3/2;z). Compute F(m,n;3/2;z)
  res = as_15_dot2_dot3(Fix(1L), a, hyp__3half(), n, s, res)
  // We now have res = C*F(m,n;3/2;z). Now compute F(m,n;3/2+ell;z):
  subst(
    arg,
    s,
    if minusp(ell) {
      as_15_dot2_dot4(a, b, hyp__3half(), num_neg(ell), s, res)
    } else {
      as_15_dot2_dot6(a, b, hyp__3half(), ell, s, res)
    },
  )
}

///|
let hyp__s_plus_c_pat : Value = try! lread(
  "((mplus) ((coeffpt) (f nonnump)) ((coeffpp) (c $numberp)))",
)

///|
/// Pattern match for s(ymbolic) + c(onstant) in parameter
fn s_plusc(exp_ : Value) -> Value raise {
  m2(exp_, hyp__s_plus_c_pat)
}

///|
fn nonnump(z : Value) -> Value raise {
  if !d_numberp(z).truthy() {
    t
  } else {
    Nil
  }
}

///|
/// Algor. III from thesis:determines which Differ. Formula to use
fn algiii(fun : Value, m : Value, n : Value, aprime : Value) -> Value raise {
  let mm = num_abs(m)
  let nn = num_abs(n)
  if nni(m).truthy() && nni(n).truthy() {
    if num_lt(m, n) {
      f81(fun, m, n, aprime)
    } else {
      f85(fun, mm, nn, aprime)
    }
  } else if hyp_negp(n).truthy() && hyp_negp(m).truthy() {
    if num_gt(num_abs(m), num_abs(n)) {
      f86(fun, mm, nn, aprime)
    } else {
      f82(fun, mm, nn, aprime)
    }
  } else if hyp_negp(m).truthy() && nni(n).truthy() {
    f83(fun, mm, nn, aprime)
  } else {
    f84(fun, mm, nn, aprime)
  }
}

///|
/// Factorial function:x*(x+1)*(x+2)...(x+n-1)
fn factf(x : Value, n : Value) -> Value raise {
  if zerop(n) {
    Fix(1L)
  } else {
    mul2(x, factf(add2(x, Fix(1L)), sub(n, Fix(1L))))
  }
}

///|
/// Formula  #85 from Yannis thesis:finds by differentiating F[2,1](a,b,c,z)
/// given F[2,1](a+m,b,c+n,z) where b=-a and c=1/2, n,m integers
///
/// Like F81, except m > n.
///
/// F(a+m,-a;c+n;z), m > n, c = 1/2, m and n are non-negative integers
///
/// A&S 15.2.3
/// diff(z^(a+m-n-1)*F(a,-a;1/2;z),z,m-n) = poch(a,m-n)*z^(a-1)*F(a+m-n,-a;1/2;z)
///
/// A&S 15.2.7
/// diff((1-z)^(a+m-1)*F(a+m-n,-a;1/2;z),z,n)
///     = (-1)^n*poch(a+m-n,n)*poch(1/2+a,n)/poch(1/2,n)*(1-z)^(a+m-n-1)
///         * F(a+m,-a;1/2+n;z)
fn f85(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    factf(inv(Fix(2L)), n),
    inv(power(Fix(-1L), n)),
    inv(factf(sub(add2(a, m), n), n)),
    inv(factf(sub(inv(Fix(2L)), mul2(a, Fix(-1L))), n)),
    inv(factf(a, num_sub(m, n))),
    power(sub(Fix(1L), q_ell), sub(sub(add2(Fix(1L), n), m), a)),
    hyp__diff(
      muln_([
        power(sub(Fix(1L), q_ell), sub(add2(a, m), Fix(1L))),
        power(q_ell, sub(Fix(1L), a)),
        hyp__diff(
          mul2(power(q_ell, sub(addn_([a, m, Fix(-1L)]), n)), fun),
          q_ell,
          num_sub(m, n),
        ),
      ]),
      q_ell,
      n,
    ),
  ])
}

///|
/// Used to find negative things that are not integers,eg RAT's
fn hyp_negp(x : Value) -> Value raise {
  if equal(asksign(x), q_d_negative) {
    t
  } else {
    Nil
  }
}

///|
/// F(a,-a+m; c+n; z) where m,n are non-negative integers, m < n, c = 1/2.
///
/// Rewrite F(a,-a+m; c+n;z) as F(-a+m, a; c+n; z). Then apply 15.2.6 to
/// F(-a,a;1/2;z), differentiating n-m times, multiply this result by
/// (1-z)^(n-a-1/2) and apply 15.2.7, differentiating m times, which gives
/// F(-a+m,a;1/2+n;z), which is what we wanted.
fn f81(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    factf(add2(inv(Fix(2L)), num_sub(n, m)), m),
    factf(inv(Fix(2L)), num_sub(n, m)),
    inv(power(Fix(-1L), m)),
    inv(factf(a, m)),
    inv(factf(addn_([inv(Fix(2L)), n, sub(a, m)]), m)),
    inv(factf(sub(inv(Fix(2L)), a), num_sub(n, m))),
    inv(factf(add2(inv(Fix(2L)), a), num_sub(n, m))),
    power(sub(Fix(1L), q_ell), sub(Fix(1L), a)),
    hyp__diff(
      mul2(
        power(sub(Fix(1L), q_ell), addn_([a, n, inv(Fix(-2L))])),
        hyp__diff(
          mul2(power(sub(Fix(1L), q_ell), inv(Fix(-2L))), fun),
          q_ell,
          num_sub(n, m),
        ),
      ),
      q_ell,
      m,
    ),
  ])
}

///|
/// Like f86, but |n|>=|m|
///
/// F(a-m,-a;1/2-n;z) where n >= m >0
///
/// G(z) = z^(m-n-1/2)*F(a,-a;1/2-n+m;z)
///      = z^(n-m+1/2)/poch(1/2-n+m,n-m)*diff(z^(-1/2)*F(a,-a;1/2;z),z,n-m)
///
/// F(a-m,-a;1/2-n;z)
///     = z^(n+1/2)*(1-z)^(m+a-1/2-n)/poch(1/2-n,m)*diff((1-z)^(n-a-1/2)*G(z),z,m)
fn f82(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    inv(factf(sub(inv(Fix(2L)), n), m)),
    inv(factf(sub(add2(inv(Fix(2L)), m), n), num_sub(n, m))),
    power(q_ell, add2(n, inv(Fix(2L)))),
    power(sub(Fix(1L), q_ell), sub(addn_([m, inv(Fix(2L)), a]), n)),
    hyp__diff(
      mul2(
        power(sub(Fix(1L), q_ell), sub(sub(n, a), inv(Fix(2L)))),
        hyp__diff(
          mul2(power(q_ell, inv(Fix(-2L))), fun),
          q_ell,
          num_sub(n, m),
        ),
      ),
      q_ell,
      m,
    ),
  ])
}

///|
/// F(a+m,-a;1/2+n;z) with m,n integers and m < 0, n >= 0
///
/// Write this more clearly as F(a-m,-a;1/2+n;z), m > 0, n >= 0
///
/// F(a-m,-a;1/2+n;z)
///     = (1-z)^(n+m+1/2)*z^(a-n+1/2)/poch(1/2+n-a,m)
///        *diff(z^(n+m-a-1/2)*(1-z)^(-1/2-n)*F(a,-a;1/2+n;z),z,m)
fn f83(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    factf(inv(Fix(2L)), n),
    inv(factf(sub(inv(Fix(2L)), a), n)),
    inv(factf(sub(add2(n, inv(Fix(2L))), a), m)),
    inv(factf(add2(inv(Fix(2L)), a), n)),
    power(sub(Fix(1L), q_ell), addn_([m, n, inv(Fix(2L))])),
    power(q_ell, add2(sub(a, n), inv(Fix(2L)))),
    hyp__diff(
      mul2(
        power(q_ell, sub(sub(num_add(m, n), a), inv(Fix(2L)))),
        hyp__diff(
          mul2(power(sub(Fix(1L), q_ell), inv(Fix(-2L))), fun),
          q_ell,
          n,
        ),
      ),
      q_ell,
      m,
    ),
  ])
}

///|
/// The last case F(a+m,-a;c+n;z), m,n integers, m >= 0, n < 0
///
/// F(a+m,-a;1/2-n;z)
///
/// diff(z^(-1/2)*F(a,-a;1/2;z),z,n) = poch(1/2-n,n)*z^(-n-1/2)*F(a,-a;1/2-n;z)
///
/// diff(z^(a+m-1)*F(a,-a;1/2-n;z),z,m) = poch(a,m)*z^(a-1)*F(a+m,-a;1/2-n;z)
fn f84(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    inv(mul2(factf(a, m), factf(sub(inv(Fix(2L)), n), n))),
    power(q_ell, sub(Fix(1L), a)),
    hyp__diff(
      mul2(
        power(q_ell, sub(addn_([a, m, n]), inv(Fix(2L)))),
        hyp__diff(mul2(power(q_ell, inv(Fix(-2L))), fun), q_ell, n),
      ),
      q_ell,
      m,
    ),
  ])
}

///|
/// Like f82, but |n|<|m|
///
/// F(a-m,-a;1/2-n;z), 0 < n < m
///
/// G(z) = z^(-a-1/2)*(1-z)^(-1/2-m+n)*F(a-m+n,-a;1/2;z)
///      = 1/poch(1/2-a,m-n)*diff(z^(-a+m-n-1/2)*(1-z)^(-1/2)*F(a,-a;1/2;z),z,m-n)
///
/// F(a-m,-a;1/2-n;z)
///      = z^(n+1/2)*(1-z)^(a+1/2)/poch(1/2-n,n)
///         *diff(z^a*(1-z)^(m-a)*G(z),z,n)
fn f86(fun : Value, m : Value, n : Value, a : Value) -> Value raise {
  muln_([
    inv(
      mul2(
        factf(sub(inv(Fix(2L)), n), n),
        factf(sub(inv(Fix(2L)), a), num_sub(m, n)),
      ),
    ),
    power(q_ell, add2(n, inv(Fix(2L)))),
    power(sub(Fix(1L), q_ell), add2(inv(Fix(2L)), a)),
    hyp__diff(
      muln_([
        power(q_ell, a),
        power(sub(Fix(1L), q_ell), sub(m, a)),
        hyp__diff(
          muln_([
            power(q_ell, sub(sub(sub(m, n), inv(Fix(2L))), a)),
            power(sub(Fix(1L), q_ell), inv(Fix(-2L))),
            fun,
          ]),
          q_ell,
          num_sub(m, n),
        ),
      ]),
      q_ell,
      n,
    ),
  ])
}

///|
/// F(-1/2+n, 1+m; 1/2+l; z)
fn hyp_atanh(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  // We start with F(-1/2,1;1/2;z) = 1-sqrt(z)*atanh(sqrt(z)). We can derive
  // the remaining forms by differentiating this enough times.
  //
  // FIXME:  Do we need to assume z > 0?  We do that anyway, here.
  let s = gensym(prefix="hyp-atanh-")
  let n = add2(a, hyp__half())
  let m = sub(b, Fix(1L))
  let ell = sub(c, hyp__half())
  let mut res = sub(
    Fix(1L),
    mul2(
      power(s, hyp__rat(1, 2)),
      take(list1(q_p_atanh), [power(s, hyp__rat(1, 2))]),
    ),
  )
  let mut new_a = hyp__mhalf()
  let mut new_b : Value = Fix(1L)
  let mut new_c = hyp__half()
  // The total number of derivates we compute is n + m + ell. We should do
  // something to reduce the number of derivatives.
  if alike1(sub(n, ell), Fix(0L)).truthy() {
    // n = ell so we can use A&S 15.2.7 or A&S 15.2.8
    if plusp(n) {
      res = as_15_dot2_dot7(new_a, new_b, new_c, n, s, res)
    } else {
      res = as_15_dot2_dot8(new_a, new_b, new_c, num_neg(n), s, res)
    }
    new_a = add2(new_a, n)
    new_c = add2(new_c, n)
  } else {
    // Adjust ell and then n. (Does order matter?)
    if plusp(ell) {
      res = as_15_dot2_dot6(new_a, new_b, new_c, ell, s, res)
      new_c = add2(new_c, ell)
    } else {
      res = as_15_dot2_dot4(new_a, new_b, new_c, num_neg(ell), s, res)
      new_c = add2(new_c, ell)
    }
    if plusp(n) {
      // A&S 15.2.3
      res = as_15_dot2_dot3(new_a, new_b, new_c, n, s, res)
      new_a = add2(new_a, n)
    } else {
      // A&S 15.2.5
      res = as_15_dot2_dot5(new_a, new_b, new_c, num_neg(n), s, res)
      new_a = add2(new_a, n)
    }
  }
  // Finally adjust m by swapping the a and b parameters, since the
  // hypergeometric function is symmetric in a and b.
  if plusp(m) {
    res = as_15_dot2_dot3(new_b, new_a, new_c, m, s, res)
    new_b = add2(new_b, m)
  } else {
    res = as_15_dot2_dot5(new_b, new_a, new_c, num_neg(m), s, res)
    new_b = add2(new_b, m)
  }
  ignore(new_b)
  // Substitute the argument into the expression and simplify the result.
  sratsimp(maxima_substitute(arg, s, res))
}
