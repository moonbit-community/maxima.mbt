// Port of src/hyp.lisp, part 1: the main entry point hgfred, parameter
// simplification, polynomial cases, dispatch on p and q, and 2F1.
//
// References:
//
// Definite integration using the generalized hypergeometric functions
// Avgoustis, Ioannis Dimitrios
// Thesis. 1977. M.S.--Massachusetts Institute of Technology. Dept.
// of Electrical Engineering and Computer Science
// http://dspace.mit.edu/handle/1721.1/16269
//
// Avgoustis, I. D., Symbolic Laplace Transforms of Special Functions,
// Proceedings of the 1977 MACSYMA Users' Conference, pp 21-41

// ---------------------------------------------------------------------------
// Local macros of hyp.lisp.

///|
/// `(simp x)` = `(simplifya x ())`
fn simp(x : Value) -> Value raise {
  simplifya(x, Nil)
}

///|
fn hyp_mabs(x : Value) -> Value raise {
  simp(mk(q_mabs, [x]))
}

///|
fn msqrt(x : Value) -> Value raise {
  power(x, symval(q_n1_sl_sl2))
}

///|
fn mexpt(x : Value) -> Value raise {
  power(q_d__pcte, x)
}

///|
fn mlog(x : Value) -> Value raise {
  simp(mk(q_p_log, [x]))
}

///|
fn msin(x : Value) -> Value raise {
  simp(mk(q_p_sin, [x]))
}

///|
fn mcos(x : Value) -> Value raise {
  simp(mk(q_p_cos, [x]))
}

///|
fn masin(x : Value) -> Value raise {
  simp(mk(q_p_asin, [x]))
}

///|
fn matan(x : Value) -> Value raise {
  simp(mk(q_p_atan, [x]))
}

///|
fn mgamma(x : Value) -> Value raise {
  simp(mk(q_p_gamma, [x]))
}

///|
fn mbinom(x : Value, y : Value) -> Value raise {
  simp(mk(q_p_binomial, [x, y]))
}

///|
fn merf(x : Value) -> Value raise {
  simp(mk(q_p_erf, [x]))
}

///|
fn n_eq1_sl_sl2(x : Value) -> Value raise {
  alike1(x, symval(q_n1_sl_sl2))
}

// ---------------------------------------------------------------------------
// Private helpers.

///|
/// `'((rat simp) n d)`
fn hyp__rat(n : Int64, d : Int64) -> Value {
  mk_simp(q_rat, [Fix(n), Fix(d)])
}

///|
/// The special `1//2`.
fn hyp__half() -> Value {
  symval(q_n1_sl_sl2)
}

///|
/// The special `3//2`.
fn hyp__3half() -> Value {
  symval(q_n3_sl_sl2)
}

///|
/// The special `-1//2`.
fn hyp__mhalf() -> Value {
  symval(q_n_1_sl_sl2)
}

///|
fn hyp__trace() -> Bool {
  symval(q_d_trace2f1).truthy()
}

///|
fn hyp__debug() -> Bool {
  symval(q_ear_debug_hyp).truthy()
}

///|
/// `(format t ctl args...)`
fn hyp__fmt(ctl : String, args : Array[Value]) -> Unit raise {
  format(t, ctl, args) |> ignore
}

///|
/// `(delete item list :count 1 :test #'equal)`, destructive like SBCL:
/// when the first element matches, the cdr is returned and the list is not
/// modified; otherwise the matching cell is spliced out.
fn hyp__delete1_equal(item : Value, l : Value) -> Value {
  match l {
    Cons(c) =>
      if equal(item, c.car) {
        c.cdr
      } else {
        let mut prev = c
        while prev.cdr is Cons(next) {
          if equal(item, next.car) {
            prev.cdr = next.cdr
            break
          }
          prev = next
        }
        l
      }
    _ => l
  }
}

///|
/// `(remove item list :count 1)` (eql test, non-destructive).
fn hyp__remove1(item : Value, l : Value) -> Value {
  let acc = Collector::new()
  let mut p = l
  while p is Cons(c) {
    if eql(item, c.car) {
      acc.append_list(c.cdr)
      return acc.result()
    }
    acc.add(c.car)
    p = c.cdr
  }
  acc.result()
}

///|
/// `(assert (>= n 0))`
fn hyp__assert_nonneg(n : Value) -> Unit raise {
  if !num_ge(n, Fix(0L)) {
    raise LispError::SimpleError("The assertion (>= N 0) failed.")
  }
}

///|
/// `(member ($sign x) '($neg $nz))`
fn hyp__sign_negnz(x : Value) -> Bool raise {
  memq(d_sign(x), list2(q_d_neg, q_d_nz)).truthy()
}

///|
/// `($diff expr var n)`
fn hyp__diff(e : Value, var_ : Value, n : Value) -> Value raise {
  d_diff(list([e, var_, n]))
}

// ---------------------------------------------------------------------------
// Functions moved from hypgeo.lisp to this place.

///|
/// Gamma function
fn gm(expr : Value) -> Value raise {
  simplifya(list2(list1(q_p_gamma), expr), Nil)
}

///|
/// sin(x)
fn sin_pct(arg : Value) -> Value raise {
  list2(list1(q_p_sin), arg)
}

///|
/// cos(x)
fn cos_pct(arg : Value) -> Value raise {
  list2(list1(q_p_cos), arg)
}

///|
/// Test if X is a number, either Lisp number or a maxima rational.
fn nump(x : Value) -> Value raise {
  if atom(x) {
    lbool(numberp(x))
  } else {
    lbool(eq(caar(simplifya(x, Nil)), q_rat))
  }
}

///|
/// In this file, maxima-integerp was used in many places. But it seems
/// that this code expects maxima-integerp to return T when it is really
/// an integer, not something that was declared an integer.
fn hyp_integerp(x : Value) -> Value raise {
  if maxima_integerp(x).truthy() {
    lbool(integerp(x))
  } else {
    Nil
  }
}

///|
/// Main entry point for simplification of hypergeometric functions.
///
/// F(a1,a2,a3,...;b1,b2,b3;z)
///
/// L1 is a (maxima) list of an's, L2 is a (maxima) list of bn's.
fn d_hgfred(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let arg_ok = (a : Value) => listp(a) && eq(caar(a), q_mlist)
  if !arg_ok(arg_l1) {
    merr("hgfred: first argument must be a list; found: ~:M", [arg_l1])
    |> ignore
  }
  if !arg_ok(arg_l2) {
    merr("hgfred: second argument must be a list; found: ~:M", [arg_l2])
    |> ignore
  }
  with_special(q_ear_checkcoefsignlist, Nil, () => hgfsimp_exec(
    cdr(arg_l1),
    cdr(arg_l2),
    arg,
  ))
}

///|
fn hgfsimp_exec(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let l1 = copy_tree(arg_l1)
  let l2 = copy_tree(arg_l2)
  let res = with_special(q_d_exponentialize, Nil, () => hgfsimp(l1, l2, arg))
  // I think hgfsimp returns FAIL and UNDEF for cases where it couldn't
  // reduce the function.
  if eq(res, q_fail) {
    fpqform(l1, l2, arg)
  } else if eq(res, q_undef) {
    q_d_und
  } else {
    res
  }
}

///|
fn hgfsimp(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let arg_l1 = macsimp(arg_l1)
  let arg_l2 = macsimp(arg_l2)
  let resimp = simpg(arg_l1, arg_l2, arg)
  if !eq(if consp(resimp) { car(resimp) } else { Nil }, q_fail) {
    return resimp
  }
  if !zerop1(arg).truthy() {
    // Do not call splitfpq for a zero argument
    let listcmdiff = intdiffl1l2(cadr(resimp), caddr(resimp))
    if listcmdiff.truthy() {
      return splitpfq(listcmdiff, cadr(resimp), caddr(resimp), arg)
    }
  }
  dispatch_spec_simp(cadr(resimp), caddr(resimp), arg)
}

///|
fn macsimp(expr : Value) -> Value raise {
  mapcar(index => d_expand(index), expr)
}

///|
/// Simplify the parameters. If L1 and L2 have common elements, remove
/// them from both L1 and L2.
fn simpg(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let il = zl_intersection(arg_l1, arg_l2)
  if il is Nil {
    simpg_exec(arg_l1, arg_l2, arg)
  } else {
    simpg_exec(del(il, arg_l1), del(il, arg_l2), arg)
  }
}

///|
fn del(a : Value, b : Value) -> Value raise {
  if a is Nil {
    b
  } else {
    del(cdr(a), hyp__delete1_equal(car(a), b))
  }
}

///|
/// Handle the simple cases where the result is either a polynomial, or is
/// undefined because we divide by zero.
fn simpg_exec(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  if zerop_in_l(arg_l1).truthy() {
    // A zero in the first index means the series terminates after the
    // first term, so the result is always 1.
    return Fix(1L)
  }
  let n = hyp_negp_in_l(arg_l1)
  if n.truthy() {
    // A negative integer in the first series means we have a polynomial.
    create_poly(arg_l1, arg_l2, n, arg)
  } else if (zerop_in_l(arg_l2).truthy() || hyp_negp_in_l(arg_l2).truthy()) &&
    every(x => mnump(x).truthy(), arg_l1) &&
    every(x => mnump(x).truthy(), arg_l2) {
    // A zero or negative number in the second index means we eventually
    // divide by zero, so we're undefined. But only do this if both
    // indices contain numbers. See Bug 1858964 for discussion.
    q_undef
  } else {
    // We failed so more complicated stuff needs to be done.
    list([q_fail, arg_l1, arg_l2])
  }
}

///|
fn intdiffl1l2(arg_l1 : Value, arg_l2 : Value) -> Value raise {
  if arg_l1 is Nil {
    Nil
  } else {
    intdiff(arg_l1, arg_l2)
  }
}

///|
/// For each element x in arg-l1 and y in arg-l2, compute d = x - y. Find
/// the smallest such non-negative integer d and return (list x d).
fn intdiff(arg_l1 : Value, arg_l2 : Value) -> Value raise {
  let mut result : Value = Nil
  // Compute all possible differences between elements in arg-l1 and
  // arg-l2. Only save the ones where the difference is a positive integer
  for x in arg_l1.iter() {
    for y in arg_l2.iter() {
      let diff = sub(x, y)
      if nni(diff).truthy() {
        result = cons(list2(x, diff), result)
      }
    }
  }
  // Find the smallest one and return it.
  let mut min = first(result)
  for x in rest(result).iter() {
    if num_lt(second(x), second(min)) {
      min = x
    }
  }
  min
}

///|
/// Create the appropriate polynomial for the hypergeometric function.
fn create_poly(
  arg_l1 : Value,
  arg_l2 : Value,
  n : Value,
  arg : Value,
) -> Value raise {
  let len1 = length(arg_l1)
  let len2 = length(arg_l2)
  // n is the smallest (in magnitude) negative integer in L1. To make
  // everything come out right, we need to make sure this value is first
  // in L1.
  let arg_l1 = cons(n, hyp__remove1(n, arg_l1))
  if len1 == 2 && len2 == 1 {
    n2f1polys(arg_l1, arg_l2, n, arg)
  } else if len1 == 1 && len2 == 1 {
    n1f1polys(arg_l2, n, arg)
  } else if len1 == 2 && len2 == 0 {
    n2f0polys(arg_l1, n, arg)
  } else {
    create_any_poly(arg_l1, arg_l2, mul2(Fix(-1L), n), arg)
  }
}

///|
fn n1f1polys(arg_l2 : Value, n : Value, arg : Value) -> Value raise {
  let c = car(arg_l2)
  let n = mul2(Fix(-1L), n)
  let fact1 = muln_([
    power(Fix(2L), n),
    take(list1(q_mfactorial), [n]),
    inv(power(Fix(-1L), n)),
  ])
  // For all of the polynomials here, I think it's ok to replace sqrt(z^2)
  // with z because when everything is expanded out they evaluate to
  // exactly the same thing. So $radexpand $all is ok here.
  let fact2 = with_special(q_d_radexpand, q_d_all, () => mul2(
    power(Fix(2L), hyp__rat(1, 2)),
    power(arg, hyp__rat(1, 2)),
  ))
  if alike1(c, hyp__rat(1, 2)).truthy() {
    // A&S 22.5.56
    // hermite(2*n,x) = (-1)^n*(2*n)!/n!*M(-n,1/2,x^2)
    //
    // M(-n,1/2,x) = (-1)^n*n!*2^n/(2*n)!*He(2*n,sqrt(2)*sqrt(x))
    muln_([
      fact1,
      inv(take(list1(q_mfactorial), [add2(n, n)])),
      hermpol(add2(n, n), fact2),
    ])
  } else if alike1(c, hyp__rat(3, 2)).truthy() {
    // A&S 22.5.57
    // hermite(2*n+1,x) = (-1)^n*(2*n+1)!/n!*M(-n,3/2,x^2)*2*x
    //
    // M(-n,3/2,x) = (-1)^n*n!*2^(n-1/2)/(2*n+1)!/sqrt(x)*He(2*n+1,sqrt(2)*sqrt(x))
    muln_([
      fact1,
      inv(power(Fix(2L), hyp__rat(1, 2))),
      inv(take(list1(q_mfactorial), [addn_([n, n, Fix(1L)])])),
      hermpol(addn_([n, n, Fix(1L)]), fact2),
      // Similarly, $radexpand here is ok to convert sqrt(z^2) to z.
      with_special(q_d_radexpand, q_d_all, () => inv(
        power(arg, hyp__rat(1, 2)),
      )),
    ])
  } else if alike1(c, neg(add2(n, n))).truthy() {
    // 1F1(-n; -2*n; z)
    muln_([
      power(Fix(-1L), n),
      inv(take(list1(q_p_binomial), [add2(n, n), n])),
      lagpol(n, sub(c, Fix(1L)), arg),
    ])
  } else if integerp(n) && numberp(c) {
    // A&S 22.5.54:
    //
    // gen_laguerre(n,alpha,x) = binomial(n+alpha,n)*hgfred([-n],[alpha+1],x);
    //
    // hgfred([-n],[alpha],x) = n! / poch(alpha, n) * gen_laguerre(n,alpha-1,x)
    //
    // See Bug 1858939.
    if zerop(c) || (minusp(c) && num_gt(c, num_neg(n))) {
      merr("hgfred: 1F1(~M; ~M; ~M) not defined.", [num_neg(n), c, arg])
    } else {
      muln_([
        take(list1(q_mfactorial), [n]),
        inv(take(list1(q_d_pochhammer), [c, n])),
        lagpol(n, sub(c, Fix(1L)), arg),
      ])
    }
  } else {
    // If c is not a number leave the result in terms of gamma functions.
    with_special(q_d_gamma_expand, t, () => muln_([
      take(list1(q_mfactorial), [n]),
      take(list1(q_p_gamma), [c]),
      inv(take(list1(q_p_gamma), [add2(c, n)])),
      lagpol(n, sub(c, Fix(1L)), arg),
    ]))
  }
}

///|
/// Hermite polynomial. Note: The Hermite polynomial used here is the He
/// polynomial, defined as (A&S 22.5.18, 22.5.19)
///
/// He(n,x) = 2^(-n/2)*H(n,x/sqrt(2))
fn hermpol(n : Value, arg : Value) -> Value raise {
  let fact = inv(power(Fix(2L), div(n, Fix(2L))))
  let x = mul2(arg, inv(power(Fix(2L), hyp__rat(1, 2))))
  mul2(
    fact,
    if symval(q_d_expand_polynomials).truthy() && integerp(n) {
      mfuncall(q_d_hermite, list2(n, x))
    } else {
      mk_simp(q_d_hermite, [n, x])
    },
  )
}

///|
/// Generalized Laguerre polynomial
fn lagpol(n : Value, a : Value, arg : Value) -> Value raise {
  if numberp(a) && zerop(a) {
    if symval(q_d_expand_polynomials).truthy() && integerp(n) {
      mfuncall(q_d_laguerre, list2(n, arg))
    } else {
      mk_simp(q_d_laguerre, [n, arg])
    }
  } else if symval(q_d_expand_polynomials).truthy() && integerp(n) {
    mfuncall(q_d_gen_laguerre, list3(n, a, arg))
  } else {
    mk_simp(q_d_gen_laguerre, [n, a, arg])
  }
}

///|
fn n2f0polys(arg_l1 : Value, n : Value, arg : Value) -> Value raise {
  let mut a = car(arg_l1)
  let mut b = cadr(arg_l1)
  if alike1(sub(b, a), hyp__rat(-1, 2)).truthy() {
    let tmp = a
    a = b
    b = tmp
  }
  if alike1(sub(b, a), hyp__rat(1, 2)).truthy() {
    // 2F0(-n,-n+1/2,z) or 2F0(-n-1/2,-n,z)
    interhermpol(n, a, b, arg)
  } else {
    // 2F0(a,b;z)
    let x = mul2(Fix(-1L), inv(arg))
    let order = mul2(Fix(-1L), n)
    muln_([
      take(list1(q_mfactorial), [order]),
      inv(power(x, order)),
      inv(power(Fix(-1L), order)),
      lagpol(order, mul2(Fix(-1L), add2(b, order)), x),
    ])
  }
}

///|
/// Compute 2F0(-n,-n+1/2;z) and 2F0(-n-1/2,-n;z) in terms of Hermite
/// polynomials:
///
/// 2F0(-n,-n+1/2;z) = y^n * He(2*n,y)
/// 2F0(-n-1/2,-n;z) = y^(2*n+1) * He(2*n+1,y)
///
/// where y = sqrt(-2/x).
fn interhermpol(n : Value, a : Value, b : Value, x : Value) -> Value raise {
  let arg = power(div(Fix(2L), mul2(Fix(-1L), x)), hyp__rat(1, 2))
  let order = if alike1(a, n).truthy() {
    mul2(Fix(-2L), n)
  } else if alike1(b, n).truthy() {
    sub(Fix(1L), add2(n, n))
  } else {
    Nil
  }
  // 2F0(-n,-n+1/2;z) = y^(-2*n)*He(2*n,y)
  // 2F0(-n-1/2,-n;z) = y^(-(2*n+1))*He(2*n+1,y)
  //
  // where y = sqrt(-2/var);
  mul2(power(arg, mul2(Fix(-1L), order)), hermpol(order, arg))
}

///|
/// F(n,b;c;z), where n is a negative integer (number or symbolic). The
/// order of the arguments must be checked by the calling routine.
fn n2f1polys(
  arg_l1 : Value,
  arg_l2 : Value,
  n : Value,
  arg : Value,
) -> Value raise {
  let v = if mnump(arg).truthy() {
    // The argument of the hypergeometric function is a number. Avoid the
    // following check which does not work for this case.
    div(add2(cadr(arg_l1), n), Fix(2L))
  } else {
    // Check if (b+n)/2 is free of the argument. At this point of the code
    // there is no check of the return value of vfvp. When nil we have no
    // solution and the result is wrong.
    let l = vfvp(div(add2(cadr(arg_l1), n), Fix(2L)), arg)
    cdr(assoc_equal(q_v, l))
  }
  if !integerp(n) || !symval(q_d_expand_polynomials).truthy() {
    // Assuming we have F(-n,b;c;z), then v is (b+n)/2. See if it can be a
    // Legendre function. We call legpol-core because we know that arg-l1
    // has the correct order.
    let lgf = legpol_core(car(arg_l1), cadr(arg_l1), car(arg_l2), arg)
    if lgf.truthy() {
      return lgf
    }
  }
  if (!integerp(n) || !symval(q_d_expand_polynomials).truthy()) &&
    alike1(sub(car(arg_l2), v), hyp__rat(1, 2)).truthy() {
    // A&S 15.4.5:
    // F(-n, n+2*a; a+1/2; x) = n!*gegen(n, a, 1-2*x)/pochhammer(2*a,n)
    //
    // So v = a, and (car arg-l2) = a + 1/2.
    mul2(
      if zerop1(v).truthy() {
        Fix(1L)
      } else {
        mul2(
          take(list1(q_mfactorial), [mul2(Fix(-1L), n)]),
          inv(take(list1(q_d_pochhammer), [mul2(Fix(2L), v), mul2(Fix(-1L), n)])),
        )
      },
      gegenpol(mul2(Fix(-1L), n), v, sub(Fix(1L), mul2(Fix(2L), arg))),
    )
  } else {
    // A&S 15.4.6 says
    // F(-n, n + a + 1 + b; a + 1; x)
    //   = n!*jacobi_p(n,a,b,1-2*x)/pochhammer(a+1,n)
    muln_([
      take(list1(q_mfactorial), [mul2(Fix(-1L), n)]),
      inv(take(list1(q_d_pochhammer), [car(arg_l2), mul2(Fix(-1L), n)])),
      jacobpol(
        mul2(Fix(-1L), n),
        add2(car(arg_l2), Fix(-1L)),
        sub(mul2(Fix(2L), v), car(arg_l2)),
        sub(Fix(1L), mul2(Fix(2L), arg)),
      ),
    ])
  }
}

///|
/// Jacobi polynomial
fn jacobpol(n : Value, a : Value, b : Value, x : Value) -> Value raise {
  if symval(q_d_expand_polynomials).truthy() && integerp(n) {
    mfuncall(q_d_jacobi_p, list4(n, a, b, x))
  } else {
    mk_simp(q_d_jacobi_p, [n, a, b, x])
  }
}

///|
/// Gegenbauer (Ultraspherical) polynomial. We use ultraspherical to match
/// specfun.
fn gegenpol(n : Value, v : Value, x : Value) -> Value raise {
  if equal(v, Fix(0L)) {
    tchebypol(n, x)
  } else if symval(q_d_expand_polynomials).truthy() && integerp(n) {
    mfuncall(q_d_ultraspherical, list3(n, v, x))
  } else {
    mk_simp(q_d_ultraspherical, [n, v, x])
  }
}

///|
/// Legendre polynomial
fn legenpol(n : Value, x : Value) -> Value raise {
  if symval(q_d_expand_polynomials).truthy() && integerp(n) {
    mfuncall(q_d_legendre_p, list2(n, x))
  } else {
    mk_simp(q_d_legendre_p, [n, x])
  }
}

///|
/// Chebyshev polynomial
fn tchebypol(n : Value, x : Value) -> Value raise {
  if symval(q_d_expand_polynomials).truthy() && integerp(n) {
    mfuncall(q_d_chebyshev_t, list2(n, x))
  } else {
    mk_simp(q_d_chebyshev_t, [n, x])
  }
}

///|
/// Expand the hypergeometric function as a polynomial. No real checks are
/// made to ensure the hypergeometric function reduces to a polynomial.
fn d_hgfpoly(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let n = hyp_negp_in_l(cdr(arg_l1))
  create_any_poly(cdr(arg_l1), cdr(arg_l2), num_neg(n), arg)
}

///|
fn create_any_poly(
  arg_l1 : Value,
  arg_l2 : Value,
  n : Value,
  arg : Value,
) -> Value raise {
  let mut arg_l1 = arg_l1
  let mut arg_l2 = arg_l2
  let mut n = n
  let mut result : Value = Fix(1L)
  let mut prodnum : Value = Fix(1L)
  let mut proden : Value = Fix(1L)
  let mut exp : Value = Fix(1L)
  while true {
    if zerop(n) {
      return result
    }
    prodnum = mul2(prodnum, mull(arg_l1))
    proden = mul2(proden, mull(arg_l2))
    result = add2(
      result,
      muln_([prodnum, power(arg, exp), inv(proden), inv(factorial(exp))]),
    )
    n = sub(n, Fix(1L))
    exp = add2(exp, Fix(1L))
    arg_l1 = incr1(arg_l1)
    arg_l2 = incr1(arg_l2)
  }
  result
}

///|
/// Compute the product of the elements of the list L.
fn mull(l : Value) -> Value raise {
  let mut acc : Value = Fix(1L)
  for x in l.iter() {
    acc = mul2(acc, x)
  }
  acc
}

///|
/// Add 1 to each element of the list L
fn incr1(l : Value) -> Value raise {
  mapcar(x => add2(x, Fix(1L)), l)
}

///|
/// Figure out the orders of generalized hypergeometric function we have
/// and call the right simplifier.
fn dispatch_spec_simp(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let len1 = length(arg_l1)
  let len2 = length(arg_l2)
  if len1 < 2 && len2 < 2 {
    // pFq where p and q < 2.
    simp2_gtf_lt2(arg_l1, arg_l2, int(len1), int(len2), arg)
  } else if len1 == 2 && len2 == 1 {
    // 2F1
    simp2f1(arg_l1, arg_l2, arg)
  } else if len1 == 2 && len2 == 0 {
    // 2F0(a,b; ; z)
    if maxima_integerp(car(arg_l1)).truthy() && hyp__sign_negnz(car(arg_l1)) {
      // 2F0(-n,b; ; z), n a positive integer
      n2f0polys(arg_l1, car(arg_l1), arg)
    } else if maxima_integerp(cadr(arg_l1)).truthy() &&
      hyp__sign_negnz(cadr(arg_l1)) {
      // 2F0(a,-n; ; z), n a positive integer
      n2f0polys(reverse(arg_l1), cadr(arg_l1), arg)
    } else {
      fpqform(arg_l1, arg_l2, arg)
    }
  } else if len1 == 1 && len2 == 2 {
    // Some 1F2 forms
    simp1f2(arg_l1, arg_l2, arg)
  } else if len1 == 2 && len2 == 2 {
    simp2f2(arg_l1, arg_l2, arg)
  } else {
    // We don't have simplifiers for any other hypergeometric function.
    fpqform(arg_l1, arg_l2, arg)
  }
}

///|
/// Handle the cases where the number of indices is less than 2.
fn simp2_gtf_lt2(
  arg_l1 : Value,
  arg_l2 : Value,
  len1 : Value,
  len2 : Value,
  arg : Value,
) -> Value raise {
  if zerop(len1) && zerop(len2) {
    // hgfred([],[],z) = e^z
    power(q_d__pcte, arg)
  } else if zerop(len1) && equal(len2, Fix(1L)) {
    if zerop1(arg).truthy() {
      // hgfred([],[b],0) = 1
      add2(arg, Fix(1L))
    } else {
      // hgfred([],[b],z) = bessel_i(b-1,2*sqrt(z))*z^((1-b)/2)*gamma(b)
      bestrig(car(arg_l2), arg)
    }
  } else if zerop(len2) {
    // hgfred([a],[],z) = 1 + sum(binomial(a+k,k)*z^k) = 1/(1-z)^a
    power(sub(Fix(1L), arg), mul2(Fix(-1L), car(arg_l1)))
  } else {
    // The general case of 1F1, the confluent hypergeomtric function.
    confl(arg_l1, arg_l2, arg)
  }
}

///|
/// Computes
///
/// bessel_i(a-1,2*sqrt(x))*gamma(a)*x^((1-a)/2)   if x > 0
/// bessel_j(a-1,2*sqrt(x))*gamma(a)*x^((1-a)/2)   if x < 0.
///
/// If a is half of an odd integer and small enough, the Bessel functions
/// are expanded in terms of trig or hyperbolic functions.
fn bestrig(b : Value, x : Value) -> Value raise {
  // I think it's ok to have $radexpand $all here so that sqrt(z^2) is
  // converted to z.
  with_special(q_d_radexpand, q_d_all, () => if mminusp(x).truthy() {
    // gamma(b)*(-x)^((1-b)/2)*bessel_j(b-1,2*sqrt(-x))
    sratsimp(
      muln_([
        power(neg(x), div(sub(Fix(1L), b), Fix(2L))),
        take(list1(q_p_gamma), [b]),
        take(list1(q_p_bessel_j), [
          sub(b, Fix(1L)),
          mul2(Fix(2L), power(neg(x), hyp__rat(1, 2))),
        ]),
      ]),
    )
  } else {
    // gamma(b)*(x)^((1-b)/2)*bessel_i(b-1,2*sqrt(x))
    sratsimp(
      muln_([
        power(x, div(sub(Fix(1L), b), Fix(2L))),
        take(list1(q_p_gamma), [b]),
        take(list1(q_p_bessel_i), [
          sub(b, Fix(1L)),
          mul2(Fix(2L), power(x, hyp__rat(1, 2))),
        ]),
      ]),
    )
  })
}

///|
/// Kummer's transformation. A&S 13.1.27
///
/// M(a,b,z) = e^z*M(b-a,b,-z)
fn kummer(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  mul2(
    mk(q_mexpt, [q_d__pcte, arg]),
    confl(
      list1(sub(car(arg_l2), car(arg_l1))),
      arg_l2,
      mul2(Fix(-1L), arg),
    ),
  )
}

///|
/// Return non-NIL if any element of the list L is zero.
fn zerop_in_l(l : Value) -> Value raise {
  lbool(some(x => numberp(x) && zerop(x), l))
}

///|
/// If the list L contains a negative integer, return the most positive of
/// the negative integers. Otherwise return NIL.
fn hyp_negp_in_l(l : Value) -> Value raise {
  let mut max_neg : Value = Nil
  for x in l.iter() {
    if integerp(x) && minusp(x) {
      if max_neg.truthy() {
        max_neg = num_max(max_neg, x)
      } else {
        max_neg = x
      }
    }
  }
  max_neg
}

///|
/// Compute the intersection of L1 and L2, possibly destructively modifying
/// L2. Preserves duplications in L1.
fn zl_intersection(arg_l1 : Value, arg_l2 : Value) -> Value raise {
  if arg_l1 is Nil {
    Nil
  } else if member_equal(car(arg_l1), arg_l2).truthy() {
    cons(
      car(arg_l1),
      zl_intersection(cdr(arg_l1), hyp__delete1_equal(car(arg_l1), arg_l2)),
    )
  } else {
    zl_intersection(cdr(arg_l1), arg_l2)
  }
}

///|
/// Whittaker M function. A&S 13.1.32 defines it as
///
/// %m[k,u](z) = exp(-z/2)*z^(u+1/2)*M(1/2+u-k,1+2*u,z)
///
/// where M is the confluent hypergeometric function.
fn whitfun(k : Value, m : Value, arg : Value) -> Value raise {
  list3(list1(q_mqapply), list([list2(q_d__pctm, q_array), k, m]), arg)
}

///|
/// Simplify 1F2([a], [b,c], arg). ARG-L1 is the list [a], and ARG-L2 is
/// the list [b, c].
fn simp1f2(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a = car(arg_l1)
  let b = first(arg_l2)
  let c = second(arg_l2)
  if alike1(a, hyp__half()).truthy() &&
    alike1(b, hyp__3half()).truthy() &&
    alike1(c, hyp__3half()).truthy() {
    // Sine integral, expintegral_si(z) = z*%f[1,2]([1/2],[3/2,3/2], -z^2/4)
    // (See http://functions.wolfram.com/06.37.26.0001.01)
    // Subst z = 2*sqrt(-y) into the above to get
    //
    //  expintegral_si(2*sqrt(-y)) = 2*%f[1,2]([1/2],[3/2,3/2], y)*sqrt(-y)
    //
    // Hence %f[1,2]([1/2],[3/2,3/2], y) = expintegral_si(2*sqrt(-y))/2/sqrt(-y)
    div(
      ftake(q_p_expintegral_si, [
        mul2(Fix(2L), power(neg(arg), hyp__half())),
      ]),
      mul2(Fix(2L), power(neg(arg), hyp__half())),
    )
  } else {
    fpqform(arg_l1, arg_l2, arg)
  }
}

///|
fn simp2f2(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a1 = first(arg_l1)
  let a2 = second(arg_l1)
  let b1 = first(arg_l2)
  let b2 = second(arg_l2)
  if num_eq(a1, Fix(1L)) &&
    num_eq(a2, Fix(1L)) &&
    num_eq(b1, Fix(2L)) &&
    num_eq(b2, Fix(2L)) {
    // Cosine integral
    // expintegral_ci(z) = -z^2/4*%f[2,2]([1,1],[2,2], -z^2/4) + log(z) + %gamma
    // (See http://functions.wolfram.com/06.38.26.0001.01)
    //
    // Hence
    //
    //   %f[2,2]([1,1],[2,2],y) =
    //     (expintegral_ci(2*sqrt(-y)) - log(2*sqrt(-y)) - %gamma)/y
    div(
      sub(
        ftake(q_p_expintegral_ci, [
          mul2(Fix(2L), power(neg(arg), hyp__half())),
        ]),
        add2(
          ftake(q_p_log, [mul2(Fix(2L), power(neg(arg), hyp__half()))]),
          q_d__pctgamma,
        ),
      ),
      arg,
    )
  } else {
    fpqform(arg_l1, arg_l2, arg)
  }
}

///|
fn simp2f1(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a = car(arg_l1)
  let b = cadr(arg_l1)
  let c = car(arg_l2)
  if zerop1(arg).truthy() {
    // F(a,b; c; 0) = 1
    return add2(arg, Fix(1L))
  }
  if hyp__trace() {
    hyp__fmt("Tracing SIMP2F1~%", [])
    hyp__fmt(" Test a or b negative integer ...~%", [])
  }
  // Look if a or b is a symbolic negative integer. The routine 2f1polys
  // handles this case.
  if maxima_integerp(a).truthy() && hyp__sign_negnz(a) {
    return n2f1polys(arg_l1, arg_l2, a, arg)
  }
  if maxima_integerp(b).truthy() && hyp__sign_negnz(b) {
    return n2f1polys(list2(b, a), arg_l2, b, arg)
  }
  if hyp__trace() {
    hyp__fmt(" Test F(1,1,2)...~%", [])
  }
  if alike1(a, Fix(1L)).truthy() &&
    alike1(b, Fix(1L)).truthy() &&
    alike1(c, Fix(2L)).truthy() {
    // F(1,1;2;z) = -log(1-z)/z, A&S 15.1.3
    if hyp__trace() {
      hyp__fmt(" Yes~%", [])
    }
    return mul2(
      inv(mul2(Fix(-1L), arg)),
      take(list1(q_p_log), [add2(Fix(1L), mul2(Fix(-1L), arg))]),
    )
  }
  if hyp__trace() {
    hyp__fmt(" Test c = 1/2 or c = 3/2...~%", [])
  }
  if alike1(c, hyp__rat(3, 2)).truthy() || alike1(c, hyp__rat(1, 2)).truthy() {
    // F(a,b; 3/2; z) or F(a,b;1/2;z)
    let lgf = trig_log(list2(a, b), list1(c), arg)
    if lgf.truthy() {
      if hyp__trace() {
        hyp__fmt(" Yes: trig-log~%", [])
      }
      return lgf
    }
  }
  if hyp__trace() {
    hyp__fmt(" Test |a-b|=1/2...~%", [])
  }
  if alike1(sub(a, b), hyp__rat(1, 2)).truthy() ||
    alike1(sub(b, a), hyp__rat(1, 2)).truthy() {
    // F(a,b;c;z) where |a-b|=1/2
    let lgf = hyp_cos(a, b, c, arg)
    if lgf.truthy() {
      if hyp__trace() {
        hyp__fmt(" Yes: hyp-cos~%", [])
      }
      return lgf
    }
  }
  if hyp__trace() {
    hyp__fmt(" Test a,b are integers, c is a numerical integer...~%", [])
  }
  if maxima_integerp(a).truthy() &&
    maxima_integerp(b).truthy() &&
    hyp_integerp(c).truthy() {
    // F(a,b;c;z) when a, and b are integers (or are declared to be
    // integers) and c is a integral number.
    let lgf = simpr2f1(list2(a, b), list1(c), arg)
    if !symbolp(lgf) {
      // Should be more specific! (DK 01/2010)
      if hyp__trace() {
        hyp__fmt(" Yes: simpr2f1~%", [])
      }
      return lgf
    }
  }
  if hyp__trace() {
    hyp__fmt(" Test a+b and c+1/2 are numerical integers...~%", [])
  }
  if hyp_integerp(add2(c, inv(Fix(2L)))).truthy() &&
    hyp_integerp(add2(a, b)).truthy() {
    // F(a,b;c;z) where a+b is an integer and c+1/2 is an integer.
    if hyp__trace() {
      hyp__fmt(" Yes: step4~%", [])
    }
    return step4(a, b, c, arg)
  }
  if hyp__trace() {
    hyp__fmt(" Test a-b+1/2 is a numerical integer...~%", [])
  }
  if hyp_integerp(add2(sub(a, b), inv(Fix(2L)))).truthy() {
    // F(a,b;c,z) where a-b+1/2 is an integer
    let lgf = step7(a, b, c, arg)
    if lgf.truthy() && !atom(lgf) {
      if hyp__trace() {
        hyp__fmt(" Yes: step7~%", [])
      }
      return lgf
    }
  }
  if hyp_integerp(add2(c, hyp__half())).truthy() {
    if hyp__trace() {
      hyp__fmt(" Test for atanh:  c+1/2 is an integer~%", [])
    }
    if hyp_integerp(add2(a, hyp__half())).truthy() &&
      hyp_integerp(b).truthy() {
      if hyp__trace() {
        hyp__fmt("  atanh with integers a+1/2 and b ~%", [])
      }
      return hyp_atanh(a, b, c, arg)
    } else if hyp_integerp(add2(b, hyp__half())).truthy() &&
      hyp_integerp(a).truthy() {
      if hyp__trace() {
        hyp__fmt("  atanh with integers a and b+1/2 ~%", [])
      }
      return hyp_atanh(b, a, c, arg)
    }
  }
  if hyp__trace() {
    hyp__fmt(" Test for Legendre function...~%", [])
  }
  let lgf = legfun(a, b, c, arg)
  if lgf.truthy() {
    if !atom(lgf) {
      // LEGFUN returned something interesting, so we're done.
      if hyp__trace() {
        hyp__fmt(" Yes: case 1~%", [])
      }
      return lgf
    }
    // LEGFUN didn't return anything, so try it with the args reversed,
    // since F(a,b;c;z) is F(b,a;c;z).
    let lgf = legfun(b, a, c, arg)
    if lgf.truthy() {
      if hyp__trace() {
        hyp__fmt(" Yes: case 2~%", [])
      }
      return lgf
    }
  }
  if hyp__trace() {
    hyp__fmt("'simp2f1-will-continue-in~%", [])
  }
  fpqform(arg_l1, arg_l2, arg)
}

///|
/// A new version of step7.
///
/// To get here, we know that a-b+1/2 is an integer. To make further
/// progress, we want a+b-1/2-c to be an integer too.
///
/// Let a-b+1/2 = p and a+b+1/2-c = q where p and q are (numerical)
/// integers.
///
/// A&S 15.2.3 and 15.2.5 allows us to increase or decrease a. Then
/// F(a,b;c;z) can be written in terms of F(a',b;c;z) where a' = a-p and
/// a'-b = a-p-b = 1/2. Also, a'+b+1/2-c = a-p+b+1/2-c = q-p = r, which is
/// also an integer.
///
/// A&S 15.2.4 and 15.2.6 allows us to increase or decrease c. Thus, we can
/// write F(a',b;c;z) in terms of F(a',b;c',z) where c' = c+r. Now
/// a'-b=1/2 and a'+b+1/2-c' = 0.
///
/// Thus F(a',b;c';z) is exactly the form we want for hyp-cos. In fact,
/// it's A&S 15.1.14: F(a,a+1/2,;1+2a;z) = 2^(2*a)*(1+sqrt(1-z))^(-2*a).
fn step7(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  let q = sub(addn_([a, b, inv(Fix(2L))]), c)
  if !hyp_integerp(q).truthy() {
    // Wrong form, so return NIL
    return Nil
  }
  // Since F(a,b;c;z) = F(b,a;c;z), we need to figure out which form to
  // use. The criterion will be the fewest number of derivatives needed.
  let p1 = add2(sub(a, b), inv(Fix(2L)))
  let r1 = sub(q, p1)
  let p2 = add2(sub(b, a), inv(Fix(2L)))
  let r2 = sub(q, p2)
  if hyp__trace() {
    hyp__fmt("step 7:~%", [])
    hyp__fmt("  q, p1, r1 = ~A ~A ~A~%", [q, p1, r1])
    hyp__fmt("     p2, r2 = ~A ~A~%", [p2, r2])
  }
  if num_le(
      num_add(num_abs(p1), num_abs(r1)),
      num_add(num_abs(p2), num_abs(r2)),
    ) {
    step7_core(a, b, c, arg)
  } else {
    step7_core(b, a, c, arg)
  }
}

///|
fn step7_core(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  let p = add2(sub(a, b), inv(Fix(2L)))
  let q = sub(addn_([a, b, inv(Fix(2L))]), c)
  let r = sub(q, p)
  let a_prime = sub(a, p)
  let c_prime = add2(Fix(1L), mul2(Fix(2L), a_prime))
  // Ok, p and q are integers. We can compute something. There are four
  // cases to handle depending on the sign of p and r.
  //
  // We need to differentiate some hypergeometric forms, so use 'ell as
  // the variable.
  let fun = hyp_cos(a_prime, add2(a_prime, hyp__half()), c_prime, q_ell)
  // fun is F(a',a'+1/2;2*a'+1;z), or NIL
  if fun is Nil {
    return Nil
  }
  if hyp__trace() {
    hyp__fmt("step7-core~%", [])
    hyp__fmt(" a,b,c = ~A ~A ~A~%", [a, b, c])
    hyp__fmt(" p,q,r = ~A ~A ~A~%", [p, q, r])
    hyp__fmt(" a', c' = ~A ~A~%", [a_prime, c_prime])
    hyp__fmt(" F(a',a'+1/2; 1+2*a';z) =~%", [])
    maxima_display(fun) |> ignore
  }
  // Compute the result, and substitute the actual argument into result.
  maxima_substitute(
    arg,
    q_ell,
    if num_ge(p, Fix(0L)) {
      if num_ge(r, Fix(0L)) {
        step_7_pp(a_prime, b, c_prime, p, r, q_ell, fun)
      } else {
        step_7_pm(a_prime, b, c_prime, p, r, q_ell, fun)
      }
    } else if num_ge(r, Fix(0L)) {
      step_7_mp(a_prime, b, c_prime, p, r, q_ell, fun)
    } else {
      step_7_mm(a_prime, b, c_prime, p, r, q_ell, fun)
    },
  )
}

///|
/// F(a,b;c;z) in terms of F(a',b;c';z)
///
/// F(a'+p,b;c'-r;z) where p >= 0, r >= 0.
fn step_7_pp(
  a : Value,
  b : Value,
  c : Value,
  p : Value,
  r : Value,
  z : Value,
  fun : Value,
) -> Value raise {
  // Apply A&S 15.2.4 and 15.2.3
  let res = as_15_dot2_dot4(a, b, c, r, z, fun)
  as_15_dot2_dot3(a, b, sub(c, r), p, z, res)
}

///|
/// p >= 0, r < 0
///
/// Let r' = -r
/// F(a'+p,b;c'-r;z) = F(a'+p,b;c'+r';z)
fn step_7_pm(
  a : Value,
  b : Value,
  c : Value,
  p : Value,
  r : Value,
  z : Value,
  fun : Value,
) -> Value raise {
  // Apply A&S 15.2.6 and 15.2.3
  let res = as_15_dot2_dot6(a, b, c, num_neg(r), z, fun)
  as_15_dot2_dot3(a, b, sub(c, r), p, z, res)
}

///|
/// p < 0, r >= 0
///
/// Let p' = -p
/// F(a'+p,b;c'-r;z) = F(a'-p',b;c'-r;z)
fn step_7_mp(
  a : Value,
  b : Value,
  c : Value,
  p : Value,
  r : Value,
  z : Value,
  fun : Value,
) -> Value raise {
  // Apply A&S 15.2.4 and 15.2.5
  let res = as_15_dot2_dot4(a, b, c, r, z, fun)
  as_15_dot2_dot5(a, b, sub(c, r), num_neg(p), z, res)
}

///|
/// p < 0 r < 0
///
/// Let p' = - p, r' = -r
///
/// F(a'+p,b;c'-r;z) = F(a'-p',b;c'+r';z)
fn step_7_mm(
  a : Value,
  b : Value,
  c : Value,
  p : Value,
  r : Value,
  z : Value,
  fun : Value,
) -> Value raise {
  // Apply A&S 15.2.6 and A&S 15.2.5
  let res = as_15_dot2_dot6(a, b, c, num_neg(r), z, fun)
  as_15_dot2_dot5(a, b, sub(c, r), num_neg(p), z, res)
}

///|
/// F(a,b;c;z) when a and b are integers (or declared to be integers) and
/// c is an integral number.
fn simpr2f1(arg_l1 : Value, arg_l2 : Value, arg : Value) -> Value raise {
  let a = first(arg_l1)
  let b = second(arg_l1)
  let c = first(arg_l2)
  let inl1p = hyp_integerp(a).truthy()
  let inl1bp = hyp_integerp(b).truthy()
  let inl2p = hyp_integerp(c).truthy()
  if inl2p {
    // c is an integer
    if inl1p && inl1bp {
      // a, b, c are (numerical) integers
      derivint(a, b, c, arg)
    } else if inl1p {
      // a and c are integers
      geredno2(b, a, c, arg)
    } else if inl1bp {
      // b and c are integers.
      geredno2(a, b, c, arg)
    } else {
      q_fail1
    }
  } else if inl1p {
    // Can't really do anything else if c is not an integer.
    if inl1bp {
      q_d
    } else {
      q_c
    }
  } else if eq(caaar(arg_l1), q_rat) {
    // How do we ever get here?
    if inl1bp {
      q_c
    } else {
      q_d
    }
  } else {
    q_failg
  }
}

///|
fn geredno2(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  if num_gt(c, b) {
    geredf(b, a, c, arg)
  } else {
    gered2(a, b, c, arg)
  }
}

///|
/// Consider F(1,1;2;z). A&S 15.1.3 says this is equal to -log(1-z)/z.
/// Using A&S 15.2.2, 15.2.7 and 15.2.6, F(a,b;c;z), where a, b, and c are
/// integers and a <= b <= c, can be written in terms of F(1,1;2;z).
///
/// If a = 1+ell, b = 1+ell+m, and c = 2+ell+m+n, we have ell = a-1,
/// m = b - a, and n = c - ell - m - 2 = c - b - 1.
fn derivint(a : Value, b : Value, c : Value, arg : Value) -> Value raise {
  if num_gt(a, b) {
    return derivint(b, a, c, arg)
  }
  let l = num_sub(a, Fix(1L))
  let m = num_sub(b, a)
  let n = num_sub(num_sub(c, b), Fix(1L))
  let psey = gensym()
  let result = muln_([
    power(Fix(-1L), m),
    factorial(num_sum([n, m, l, Fix(1L)])),
    inv(factorial(n)),
    inv(factorial(l)),
    inv(factorial(num_add(n, m))),
    inv(factorial(num_add(m, l))),
    power(sub(Fix(1L), psey), sub(n, l)),
    hyp__diff(
      mul2(
        power(sub(Fix(1L), psey), num_add(m, l)),
        hyp__diff(
          muln_([
            power(psey, Fix(-1L)),
            Fix(-1L),
            take(list1(q_p_log), [sub(Fix(1L), psey)]),
          ]),
          psey,
          l,
        ),
      ),
      psey,
      num_add(n, m),
    ),
  ])
  if onep1(arg).truthy() {
    d_limit(list([result, psey, arg]))
  } else {
    maxima_substitute(arg, psey, result)
  }
}

///|
/// Handle F(a, b; c; z) for certain values of a, b, and c.
fn hyp_cos(a : Value, b : Value, c : Value, z : Value) -> Value raise {
  let a1 = div(sub(add2(a, b), div(Fix(1L), Fix(2L))), Fix(2L))
  let z1 = sub(Fix(1L), z)
  // a1 = (a+b-1/2)/2
  // z1 = 1-z
  if eql(
      Fix(0L),
      d_ratsimp(sub(sub(add2(a, b), div(Fix(1L), Fix(2L))), c), Nil),
    ) {
    // a+b-1/2 = c
    //
    // A&S 15.1.14
    //
    // F(a,a+1/2;2*a;z)
    //    = 2^(2*a-1)*(1-z)^(-1/2)*(1+sqrt(1-z))^(1-2*a)
    //
    // But if 1-2*a is a negative integer, let's rationalize the answer
    // to give
    //
    // F(a,a+1/2;2*a;z)
    //   = 2^(2*a-1)*(1-z)^(-1/2)*(1-sqrt(1-z))^(2*a-1)/z^(2*a-1)
    if hyp__trace() {
      hyp__fmt("   Case a+b-1/2=c~%", [])
    }
    let n2a_1 = sub(mul2(a1, Fix(2L)), Fix(1L))
    if integerp(n2a_1) && plusp(n2a_1) {
      // 2^(2*a-1)*(1-z)^(-1/2)*(1-sqrt(1-z))^(2*a-1)/z^(2*a-1)
      muln_([
        power(Fix(2L), n2a_1),
        inv(power(z1, hyp__half())),
        power(sub(Fix(1L), power(z1, hyp__half())), n2a_1),
        inv(power(z, n2a_1)),
      ])
    } else {
      // 2^(2*a-1)*(1-z)^(-1/2)*(1+sqrt(1-z))^(1-2*a)
      muln_([
        power(Fix(2L), sub(mul2(a1, Fix(2L)), Fix(1L))),
        inv(power(z1, div(Fix(1L), Fix(2L)))),
        power(
          add2(Fix(1L), power(z1, div(Fix(1L), Fix(2L)))),
          sub(Fix(1L), mul2(Fix(2L), a1)),
        ),
      ])
    }
  } else if eql(
      Fix(0L),
      d_ratsimp(sub(add2(Fix(1L), mul2(Fix(2L), a1)), c), Nil),
    ) {
    // c = 1+2*a1 = a+b+1/2
    //
    // A&S 15.1.13:
    //
    // F(a,1/2+a;1+2*a;z) = 2^(2*a)*(1+sqrt(1-z))^(-2*a)
    //
    // But if 2*a is a positive integer, let's rationalize the answer to
    // give
    //
    // F(a,1/2+a;1+2*a;z) = 2^(2*a)*(1-sqrt(1-z))^(2*a)/z^(2*a)
    if hyp__trace() {
      hyp__fmt("   Case c=1+2*a=a+b+1/2~%", [])
    }
    let n2a = sub(c, Fix(1L))
    if integerp(n2a) && plusp(n2a) {
      // 2^(2*a)*(1-sqrt(1-z))^(2*a)/z^(2*a)
      muln_([
        power(Fix(2L), n2a),
        power(sub(Fix(1L), power(z1, hyp__half())), n2a),
        power(z, mul2(Fix(-1L), n2a)),
      ])
    } else {
      // 2^(2*a)*(1+sqrt(1-z))^(-2*a)
      mul2(
        power(Fix(2L), n2a),
        power(add2(Fix(1L), power(z1, hyp__half())), mul2(Fix(-1L), n2a)),
      )
    }
  } else {
    Nil
  }
}

///|
/// Is A a non-negative integer?
fn nni(a : Value) -> Value raise {
  if hyp_integerp(a).truthy() {
    lbool(!minusp(a))
  } else {
    Nil
  }
}
