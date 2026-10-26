// Port of src/combin.lisp (part 2): continued fractions, summation,
// products, deftaylor, polydecomp.

// ---------------------------------------------------------------------------
// continued fraction stuff

///|
fn d_cfdisrep(a : Value) -> Value raise {
  if !d_listp(a).truthy() {
    merr("cfdisrep: argument must be a list; found ~M", [a])
  } else if cddr(a) is Nil {
    cadr(a)
  } else if equal(cadr(a), int(0)) {
    list3(list1(q_mexpt), cfdisrep1(cddr(a)), int(-1))
  } else {
    cfdisrep1(cdr(a))
  }
}

///|
fn cfdisrep1(a : Value) -> Value raise {
  if cdr(a).truthy() {
    let first_ = car(a)
    let a = cfdisrep1(cdr(a))
    list3(
      list3(q_mplus, q_simp, q_cf),
      first_,
      if integerp(a) {
        list3(list2(q_rat, q_simp), int(1), a)
      } else {
        list3(list2(q_mexpt, q_simp), a, int(-1))
      },
    )
  } else {
    car(a)
  }
}

///|
fn cfmak(a : Value) -> Value raise {
  let a = meval(a)
  if integerp(a) {
    list1(a)
  } else if eq(caar(a), q_mlist) {
    cdr(a)
  } else if eq(caar(a), q_rat) {
    ratcf(cadr(a), caddr(a))
  } else {
    merr("cf: continued fractions must be lists or integers; found ~M", [a])
  }
}

///|
fn makcf(a : Value) -> Value raise {
  if cdr(a) is Nil {
    car(a)
  } else {
    cons(list3(q_mlist, q_simp, q_cf), a)
  }
}

///|
fn d_cf(a : Value) -> Value raise {
  cfratsimp(
    with_special(q_d_listarith, Nil, () => cfeval(meval(fexprcheck(a)))),
  )
}

///|
/// Definition of cfratsimp as given in SF bug report # 620928.
fn cfratsimp(a : Value) -> Value raise {
  if atom(a) {
    a
  } else if memq(q_cf, car(a)).truthy() {
    a
  } else {
    let pq = cf_back_recurrence(cdr(a))
    cons(list3(q_mlist, q_cf, q_simp), find_cf(car(pq), cadr(pq)))
  }
}

///|
/// Expand nth degree roots of integers into continued fraction
/// approximations. E.g. cf(2^(1/3))
fn cfnroot(b : Value) -> Value raise {
  with_special(q_d_algebraic, q_d_true, () => {
    let mut b = b
    let mut ans = list1(list2(q_mlist, q_xf))
    let n = to_int(symval(q_d_cflength))
    for _i in 0..<n {
      let ent = meval(list2(list1(q_d_floor), b))
      ans = cons(ent, ans)
      b = d_ratsimp(m_sl_sl(m_(b, a2=ent)), Nil)
    }
    nreverse(ans)
  })
}

///|
fn cfeval(a : Value) -> Value raise {
  with_special(q_d_ratprint, Nil, () => {
    if integerp(a) {
      list2(list2(q_mlist, q_cf), a)
    } else if floatp(a) {
      let a = maxima_rationalize(a)
      cons(list2(q_mlist, q_cf), ratcf(car(a), cdr(a)))
    } else if d_bfloatp(a).truthy() {
      with_special(q_d_bftorat, t, () => {
        let a = bigfloat2rat(a)
        cons(list2(q_mlist, q_cf), ratcf(car(a), cdr(a)))
      })
    } else if atom(a) {
      merr("cf: ~:M is not a continued fraction.", [a])
    } else if eq(caar(a), q_rat) {
      cons(list2(q_mlist, q_cf), ratcf(cadr(a), caddr(a)))
    } else if eq(caar(a), q_mlist) {
      cfratsimp(a)
    } else if mtimesp(a).truthy() &&
      cddr(a).truthy() &&
      cdddr(a) is Nil &&
      fixnump(cadr(a)) &&
      mexptp(caddr(a)).truthy() &&
      fixnump(cadr(caddr(a))) &&
      alike1(caddr(caddr(a)), mk(q_rat, [int(1), int(2)])).truthy() {
      cfsqrt(cfeval(num_mul(expt(cadr(a), int(2)), cadr(caddr(a)))))
    } else if eq(caar(a), q_mexpt) &&
      integerp(caddr(a)) &&
      num_gt(caddr(a), int(0)) {
      // case when a continuous fraction is raised to an integer power
      cfexpt(cadr(a), caddr(a))
    } else if eq(caar(a), q_mexpt) {
      if alike1(caddr(a), mk(q_rat, [int(1), int(2)])).truthy() {
        cfsqrt(cfeval(cadr(a))) // square root of an integer
      } else if alike1(caddr(a), mk(q_rat, [int(-1), int(2)])).truthy() {
        cfquot(int(1), cfsqrt(cfeval(cadr(a)))) // inverse square root
      } else if integerp(m_star(list2(int(2), caddr(a)))) {
        // a^(n/2) was sqrt(a^n)
        cfsqrt(cfeval(cfexpt(cadr(a), m_star(list2(int(2), caddr(a))))))
      } else if integerp(cadr(a)) {
        cfnroot(a)
      } else {
        cfexpt(cfeval(cadr(a)), caddr(a))
      }
    } else {
      let op = caar(a)
      let fun = if eq(op, q_mplus) {
        q_cfplus
      } else if eq(op, q_mtimes) {
        q_cftimes
      } else if eq(op, q_mquotient) {
        q_cfquot
      } else if eq(op, q_mdifference) {
        q_cfdiff
      } else if eq(op, q_mminus) {
        q_cfminus
      } else {
        Nil
      }
      if fun.truthy() {
        cf(cfeval(cadr(a)), cddr(a), fun)
      } else if eq(caar(a), q_mrat) {
        cfeval(d_ratdisrep(a))
      } else {
        merr("cf: ~:M is not a continued fraction.", [a])
      }
    }
  })
}

///|
fn cf(a : Value, l : Value, fun : Value) -> Value raise {
  if l is Nil {
    a
  } else {
    cf(funcall(fun, [a, meval(list2(list1(q_d_cf), car(l)))]), cdr(l), fun)
  }
}

///|
fn cfplus(a : Value, b : Value) -> Value raise {
  let a = cfmak(a)
  let b = cfmak(b)
  makcf(cffun(combin__nums([0, 1, 1, 0]), combin__nums([0, 0, 0, 1]), a, b))
}

///|
fn cftimes(a : Value, b : Value) -> Value raise {
  let a = cfmak(a)
  let b = cfmak(b)
  makcf(cffun(combin__nums([1, 0, 0, 0]), combin__nums([0, 0, 0, 1]), a, b))
}

///|
fn cfdiff(a : Value, b : Value) -> Value raise {
  let a = cfmak(a)
  let b = cfmak(b)
  makcf(cffun(combin__nums([0, 1, -1, 0]), combin__nums([0, 0, 0, 1]), a, b))
}

///|
fn cfmin(a : Value) -> Value raise {
  let a = cfmak(a)
  makcf(
    cffun(
      combin__nums([0, 0, -1, 0]),
      combin__nums([0, 0, 0, 1]),
      a,
      combin__nums([0]),
    ),
  )
}

///|
fn cfquot(a : Value, b : Value) -> Value raise {
  let a = cfmak(a)
  let b = cfmak(b)
  makcf(cffun(combin__nums([0, 1, 0, 0]), combin__nums([0, 0, 1, 0]), a, b))
}

///|
fn cfexpt(b : Value, e : Value) -> Value raise {
  let mut b = cfmak(b)
  if !integerp(e) {
    return merr(
      "cf: can't raise continued fraction to non-integral power ~M",
      [e],
    )
  }
  let n0 = num_abs(e)
  let mut n = ash(n0, -1)
  let mut s = if oddp(n0) { b } else { combin__nums([1]) }
  while !zerop(n) {
    b = cffun(combin__nums([1, 0, 0, 0]), combin__nums([0, 0, 0, 1]), b, b)
    if oddp(n) {
      s = cffun(combin__nums([1, 0, 0, 0]), combin__nums([0, 0, 0, 1]), s, b)
    }
    n = ash(n, -1)
  }
  makcf(
    if numberp(e) && plusp(e) {
      s
    } else {
      cffun(
        combin__nums([0, 0, 0, 1]),
        combin__nums([0, 1, 0, 0]),
        b,
        combin__nums([1]),
      )
    },
  )
}

///|
fn conf1(f : Value, g : Value, a : Value, b : Value) -> Value raise {
  let den = conf2(g, a, b)
  if zerop(den) {
    num_mul(signum(conf2(f, a, b)), expt(int(2), int(31)))
  } else {
    num_truncate(conf2(f, a, b), b=den).0
  }
}

///|
/// 2*(abn_0+an_1+bn_2+n_3)
fn conf2(n : Value, a : Value, b : Value) -> Value raise {
  num_mul(
    int(2),
    num_sum([
      num_mul(num_mul(car(n), a), b),
      num_mul(cadr(n), a),
      num_mul(caddr(n), b),
      cadddr(n),
    ]),
  )
}

///|
/// Returns two lists such that pp_i/qq_i is the quotient of the first i
/// terms of cf.
fn cf_convergents_p_q(cf : Value, n? : Value) -> Value raise {
  let n = match n {
    Some(v) => v
    None => int(length(cf))
  }
  let mut cf = cf
  match length(cf) {
    0 => int(1)
    1 => list1(int(1))
    _ => {
      let mut pp = list2(num_add(num_mul(first(cf), second(cf)), int(1)), car(cf))
      let mut qq = list2(second(cf), int(1))
      format(t, "~%The value of ~A is ~A", [sym("pp"), pp]) |> ignore
      format(t, "~%The value of ~A is ~A", [sym("qq"), qq]) |> ignore
      cf = cddr(cf)
      let mut i = int(2)
      while num_le(i, n) && cf.truthy() {
        pp = cons(num_add(num_mul(car(cf), car(pp)), second(pp)), pp)
        qq = cons(num_add(num_mul(car(cf), car(qq)), second(qq)), qq)
        cf = cdr(cf)
        i = num_add(i, int(1))
      }
      list2(reverse(pp), reverse(qq))
    }
  }
}

///|
fn find_cf1(p : Value, q : Value, so_far : Value) -> Value raise {
  let mut p = p
  let mut q = q
  let mut so_far = so_far
  while true {
    let (quot0, rem0) = num_truncate(p, b=q)
    let mut quot = quot0
    let mut rem = rem0
    if minusp(rem) {
      rem = num_add(rem, q)
      quot = num_add(quot, int(-1))
    } else if zerop(rem) {
      return cons(quot, so_far)
    }
    so_far = cons(quot, so_far)
    p = q
    q = rem
  }
  so_far
}

///|
/// Returns the continued fraction for p and q integers, q not zero.
fn find_cf(p : Value, q : Value) -> Value raise {
  let mut p = p
  let mut q = q
  if zerop(q) {
    maxima_error(Str("find-cf: quotient by zero"), Nil) |> ignore
  } else if minusp(q) {
    p = num_neg(p)
    q = num_neg(q)
  }
  nreverse(find_cf1(p, q, Nil))
}

///|
/// Converts CF (a continued fraction list) to a list of numerator
/// denominator using recurrence from end.
fn cf_back_recurrence(cf : Value) -> Value raise {
  let mut num_gg = int(0)
  let mut den_gg = int(1)
  for v in reverse(cf).iter() {
    let mut tem = num_mul(den_gg, v)
    tem = num_add(tem, num_gg)
    num_gg = den_gg
    den_gg = tem
  }
  if num_le(den_gg, int(0)) && minusp(num_gg) {
    list2(num_neg(den_gg), num_neg(num_gg))
  } else {
    list2(den_gg, num_gg)
  }
}

///|
fn cffun(f : Value, g : Value, a : Value, b : Value) -> Value raise {
  let mut f = f
  let mut g = g
  let mut a = a
  let mut b = b
  let mut c : Value = Nil
  while true {
    if zerop(cadddr(g)) && zerop(caddr(g)) && zerop(cadr(g)) && zerop(car(g)) {
      return reverse(c)
    }
    let w = conf1(f, g, car(a), one_plus(car(b)))
    let mut v = conf1(f, g, car(a), car(b))
    if equal(w, v) &&
      equal(conf1(f, g, one_plus(car(a)), car(b)), v) &&
      equal(conf1(f, g, one_plus(car(a)), one_plus(car(b))), v) {
      let old_f = f
      f = g
      let vv = v
      g = mapcar2((x, y) => num_sub(x, num_mul(vv, y)), old_f, g)
      c = cons(v, c)
      continue
    }
    if num_lt(
        num_abs(num_sub(conf1(f, g, one_plus(car(a)), car(b)), v)),
        num_abs(num_sub(w, v)),
      ) {
      v = cdr(b)
      if v.truthy() {
        f = conf6(f, b)
        g = conf6(g, b)
        b = v
      } else {
        f = conf7(f, b)
        g = conf7(g, b)
      }
    } else {
      v = cdr(a)
      if v.truthy() {
        f = conf4(f, a)
        g = conf4(g, a)
        a = v
      } else {
        f = conf5(f, a)
        g = conf5(g, a)
      }
    }
  }
  Nil
}

///|
/// n_0*a_0+n_2,n_1*a_0+n_3,n_0,n_1
fn conf4(n : Value, a : Value) -> Value raise {
  list4(
    num_add(num_mul(car(n), car(a)), caddr(n)),
    num_add(num_mul(cadr(n), car(a)), cadddr(n)),
    car(n),
    cadr(n),
  )
}

///|
/// 0,0, n_0*a_0,n_2
fn conf5(n : Value, a : Value) -> Value raise {
  list4(
    int(0),
    int(0),
    num_add(num_mul(car(n), car(a)), caddr(n)),
    num_add(num_mul(cadr(n), car(a)), cadddr(n)),
  )
}

///|
fn conf6(n : Value, b : Value) -> Value raise {
  list4(
    num_add(num_mul(car(n), car(b)), cadr(n)),
    car(n),
    num_add(num_mul(caddr(n), car(b)), cadddr(n)),
    caddr(n),
  )
}

///|
fn conf7(n : Value, b : Value) -> Value raise {
  list4(
    int(0),
    num_add(num_mul(car(n), car(b)), cadr(n)),
    int(0),
    num_add(num_mul(caddr(n), car(b)), cadddr(n)),
  )
}

///|
fn cfsqrt(n : Value) -> Value raise {
  let mut n = n
  if cddr(n).truthy() {
    // A non integer
    merr("cf: argument of sqrt must be an integer; found ~M", [n]) |> ignore
  } else {
    n = cadr(n)
  }
  n = sqcont(n)
  if num_eq(symval(q_d_cflength), int(1)) {
    cons(list2(q_mlist, q_simp), n)
  } else {
    let mut i = int(2)
    let a = copy_tree(cdr(n))
    while !num_gt(i, symval(q_d_cflength)) {
      n = nconc(n, copy_tree(a))
      i = num_add(i, int(1))
    }
    cons(list2(q_mlist, q_simp), n)
  }
}

///|
fn d_qunit(n : Value) -> Value raise {
  let isqrtn = d_isqrt(n)
  if !integerp(n) || minusp(n) || num_eq(num_mul(isqrtn, isqrtn), n) {
    merr("qunit: Argument must be a positive non quadratic integer.", [])
    |> ignore
  }
  let l = sqcont(n)
  list3(
    list1(q_mplus),
    pelso1(l, int(0), int(1)),
    list3(
      list1(q_mtimes),
      list3(list1(q_mexpt), n, mk(q_rat, [int(1), int(2)])),
      pelso1(l, int(1), int(0)),
    ),
  )
}

///|
fn pelso1(l : Value, a : Value, b : Value) -> Value raise {
  let mut a = a
  let mut b = b
  let mut i = l
  while true {
    if cdr(i) is Nil {
      return b
    }
    let old_a = a
    a = b
    b = num_add(old_a, num_mul(car(i), b))
    i = cdr(i)
  }
  b
}

///|
fn sqcont(n : Value) -> Value raise {
  let a0 = d_isqrt(n)
  let mut a = list1(a0)
  let mut q2 = int(1)
  let mut m1 = a0
  let mut q1 = num_sub(n, num_mul(m1, m1))
  let l = num_mul(int(2), a0)
  while true {
    a = cons(num_truncate(num_add(m1, a0), b=q1).0, a)
    if equal(car(a), l) {
      return nreverse(a)
    }
    let m = num_sub(num_mul(car(a), q1), m1)
    let q = num_add(q2, num_mul(car(a), num_sub(m1, m)))
    q2 = q1
    q1 = q
    m1 = m
  }
  Nil
}

///|
fn ratcf(x : Value, y : Value) -> Value raise {
  let mut x = x
  let mut y = y
  let mut a : Value = Nil
  while true {
    if equal(y, int(1)) {
      return nreverse(cons(x, a))
    } else if minusp(x) {
      let b = num_add(y, num_rem(x, y))
      a = cons(num_sub(num_truncate(x, b=y).0, int(1)), a)
      x = y
      y = b
    } else if num_gt(y, x) {
      a = cons(int(0), a)
      let b = x
      x = y
      y = b
    } else if equal(x, y) {
      return nreverse(cons(int(1), a))
    } else {
      let b = num_rem(x, y)
      a = cons(num_truncate(x, b=y).0, a)
      x = y
      y = b
    }
  }
  Nil
}

///|
fn d_cfexpand(x : Value) -> Value raise {
  if !d_listp(x).truthy() {
    x
  } else {
    cons(list1(q_d_matrix), cfexpand(cdr(x)))
  }
}

///|
fn cfexpand(ll : Value) -> Value raise {
  let mut p1 = int(0)
  let mut p2 = int(1)
  let mut q1 = int(1)
  let mut q2 = int(0)
  let mut l = ll
  while !(l is Nil) {
    let np2 = simplify(
      list3(list1(q_mplus), list3(list1(q_mtimes), car(l), p2), p1),
    )
    let nq2 = simplify(
      list3(list1(q_mplus), list3(list1(q_mtimes), car(l), q2), q1),
    )
    p1 = p2
    p2 = np2
    q1 = q2
    q2 = nq2
    l = cdr(l)
  }
  list2(list3(list1(q_mlist), p2, p1), list3(list1(q_mlist), q2, q1))
}

// ---------------------------------------------------------------------------
// Summation stuff

///|
fn simpsum2(exp_ : Value, i : Value, lo : Value, hi : Value) -> Value raise {
  with_special(q_d_simpsum, Nil, () => {
    let mut exp_ = exp_
    let mut lo = lo
    let mut plus = list1(int(0))
    let times = int(1)
    if (eq(hi, q_d_inf) && eq(lo, q_d_minf)) ||
      equal(int(0), m_plus(list2(hi, lo))) {
      set(q_d_simpsum, t) |> ignore
      lo = int(0)
      plus = cons(
        m_star(list3(int(-1), times, maxima_substitute(int(0), i, exp_))),
        plus,
      )
      exp_ = m_plus(list2(exp_, maxima_substitute(m_(i), i, exp_)))
    }
    let u = m_(hi, a2=lo)
    if eq(d_sign(u), q_d_neg) {
      if equal(u, int(-1)) {
        return int(0)
      } else {
        return merr("sum: lower bound ~M greater than upper bound ~M", [lo, hi])
      }
    } else if free(exp_, i).truthy() {
      return m_plusl(cons(freesum(exp_, lo, hi, times), plus))
    } else {
      let (e2, p2) = sumsum_mv(exp_, i, lo, hi, plus, times)
      exp_ = e2
      plus = p2
      if exp_.truthy() {
        exp_ = m_star(
          list2(
            times,
            dosum(
              cadr(exp_),
              caddr(exp_),
              cadddr(exp_),
              cadr(cdddr(exp_)),
              t,
              evaluate_summand=Nil,
            ),
          ),
        )
      } else {
        return m_plusl(plus)
      }
    }
    m_plusl(cons(exp_, plus))
  })
}

///|
/// The closure variables COMBIN-SUM and COMBIN-USUM shared by ADSUM,
/// ADUSUM, FPOLYSUM, FBINO, ISUM and SUMSUM.
let combin__sum : Ref[Value] = { val: Nil }

///|
let combin__usum : Ref[Value] = { val: Nil }

///|
fn adsum(e : Value) -> Value raise {
  combin__sum.val = cons(simplify(e), combin__sum.val)
  combin__sum.val
}

///|
fn adusum(e : Value) -> Value raise {
  combin__usum.val = cons(simplify(e), combin__usum.val)
  combin__usum.val
}

///|
/// Sums of polynomials using
///   bernpoly(x+1, n) - bernpoly(x, n) = n*x^(n-1)
/// which implies
///   sum(k^n, k, A, B) = 1/(n+1)*(bernpoly(B+1, n+1) - bernpoly(A, n+1))
fn fpolysum(e : Value, lo : Value, hi : Value, poly_var : Value) -> Value raise {
  let e = d_expand(d_ratdisrep(d_rat(e, list1(poly_var))))
  let a = combin__fpoly1(e, lo, poly_var)
  with_special(q_d_prederror, Nil, () => if a is Nil {
    int(0)
  } else if eql(lo, int(0)) || eql(lo, int(1)) {
    maxima_substitute(hi, q_foo, a)
  } else {
    list3(
      list1(q_mplus),
      maxima_substitute(hi, q_foo, a),
      list3(
        list1(q_mtimes),
        int(-1),
        maxima_substitute(list3(list1(q_mplus), lo, int(-1)), q_foo, a),
      ),
    )
  })
}

///|
fn combin__fpoly1(e : Value, lo : Value, poly_var : Value) -> Value raise {
  if smono(e, poly_var).truthy() {
    combin__fpoly2(symval(q_n_stara), symval(q_n_starn), e, lo)
  } else if eq(caar(e), q_mplus) {
    cons(list1(q_mplus), mapcar(x => combin__fpoly1(x, lo, poly_var), cdr(e)))
  } else {
    adusum(e) |> ignore
    int(0)
  }
}

///|
fn combin__fpoly2(a : Value, n : Value, e : Value, lo : Value) -> Value raise {
  if !(integerp(n) && num_gt(n, int(-1))) {
    adusum(e) |> ignore
    int(0)
  } else if equal(n, int(0)) {
    m_star(
      list2(
        if numberp(lo) && zerop(lo) {
          m1_plus(q_foo)
        } else {
          q_foo
        },
        a,
      ),
    )
  } else {
    d_ratsimp(
      m_star(
        list3(
          a,
          list3(list1(q_rat), int(1), one_plus(n)),
          m_(
            d_bernpoly(m_plus(list2(q_foo, int(1))), one_plus(n)),
            a2=ftake(q_p_bern, [one_plus(n)]),
          ),
        ),
      ),
      Nil,
    )
  }
}

///|
/// fbino can do these sums:
///  a) sum(binomial(n,k),k,0,n) -> 2^n
///  b) sum(binomial(n-k,k,k,0,n) -> fib(n+1)
///  c) sum(binomial(n,2k),k,0,n) -> 2^(n-1)
///  d) sum(binomial(a+k,b),k,l,h) -> binomial(h+a+1,b+1) - binomial(l+a,b+1)
fn fbino(e : Value, y : Value, lo : Value, hi : Value, poly_var : Value) -> Value raise {
  // check that n and d are linear in poly-var
  let mut n = m2(cadr(e), list3(q_n, q_linear_star, poly_var))
  if n is Nil {
    return adusum(e)
  }
  n = cdr(assq(q_n, n))
  let mut d = m2(caddr(e), list3(q_d, q_linear_star, poly_var))
  if d is Nil {
    return adusum(e)
  }
  d = cdr(assq(q_d, d))
  // binomial(a+b*k,c+b*k) -> binomial(a+b*k, a-c)
  if equal(cdr(n), cdr(d)) {
    d = cons(m_(car(n), a2=car(d)), int(0))
  }
  let mut l = lo
  let mut h = hi
  if numberp(cdr(d)) &&
    (
      minusp(cdr(d)) ||
      (zerop(cdr(d)) && numberp(cdr(n)) && minusp(cdr(n)))
    ) {
    // substitute k with -k in sum(binomial(a+b*k, c-d*k)) and
    // sum(binomial(a-b*k,c))
    rplacd(d, num_neg(cdr(d))) |> ignore
    rplacd(n, num_neg(cdr(n))) |> ignore
    l = m_(hi)
    h = m_(lo)
  }
  let binom = fn(a : Value, b : Value) -> Value {
    list3(list1(q_p_binomial), a, b)
  }
  let zero_or = fn(x : Value, other : Value) -> Bool {
    eq(x, q_d_zero) || eq(x, other)
  }
  if equal(int(0), cdr(d)) && equal(int(1), cdr(n)) {
    // sum(binomial(a+k,c),k,l,h)
    adsum(
      m_star(
        list2(
          y,
          m_(
            binom(m_plus(list3(h, car(n), int(1))), m_plus(list2(car(d), int(1)))),
            a2=binom(m_plus(list2(l, car(n))), m_plus(list2(car(d), int(1)))),
          ),
        ),
      ),
    )
  } else if equal(int(1), cdr(d)) && equal(int(0), cdr(n)) {
    // sum(binomial(n,k),k,0,n)=2^n
    // sum(binomial(n,k+c),k,l,h)=sum(binomial(n,k+c+l),k,0,h-l)
    let h1 = m_(h, a2=l)
    let c = m_plus(list2(car(d), l))
    if integerp(m_(car(n), a2=h1)) && integerp(c) {
      adsum(m_star(list2(y, m_hat(int(2), car(n))))) |> ignore
      if zero_or(asksign(m_(m_plus(list2(h1, c)), a2=car(n))), q_d_negative) {
        adsum(
          m_star(
            list3(
              int(-1),
              y,
              dosum(
                binom(car(n), poly_var),
                poly_var,
                m_plus(list3(h1, c, int(1))),
                car(n),
                t,
                evaluate_summand=Nil,
              ),
            ),
          ),
        )
        |> ignore
      }
      if num_gt(c, int(0)) {
        adsum(
          m_star(
            list3(
              int(-1),
              y,
              dosum(
                binom(car(n), poly_var),
                poly_var,
                int(0),
                m_(c, a2=int(1)),
                t,
                evaluate_summand=Nil,
              ),
            ),
          ),
        )
      } else {
        Nil
      }
    } else {
      adusum(e)
    }
  } else if equal(int(-1), cdr(n)) && equal(int(1), cdr(d)) {
    // sum(binomial(b-k,k),k,0,floor(b/2))=fib(b+1)
    // sum(binomial(a-k,b+k),k,l,h)=sum(binomial(a+b-k,k),k,l+b,h+b)
    let h1 = m_plus(list2(h, car(d)))
    let l1 = m_plus(list2(l, car(d)))
    let a1 = m_plus(list2(car(n), car(d)))
    // sum(binomial(a1-k,k),k,0,floor(a1/2))=fib(a1+1)
    // we only do sums with h>floor(a1/2)
    if integerp(l1) &&
      zero_or(asksign(m_(h1, a2=m_sl_sl(a1, a2=int(2)))), q_d_positive) {
      adsum(m_star(list2(y, d_fib(m_plus(list2(a1, int(1))))))) |> ignore
      if num_gt(l1, int(0)) {
        adsum(
          m_star(
            list3(
              int(-1),
              y,
              dosum(
                binom(m_(a1, a2=poly_var), poly_var),
                poly_var,
                int(0),
                m_(l1, a2=int(1)),
                t,
                evaluate_summand=Nil,
              ),
            ),
          ),
        )
      } else {
        Nil
      }
    } else {
      adusum(e)
    }
  } else if equal(int(0), cdr(n)) && equal(int(2), cdr(d)) && integerp(car(d)) {
    // sum(binomial(n,2*k),k,0,floor(n/2))=2^(n-1)
    // sum(binomial(n,2*k+1),k,0,floor((n-1)/2))=2^(n-1)
    let a = car(n)
    let r1 = if oddp(car(d)) { int(1) } else { int(0) }
    let l1 = if oddp(car(d)) {
      m_plus(list2(l, num_truncate(num_sub(car(d), int(1)), b=int(2)).0))
    } else {
      m_plus(list2(l, num_truncate(car(d), b=int(2)).0))
    }
    // we only do sums with 2*h+b >= a
    if integerp(l1) &&
      zero_or(asksign(m_(m_plus(list3(h, h, car(d))), a2=a)), q_d_positive) {
      adsum(m_star(list2(y, m_hat(int(2), m_(a, a2=int(1)))))) |> ignore
      if num_gt(l1, int(0)) {
        adsum(
          m_star(
            list3(
              int(-1),
              y,
              dosum(
                binom(a, m_plus(list3(poly_var, poly_var, r1))),
                poly_var,
                int(0),
                m_(l1, a2=int(1)),
                t,
                evaluate_summand=Nil,
              ),
            ),
          ),
        )
      } else {
        Nil
      }
    } else {
      adusum(e)
    }
  } else {
    // other sums we can't do
    adusum(e)
  }
}

///|
fn isum(e : Value, lo : Value, poly_var : Value) -> Value raise {
  if combin__isum_giveup(e, poly_var).truthy() {
    combin__sum.val = Nil
    combin__usum.val = list1(e)
    combin__usum.val
  } else {
    let r = catch_tag(q_isumout, () => combin__isum1(e, lo, poly_var))
    if eq(r, q_divergent) {
      merr("sum: sum is divergent.", [])
    } else {
      Nil
    }
  }
}

///|
fn combin__isum_giveup(e : Value, poly_var : Value) -> Value raise {
  if atom(e) {
    Nil
  } else if eq(caar(e), q_mexpt) {
    lbool(
      !(free(cadr(e), poly_var).truthy() || ratp(caddr(e), poly_var).truthy()),
    )
  } else if eq(caar(e), q_mplus) || eq(caar(e), q_mtimes) {
    let l = mapcar(x => combin__isum_giveup(x, poly_var), cdr(e))
    lbool(some(x => x.truthy(), l))
  } else {
    t
  }
}

///|
fn combin__isum1(e : Value, lo : Value, poly_var : Value) -> Value raise {
  if free(e, poly_var).truthy() {
    if !eq(asksign(e), q_d_zero) {
      throw_tag(q_isumout, q_divergent)
    } else {
      Nil
    }
  } else if ratp(e, poly_var).truthy() {
    adsum(combin__ipoly1(d_expand(e), lo, poly_var))
  } else if eq(caar(e), q_mplus) {
    mapc(x => combin__isum1(x, lo, poly_var) |> ignore, cdr(e))
  } else {
    let g = combin__isgeo(e, lo, poly_var)
    if g.truthy() {
      g
    } else {
      adusum(e)
    }
  }
}

///|
fn combin__ipoly1(e : Value, lo : Value, poly_var : Value) -> Value raise {
  if smono(e, poly_var).truthy() {
    let a = symval(q_n_stara)
    let n = symval(q_n_starn)
    combin__ipoly2(
      a,
      n,
      lo,
      asksign(simplify(list3(list1(q_mplus), symval(q_n_starn), int(1)))),
      poly_var,
    )
  } else if mplusp(e).truthy() {
    cons(list1(q_mplus), mapcar(x => combin__ipoly1(x, lo, poly_var), cdr(e)))
  } else {
    adusum(e) |> ignore
    int(0)
  }
}

///|
fn combin__ipoly2(
  a : Value,
  n : Value,
  lo : Value,
  sign : Value,
  poly_var : Value,
) -> Value raise {
  let s = asksign(lo)
  if eq(s, q_d_zero) || eq(s, q_d_negative) {
    throw_tag(q_isumout, q_divergent) |> ignore
  }
  if !equal(lo, int(1)) {
    with_special(q_d_simpsum, t, () => adsum(
      list([
        list1(q_p_sum),
        list4(list1(q_mtimes), a, int(-1), list3(list1(q_mexpt), poly_var, n)),
        poly_var,
        int(1),
        list3(list1(q_mplus), int(-1), lo),
      ]),
    ))
    |> ignore
  }
  if eq(sign, q_d_negative) {
    list3(
      list1(q_mtimes),
      a,
      ftake(q_p_zeta, [meval(list3(list1(q_mtimes), int(-1), n))]),
    )
  } else {
    throw_tag(q_isumout, q_divergent)
  }
}

///|
fn combin__isgeo(e : Value, lo : Value, poly_var : Value) -> Value raise {
  let r = d_ratsimp(
    div_star(
      maxima_substitute(list3(list1(q_mplus), poly_var, int(1)), poly_var, e),
      e,
    ),
    Nil,
  )
  if free(r, poly_var).truthy() {
    combin__isgeo1(
      maxima_substitute(lo, poly_var, e),
      r,
      asksign(
        simplify(list3(list1(q_mplus), list2(list1(q_mabs), r), int(-1))),
      ),
    )
  } else {
    Nil
  }
}

///|
fn combin__isgeo1(a : Value, r : Value, sign : Value) -> Value raise {
  if eq(sign, q_d_positive) {
    throw_tag(q_isumout, q_divergent)
  } else if eq(sign, q_d_zero) {
    throw_tag(q_isumout, q_divergent)
  } else if eq(sign, q_d_negative) {
    adsum(
      list3(
        list1(q_mtimes),
        a,
        list3(
          list1(q_mexpt),
          list3(list1(q_mplus), int(1), list3(list1(q_mtimes), int(-1), r)),
          int(-1),
        ),
      ),
    )
  } else {
    Nil
  }
}

///|
/// Primary value of SUMSUM.
fn sumsum(
  e : Value,
  poly_var : Value,
  lo : Value,
  hi : Value,
  n_starplus : Value,
  n_startimes : Value,
) -> Value raise {
  sumsum_mv(e, poly_var, lo, hi, n_starplus, n_startimes).0
}

///|
/// SUMSUM returns two values: the unsummed part (or nil) and the new
/// *PLUS list.
fn sumsum_mv(
  e : Value,
  poly_var : Value,
  lo : Value,
  hi : Value,
  n_starplus : Value,
  n_startimes : Value,
) -> (Value, Value) raise {
  combin__sum.val = Nil
  combin__usum.val = Nil
  if eq(hi, q_d_inf) {
    if symval(q_n_starinfsumsimp).truthy() {
      isum(e, lo, poly_var) |> ignore
    } else {
      combin__usum.val = list1(e)
    }
  } else {
    combin__finite_sum(e, int(1), lo, hi, poly_var) |> ignore
  }
  if combin__sum.val is Nil {
    return (list([list1(q_p_sum), e, poly_var, lo, hi]), Nil)
  }
  let plus = nconc(
    mapcar(
      q => simptimes(list3(list1(q_mtimes), n_startimes, q), int(1), Nil),
      combin__sum.val,
    ),
    n_starplus,
  )
  let first_ = if combin__usum.val.truthy() {
    combin__usum.val = list([
      list1(q_p_sum),
      simplus(cons(list1(q_plus), combin__usum.val), int(1), t),
      poly_var,
      lo,
      hi,
    ])
    combin__usum.val
  } else {
    Nil
  }
  (first_, plus)
}

///|
fn combin__finite_sum(
  e : Value,
  y : Value,
  lo : Value,
  hi : Value,
  poly_var : Value,
) -> Value raise {
  if e is Nil {
    t
  } else if free(e, poly_var).truthy() {
    adsum(m_star(list3(y, e, m_plus(list3(hi, int(1), m_(lo))))))
  } else if poly_q(e, poly_var).truthy() {
    adsum(m_star(list2(y, fpolysum(e, lo, hi, poly_var))))
  } else if eq(caar(e), q_p_binomial) {
    fbino(e, y, lo, hi, poly_var)
  } else if eq(caar(e), q_mplus) {
    mapc(q => combin__finite_sum(q, y, lo, hi, poly_var) |> ignore, cdr(e))
  } else {
    let g = if mtimesp(e).truthy() || mexptp(e).truthy() || mplusp(e).truthy() {
      combin__fsgeo(e, y, lo, hi, poly_var)
    } else {
      Nil
    }
    if g.truthy() {
      g
    } else {
      adusum(e) |> ignore
      Nil
    }
  }
}

///|
fn combin__fsgeo(
  e : Value,
  y : Value,
  lo : Value,
  hi : Value,
  poly_var : Value,
) -> Value raise {
  let r = d_ratsimp(
    div_star(
      maxima_substitute(list3(list1(q_mplus), poly_var, int(1)), poly_var, e),
      e,
    ),
    Nil,
  )
  if equal(r, int(1)) {
    adsum(
      list3(
        list1(q_mtimes),
        list4(list1(q_mplus), int(1), hi, list3(list1(q_mtimes), int(-1), lo)),
        maxima_substitute(lo, poly_var, e),
      ),
    )
  } else if free(r, poly_var).truthy() {
    adsum(
      list([
        list1(q_mtimes),
        y,
        maxima_substitute(int(0), poly_var, e),
        list3(
          list1(q_mplus),
          list3(list1(q_mexpt), r, list3(list1(q_mplus), hi, int(1))),
          list3(list1(q_mtimes), int(-1), list3(list1(q_mexpt), r, lo)),
        ),
        list3(list1(q_mexpt), list3(list1(q_mplus), r, int(-1)), int(-1)),
      ]),
    )
  } else {
    Nil
  }
}

// ---------------------------------------------------------------------------
// product routines

///|
fn d_product(l : Value) -> Value raise {
  arg_count_check(int(4), l) |> ignore
  let l = cdr(l)
  dosum(car(l), cadr(l), meval(caddr(l)), meval(cadddr(l)), Nil, evaluate_summand=t)
}

///|
fn simpprod(x : Value, y : Value, z : Value) -> Value raise {
  let y = with_special(q_d_ratsimpexpons, t, () => if equal(y, int(1)) {
    maybe_simplifya(cadr(x), z)
  } else {
    simptimes(list3(list1(q_mexpt), cadr(x), y), int(1), z)
  })
  simpprod1(
    y,
    caddr(x),
    maybe_simplifya(cadddr(x), z),
    maybe_simplifya(cadr(cdddr(x)), z),
  )
}

///|
fn d_taytorat(e : Value) -> Value raise {
  if mbagp(e).truthy() {
    cons(car(e), mapcar(x => d_taytorat(x), cdr(e)))
  } else if atom(e) || memq(q_trunc, cdar(e)) is Nil {
    ratf(e)
  } else {
    let r = catch_tag(q_srrat, () => srrat(e))
    if r.truthy() {
      r
    } else {
      ratf(d_ratdisrep(e))
    }
  }
}

///|
fn srrat(e : Value) -> Value raise {
  if some(v => switch(q_multivar, v).truthy(), mrat_tlist(e)) {
    Nil
  } else {
    cons(
      list4(q_mrat, q_simp, mrat_varlist(e), mrat_genvar(e)),
      srrat2(mrat_ps(e)),
    )
  }
}

///|
fn srrat2(e : Value) -> Value raise {
  if pscoefp(e).truthy() {
    e
  } else {
    srrat3(terms(e), gvar(e))
  }
}

///|
fn srrat3(l : Value, poly_var : Value) -> Value raise {
  if l is Nil {
    cons(int(0), int(1))
  } else if !eq1(cdr(le(l))) {
    throw_tag(q_srrat, Nil)
  } else if n__term(l) is Nil {
    rattimes(
      cons(list3(poly_var, car(le(l)), int(1)), int(1)),
      srrat2(lc(l)),
      t,
    )
  } else {
    ratplus(
      rattimes(
        cons(list3(poly_var, car(le(l)), int(1)), int(1)),
        srrat2(lc(l)),
        t,
      ),
      srrat3(n__term(l), poly_var),
    )
  }
}

///|
fn d_deftaylor(l : Value) -> Value raise {
  let mut l = l
  let mut ops : Value = Nil
  while true {
    l = cdr(l)
    if l is Nil {
      return cons(list1(q_mlist), ops)
    }
    let fun = meval(car(l))
    let mut series = meval(cadr(l))
    l = cdr(l)
    let mut param : Value = Nil
    let mut op : Value = Nil
    let bad = if atom(fun) {
      true
    } else if eq(caar(fun), q_mqapply) {
      if cdddr(fun).truthy() || cddr(fun) is Nil {
        // must be one parameter, must have exactly one
        true
      } else {
        let mut subs = cdadr(fun)
        let mut r = false
        while true {
          if subs is Nil {
            op = caaadr(fun)
            if cddr(fun).truthy() {
              param = caddr(fun)
            }
            r = false
            break
          }
          if !atom(car(subs)) {
            r = true
            break
          }
          subs = cdr(subs)
        }
        r
      }
    } else {
      op = caar(fun)
      if cdr(fun).truthy() {
        param = cadr(fun)
      }
      (zl_get(op, q_op).truthy() && !eq(op, q_mfactorial)) ||
      !atom(cadr(fun)) ||
      length(fun) != 2
    }
    if bad {
      merr("deftaylor: don't know how to handle this function: ~M", [fun])
      |> ignore
    }
    if zl_get(op, q_sp2).truthy() {
      mtell(list2(Str("deftaylor: redefining ~:M.~%"), op)) |> ignore
    }
    if param.truthy() {
      series = subst(q_sp2var, param, series)
    }
    series = subsum(q_n_starindex, series)
    putprop(op, series, q_sp2) |> ignore
    if eq(caar(fun), q_mqapply) {
      putprop(op, cdadr(fun), q_sp2subs) |> ignore
    }
    add2lnc(op, symval(q_d_props)) |> ignore
    ops = cons(op, ops)
  }
  Nil
}

///|
fn subsum(combin_i : Value, e : Value) -> Value raise {
  susum1(combin_i, e)
}

///|
fn susum1(combin_i : Value, e : Value) -> Value raise {
  if atom(e) {
    e
  } else if eq(caar(e), q_p_sum) {
    if smonop(cadr(e), q_sp2var) is Nil {
      merr("deftaylor: argument must be a power series at 0.", [])
    } else {
      subst(combin_i, caddr(e), e)
    }
  } else {
    recur_apply(lfunc("susum1", args => susum1(combin_i, arg(args, 0))), e)
  }
}

///|
/// Shared loop of $POLYDECOMP and POLYDECOMP: combine the decomposition
/// components (as headerless rat forms) in place.
fn combin__polydecomp_loop(p : Value, poly_var : Value) -> Unit raise {
  let mut l = p
  while !(l is Nil) {
    let a = pdecpow(car(l), poly_var)
    if a.truthy() {
      rplaca(l, car(a)) |> ignore
      if cdr(l).truthy() {
        rplacd(
          l,
          cons(
            ratplus(
              rattimes(cadr(l), cons(ptterm(cdr(caadr(a)), int(1)), cdadr(a)), t),
              cons(ptterm(cdr(caadr(a)), int(0)), cdadr(a)),
            ),
            cddr(l),
          ),
        )
        |> ignore
      } else if equal(cadr(a), cons(list3(poly_var, int(1), int(1)), int(1))) {
        ()
      } else {
        rplacd(l, list1(cadr(a))) |> ignore
      }
    }
    l = cdr(l)
  }
}

///|
fn d_polydecomp(e : Value, v : Value) -> Value raise {
  with_specials(
    [
      (q_varlist, list1(v)),
      (q_genvar, Nil),
      (q_d_factorflag, Nil),
      (q_d_ratfac, Nil),
    ],
    () => {
      let mut p = cdr(ratf(ratdisrep(e)))
      let mut poly_var = cdr(ratf(v))
      if cdr(poly_var) is Nil ||
        !equal(cdar(poly_var), list2(int(1), int(1))) {
        merr("polydecomp: second argument must be an atom; found ~M", [v])
        |> ignore
      } else {
        poly_var = caar(poly_var)
      }
      let mut den : Value = Nil
      if pcoefp(cdr(p)).truthy() || !eq(cadr(p), poly_var) {
        den = cdr(p)
        p = car(p)
      } else {
        merr(
          "polydecomp: cannot apply 'polydecomp' to a rational function.",
          [],
        )
        |> ignore
      }
      cons(
        list1(q_mlist),
        if pcoefp(p).truthy() || !eq(car(p), poly_var) {
          list1(rdis(cons(p, den)))
        } else {
          p = pdecomp(p, poly_var)
          p = mapcar(q => cons(q, int(1)), p)
          combin__polydecomp_loop(p, poly_var)
          cons(
            rdis(cons(caar(p), ptimes(cdar(p), den))),
            mapcar(x => rdis(x), cdr(p)),
          )
        },
      )
    },
  )
}

///|
/// POLYDECOMP is like $POLYDECOMP except it takes a poly in *POLY* format
/// (numerator of a RAT form) and returns a list of headerless rat forms.
fn polydecomp(p : Value, poly_var : Value) -> Value raise {
  with_specials([(q_d_factorflag, Nil), (q_d_ratfac, Nil)], () => if pcoefp(p).truthy() ||
    !eq(car(p), poly_var) {
    cons(p, Nil)
  } else {
    let mut p = pdecomp(p, poly_var)
    p = mapcar(q => cons(q, int(1)), p)
    combin__polydecomp_loop(p, poly_var)
    cons(cons(caar(p), cdar(p)), cdr(p))
  })
}

///|
/// f = g(h(poly-var))
fn pdecred(f : Value, h : Value, poly_var : Value) -> Value raise {
  let mut f = f
  let fails = if pcoefp(h).truthy() ||
    !eq(car(h), poly_var) ||
    equal(cadr(h), int(1)) ||
    !zerop(num_rem(cadr(f), cadr(h))) {
    true
  } else {
    f = pdivide(f, h)
    !pzerop(caadr(f)).truthy() && equal(cdadr(f), int(1))
  }
  if fails {
    return Nil
  }
  let mut q = pdivide(caar(f), h)
  let mut i = 1
  let mut combin_ans : Value = Nil
  let ok = fn(q : Value) -> Bool raise {
    equal(cdadr(q), int(1)) &&
    (pcoefp(caadr(q)).truthy() || !eq(caar(cadr(q)), poly_var))
  }
  while !pzerop(caar(q)).truthy() {
    if ok(q) {
      if !pzerop(caadr(q)).truthy() {
        combin_ans = cons(int(i), cons(caadr(q), combin_ans))
      }
    } else {
      return Nil
    }
    q = pdivide(caar(q), h)
    i += 1
  }
  if ok(q) {
    psimp(poly_var, cons(int(i), cons(caadr(q), combin_ans)))
  } else {
    Nil
  }
}

///|
fn pdecomp(p : Value, poly_var : Value) -> Value raise {
  let c = ptterm(cdr(p), int(0))
  // CRE form of the polynomial x (with the actual variable in poly-var).
  let poly_x = list3(poly_var, int(1), int(1))
  let a = combin__pdecomp_star(pdifference(p, c), poly_var, poly_x)
  cons(pcplus(c, car(a)), cdr(a))
}

///|
fn combin__pdecomp1(
  prod : Value,
  l : Value,
  poly : Value,
  poly_var : Value,
) -> Value raise {
  if l is Nil {
    if !equal(cadr(prod), cadr(poly)) {
      let l = pdecred(poly, prod, poly_var)
      if l.truthy() {
        list2(l, prod)
      } else {
        Nil
      }
    } else {
      Nil
    }
  } else {
    let r = combin__pdecomp1(prod, cdr(l), poly, poly_var)
    if r.truthy() {
      r
    } else {
      combin__pdecomp1(ptimes(car(l), prod), cdr(l), poly, poly_var)
    }
  }
}

///|
fn combin__pdecomp_star(poly : Value, poly_var : Value, poly_x : Value) -> Value raise {
  let l = pdecgdfrm(pfactor(pquotient(poly, poly_x)))
  if pdecprimep(cadr(poly)).truthy() {
    return list1(poly)
  }
  let a = combin__pdecomp1(poly_x, l, poly, poly_var)
  if a is Nil {
    list1(poly)
  } else {
    append(combin__pdecomp_star(car(a), poly_var, poly_x), cdr(a))
  }
}

///|
/// Get list of divisors
fn pdecgdfrm(l : Value) -> Value raise {
  let mut ll = list1(car(l))
  let mut l = copy_list(l)
  while true {
    rplaca(cdr(l), num_sub(cadr(l), int(1))) |> ignore
    if numberp(cadr(l)) && zerop(cadr(l)) {
      l = cddr(l)
    }
    if l is Nil {
      return ll
    }
    ll = cons(car(l), ll)
  }
  ll
}

///|
fn pdecprimep(x : Value) -> Value raise {
  let x = cfactorw(x)
  lbool(cddr(x) is Nil && equal(cadr(x), int(1)))
}

///|
fn pdecpow(p : Value, poly_var : Value) -> Value raise {
  let p = car(p)
  let p1 = pderivative(p, poly_var)
  let mut p1p = oldcontent(p1)
  let p1c = car(p1p)
  p1p = cadr(p1p)
  let p2 = pderivative(p1, poly_var)
  let p2p = cadr(oldcontent(p2))
  let lin = testdivide(p1p, p2p)
  if lin.truthy() && !pcoefp(lin).truthy() && eq(car(lin), poly_var) {
    let a = ratreduce(p1c, ptimes(cadr(p), caddr(lin)))
    list2(
      ratplus(
        rattimes(cons(list3(poly_var, cadr(p), int(1)), int(1)), a, t),
        ratdif(cons(p, int(1)), rattimes(a, cons(pexpt(lin, cadr(p)), int(1)), t)),
      ),
      cons(lin, int(1)),
    )
  } else {
    Nil
  }
}

///|
fn init_combin_2() -> Unit {
  // Functions nested in top-level LETs are not in the generated registry.
  defun(sym("getfactorial"), args => getfactorial(arg(args, 0)))
  defun(sym("factplus1"), args => factplus1(arg(args, 0), arg(args, 1), arg(args, 2)))
  defun(sym("factpluscomb"), args => factpluscomb(arg(args, 0)))
  defun(sym("ffib"), args => ffib(arg(args, 0)))
  defun(sym("adsum"), args => adsum(arg(args, 0)))
  defun(sym("adusum"), args => adusum(arg(args, 0)))
  defun(sym("fpolysum"), args => fpolysum(
    arg(args, 0),
    arg(args, 1),
    arg(args, 2),
    arg(args, 3),
  ))
  defun(sym("fbino"), args => fbino(
    arg(args, 0),
    arg(args, 1),
    arg(args, 2),
    arg(args, 3),
    arg(args, 4),
  ))
  defun(sym("isum"), args => isum(arg(args, 0), arg(args, 1), arg(args, 2)))
  defun(sym("sumsum"), args => sumsum(
    arg(args, 0),
    arg(args, 1),
    arg(args, 2),
    arg(args, 3),
    arg(args, 4),
    arg(args, 5),
  ))
}
