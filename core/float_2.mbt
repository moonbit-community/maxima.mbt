// Port of src/float.lisp, part 2: the constants %e, %pi, %gamma, log(2),
// %catalan and %phi (computed by binary splitting and memoized per
// precision), and the elementary functions exp, log, sin, cos, tan, atan.

///|
let float__table_fpe : Map[Int64, Value] = {}

///|
let float__table_fppi : Map[Int64, Value] = {}

///|
let float__table_fpgamma : Map[Int64, Value] = {}

///|
let float__table_fplog2 : Map[Int64, Value] = {}

///|
let float__table_fpcatalan : Map[Int64, Value] = {}

///|
let float__table_fpphi : Map[Int64, Value] = {}

///|
/// The memoizing closure of float.lisp's MEMOIZE macrolet: look up the
/// value of a constant for the current fpprec, computing it if needed.
/// Each value is a bigfloat number without the bigfloat tag.
fn float__memo(
  tbl : Map[Int64, Value],
  compute : () -> Value raise,
) -> Value raise {
  let key = to_int64(float__prec())
  match tbl.get(key) {
    Some(v) => v
    None => {
      let v = compute()
      tbl[key] = v
      v
    }
  }
}

///|
fn float__fpe() -> Value raise {
  float__memo(float__table_fpe, () => cdr(fpe1()))
}

///|
fn float__fppi() -> Value raise {
  float__memo(float__table_fppi, () => cdr(fppi1()))
}

///|
fn float__fpgamma() -> Value raise {
  float__memo(float__table_fpgamma, () => cdr(fpgamma1()))
}

///|
fn float__fplog2() -> Value raise {
  float__memo(float__table_fplog2, () => comp_log2())
}

///|
fn float__fpcatalan() -> Value raise {
  float__memo(float__table_fpcatalan, () => cdr(fpcatalan1()))
}

///|
fn float__fpphi() -> Value raise {
  float__memo(float__table_fpphi, () => cdr(fpphi1()))
}

///|
/// CL `(log n)` of a rational: a single-float (computed in double and
/// rounded, as SBCL does).
fn float__slog(x : Double) -> Float {
  Float::from_double(@math.ln(x))
}

///|
/// CL `(ceiling x)` of a float, as an integer Value.
fn float__fceiling(x : Double) -> Value raise {
  ceiling1(Flo(x))
}

// The values of %e, %pi, %gamma and log(2) are computed by the technique of
// binary splitting. See http://www.ginac.de/CLN/binsplit.pdf for details.

///|
/// Euler's number E
fn fpe1() -> Value raise {
  // compute additional bits
  let e = compe(float__addi(float__prec(), 12))
  // round to fpprec
  bcons(list([fpround(car(e)), cadr(e)]))
}

///|
/// Taylor: %e = sum(s[i] ,i,0,inf) where s[i] = 1/i!
fn compe(prec : Value) -> Value raise {
  with_special(q_fpprec, prec, () => {
    let (tt, qq) = split_taylor_e(Fix(0L), taylor_e_size(prec))
    fpquotient(intofp(tt), intofp(qq))
  })
}

///|
/// binary splitting: s[i] = 1/(q[0]*q[1]*..*q[i]), q[0] = 1, q[i] = i
fn split_taylor_e(i : Value, j : Value) -> (Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    let qq : Value = if num_eq(i, Fix(0L)) { Fix(1L) } else { i }
    (Fix(1L), qq)
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, ql) = split_taylor_e(i, m)
    let (tr, qr) = split_taylor_e(m, j)
    let qq = num_mul(ql, qr)
    let tt = num_add(num_mul(qr, tl), tr)
    (tt, qq)
  }
}

///|
/// stop when i! > 2^fpprec:
///   log(i!) = sum(log(k), k,1,i) > fpprec * log(2)
fn taylor_e_size(prec : Value) -> Value raise {
  // ACC starts as the integer 0 and accumulates single-floats.
  let mut acc : Float = 0.0
  let lim : Float = Float::from_double(to_double(prec)) * float__slog(2.0)
  let mut i = 1
  while !(acc > lim) {
    acc = acc + float__slog(i.to_double())
    i += 1
  }
  int(i)
}

///|
/// PI
fn fppi1() -> Value raise {
  let pi1 = comppi(float__addi(float__prec(), 10))
  bcons(list([fpround(car(pi1)), cadr(pi1)]))
}

///|
/// Chudnovsky & Chudnovsky:
///
/// C^(3/2)/(12*%pi) = sum(s[i], i,0,inf),
///    where s[i] = (-1)^i*(6*i)!*(A*i+B) / (i!^3*(3*i)!*C^(3*i))
///       and A = 545140134, B = 13591409, C = 640320
fn comppi(prec : Value) -> Value raise {
  with_special(q_fpprec, prec, () => {
    // STEP 1: compute n/d = sqrt(10005) by quadratic Heron iteration:
    //   n[i+1] = n[i]^2+a*d[i]^2, d[i+1] = 2*n[i]*d[i]
    let (nr0, n0, d0) = sqrt_10005_constants(float__prec())
    let mut n = n0
    let mut d = d0
    let mut i : Value = Fix(0L)
    while num_lt(i, nr0) {
      let oldn = n
      n = num_add(num_mul(n, n), num_mul(num_mul(Fix(10005L), d), d))
      d = num_mul(num_mul(Fix(2L), oldn), d)
      i = one_plus(i)
    }
    // STEP 2: divide C^(3/2)/12 = 3335*2^7*sqrt(10005) by
    // Chudnovsky-sum = tt/qq.  nr of summands:
    // fpprec*log(2)/log(C^3/(24*6*2*6))
    let nr = float__fceiling(to_double(float__prec()) * 0.021226729578153)
    let (tt, qq, _) = split_chudnovsky(Fix(0L), one_plus(nr))
    n = num_mul(Fix(3335L), n)
    let n_starqq = intofp(num_mul(n, qq))
    fpquotient(
      list([car(n_starqq), num_add(cadr(n_starqq), Fix(7L))]),
      intofp(num_mul(d, tt)),
    )
  })
}

///|
/// The returned n and d serve as start values for the iteration.  n/d =
/// sqrt(10005) with a precision of p = ceiling(prec/2^nr) bits where nr is
/// the number of needed iterations.
fn sqrt_10005_constants(prec : Value) -> (Value, Value, Value) raise {
  let (nr, p) = if num_lt(prec, Fix(128L)) {
    (Value::Fix(0L), prec)
  } else {
    let ilen = integer_length(prec)
    let nr = ilen - 7
    (
      int(nr),
      float__fceiling(
        to_double(prec) * to_double(expt(Flo(2.0), int(-nr))),
      ),
    )
  }
  let (n, d) = if num_le(p, Fix(76L)) {
    (lread("256192036001"), lread("2561280120"))
  } else if num_le(p, Fix(89L)) {
    (lread("51244811200700"), lread("512320048001"))
  } else if num_le(p, Fix(102L)) {
    (lread("2050048640064001"), lread("20495363200160"))
  } else if num_le(p, Fix(115L)) {
    (lread("410060972824000900"), lread("4099584960080001"))
  } else {
    (lread("16404488961600100001"), lread("164003893766400200"))
  }
  (nr, n, d)
}

///|
/// binary splitting:
///        a[i] * p[0]*p[1]*p[2]*..*p[i]
/// s[i] = -----------------------------
///               q[0]*q[1]*q[2]*..*q[i]
///  where a[0] = B, p[0] = q[0] = 1, a[i] = A*i+B,
///        p[i] = - (6*i-5)*(2*i-1)*(6*i-1), q[i] = C^3/24*i^3
fn split_chudnovsky(i : Value, j : Value) -> (Value, Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    if num_eq(i, Fix(0L)) {
      let aa : Value = Fix(13591409L)
      (aa, Fix(1L), Fix(1L))
    } else {
      let aa = num_add(num_mul(i, Fix(545140134L)), Fix(13591409L))
      let pp_qq = num_div(
        num_mul(
          num_mul(
            num_sub(Fix(5L), num_mul(Fix(6L), i)),
            num_sub(num_mul(Fix(2L), i), Fix(1L)),
          ),
          num_sub(num_mul(Fix(6L), i), Fix(1L)),
        ),
        lread("10939058860032000"),
      )
      // C^3/24
      let pp = numerator(pp_qq)
      let qq = num_mul(denominator(pp_qq), expt(i, Fix(3L)))
      let tt = num_mul(aa, pp)
      (tt, qq, pp)
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, ql, pl) = split_chudnovsky(i, m)
    let (tr, qr, pr) = split_chudnovsky(m, j)
    let pp = num_mul(pl, pr)
    let qq = num_mul(ql, qr)
    let tt = num_add(num_mul(qr, tl), num_mul(pl, tr))
    (tt, qq, pp)
  }
}

///|
/// Euler-Mascheroni constant GAMMA
fn fpgamma1() -> Value raise {
  let res = comp_bf_pctgamma(float__addi(float__prec(), 14))
  bcons(list([fpround(car(res)), cadr(res)]))
}

///|
/// Brent-McMillan algorithm
///
/// Let alpha = 4.970625759544, n > 0 and N-1 >= alpha*n,
///       H(k) = sum(1/i, i,1,k)
///       S = sum(H(k)*(n^k/k!)^2, k,0,N-1)
///       I = sum((n^k/k!)^2, k,0,N-1)
///       T = 1/(4*n)*sum((2*k)!^3/(k!^4*(16*n)^(2*k)), k,0,2*n-1)
/// and   %gamma = S/I - T/I^2 - log(n)
/// Then  |%gamma - gamma| < 24 * e^(-8*n)
fn comp_bf_pctgamma(prec : Value) -> Value raise {
  with_special(q_fpprec, prec, () => {
    let n = float__fceiling(
      0.125 * (to_double(prec) * @math.ln(2.0) + @math.ln(24.0)),
    )
    let n2 = num_mul(n, n)
    let alpha = 4.970625759544
    let lim = float__fceiling(alpha * to_double(n))
    let (vv, tt, qq, dd, _, _) = split_gamma_1(Fix(1L), one_plus(lim), n2)
    // sums      = vv/(qq*dd)
    // sumi      = tt/qq
    // sums/sumi = vv/(qq*dd)*qq/tt = vv/(dd*tt)
    let sums_slsumi = fpquotient(intofp(vv), intofp(num_mul(dd, tt)))
    let sumi = fpquotient(intofp(tt), intofp(qq))
    let sumi2 = fptimes_star(sumi, sumi)
    let (ttt, qqq, _) = split_gamma_2(
      Fix(0L),
      num_mul(Fix(2L), n),
      num_mul(Fix(32L), n2),
    )
    // sumt       = 1/(4*n)*ttt/qqq
    // sumt/sumi2 = ttt/(4*n*qqq*sumi2)
    let sumt_slsumi2 = fpquotient(
      intofp(ttt),
      fptimes_star(intofp(num_mul(num_mul(Fix(4L), n), qqq)), sumi2),
    )
    // %gamma :
    fpdifference(sums_slsumi, fpplus(sumt_slsumi2, log_n(n)))
  })
}

///|
/// split S and I simultaneously (see comp-bf%gamma).
fn split_gamma_1(
  i : Value,
  j : Value,
  n2 : Value,
) -> (Value, Value, Value, Value, Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    if num_eq(i, Fix(1L)) {
      // S[0] is 0 -> start with i=1 and add I[0]=1 to tt :
      let pp = n2
      let cc : Value = Fix(1L)
      let dd : Value = Fix(1L)
      let qq : Value = Fix(1L)
      let tt = one_plus(n2)
      let vv = n2
      (vv, tt, qq, dd, cc, pp)
    } else {
      let pp = n2
      let cc : Value = Fix(1L)
      let dd = i
      let qq = num_mul(i, i)
      let tt = pp
      let vv = tt
      (vv, tt, qq, dd, cc, pp)
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (vl, tl, ql, dl, cl, pl) = split_gamma_1(i, m, n2)
    let (vr, tr, qr, dr, cr, pr) = split_gamma_1(m, j, n2)
    let pp = num_mul(pl, pr)
    let cc = num_add(num_mul(cl, dr), num_mul(dl, cr))
    let dd = num_mul(dl, dr)
    let qq = num_mul(ql, qr)
    let tmp = num_mul(pl, tr)
    let tt = num_add(num_mul(tl, qr), tmp)
    let vv = num_add(
      num_mul(dr, num_add(num_mul(vl, qr), num_mul(cl, tmp))),
      num_mul(num_mul(dl, pl), vr),
    )
    (vv, tt, qq, dd, cc, pp)
  }
}

///|
/// split 4*n*T: T[0] = 1, T[i]/T[i-1] = (2*i-1)^3/(32*i*n^2)
fn split_gamma_2(
  i : Value,
  j : Value,
  n2_star32 : Value,
) -> (Value, Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    if num_eq(i, Fix(0L)) {
      (Fix(1L), Fix(1L), Fix(1L))
    } else {
      let pp = expt(one_minus(num_mul(Fix(2L), i)), Fix(3L))
      let qq = num_mul(i, n2_star32)
      (pp, qq, pp)
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, ql, pl) = split_gamma_2(i, m, n2_star32)
    let (tr, qr, pr) = split_gamma_2(m, j, n2_star32)
    let pp = num_mul(pl, pr)
    let qq = num_mul(ql, qr)
    let tt = num_add(num_mul(tl, qr), num_mul(pl, tr))
    (tt, qq, pp)
  }
}

///|
/// log(2) = 18*L(26) - 2*L(4801) + 8*L(8749)  where L(k) = atanh(1/k)
fn comp_log2() -> Value raise {
  let res = with_special(q_fpprec, float__addi(float__prec(), 12), () => fpplus(
    fpdifference(
      n_staratanh_1_slk(Fix(18L), Fix(26L)),
      n_staratanh_1_slk(Fix(2L), Fix(4801L)),
    ),
    n_staratanh_1_slk(Fix(8L), Fix(8749L)),
  ))
  list([fpround(car(res)), cadr(res)])
}

///|
/// Taylor: atanh(1/k) = sum(s[i], i,0,inf) where s[i] = 1/((2*i+1)*k^(2*i+1))
fn n_staratanh_1_slk(n : Value, k : Value) -> Value raise {
  let k2 = num_mul(k, k)
  let ratio : Float = float__slog(2.0) / float__slog(to_double(k2))
  let nr = ceiling1(
    Flo((Float::from_double(to_double(float__prec())) * ratio).to_double()),
  )
  let (tt, qq, bb) = split_atanh_1_slk(Fix(0L), one_plus(nr), k, k2)
  fpquotient(intofp(num_mul(n, tt)), intofp(num_mul(bb, qq)))
}

///|
/// binary splitting: s[i] = 1/(b[i] * q[0]*..*q[i]), b[0] = 1, q[0] = k,
/// b[i] = 2*i+1, q[i] = k^2
fn split_atanh_1_slk(
  i : Value,
  j : Value,
  k : Value,
  k2 : Value,
) -> (Value, Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    if num_eq(i, Fix(0L)) {
      (Fix(1L), k, Fix(1L))
    } else {
      (Fix(1L), k2, one_plus(num_mul(Fix(2L), i)))
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, ql, bl) = split_atanh_1_slk(i, m, k, k2)
    let (tr, qr, br) = split_atanh_1_slk(m, j, k, k2)
    let bb = num_mul(bl, br)
    let qq = num_mul(ql, qr)
    let tt = num_add(num_mul(num_mul(br, qr), tl), num_mul(bl, tr))
    (tt, qq, bb)
  }
}

///|
/// log(n) = log(n/2^k) + k*log(2)   (integer n > 0)
fn log_n(n : Value) -> Value raise {
  if num_eq(Fix(1L), n) {
    list([Fix(0L), Fix(0L)])
  } else if num_eq(Fix(2L), n) {
    comp_log2()
  } else {
    let res = with_special(q_fpprec, float__addi(float__prec(), 10), () => {
      let mut k = integer_length(n)
      // choose k so that |n/2^k - 1| is as small as possible:
      if to_double(n) < 2.0 / 3.0 * to_double(ash(Fix(1L), k)) {
        k -= 1
      }
      // now |n/2^k - 1| <= 1/3
      fpplus(
        log_u_sl2_hatk(n, int(k), float__prec()),
        fptimes_star(intofp(int(k)), comp_log2()),
      )
    })
    list([fpround(car(res)), cadr(res)])
  }
}

///|
/// log(1+u/v)  = 2 * sum(s[i], i,0,inf)
///   where s[i] = (u/(2*v+u))^(2*i+1)/(2*i+1)
/// integer u k; x = u/2^k; |x - 1| < 1
fn log_u_sl2_hatk(u0 : Value, k0 : Value, prec : Value) -> Value raise {
  // x <-- x - 1
  let mut u = num_sub(u0, float__ash(Fix(1L), k0))
  let mut k = k0
  if num_eq(Fix(0L), u) {
    list([Fix(0L), Fix(0L)])
  } else {
    while evenp(u) {
      u = ash(u, -1)
      k = one_minus(k)
    }
    let u2 = num_mul(u, u)
    let w = num_add(u, float__ash(Fix(2L), k))
    let w2 = num_mul(w, w)
    let lw : Float = float__slog(to_double(num_abs(num_div(w, u))))
    let f : Float = float__slog(2.0) / 2.0 / lw
    let nr = ceiling1(Flo((Float::from_double(to_double(prec)) * f).to_double()))
    let (tt, qq, bb, _) = split_log_1_plusu_slv(
      Fix(0L),
      one_plus(nr),
      u,
      u2,
      w,
      w2,
    )
    // sum
    let lg_sl2 = fpquotient(intofp(tt), intofp(num_mul(bb, qq)))
    // 2*sum
    list([car(lg_sl2), one_plus(cadr(lg_sl2))])
  }
}

///|
/// binary splitting:
///               p[0]*p[1]*p[2]*..*p[i]
/// s[i] = -----------------------------
///        b[i] * q[0]*q[1]*q[2]*..*q[i]
///  where b[0] = 1, p[0] = u, q[0] = w = 2*v+u, b[i] = 2*i+1, p[i] = u^2,
///  q[i] = w^2
fn split_log_1_plusu_slv(
  i : Value,
  j : Value,
  u : Value,
  u2 : Value,
  w : Value,
  w2 : Value,
) -> (Value, Value, Value, Value) raise {
  if num_eq(num_sub(j, i), Fix(1L)) {
    if num_eq(i, Fix(0L)) {
      (u, w, Fix(1L), u)
    } else {
      (u2, w2, one_plus(num_mul(Fix(2L), i)), u2)
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, ql, bl, pl) = split_log_1_plusu_slv(i, m, u, u2, w, w2)
    let (tr, qr, br, pr) = split_log_1_plusu_slv(m, j, u, u2, w, w2)
    let bb = num_mul(bl, br)
    let pp = num_mul(pl, pr)
    let qq = num_mul(ql, qr)
    let tt = num_add(
      num_mul(num_mul(br, qr), tl),
      num_mul(num_mul(bl, pl), tr),
    )
    (tt, qq, bb, pp)
  }
}

///|
fn fpcatalan1() -> Value raise {
  // Use 5 extra bits when computing %catalan.
  let catalan = cdr(bf_comp_catalan(float__addi(float__prec(), 5)))
  // Round value that has extra bits to the current number of bits in a
  // bfloat.
  bcons(list([fpround(car(catalan)), cadr(catalan)]))
}

///|
fn fpphi1() -> Value raise {
  let phi = with_special(q_fpprec, float__addi(float__prec(), 2), () => {
    // Use couple of extra bits to compute %phi = (1+sqrt(5))/2.
    cdr(
      d_bfloat(
        div(add2(Fix(1L), power(Fix(5L), symval(q_n1_sl_sl2))), Fix(2L)),
      ),
    )
  })
  bcons(list([fpround(car(phi)), cadr(phi)]))
}

// ---------------------------------------------------------------------------
// atan, tan

///|
fn atanbigfloat(x : Value) -> Value raise {
  n_starfpatan(car(x), cdr(x))
}

///|
fn n_starfpatan(a : Value, y : Value) -> Value raise {
  fpend(
    with_special(q_fpprec, float__addi(float__prec(), 8), () => if y is Nil {
      if d_bfloatp(a).truthy() {
        fpatan(cdr(d_bfloat(a)))
      } else {
        list2(list1(q_p_atan), a)
      }
    } else {
      fpatan2(cdr(d_bfloat(a)), cdr(d_bfloat(car(y))))
    }),
  )
}

///|
/// Bigfloat atan
fn fpatan(x : Value) -> Value raise {
  let one = intofp(Fix(1L))
  let two = intofp(Fix(2L))
  if fpgreaterp(fpabs(x), one).truthy() {
    // |x| > 1.  Use A&S 4.4.5:
    //    atan(x) + acot(x) = +/- pi/2 (+ for x >= 0, - for x < 0)
    // and A&S 4.4.8
    //    acot(z) = atan(1/z)
    let tmp = fpquotient(float__fppi(), two)
    let ans = fpdifference(tmp, fpatan(fpquotient(one, x)))
    if fplessp(x, intofp(Fix(0L))).truthy() {
      fpdifference(ans, float__fppi())
    } else {
      ans
    }
  } else if fpgreaterp(fpabs(x), fpquotient(one, two)).truthy() {
    // |x| > 1/2.  Use A&S 4.4.42, third formula:
    //   atan(z) = z/(1+z^2)*[1 + 2/3*r + (2*4)/(3*5)*r^2 + ...]
    //   r = z^2/(1+z^2)
    let tmp = fpquotient(x, fpplus(fptimes_star(x, x), one))
    let x2 = fptimes_star(x, tmp)
    let mut ans = one
    let mut term = one
    let mut oans = Value::Nil
    let mut n = 0
    while !equal(ans, oans) {
      term = fptimes_star(
        term,
        fptimes_star(
          x2,
          fpquotient(intofp(int(2 + 2 * n)), intofp(int(2 * n + 3))),
        ),
      )
      oans = ans
      ans = fpplus(term, ans)
      n += 1
    }
    fptimes_star(tmp, ans)
  } else {
    // |x| <= 1/2.  Use Taylor series (A&S 4.4.42, first formula).  The n'th
    // term is (-1)^n*x^(2*n+1)/(2*n+1); stop when |x^(2*n)| <= tol.  Since
    // tol is basically 2^(-fpprec), n = fpprec/2.  But double it.
    let mut ans = x
    let x2 = fpminus(fptimes_star(x, x))
    let mut term = x
    let mut oans = Value::Nil
    let max_n = float__prec()
    let mut n : Value = Fix(3L)
    while !(equal(ans, oans) || num_ge(n, max_n)) {
      term = fptimes_star(term, x2)
      oans = ans
      ans = fpplus(ans, fpquotient(term, intofp(n)))
      n = num_add(n, Fix(2L))
    }
    ans
  }
}

///|
/// Compute atan(x+%i*y) when X and Y are bigfloat objects.  Y is optional.
fn big_float_atan(x : Value, y? : Value = Nil) -> Value raise {
  if y.truthy() &&
    zerop1(x).truthy() &&
    zerop1(sub(mul2(y, y), Fix(1L))).truthy() {
    // The poles at +/-%i.
    domain_error(add2(x, mul2(q_d__pcti, y)), q_atan)
  } else if y.truthy() {
    // atan(z) = -i*atanh(i*z)
    let (u, v) = complex_atanh(neg(y), x)
    // -%i*(u+%i*v) = v - %i*u
    sub(v, mul2(q_d__pcti, u))
  } else {
    bcons(fpatan(cdr(bigfloatp(x))))
  }
}

///|
/// atan(y/x) taking into account the quadrant.  (Also equal to
/// arg(x+%i*y).)
fn fpatan2(y : Value, x : Value) -> Value raise {
  if equal(car(x), Fix(0L)) {
    // atan(y/0) = atan(inf), but what sign?
    if equal(car(y), Fix(0L)) {
      merr("atan2: atan2(0, 0) is undefined.", [])
    } else if minusp(car(y)) {
      // We're on the negative imaginary axis, so -pi/2.
      fpquotient(float__fppi(), intofp(Fix(-2L)))
    } else {
      // The positive imaginary axis, so +pi/2
      fpquotient(float__fppi(), intofp(Fix(2L)))
    }
  } else if plusp(car(x)) {
    // x > 0.  atan(y/x) is the correct value.
    fpatan(fpquotient(y, x))
  } else if !minusp(car(y)) {
    // x < 0, and y >= 0.  We're in quadrant II or on the negative real
    // axis, so the angle we want is pi+atan(y/x).
    fpplus(float__fppi(), fpatan(fpquotient(y, x)))
  } else {
    // x < 0 and y < 0.  We're in quadrant III, so the angle we want is
    // atan(y/x)-pi.
    fpdifference(fpatan(fpquotient(y, x)), float__fppi())
  }
}

///|
fn tanbigfloat(a0 : Value) -> Value raise {
  let a = car(a0)
  fpend(
    with_special(q_fpprec, float__addi(float__prec(), 8), () => if d_bfloatp(
        a,
      ).truthy() {
      let a = cdr(d_bfloat(a))
      fpquotient(fpsin(a, t), fpsin(a, Nil))
    } else {
      list2(list1(q_p_tan), a)
    }),
  )
}

// ---------------------------------------------------------------------------
// exp

///|
/// exp(x)
///
/// For negative x, use exp(-x) = 1/exp(x)
///
/// For x > 0, exp(x) = exp(r+y) = exp(r) * exp(y), where x = r + y and
/// r = floor(x).
fn fpexp(x : Value) -> Value raise {
  if minusp(car(x)) {
    return fpquotient(fpone(), fpexp(fpabs(x)))
  }
  let r = fpintpart(x, skip_exponent_check_p=t)
  if num_lt(r, Fix(2L)) {
    fpexp1(x)
  } else {
    let s = fpexp1(fpdifference(x, intofp(r)))
    // patch for full precision %E
    fptimes_star(
      s,
      cdr(
        bigfloatp(
          with_special(
            q_fpprec,
            num_add(float__prec(), int(integer_length(r) - 1)),
            () => bcons(fpexpt(float__fpe(), r)),
          ),
        ),
      ),
    )
  }
}

///|
/// exp(x) for small x, using Taylor series.
fn fpexp1(x : Value) -> Value raise {
  let mut term = fpone()
  let mut ans = term
  let mut oans = Value::Nil
  let mut n = 1
  while !equal(ans, oans) {
    term = fpquotient(fptimes_star(x, term), intofp(int(n)))
    oans = ans
    ans = fpplus(ans, term)
    n += 1
  }
  ans
}

///|
fn n_starfpexp(a : Value) -> Value raise {
  fpend(
    with_special(q_fpprec, float__addi(float__prec(), 8), () => if d_bfloatp(
        a,
      ).truthy() {
      fpexp(cdr(bigfloatp(a)))
    } else {
      list([list1(q_mexpt), q_d__pcte, a])
    }),
  )
}

// ---------------------------------------------------------------------------
// sin, cos

///|
fn n_starfpsin(a : Value, fl : Value) -> Value raise {
  fpend(
    with_special(q_fpprec, float__addi(float__prec(), 8), () => if d_bfloatp(
        a,
      ).truthy() {
      fpsin(cdr(d_bfloat(a)), fl)
    } else if fl.truthy() {
      list2(list1(q_p_sin), a)
    } else {
      list2(list1(q_p_cos), a)
    }),
  )
}

///|
/// needed for e.g. ASIN(.123567812345678B0) with FPPREC 16, to get rid of
/// the minuscule imaginary part of the a+bi answer.
fn fparcsimp(e : Value) -> Value raise {
  if mplusp(e).truthy() &&
    cdddr(e) is Nil &&
    mtimesp(caddr(e)).truthy() &&
    cdddr(caddr(e)) is Nil &&
    d_bfloatp(cadr(caddr(e))).truthy() &&
    eq(caddr(caddr(e)), q_d__pcti) &&
    num_lt(caddr(cadr(caddr(e))), num_add(num_neg(float__prec()), Fix(2L))) {
    cadr(e)
  } else {
    e
  }
}

///|
fn sinbigfloat(x : Value) -> Value raise {
  n_starfpsin(car(x), t)
}

///|
fn cosbigfloat(x : Value) -> Value raise {
  n_starfpsin(car(x), Nil)
}

///|
/// THIS VERSION OF FPSIN COMPUTES SIN OR COS TO PRECISION FPPREC, BUT
/// CHECKS FOR THE POSSIBILITY OF CATASTROPHIC CANCELLATION DURING ARGUMENT
/// REDUCTION (E.G. SIN(N*%PI+EPSILON)).  FL is T for sin and NIL for cos.
fn fpsin(x0 : Value, fl : Value) -> Value raise {
  with_special(q_n_starcancelled, Nil, () => {
    let sign = if fl.truthy() { plusp(car(x0)) } else { true }
    let x = fpabs(x0)
    if equal(car(x), Fix(0L)) {
      return if fl.truthy() {
        intofp(Fix(0L))
      } else {
        intofp(Fix(1L))
      }
    }
    let oldprec = float__prec()
    let xt = bcons(x)
    cdr(
      bigfloatp(
        with_specials(
          [
            (q_fpprec, num_max(float__prec(), num_add(float__prec(), cadr(x)))),
            (q_n_starcancelled, Fix(0L)),
          ],
          () => {
            let xt = xt
            while true {
              let mut x = cdr(bigfloatp(xt))
              let piby2 = fpquotient(float__fppi(), intofp(Fix(2L)))
              let mut r = fpintpart(
                fpquotient(x, piby2),
                skip_exponent_check_p=t,
              )
              x = fpplus(x, fptimes_star(intofp(num_neg(r)), piby2))
              let k = symval(q_n_starcancelled)
              fpplus(x, fpminus(piby2)) |> ignore
              set(q_n_starcancelled, num_max(k, symval(q_n_starcancelled)))
              |> ignore
              if symval(q_ear_fpsincheck).truthy() {
                print(
                  list([
                    sym("*canc="),
                    symval(q_n_starcancelled),
                    sym("fpprec="),
                    float__prec(),
                    sym("oldprec="),
                    oldprec,
                  ]),
                )
                |> ignore
              }
              let canc = symval(q_n_starcancelled)
              if !num_gt(oldprec, num_sub(float__prec(), canc)) {
                r = num_rem(r, Fix(4L))
                let ri = to_int(r)
                let res = if fl.truthy() {
                  match ri {
                    0 => fpsin1(x)
                    1 => fpcos1(x)
                    2 => fpminus(fpsin1(x))
                    3 => fpminus(fpcos1(x))
                    _ => Nil
                  }
                } else {
                  match ri {
                    0 => fpcos1(x)
                    1 => fpminus(fpsin1(x))
                    2 => fpminus(fpcos1(x))
                    3 => fpsin1(x)
                    _ => Nil
                  }
                }
                return bcons(if sign { res } else { fpminus(res) })
              } else {
                set(q_fpprec, num_add(float__prec(), canc)) |> ignore
              }
            }
            Nil
          },
        ),
      ),
    )
  })
}

///|
fn fpcos1(x : Value) -> Value raise {
  fpsincos1(x, Nil)
}

///|
/// Compute SIN or COS in (0,PI/2).  FL is T for SIN, NIL for COS.
///
/// Use Taylor series
fn fpsincos1(x : Value, fl : Value) -> Value raise {
  let mut ans = if fl.truthy() { x } else { intofp(Fix(1L)) }
  let x2 = fpminus(fptimes_star(x, x))
  let mut term = ans
  let mut oans = Value::Nil
  let mut n = if fl.truthy() { 3 } else { 2 }
  while !equal(ans, oans) {
    term = fptimes_star(term, fpquotient(x2, intofp(int(n * (n - 1)))))
    oans = ans
    ans = fpplus(ans, term)
    n += 2
  }
  ans
}

///|
fn fpsin1(x : Value) -> Value raise {
  fpsincos1(x, t)
}

// ---------------------------------------------------------------------------
// log

///|
fn logbigfloat(a : Value) -> Value raise {
  if d_bfloatp(car(a)).truthy() {
    big_float_log(d_bfloat(car(a)))
  } else {
    list2(list1(q_p_log), car(a))
  }
}

///|
/// Computes the log of a bigfloat number, using the series
///
///   log(1+x) = 2*sum((x/(x+2))^(2*n+1)/(2*n+1),n,0,inf)
///
/// which converges for x > 0.  Note that FPLOG is given 1+X, not X.  To aid
/// convergence of the series, we scale 1+x until 1/e <= 1+x <= e.
fn fplog(x0 : Value) -> Value raise {
  let mut x = x0
  if !plusp(car(x)) {
    merr("fplog: argument must be positive; found: ~M", [car(x)]) |> ignore
  }
  let e = float__fpe()
  let over = fpquotient(fpone(), e)
  let mut ans = 0
  // Scale X until 1/e <= X <= E.  ANS keeps track of how many factors of E
  // were used.  Set X to NIL if X is E.  1/e itself has to count as in
  // range.
  while true {
    if equal(x, e) {
      x = Nil
      break
    } else if fplessp(x, e).truthy() && !fplessp(x, over).truthy() {
      break
    } else if fplessp(x, over).truthy() {
      x = fptimes_star(x, e)
      ans -= 1
    } else {
      ans += 1
      x = fpquotient(x, e)
    }
  }
  if x is Nil {
    return intofp(int(1 + ans))
  }
  // Prepare X for the series.  The series is for 1 + x, so get x from our
  // X.  TERM is (x/(x+2)).  X becomes (x/(x+2))^2.
  x = fpdifference(x, fpone())
  let ansv = intofp(int(ans))
  let two = intofp(Fix(2L))
  let mut term = fpquotient(x, fpplus(x, two))
  x = fpexpt(term, Fix(2L))
  // Sum the series until the sum (in ANS) doesn't change anymore.
  let mut sum = intofp(Fix(0L))
  let mut oldans = Value::Nil
  let mut n = 1
  while !equal(sum, oldans) {
    oldans = sum
    sum = fpplus(sum, fpquotient(term, intofp(int(n))))
    term = fptimes_star(term, x)
    n += 2
  }
  fpplus(ansv, fptimes_star(two, sum))
}

///|
fn mabsbigfloat(l : Value) -> Value raise {
  let r = bigfloatp(car(l))
  if r is Nil {
    list2(list1(q_mabs), car(l))
  } else {
    bcons(fpabs(cdr(r)))
  }
}
