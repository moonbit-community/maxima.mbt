// Port of share/contrib/binsplit/binsplit.lisp (Volker van Nek, 2014): exp,
// log, sin, asin and friends for bigfloats in Maxima, an implementation of
// the binary splitting algorithms described in
// http://www.ginac.de/CLN/binsplit.pdf .
//
// Functions at Maxima level
//
//   bs_asin(x), bs_acos(x), where 0 <= x <= 1
//   bs_atan(x), bs_acot(x)        0 <= x
//   bs_sin(x),  bs_cos(x)         0 <= x <= pi/2
//   bs_tan(x),  bs_cot(x)         0 <= x < pi/2
//   bs_exp(x)                     0 <= x < 1
//   bs_log(x)                     x > 0
//   bs_expm1(x)                   0 <= x < log(2)
//   bs_log1p(eps)                 eps > -1
//                                 x and eps are real valued bigfloats

///|
/// (ldb (byte size pos) n)
fn share_binsplit__ldb(size : Value, pos : Value, n : Value) -> Value raise {
  logand(
    ash(n, -to_int(pos)),
    num_sub(ash(int(1), to_int(size)), int(1)),
  )
}

///|
/// (let* ((fpprec (+ fpprec extra))) body)
fn[T] share_binsplit__with_extra_prec(
  extra : Value,
  body : () -> T raise,
) -> T raise {
  with_special(q_fpprec, num_add(symval(q_fpprec), extra), body)
}

///|
/// The CL single-float (log n) of an integer or ratio.
fn share_binsplit__slog(n : Value) -> Float raise {
  Float::from_double(@math.ln(to_double(n)))
}

///|
/// The CL single-float conversion of a rational.
fn share_binsplit__sfloat(n : Value) -> Float raise {
  Float::from_double(to_double(n))
}

//----------------------------------------------------------------------------
// Compute phi = asin(x) or acos(x), where 0 <= x <= 1
//      or phi = atan(x) or acot(x), where 0 <= x.

///|
fn d_bs_asin(x : Value) -> Value raise {
  bs_asincos(x, q_asin)
}

///|
fn d_bs_acos(x : Value) -> Value raise {
  bs_asincos(x, q_acos)
}

///|
fn d_bs_atan(x : Value) -> Value raise {
  bs_asincos(x, q_atan)
}

///|
fn d_bs_acot(x : Value) -> Value raise {
  bs_asincos(x, q_acot)
}

///|
fn bs_asincos(x : Value, fn_ : Value) -> Value raise {
  // phi = carg(z), where ..
  let phi = share_binsplit__with_extra_prec(int(12), () => {
    // needs testing
    let x = cdr(bigfloatp(x))
    let xx = fptimes_star(x, x)
    let one = fpone()
    let mut re_z : Value = Nil
    let mut im_z : Value = Nil
    if eq(fn_, q_asin) || eq(fn_, q_acos) {
      let y = fproot(bcons(fpdifference(one, xx)), int(2))
      if eq(fn_, q_asin) {
        // asin: .. z = sqrt(1-x^2) + %i * x
        re_z = y
        im_z = x
      } else {
        // acos: .. z = x + %i * sqrt(1-x^2)
        re_z = x
        im_z = y
      }
    } else {
      let y = fpquotient(one, fproot(bcons(fpplus(one, xx)), int(2)))
      if eq(fn_, q_atan) {
        // atan: .. z = 1/sqrt(x^2+1) + %i * x/sqrt(x^2+1)
        re_z = y
        im_z = fptimes_star(x, y)
      } else {
        // acot: .. z = x/sqrt(x^2+1) + %i * 1/sqrt(x^2+1)
        re_z = fptimes_star(x, y)
        im_z = y
      }
    }
    bcons(bs_carg1(re_z, im_z, symval(q_fpprec)))
  })
  bigfloatp(phi)
}

///|
/// Compute phi = carg(z) in quadrant I, where |z| = 1.
///
/// im(z) < 1/2: Algorithm bs-carg11 moves z along the unit circle down to
///    the real axis while counting the angular movement (Haible &
///    Papanikolaou, 2.2.8).
/// im(z) < 1/sqrt(2): phi/2 = carg(sqrt(z)).
/// im(z) = 1/sqrt(2): phi = pi/4.
/// im(z) > 1/sqrt(2): pi/2 - phi = carg(imagpart(z) + %i*realpart(z)).
fn bs_carg1(re_z : Value, im_z : Value, prec : Value) -> Value raise {
  // assumes |z| = 1, quadrant 1
  if zerop(car(fpdifference(re_z, im_z))) {
    let pi = float__fppi()
    list([car(pi), num_sub(cadr(pi), int(2))]) // pi/4
  } else if fpgreaterp(im_z, re_z).truthy() {
    // im-z > 1/sqrt(2) (i.e. phi > pi/4)
    let pi = float__fppi()
    let pi_2 = list([car(pi), one_minus(cadr(pi))])
    fpdifference(pi_2, bs_carg1(im_z, re_z, prec))
  } else {
    let mut e = 0
    let mut re_z = re_z
    let mut im_z = im_z
    // bs-carg11 needs im-z < 1/2  (i.e. phi < pi/6)
    // when im-z >= 1/2 bisect phi by taking the complex sqrt
    if !fplessp(im_z, cdr(symval(q_ear_bfhalf))).truthy() {
      let (r, i) = complex_sqrt(bcons(re_z), bcons(im_z))
      re_z = r
      im_z = i
      e = 1
    }
    let phi = bs_carg11(list([re_z, im_z]), prec)
    list([car(phi), num_add(cadr(phi), int(e))])
  }
}

///|
/// assumes |z| = 1, 0 < Re(z) <= 1, 0 <= Im(z) < 1/2
fn bs_carg11(z : Value, prec : Value) -> Value raise {
  let one = fpone()
  let mut z = z
  let mut phi = list([int(0), int(0)])
  let mut im_z = cadr(z)
  // stop when im-z = 0 within current prec
  while fpgreaterp(fpplus(one, im_z), one).truthy() {
    let k = num_neg(cadr(im_z)) // im-z < 2^-k
    let u = share_binsplit__ldb(k, num_sub(prec, k), car(im_z)) // first k significant mantissa bit
    let e = complex_exp__pcti_staru_sl2_hat2k(num_neg(u), k, prec)
    z = complex_fptimes_star(z, e)
    let alpha = intofp(u)
    let alpha = list([car(alpha), num_sub(cadr(alpha), num_mul(int(2), k))])
    phi = fpplus(phi, alpha)
    im_z = cadr(z)
  }
  phi
}

///|
/// compute exp(%i*u/2^2k) where u < 2^k, integer u,k
fn complex_exp__pcti_staru_sl2_hat2k(
  u : Value,
  k : Value,
  prec : Value,
) -> Value raise {
  if num_eq(int(0), u) {
    list([fpone(), list([int(0), int(0)])])
  } else {
    let z = num_mul(int(2), k)
    let kk = k // see (**) below why k is param for bs-exp-u/2^z-series-size
    complex_exp__pcti_staru_sl2_hatz(u, z, kk, prec)
  }
}

///|
/// u is integer or complex with integer parts
fn split_bs_exp_u_sl2_hatz(
  i : Value,
  j : Value,
  u : Value,
  z : Value,
) -> (Value, Value, Value, Value) raise {
  let mut pp : Value = Nil
  let mut qq : Value = Nil
  let mut zz : Value = Nil
  let mut tt : Value = Nil
  if num_eq(num_sub(j, i), int(1)) {
    if num_eq(i, int(0)) {
      pp = int(1)
      qq = int(1)
      zz = int(0)
      tt = int(1)
    } else {
      pp = u
      qq = i
      zz = z
      tt = pp
    }
  } else {
    let m = ash(num_add(i, j), -1)
    let (tl, zl, ql, pl) = split_bs_exp_u_sl2_hatz(i, m, u, z)
    let (tr, zr, qr, pr) = split_bs_exp_u_sl2_hatz(m, j, u, z)
    pp = num_mul(pl, pr)
    qq = num_mul(ql, qr)
    zz = num_add(zl, zr)
    tt = num_mul(qr, tl)
    tt = if complexp(u) {
      complex(
        ash(realpart(tt), to_int(zr)),
        i=ash(imagpart(tt), to_int(zr)),
      )
    } else {
      ash(tt, to_int(zr))
    }
    tt = num_add(tt, num_mul(pl, tr))
  }
  (tt, zz, qq, pp)
}

///|
fn complex_fptimes_star(a : Value, b : Value) -> Value raise {
  let x1 = car(a)
  let y1 = cadr(a)
  let x2 = car(b)
  let y2 = cadr(b)
  list([
    fpdifference(fptimes_star(x1, x2), fptimes_star(y1, y2)),
    fpplus(fptimes_star(x1, y2), fptimes_star(x2, y1)),
  ])
}

///|
fn complex_fpsquare(a : Value) -> Value raise {
  let x = car(a)
  let y = cadr(a)
  let xy = fptimes_star(x, y)
  list([
    fpdifference(fptimes_star(x, x), fptimes_star(y, y)),
    list([car(xy), one_plus(cadr(xy))]),
  ])
}

//----------------------------------------------------------------------------
// Compute sin(x), cos(x), tan(x), cot(x), where 0 <= x <= %pi/2

///|
fn d_bs_sin(x : Value) -> Value raise {
  bs_sincos(x, q_sin)
}

///|
fn d_bs_cos(x : Value) -> Value raise {
  bs_sincos(x, q_cos)
}

///|
fn d_bs_tan(x : Value) -> Value raise {
  bs_sincos(x, q_tan)
}

///|
fn d_bs_cot(x : Value) -> Value raise {
  bs_sincos(x, q_cot)
}

///|
/// 0 <= x <= pi/2
fn bs_sincos(x : Value, fn_ : Value) -> Value raise {
  let xx = cdr(x)
  if num_eq(int(0), car(xx)) ||
    num_lt(cadr(xx), num_neg(symval(q_fpprec))) {
    // x is zero within current prec
    return if eql(fn_, q_sin) {
      xx
    } else if eql(fn_, q_cos) {
      intofp(int(1))
    } else if eql(fn_, q_tan) {
      xx
    } else if eql(fn_, q_cot) {
      merror(Str("attempted quotient by zero."), Nil)
    } else {
      Nil
    }
  }
  let pi_1 = float__fppi()
  let pi_2 = list([car(pi_1), one_minus(cadr(pi_1))])
  let dx = fpdifference(pi_2, xx)
  if num_eq(int(0), car(dx)) || num_lt(cadr(dx), num_neg(symval(q_fpprec))) {
    // x is pi/2 within current prec
    return if eql(fn_, q_sin) {
      intofp(int(1))
    } else if eql(fn_, q_cos) {
      dx
    } else if eql(fn_, q_tan) {
      merror(Str("attempted quotient by zero."), Nil)
    } else if eql(fn_, q_cot) {
      dx
    } else {
      Nil
    }
  }
  let res = share_binsplit__with_extra_prec(int(12), () => {
    // needs testing
    let x = cdr(bigfloatp(x))
    bcons({
      let (re, im) = bs_exp__pcti_starx_mv(x, symval(q_fpprec))
      if eq(fn_, q_sin) {
        im
      } else if eq(fn_, q_cos) {
        re
      } else if eq(fn_, q_tan) {
        fpquotient(im, re)
      } else if eq(fn_, q_cot) {
        fpquotient(re, im)
      } else {
        Nil
      }
    })
  })
  bigfloatp(res)
}

///|
/// The primary value of BS-EXP-%I*X.
fn bs_exp__pcti_starx(x : Value, prec : Value) -> Value raise {
  bs_exp__pcti_starx_mv(x, prec).0
}

///|
/// BS-EXP-%I*X returns the real and imaginary part of exp(%i*x) as two
/// values. Assumes 0 <= x <= pi/2.
fn bs_exp__pcti_starx_mv(x : Value, prec : Value) -> (Value, Value) raise {
  let mut mant = car(x)
  let mut e = cadr(x)
  let mut acc = list([intofp(int(1)), list([int(0), int(0)])]) // complex-(1,0)
  let mut x_2 = false
  if fpgreaterp(x, floattofp(Flo(3.141592653589793 / 4.0))).truthy() {
    // is x > pi/4 ?
    e = one_minus(e) // x <-- x/2
    x_2 = true
  }
  // now x <= pi/4 (the algorithm needs x < 1)
  let mut k = int(0)
  let mut nr = int(1)
  let mut pos1 = int(1)
  let mut pos2 = int(1)
  while !num_eq(int(0), pos2) {
    pos2 = num_sub(prec, num_add(pos1, e))
    if num_lt(pos2, int(0)) {
      mant = ash(mant, to_int(num_neg(pos2)))
      pos2 = int(0)
    }
    let u = share_binsplit__ldb(nr, pos2, mant)
    let tmp = complex_exp__pcti_staru_sl2_hat2_hatk(u, k, prec)
    acc = complex_fptimes_star(acc, tmp)
    nr = pos1
    k = one_plus(k)
    pos1 = ash(pos1, 1)
  }
  if x_2 {
    acc = complex_fpsquare(acc) // exp(%i*x) = exp(%i*x/2)^2
  }
  (car(acc), cadr(acc))
}

///|
/// compute exp(%i*u/2^2^k) where u < 2^2^(k-1) resp. 2^-1 for k=0, integer
/// u,k
fn complex_exp__pcti_staru_sl2_hat2_hatk(
  u : Value,
  k : Value,
  prec : Value,
) -> Value raise {
  if num_eq(int(0), u) {
    list([fpone(), list([int(0), int(0)])])
  } else {
    let z = ash(int(1), to_int(k))
    // param for bs-exp-u/2^z-series-size, see (*)
    let kk = if num_eq(k, int(0)) {
      num_div(int(1), int(2))
    } else {
      ash(int(1), to_int(one_minus(k)))
    }
    complex_exp__pcti_staru_sl2_hatz(u, z, kk, prec)
  }
}

///|
fn complex_exp__pcti_staru_sl2_hatz(
  u : Value,
  z : Value,
  kk : Value,
  prec : Value,
) -> Value raise {
  let nr = bs_exp_u_sl2_hatz_series_size(kk, prec)
  let mut u = u
  let mut z = z
  let mut i = 0
  while !logbitp(i, u) {
    i = i + 1
  }
  u = ash(u, -i)
  z = num_sub(z, int(i))
  let (tt, zz, qq, _) = split_bs_exp_u_sl2_hatz(
    int(0),
    one_plus(nr),
    complex(int(0), i=u),
    z,
  )
  let qq = intofp(qq)
  let x = fpquotient(intofp(realpart(tt)), qq)
  let y = fpquotient(intofp(imagpart(tt)), qq)
  let x = list([car(x), num_sub(cadr(x), zz)])
  let y = list([car(y), num_sub(cadr(y), zz)])
  list([x, y])
}

//----------------------------------------------------------------------------
// exp(x)-1 for 0 <= x < log(2)
//
// x = mantissa*2^e = 2^(e-1) + ... where e <= 0
//
// exp(x) = 1 + x + x^2/2! + ... = 1 + 2^(e-1) + ...
//
// exp(x)-1 looses |e-1| bits precision

///|
fn d_bs_expm1(x : Value) -> Value raise {
  bs_expm1(x)
}

///|
/// 0 <= x < log(2)
fn bs_expm1(x : Value) -> Value raise {
  let x = bigfloatp(x)
  let extra = one_plus(num_neg(caddr(x)))
  let res = share_binsplit__with_extra_prec(extra, () => bcons(
    fpdifference(cdr(bs_exp(x)), fpone()),
  ))
  bigfloatp(res)
}

//----------------------------------------------------------------------------
// exp(x), real 0 <= x < 1

///|
fn d_bs_exp(x : Value) -> Value raise {
  bs_exp(x)
}

///|
/// assume 0 <= x < 1
fn bs_exp(x : Value) -> Value raise {
  let exp1 = share_binsplit__with_extra_prec(int(12), () => {
    // needs testing
    let x = cdr(bigfloatp(x))
    let mut mant = car(x)
    let e = cadr(x)
    let mut res = fpone()
    let mut nr = int(1) // nr of extracted bits
    let mut k = int(0)
    let mut pos1 = int(1)
    let mut pos2 = int(1)
    while !num_eq(int(0), pos2) {
      pos2 = num_sub(symval(q_fpprec), num_add(pos1, e))
      if num_lt(pos2, int(0)) {
        mant = ash(mant, to_int(num_neg(pos2)))
        pos2 = int(0)
      }
      let u = share_binsplit__ldb(nr, pos2, mant)
      res = fptimes_star(
        res,
        bs_exp_u_sl2_hat2_hatk(u, k, symval(q_fpprec)),
      )
      nr = pos1
      k = one_plus(k)
      pos1 = ash(pos1, 1)
    }
    bcons(res)
  })
  bigfloatp(exp1)
}

///|
/// compute exp(u/2^2^k) where u < 2^2^(k-1), integer u,k (k >= 0)
fn bs_exp_u_sl2_hat2_hatk(u : Value, k : Value, prec : Value) -> Value raise {
  if num_eq(int(0), u) {
    fpone()
  } else {
    let z = ash(int(1), to_int(k))
    // param for bs-exp-u/2^z-series-size, see (*)
    let kk = if num_eq(k, int(0)) {
      num_div(int(1), int(2))
    } else {
      ash(int(1), to_int(one_minus(k)))
    }
    bs_exp_u_sl2_hatz(u, z, kk, prec)
  }
}

///|
/// (*) End the Taylor-series when (u/2^2^k)^i/i! < 1/2^fpprec.
///
/// u might not fit into a float. Use bound u < 2^2^(k-1), i.e. u/2^2^k <
/// 1/2^2^(k-1).
///
/// So end when i!*(2^2^(k-1))^i > 2^fpprec or
///
/// log(i!) + i * 2^(k-1)*log(2) = sum(log(n) + 2^(k-1)*log(2), n,1,i) >
/// fpprec * log(2).
///
/// (The Lisp code computes in single-float: (log 2) of an integer is a
/// single-float.)
fn bs_exp_u_sl2_hatz_series_size(kk : Value, prec : Value) -> Value raise {
  let log2 = share_binsplit__slog(int(2))
  let kk = share_binsplit__sfloat(kk) * log2
  let mut n = 1
  let mut acc : Float = 0.0
  let lim = share_binsplit__sfloat(prec) * log2
  while !(acc > lim) {
    acc = acc + (share_binsplit__slog(int(n)) + kk)
    n = n + 1
  }
  int(n)
}

///|
/// compute exp(u/2^z), integer u,z
fn bs_exp_u_sl2_hatz(u : Value, z : Value, kk : Value, prec : Value) -> Value raise {
  let mut u = u
  let mut z = z
  let mut i = 0
  while !logbitp(i, u) {
    i = i + 1
  }
  u = ash(u, -i)
  z = num_sub(z, int(i))
  let nr = bs_exp_u_sl2_hatz_series_size(kk, prec)
  let (tt, zz, qq, _) = split_bs_exp_u_sl2_hatz(int(0), one_plus(nr), u, z)
  let tt_qq = fpquotient(intofp(tt), intofp(qq))
  list([car(tt_qq), num_sub(cadr(tt_qq), zz)])
}

//----------------------------------------------------------------------------
// Compute log(1 + eps), real eps > -1

///|
fn d_bs_log1p(eps : Value) -> Value raise {
  bs_log1p(eps)
}

///|
/// eps = x - 1
fn bs_log1p(eps : Value) -> Value raise {
  let eps = bigfloatp(eps)
  let res = {
    let extra = one_plus(num_neg(caddr(eps))) // give |e-1| extra bits
    share_binsplit__with_extra_prec(extra, () => {
      // x = 1 + eps = m*2^e = 2^(e-1) + ...
      let x = bcons(fpplus(cdr(bigfloatp(eps)), fpone()))
      bs_log(x)
    })
  }
  bigfloatp(res)
}

//----------------------------------------------------------------------------
// Compute log(x), real x > 0
//
// Use log(x) = log(x/2^k) + k*log(2), where x/2^k < 1.

///|
fn d_bs_log(x : Value) -> Value raise {
  bs_log(x)
}

///|
/// assume x > 0
fn bs_log(x : Value) -> Value raise {
  let res = share_binsplit__with_extra_prec(int(12), () => {
    // needs more testing
    let x = cdr(bigfloatp(x))
    let m = car(x)
    let mut k = cadr(x) // mantissa, exponent
    with_special(q_d_float2bf, t, () => {
      let mut x = list([m, int(0)]) // now x = 0 or 1/2 <= x < 1
      // choose k so that |x - 1| is as small as possible:
      if fplessp(x, floattofp(Flo(2.0 / 3.0))).truthy() {
        x = list([m, int(1)])
        k = one_minus(k)
      }
      // now |x - 1| <= 1/3 < 1/2
      let lgx = bs_log1(x, symval(q_fpprec))
      bcons(
        if num_eq(k, int(0)) {
          lgx
        } else {
          fpplus(lgx, fptimes_star(intofp(k), comp_log2()))
        },
      )
    })
  })
  bigfloatp(res)
}

///|
/// assume |x - 1| < 1/2
fn bs_log1(x : Value, prec : Value) -> Value raise {
  let one = fpone()
  let mut x = x
  let mut y = list([int(0), int(0)])
  let mut pos = int(1)
  while !num_eq(int(0), pos) {
    let mut dx = fpdifference(x, one)
    let posp = fpposp(dx).truthy()
    dx = fpabs(dx)
    if !fpposp(dx).truthy() {
      return y
    }
    let k = num_neg(cadr(dx)) // |x - 1| < 2^-k
    let m_len = integer_length(car(dx)) // m-len isn't always prec
    pos = num_sub(int(m_len), k)
    let mut u = share_binsplit__ldb(k, pos, car(dx)) // first k significant mantissa bits
    u = if posp { u } else { num_neg(u) }
    let e = bs_exp_u_sl2_hat2k(num_neg(u), k, prec)
    x = fptimes_star(x, e)
    let z = intofp(u)
    let z = list([car(z), num_sub(cadr(z), num_mul(int(2), k))])
    y = fpplus(y, z)
  }
  y
}

///|
/// compute exp(u/2^2k) where u < 2^k, integer u,k (k >= 0)
///
/// (**) End the Taylor-series when (u/2^(2*k))^i/i! < 1/2^fpprec.
///
/// u might not fit into a float. Use bound u < 2^k, i.e. u/2^(2*k) < 1/2^k.
///
/// So end when i!*(2^k)^i > 2^fpprec or
///
/// log(i!) + i * k*log(2) = sum(log(n) + k*log(2), n,1,i) > fpprec * log(2).
fn bs_exp_u_sl2_hat2k(u : Value, k : Value, prec : Value) -> Value raise {
  if num_eq(int(0), u) {
    fpone()
  } else {
    // k is param for bs-exp-u/2^z-series-size, see (**)
    bs_exp_u_sl2_hatz(u, num_mul(int(2), k), k, prec)
  }
}
