// Port of share/stats/numstats.lisp (Mario Rodriguez Riotorto, 2006):
// numerical routines used by package 'stats'.
//
// The recursions use CL generic arithmetic on Values, as the Lisp code does.
// $test_normality computes in double floats (FLONUM) with MoonBit Doubles,
// keeping the order of every CL arithmetic form; log/exp/sqrt/expt go through
// the runtime's CL functions.

///|
/// Wilcoxon-Mann-Whitney recursion.
///
/// This recursion is used when computing exact probabilities for the
/// distribution of the rank statistic in the Wilcoxon-Mann-Whitney test,
/// specially for small samples. It's defined as
///            a(i,j,k) = a(i,j-1,j-k) + a(i-k,j-1,j-k-1)
/// Reference:
///    Klotz, Jerome (2006) 'A Computational Approach to Statistics',
///         available at www.stat.wisc.edu/~klotz/Book.pdf
fn rank_sum_recursion(i : Value, j : Value, k : Value) -> Value raise {
  match (i, j, k) {
    (Fix(i), Fix(j), Fix(k)) => Fix(share_numstats__rank_sum_fix(i, j, k))
    _ =>
      if minusp(i) || minusp(j) || minusp(k) {
        Fix(0L)
      } else if zerop(i) {
        Fix(1L)
      } else {
        num_add(
          rank_sum_recursion(i, num_sub(j, Fix(1L)), num_sub(j, k)),
          rank_sum_recursion(
            num_sub(i, k),
            num_sub(j, Fix(1L)),
            num_add(num_add(j, num_neg(k)), Fix(-1L)),
          ),
        )
      }
  }
}

///|
/// rank_sum_recursion on fixnums (the counts are bounded by the number of
/// recursive calls, so they cannot overflow).
fn share_numstats__rank_sum_fix(i : Int64, j : Int64, k : Int64) -> Int64 {
  if i < 0L || j < 0L || k < 0L {
    0L
  } else if i == 0L {
    1L
  } else {
    share_numstats__rank_sum_fix(i, j - 1L, j - k) +
    share_numstats__rank_sum_fix(i - k, j - 1L, j + -k + -1L)
  }
}

///|
/// Signed rank recursion.
///
/// This recursion is used when computing exact probabilities for the true
/// distribution of statistic in the signed rank test, specially for small
/// samples. It's defined as
///            a(i,j) = a(i,j-1) + a(i-j,j-1)
/// Reference:
///    Klotz, Jerome (2006) 'A Computational Approach to Statistics',
///         available at www.stat.wisc.edu/~klotz/Book.pdf
///    R statistical package. File signrank.c
fn signed_rank_recursion(i : Value, j : Value) -> Value raise {
  let u = num_div(num_mul(j, num_add(j, Fix(1L))), Fix(2L))
  let c = floor1(num_div(u, Fix(4L)))
  let i = if num_gt(i, c) { num_sub(u, i) } else { i }
  if minusp(i) || minusp(j) {
    Fix(0L)
  } else if zerop(i) {
    Fix(1L)
  } else {
    num_add(
      signed_rank_recursion(i, num_sub(j, Fix(1L))),
      signed_rank_recursion(num_sub(i, j), num_sub(j, Fix(1L))),
    )
  }
}

///|
/// Calculates the algebraic polynomial of order (- (length cc) 1) with
/// array of coefficients cc. Zero order coefficient is (aref cc 0).
fn swpoly(cc : Value, x : Value) -> Value raise {
  let mut ret_val = aref1(cc, 0)
  let nord = share_numstats__vector_length(cc)
  if nord > 1 {
    let mut p = num_mul(x, aref1(cc, nord - 1))
    let mut j = nord - 2
    while j != 0 {
      p = num_mul(x, num_add(p, aref1(cc, j)))
      j -= 1
    }
    ret_val = num_add(ret_val, p)
  }
  ret_val
}

///|
fn share_numstats__vector_length(v : Value) -> Int raise {
  match v {
    Vec(a) => a.data.length()
    _ => length(v)
  }
}

///|
fn share_numstats__vec(xs : Array[Double]) -> Value {
  vector(xs.map(x => Flo(x)))
}

///|
fn share_numstats__poly(cc : Value, x : Double) -> Double raise {
  to_double(swpoly(cc, Flo(x)))
}

///|
fn share_numstats__log(x : Double) -> Double raise {
  to_double(llog(Flo(x)))
}

///|
fn share_numstats__exp(x : Double) -> Double raise {
  to_double(lexp(Flo(x)))
}

///|
fn share_numstats__sqrt(x : Double) -> Double raise {
  to_double(lsqrt(Flo(x)))
}

///|
fn share_numstats__expt(x : Double, y : Double) -> Double raise {
  to_double(expt(Flo(x), Flo(y)))
}

///|
fn share_numstats__signum(n : Int) -> Double {
  if n > 0 {
    1.0
  } else if n < 0 {
    -1.0
  } else {
    0.0
  }
}

///|
/// Calculates the Shapiro-Wilk test and its significance level.
/// This is a translation from Fortran to Lisp of swilk.f, which translation
/// to C is used by the R statistical package. This is
/// Algorithm AS R94, Applied Statistics (1995), vol.44, no.4, 547-551
/// Argument 'x' is a Maxima list containing numbers. Optional argument 'n1'
/// is the number of uncensored observations.
fn d_test_normality(x : Value, n1? : Value = Nil) -> Value raise {
  let mut x = x
  if !(d_listp(x).truthy() ||
    (d_matrixp(x).truthy() && num_eq(d_length(d_first(x)), Fix(1L)))) {
    merr("First argument of 'test_normality' must be a Maxima list", [])
    |> ignore
  }
  if d_matrixp(x).truthy() {
    x = d_first(d_transpose(x))
  }
  let xl = sort_list(mapcar(e => d_float(e), rest(x)), (a, b) => num_lt(a, b))
  let n1 = if n1 is Nil { int(length(xl)) } else { n1 }
  let b = bind(q_d_numer, symval(q_d_stats_numer))
  defer unbind(b)
  let n = length(xl)
  let n2 = n / 2
  let mut w = 0.0
  let mut pw = 0.0
  // initialized data
  let z90 = 1.2816
  let z95 = 1.6449
  let z99 = 2.3263
  let zm = 1.7509
  let zss = 0.56268
  let bf1 = 0.8378
  let xx90 = 0.556
  let xx95 = 0.622
  let sqrth = 0.70711
  let small = 1.0e-19
  let pi6 = 1.909859
  let stqr = 1.047198
  // polynomial coefficients
  let g = share_numstats__vec([-2.273, 0.459])
  let c1 = share_numstats__vec([
    0.0, 0.221157, -0.147981, -2.07119, 4.434685, -2.706056,
  ])
  let c2 = share_numstats__vec([
    0.0, 0.042981, -0.293762, -1.752461, 5.682633, -3.582633,
  ])
  let c3 = share_numstats__vec([0.544, -0.39978, 0.025054, -6.714e-4])
  let c4 = share_numstats__vec([1.3822, -0.77857, 0.062767, -0.0020322])
  let c5 = share_numstats__vec([-1.5861, -0.31082, -0.083751, 0.0038915])
  let c6 = share_numstats__vec([-0.4803, -0.082676, 0.0030302])
  let c7 = share_numstats__vec([0.164, 0.533])
  let c8 = share_numstats__vec([0.1736, 0.315])
  let c9 = share_numstats__vec([0.256, -0.00635])
  let an = n.to_double()
  let ncens = num_sub(int(n), n1) // number of censored observations
  let nn2 = n / 2
  if n < 3 || n > 5000 {
    merr("Sample size must be between 3 and 5000", []) |> ignore
  }
  let range = num_sub(car(last(xl)), first(xl))
  if num_lt(range, Flo(small)) {
    merr("All observations are identical", []) |> ignore
  }
  if num_lt(n1, Fix(3L)) {
    merr("Number of uncensored observations is too small", []) |> ignore
  }
  if minusp(ncens) {
    merr(
      "Number of uncensored observations is greater than total sample size!!",
      [],
    )
    |> ignore
  }
  if plusp(ncens) && n < 20 {
    merr("Sample size is too small, and censored data are not allowed", [])
    |> ignore
  }
  let delta = to_double(num_div(ncens, Flo(an)))
  if delta > 0.8 {
    merr("Ratio of censored observations is too great (>80%)", []) |> ignore
  }
  let range = to_double(range)
  let xs : Array[Double] = []
  for e in xl.iter() {
    xs.push(to_double(e))
  }

  // calculate coefficients for statistic w
  let a = Array::make(n2 + 1, 0.0)
  if n == 3 {
    a[1] = sqrth
  } else {
    let an25 = 0.25 + an
    let mut summ2 = 0.0
    for i = 1; i <= n2; i = i + 1 {
      a[i] = to_double(
        mul2_star(
          Flo(1.414213562373095),
          simplify(
            list([
              list1(q_p_inverse_erf),
              add2_star(
                mul2_star(Flo(2.0), Flo((i.to_double() - 0.375) / an25)),
                Fix(-1L),
              ),
            ]),
          ),
        ),
      )
      summ2 = summ2 + a[i] * a[i]
    }
    summ2 = summ2 * 2.0
    let ssumm2 = share_numstats__sqrt(summ2)
    let rsn = 1.0 / share_numstats__sqrt(an)
    let a1 = share_numstats__poly(c1, rsn) - a[1] / ssumm2
    // normalize a
    let mut i1 = 0
    let mut fac = 0.0
    if n > 5 {
      i1 = 3
      let a2 = share_numstats__poly(c2, rsn) - a[2] / ssumm2
      fac = share_numstats__sqrt(
        (summ2 + a[1] * a[1] * -2.0 + a[2] * a[2] * -2.0) /
        (1.0 + a1 * a1 * -2.0 + a2 * a2 * -2.0),
      )
      a[2] = a2
    } else {
      i1 = 2
      fac = share_numstats__sqrt(
        (summ2 - 2.0 * a[1] * a[1]) / (1.0 - 2.0 * a1 * a1),
      )
    }
    a[1] = a1
    for i = i1; i <= nn2; i = i + 1 {
      a[i] = a[i] / -fac
    }
  }

  // check for correct sort order on range - scaled X
  let mut xx = xs[0] / range
  let mut sx = xx
  let mut sa = -a[1]
  let mut j = n - 1
  let mut i = 1
  while num_lt(int(i), n1) {
    let xi = xs[i] / range
    sx = sx + xi
    i = i + 1
    if i != j {
      sa = sa +
        share_numstats__signum(i - j) * a[if i < j { i } else { j }]
    }
    xx = xi
    j = j - 1
  }

  // Calculate W statistic as squared correlation
  // between data and coefficients
  sa = to_double(num_div(Flo(sa), n1))
  sx = to_double(num_div(Flo(sx), n1))
  let mut ssa = 0.0
  let mut ssx = 0.0
  let mut sax = 0.0
  let mut j = n - 1
  let mut i = 0
  while num_lt(int(i), n1) {
    let asa = if i != j {
      share_numstats__signum(i - j) * a[1 + (if i < j { i } else { j })] - sa
    } else {
      -sa
    }
    let xsx = xs[i] / range - sx
    ssa = ssa + asa * asa
    ssx = ssx + xsx * xsx
    sax = sax + asa * xsx
    j = j - 1
    i = i + 1
  }

  // w1 equals (1-w) calculated to avoid excessive rounding error
  // for W very near 1 (a potential problem in very large samples)
  let ssassx = share_numstats__sqrt(ssa * ssx)
  let w1 = (ssassx - sax) * (ssassx + sax) / (ssa * ssx)
  w = 1.0 - w1

  // calculate significance level for w
  let fin = () => {
    if n == 3 {
      pw = pi6 *
        (to_double(funcall(q_d_asin, [Flo(share_numstats__sqrt(w))])) - stqr)
      return ()
    }
    let mut y = share_numstats__log(w1)
    let xx = share_numstats__log(an)
    let mut m = 0.0
    let mut s = 0.0
    if n <= 11 {
      let gamma = share_numstats__poly(g, an)
      if y >= gamma {
        pw = small
        return ()
      }
      y = -share_numstats__log(gamma - y)
      m = share_numstats__poly(c3, an)
      s = share_numstats__exp(share_numstats__poly(c4, an))
    } else {
      // n >= 12
      m = share_numstats__poly(c5, xx)
      s = share_numstats__exp(share_numstats__poly(c6, xx))
    }
    // censoring by proportion ncens/n
    // calculate mean and sd of normal equivalent deviate of w
    if plusp(ncens) {
      let ld = -share_numstats__log(delta)
      let bf = 1.0 + xx * bf1
      let z90f = z90 +
        bf *
        share_numstats__expt(
          share_numstats__poly(c7, share_numstats__expt(xx90, xx)),
          ld,
        )
      let z95f = z95 +
        bf *
        share_numstats__expt(
          share_numstats__poly(c8, share_numstats__expt(xx95, xx)),
          ld,
        )
      let z99f = z99 +
        bf * share_numstats__expt(share_numstats__poly(c9, xx), ld)
      // regress z90F,...,z99F on normal deviates z90,...,z99 to get
      // pseudo-mean and pseudo-sd of z as the slope and intercept
      let zfm = (z90f + z95f + z99f) / 3.0
      let zsd = (z90 * (z90f - zfm) + z95 * (z95f - zfm) + z99 * (z99f - zfm)) /
        zss
      let zbar = zfm - zsd * zm
      m = m + zbar * s
      s = s * zsd
    }
    pw = 0.5 -
      0.5 *
      to_double(mfuncall(q_p_erf, list1(Flo((y - m) / (1.41421356 * s)))))
  }
  fin()

  // the result is an 'inference_result' Maxima object
  d_inference_result(
    Str("SHAPIRO - WILK TEST"),
    list([
      list1(q_mlist),
      list([list1(q_mlist), q_d_statistic, Flo(w)]),
      list([list1(q_mlist), q_d_p_value, Flo(pw)]),
    ]),
    list([list1(q_mlist), Fix(1L), Fix(2L)]),
  )
}

///|
fn init_share_numstats() -> Unit raise {

}
