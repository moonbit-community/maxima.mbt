// Port of share/distrib/numdistrib.lisp (Mario Rodriguez Riotorto,
// 2005-2009): a set of numerical routines used by package distrib.mac.
//
// The Lisp code computes in double floats (FLONUM); the port does the same
// with MoonBit Doubles, keeping the association order of every CL n-ary
// arithmetic form so that results (and random variates) are bit-identical.
// Parameters declared FLONUM / INTEGER are type-checked, as SBCL does.
// The persistent generator state kept by the Lisp code in special
// variables (*rnormal-iset*, *rbeta-...*, *rbin-...*, *rpos-...*,
// *rhyp-...*) is kept in a private record.

///|
extern "C" fn share_numdistrib__c_log(x : Double) -> Double = "log"

///|
extern "C" fn share_numdistrib__c_exp(x : Double) -> Double = "exp"

///|
/// (log x) of a double.
fn share_numdistrib__log(x : Double) -> Double raise {
  if x > 0.0 {
    share_numdistrib__c_log(x)
  } else {
    to_double(llog(Flo(x)))
  }
}

///|
/// (log n) of an integer: SBCL returns a single-float.
fn share_numdistrib__log_int(n : Int64) -> Double raise {
  if n > 0L {
    Float::from_double(share_numdistrib__c_log(n.to_double())).to_double()
  } else {
    to_double(llog(Fix(n)))
  }
}

///|
fn share_numdistrib__exp(x : Double) -> Double {
  share_numdistrib__c_exp(x)
}

///|
/// (sqrt x) of a double.
fn share_numdistrib__sqrt(x : Double) -> Double raise {
  if x >= 0.0 {
    x.sqrt()
  } else {
    to_double(lsqrt(Flo(x)))
  }
}

///|
/// (expt x n), double base and integer power.
fn share_numdistrib__expti(x : Double, n : Int64) -> Double raise {
  to_double(expt(Flo(x), Fix(n)))
}

///|
/// (expt x y), double base and power.
fn share_numdistrib__exptf(x : Double, y : Double) -> Double raise {
  to_double(expt(Flo(x), Flo(y)))
}

///|
/// CL (round x) of a double: to the nearest integer, ties to even.
fn share_numdistrib__round(x : Double) -> Int64 {
  let f = x.floor()
  let diff = x - f
  let fi = f.to_int64()
  if diff < 0.5 {
    fi
  } else if diff > 0.5 {
    fi + 1L
  } else if fi % 2L == 0L {
    fi
  } else {
    fi + 1L
  }
}

///|
/// CL (floor x) of a double.
fn share_numdistrib__floor(x : Double) -> Int64 {
  x.floor().to_int64()
}

///|
/// A FLONUM-declared parameter.
fn share_numdistrib__fl(v : Value) -> Double raise {
  match v {
    Flo(d) => d
    _ => raise type_error(v, "double-float")
  }
}

///|
/// An INTEGER-declared parameter.
fn share_numdistrib__int(v : Value) -> Int64 raise {
  match v {
    Fix(n) => n
    _ => raise type_error(v, "integer")
  }
}

///|
/// ($random 1.0)
fn share_numdistrib__random() -> Double raise {
  to_double(d_random(Flo(1.0)))
}

///|
/// Common tail of the rnd* functions: if SS=0, returns one variate,
/// otherwise a maxima list of SS variates.
fn share_numdistrib__sample(
  ss : Value,
  one : () -> Value raise,
) -> Value raise {
  if num_eq(ss, Fix(0L)) {
    one()
  } else {
    let mut sample : Value = Nil
    let n = to_int64(ss)
    for _ in 0L..<n {
      sample = cons(one(), sample)
    }
    cons(list2(q_mlist, q_simp), sample)
  }
}

///|
/// Persistent state of the generators.
priv struct ShareNumdistribState {
  // normal (Box-Mueller)
  mut rnormal_iset : Int
  mut rnormal_gset : Double
  // beta (Cheng)
  mut rbeta_olda : Double
  mut rbeta_oldb : Double
  mut rbeta_alpha : Double
  mut rbeta_beta : Double
  mut rbeta_gamma : Double
  mut rbeta_delta : Double
  mut rbeta_k1 : Double
  mut rbeta_k2 : Double
  mut rbeta_a : Double
  mut rbeta_b : Double
  // binomial (Kachitvichyanukul-Schmeiser)
  mut rbin_psave : Double
  mut rbin_nsave : Int64
  mut rbin_m : Int64
  mut rbin_xnp : Double
  mut rbin_p : Double
  mut rbin_q : Double
  mut rbin_ffm : Double
  mut rbin_xnpq : Double
  mut rbin_fm : Int64
  mut rbin_xm : Double
  mut rbin_xl : Double
  mut rbin_xr : Double
  mut rbin_c : Double
  mut rbin_al : Double
  mut rbin_xll : Double
  mut rbin_xlr : Double
  mut rbin_p1 : Double
  mut rbin_p2 : Double
  mut rbin_p3 : Double
  mut rbin_p4 : Double
  mut rbin_qn : Double
  mut rbin_r : Double
  mut rbin_g : Double
  // Poisson (Ahrens-Dieter)
  mut rpos_muold : Double
  mut rpos_muprev : Double
  mut rpos_s : Double
  mut rpos_l : Int64
  mut rpos_d : Double
  mut rpos_p0 : Double
  mut rpos_omega : Double
  mut rpos_b1 : Double
  mut rpos_b2 : Double
  mut rpos_c : Double
  mut rpos_c0 : Double
  mut rpos_c1 : Double
  mut rpos_c2 : Double
  mut rpos_c3 : Double
  mut rpos_m : Int64
  mut rpos_p : Double
  mut rpos_q : Double
  rpos_pp : Array[Double]
  // hypergeometric (Kachitvichyanukul-Schmeiser)
  mut rhyp_n1s : Int64
  mut rhyp_n2s : Int64
  mut rhyp_ks : Int64
  mut rhyp_k : Int64
  mut rhyp_n1 : Int64
  mut rhyp_n2 : Int64
  mut rhyp_m : Double
  mut rhyp_minjx : Int64
  mut rhyp_maxjx : Int64
  mut rhyp_tn : Int64
  mut rhyp_a : Double
  mut rhyp_d : Double
  mut rhyp_s : Double
  mut rhyp_w : Double
  mut rhyp_xl : Double
  mut rhyp_xr : Double
  mut rhyp_kl : Double
  mut rhyp_kr : Double
  mut rhyp_lamdl : Double
  mut rhyp_lamdr : Double
  mut rhyp_p1 : Double
  mut rhyp_p2 : Double
  mut rhyp_p3 : Double
  // whether *rhyp-p3* and friends (case III) have been set
  mut rhyp_h2pe_bound : Bool
}

///|
let share_numdistrib__st : ShareNumdistribState = {
  rnormal_iset: 0,
  rnormal_gset: 0.0,
  rbeta_olda: -1.0,
  rbeta_oldb: -1.0,
  rbeta_alpha: 0.0,
  rbeta_beta: 0.0,
  rbeta_gamma: 0.0,
  rbeta_delta: 0.0,
  rbeta_k1: 0.0,
  rbeta_k2: 0.0,
  rbeta_a: 0.0,
  rbeta_b: 0.0,
  rbin_psave: -1.0,
  rbin_nsave: -1L,
  rbin_m: 0L,
  rbin_xnp: 0.0,
  rbin_p: 0.0,
  rbin_q: 0.0,
  rbin_ffm: 0.0,
  rbin_xnpq: 0.0,
  rbin_fm: 0L,
  rbin_xm: 0.0,
  rbin_xl: 0.0,
  rbin_xr: 0.0,
  rbin_c: 0.0,
  rbin_al: 0.0,
  rbin_xll: 0.0,
  rbin_xlr: 0.0,
  rbin_p1: 0.0,
  rbin_p2: 0.0,
  rbin_p3: 0.0,
  rbin_p4: 0.0,
  rbin_qn: 0.0,
  rbin_r: 0.0,
  rbin_g: 0.0,
  rpos_muold: 0.0,
  rpos_muprev: 0.0,
  rpos_s: 0.0,
  rpos_l: 0L,
  rpos_d: 0.0,
  rpos_p0: 0.0,
  rpos_omega: 0.0,
  rpos_b1: 0.0,
  rpos_b2: 0.0,
  rpos_c: 0.0,
  rpos_c0: 0.0,
  rpos_c1: 0.0,
  rpos_c2: 0.0,
  rpos_c3: 0.0,
  rpos_m: 0L,
  rpos_p: 0.0,
  rpos_q: 0.0,
  rpos_pp: Array::make(35, 0.0),
  rhyp_n1s: -1L,
  rhyp_n2s: -1L,
  rhyp_ks: -1L,
  rhyp_k: 0L,
  rhyp_n1: 0L,
  rhyp_n2: 0L,
  rhyp_m: 0.0,
  rhyp_minjx: 0L,
  rhyp_maxjx: 0L,
  rhyp_tn: 0L,
  rhyp_a: 0.0,
  rhyp_d: 0.0,
  rhyp_s: 0.0,
  rhyp_w: 0.0,
  rhyp_xl: 0.0,
  rhyp_xr: 0.0,
  rhyp_kl: 0.0,
  rhyp_kr: 0.0,
  rhyp_lamdl: 0.0,
  rhyp_lamdr: 0.0,
  rhyp_p1: 0.0,
  rhyp_p2: 0.0,
  rhyp_p3: 0.0,
  rhyp_h2pe_bound: false,
}

// Incomplete gamma and beta and related functions

///|
/// Natural logarithm of the gamma function. This function is called from
/// some numerical routines below.
fn lngamma(p : Value) -> Value raise {
  simplify(list2(list1(q_p_log_gamma), p))
}

///|
fn share_numdistrib__lngamma(p : Double) -> Double raise {
  to_double(lngamma(Flo(p)))
}

///|
///  Natural logarithm of the beta function
///  Conditions: 0<p,q<1.0e302
fn lnbeta(p : Value, q : Value) -> Value raise {
  let a = lngamma(p)
  let b = lngamma(q)
  num_add(num_add(a, b), num_neg(lngamma(num_add(p, q))))
}

///|
/// Lower regularized gamma incomplete. This function is called from
/// some numerical routines below.
fn igamma(x : Value, p : Value) -> Value raise {
  num_sub(
    Flo(1.0),
    simplify(list3(list1(q_p_gamma_incomplete_regularized), p, x)),
  )
}

///|
fn share_numdistrib__igamma(x : Double, p : Double) -> Double raise {
  to_double(igamma(Flo(x), Flo(p)))
}

///|
///  Returns incomplete beta regularized in float format.
///  Conditions: 0<=x<=1; a, b>0
fn ibeta(x : Value, a : Value, b : Value) -> Value raise {
  share_numdistrib__fl(x) |> ignore
  share_numdistrib__fl(a) |> ignore
  share_numdistrib__fl(b) |> ignore
  with_special(q_d_numer, t, () => simplify(
    list([list1(q_p_beta_incomplete_regularized), a, b, x]),
  ))
}

///|
///  Inverse of the incomplete beta function.
///  Reference:
///     algorithm as 109 appl. statist. (1977), vol.26, no.1
///  Comments: Translated from Fortran.
///  Conditions: 0<x<1; p,q>0
fn iibeta(x : Value, p : Value, q : Value) -> Value raise {
  let x = share_numdistrib__fl(x)
  let p = share_numdistrib__fl(p)
  let q = share_numdistrib__fl(q)
  let sae = -300.0
  let zero = 0.0
  let one = 1.0
  let two = 2.0
  let three = 3.0
  let four = 4.0
  let five = 5.0
  let six = 6.0
  let beta = to_double(lnbeta(Flo(p), Flo(q)))
  let fpu = share_numdistrib__exptf(10.0, sae)
  let mut xiibeta = x
  // change tail if necessary
  let (a, pp, qq, indx) = if x <= 0.5 {
    (x, p, q, false)
  } else {
    (one - x, q, p, true)
  }
  // calculate the initial approximation
  let mut r = share_numdistrib__sqrt(-share_numdistrib__log(a * a))
  let mut y = r +
    -((2.30753 + 0.27061 * r) / (one + (0.99229 + 0.04481 * r) * r))
  let mut tt = 0.0
  if pp > one && qq > one {
    r = (y * y + -three) / six
    let s = one / (pp + pp + -one)
    tt = one / (qq + qq + -one)
    let h = two / (s + tt)
    let w = y * share_numdistrib__sqrt(h + r) / h +
      -((tt - s) * (r + five / six + -two / (three * h)))
    xiibeta = pp / (pp + qq * share_numdistrib__exp(w + w))
  } else {
    r = qq + qq
    tt = one / (9.0 * qq)
    tt = r *
      share_numdistrib__expti(one + -tt + y * share_numdistrib__sqrt(tt), 3L)
    if tt <= zero {
      xiibeta = one -
        share_numdistrib__exp(
          (share_numdistrib__log((one - a) * qq) + beta) / qq,
        )
    } else {
      tt = (four * pp + r + -two) / tt
      if tt <= one {
        xiibeta = share_numdistrib__exp(
          (share_numdistrib__log(a * pp) + beta) / pp,
        )
      } else {
        xiibeta = one + -(two / (tt + one))
      }
    }
  }
  // solve for x by a modified newton-raphson method,
  // using the function ibeta
  r = one - pp
  tt = one - qq
  let mut yprev = zero
  let mut sq = one
  let mut prev = one
  if xiibeta < 1.0e-4 {
    xiibeta = 1.0e-4
  }
  if xiibeta > 0.9999 {
    xiibeta = 0.9999
  }
  let iex = {
    let v = -5.0 / share_numdistrib__expti(pp, 2L) +
      -(one / share_numdistrib__exptf(a, 0.2)) +
      -13.0
    if v >= sae {
      v
    } else {
      sae
    }
  }
  let acu = share_numdistrib__exptf(10.0, iex)
  let mut tx = 0.0
  let mut g = 0.0
  let mut lbl = 7
  while true {
    match lbl {
      7 => {
        y = to_double(ibeta(Flo(xiibeta), Flo(pp), Flo(qq)))
        let xin = xiibeta
        y = (y - a) *
          share_numdistrib__exp(
            beta +
            r * share_numdistrib__log(xin) +
            tt * share_numdistrib__log(one - xin),
          )
        if y * yprev <= zero {
          prev = if sq >= fpu { sq } else { fpu }
        }
        g = one
        lbl = 9
      }
      9 => {
        let adj = g * y
        sq = adj * adj
        if sq >= prev {
          lbl = 10
          continue
        }
        tx = xiibeta - adj
        if tx >= zero && tx <= one {
          lbl = 11
          continue
        }
        lbl = 10
      }
      10 => {
        g = g / three
        lbl = 9
      }
      11 => {
        if prev <= acu {
          break
        }
        if y * y <= acu {
          break
        }
        if tx == zero || tx == one {
          lbl = 10
          continue
        }
        if tx == xiibeta {
          break
        }
        xiibeta = tx
        yprev = y
        lbl = 7
      }
      _ => break
    }
  }
  Flo(if indx { one - xiibeta } else { xiibeta })
}

///|
///  Inverse of the incomplete gamma function.
///  Comments: solves by the partition method the
///            equation g(x)=0, where g(x)=igamma(x,p)-y
///            This procedure is accurate about 14 significant
///            digits except for small regions for x is in the vicinity of
///            0 and 1.
///  Conditions: 0<x<1; p>0
fn iigamma(x : Value, p : Value) -> Value raise {
  let x = share_numdistrib__fl(x)
  let p = share_numdistrib__fl(p)
  let mut a = 0.0
  let mut b = 0.0
  let mut ga = 100.0
  let mut gb = 100.0
  let err = 1.0e-16
  let mut i = 0L
  while !(ga * gb <= 0.0) {
    a = share_numdistrib__expti(1.5, i) - 1.0
    b = share_numdistrib__expti(1.5, i + 1L) - 1.0
    ga = share_numdistrib__igamma(a, p) - x
    gb = share_numdistrib__igamma(b, p) - x
    i += 1L
  }
  // now we know the solution is in [a, b]
  if ga.abs() < err {
    Flo(a)
  } else if gb.abs() < err {
    Flo(b)
  } else {
    while true {
      let m = (a + b) / 2.0
      if m == a || m == b {
        return Flo(m)
      }
      let gm = share_numdistrib__igamma(m, p) - x
      if gm.abs() < err {
        return Flo(m)
      }
      if ga * gm <= 0.0 {
        b = m
        gb = gm
      } else {
        a = m
        ga = gm
      }
    }
    Nil
  }
}

// Numerical routines for the noncentral chi2

///|
/// Cumulative probability of the noncentral chi-square distribution.
/// Reference:
///    Ding, C. G. (1992)
///    Algorithm AS275: Computing the non-central chi-squared
///    distribution function. Appl.Statist., 41, 478-482.
/// Comments: This is a translation of the C code in the R program.
/// Conditions: x>0; f>0 (degrees of freedom) ; theta>0 (non centrality
/// param.)
fn cdfnchi2(
  x : Value,
  f : Value,
  theta : Value,
  errmax : Value,
  reltol : Value,
  itrmax : Value,
) -> Value raise {
  let x = share_numdistrib__fl(x)
  let f = share_numdistrib__fl(f)
  let theta = share_numdistrib__fl(theta)
  let errmax = share_numdistrib__fl(errmax)
  let reltol = share_numdistrib__fl(reltol)
  let itrmax = share_numdistrib__fl(itrmax)
  if theta < 80.0 {
    let mut sum = 0.0
    let lamda = 0.5 * theta
    let mut i = 0L
    let mut pr = share_numdistrib__exp(-lamda)
    while i != 100L {
      sum = sum +
        pr * share_numdistrib__igamma(0.5 * x, 0.5 * f + i.to_double())
      i += 1L
      pr = pr * (lamda / i.to_double())
    }
    Flo(sum)
  } else {
    let dbl_epsilon = 1.77635683940025e-15
    let dbl_min_exp = -707.7032713517042 // ln(2) * DBL_MIN_EXP
    let lam = 0.5 * theta
    let mut lamsml = -lam < dbl_min_exp
    let mut lu = -1.0
    let mut l_lam = -1.0
    let mut l_x = -1.0
    let mut u = 1.0
    let mut v = 1.0
    let mut x2 = 1.0
    let mut f2 = 1.0
    let mut f_x_2n = 1.0
    let mut tt = 1.0
    let mut lt = 1.0
    let mut tsml = false
    let mut ans = 1.0
    let mut term = 1.0
    let mut is_b = false
    let mut is_r = false
    let mut is_it = false
    let mut n = 0L
    let mut f_2n = 1.0
    let mut bound = 1.0
    if lamsml {
      // non centrality parameter too large
      u = 0.0
      lu = -lam
      l_lam = share_numdistrib__log(lam)
    } else {
      u = share_numdistrib__exp(-lam)
    }
    // evaluate the first term
    v = u
    x2 = 0.5 * x
    f2 = 0.5 * f
    f_x_2n = f - x
    tt = x2 - f2
    if f2 * dbl_epsilon > 0.125 && tt.abs() < dbl_epsilon.sqrt() * f2 {
      // very large f and x ~= f: probably needs other algorithm
      // evade cancellation error
      lt = (1.0 - tt) * (2.0 - tt / (f2 + 1.0)) -
        0.5 * share_numdistrib__log(2.0 * 3.141592653589793 * (f2 + 1.0))
    } else {
      // Usual case 2: careful not to overflow
      lt = f2 * share_numdistrib__log(x2) -
        x2 -
        share_numdistrib__lngamma(f2 + 1.0)
    }
    tsml = lt < dbl_min_exp
    if tsml && x > f + theta + 5.0 * (2.0 * (f + 2.0 * theta)).sqrt() {
      // x > E[X] + 5* sigma(X)
      ans = 1.0
    } else {
      if tsml {
        l_x = share_numdistrib__log(x)
        ans = 0.0
        term = 0.0
        tt = 0.0
      } else {
        tt = share_numdistrib__exp(lt)
        ans = v * tt
        term = ans
      }
      is_b = false
      is_r = false
      is_it = false
      n = 1L
      f_2n = f + 2.0
      f_x_2n = f_x_2n + 2.0
      while true {
        // f_2n = f + 2*n
        // f_x_2n = f - x + 2*n   > 0  <=> (f+2n)  >   x
        if f_x_2n > 0.0 {
          // find the error bound and check for convergence
          bound = tt * x / f_x_2n
          is_b = bound <= errmax
          is_r = term <= reltol * ans
          is_it = n.to_double() > itrmax
          // convergence only if BOTH absolute and relative error < 'bnd'
          if (is_b && is_r) || is_it {
            break
          }
        }
        // evaluate the next term of the
        // expansion and then the partial sum
        if lamsml {
          lu = lu + l_lam + -share_numdistrib__log_int(n)
          if lu >= dbl_min_exp {
            // no underflow anymore => change regime
            v = share_numdistrib__exp(lu) // the first non-0 'u'
            u = v
            lamsml = false
          }
        } else {
          u = u * (lam / n.to_double())
          v = v + u
        }
        if tsml {
          lt = lt + l_x + -share_numdistrib__log(f_2n)
          if lt >= dbl_min_exp {
            tt = share_numdistrib__exp(lt) // the first non-0 'tt'
            tsml = false
          }
        } else {
          tt = tt * (x / f_2n)
        }
        if !lamsml && !tsml {
          term = v * tt
          ans = ans + term
        }
        n += 1L
        f_2n = f_2n + 2.0
        f_x_2n = f_x_2n + 2.0
      }
      if is_it {
        d_print(
          list1(
            format(
              Nil,
              "Warning: cdf_noncentral_chi2 not converged in ~a iterations",
              [Flo(itrmax)],
            ),
          ),
        )
        |> ignore
      }
    }
    ignore(bound)
    Flo(ans)
  }
}

///|
/// Quantiles of the noncentral chi-square distribution.
/// Method: First calculate suboptimal Pearson's approximation, then
///     estimate an interval and apply bipartite method.
/// Comments: This is a translation of the C code in the R program.
/// Conditions: 0<p<1; f>0 (degrees of freedom) ; theta>0 (non centrality
/// param.)
fn qnchi2(p : Value, df : Value, lambda : Value) -> Value raise {
  let accu = 1.0e-13
  let racc = 8.881784197001254e-16 // (* 8 +flonum-epsilon+)
  let dbl_epsilon = 8.881784197001254e-16
  let dbl_min = 2.2250738585072014e-308
  let dbl_max = 1.7976931348623157e308
  let eps = 1.0e-11 // must be > accu
  let reps = 1.0e-10 // relative tolerance
  let mut ux = 1.0
  let mut lx = 1.0
  let mut nx = 1.0
  let mut pp = 1.0
  // This is Pearson's (1959) approximation,
  // which is usually good to 4 figs or so.
  {
    let b = num_div(
      num_mul(lambda, lambda),
      num_add(df, num_mul(Flo(3.0), lambda)),
    )
    let c = num_div(
      num_add(df, num_mul(Flo(3.0), lambda)),
      num_add(df, num_mul(Flo(2.0), lambda)),
    )
    let ff = num_div(num_add(df, num_mul(Flo(2.0), lambda)), num_mul(c, c))
    ux = to_double(
      num_add(
        b,
        num_mul(num_mul(c, Flo(2.0)), iigamma(p, num_mul(Flo(0.5), ff))),
      ),
    )
    if ux < 0.0 {
      ux = 1.0
    }
  }
  let pd = to_double(p)
  let cdf = fn(x : Double, e : Double, r : Double, it : Double) raise {
    to_double(cdfnchi2(Flo(x), df, lambda, Flo(e), Flo(r), Flo(it)))
  }
  // finding an upper and lower bound
  if pd > 1.0 - dbl_epsilon {
    // probability near 1
    q_d_inf
  } else {
    pp = {
      let a = 1.0 - dbl_epsilon
      let b = pd * (1.0 + eps)
      if a <= b {
        a
      } else {
        b
      }
    }
    while true {
      if ux >= dbl_max || cdf(ux, eps, reps, 10000.0) >= pp {
        break
      }
      ux = 2.0 * ux
    }
    pp = pd * (1.0 - eps)
    lx = if ux <= dbl_max { ux } else { dbl_max }
    while true {
      if lx <= dbl_min || cdf(lx, eps, reps, 10000.0) <= pp {
        break
      }
      lx = 0.5 * lx
    }
    // interval (lx,ux)  halving
    while true {
      nx = 0.5 * (lx + ux)
      if cdf(nx, accu, racc, 100000.0) > pd {
        ux = nx
      } else {
        lx = nx
      }
      if (ux - lx) / nx <= accu {
        break
      }
    }
    Flo(0.5 * (ux + lx))
  }
}

// Numerical routines for the noncentral t

///|
/// Cumulative probability of the noncentral Student's t distribution.
/// Reference:
///    Algorithm AS243: Appl.Statist., Lenth,R.V. (1989), vol. 38, no. 1
/// Conditions: df>0 (degrees of freedom)
fn cdfnt(x : Value, df : Value, delta : Value) -> Value raise {
  let x = share_numdistrib__fl(x)
  let df = share_numdistrib__fl(df)
  let delta = share_numdistrib__fl(delta)
  let alnrpi = 0.5723649429247001 // log(sqrt(%pi))
  let r2pi = 0.7978845608028654 // sqrt(2/%pi)
  let r2 = 1.4142135623730951 // sqrt(2)
  let errmax = 1.0e-12
  let itrmax = 1000L
  let mut negdel = false
  let mut it = 1L
  let mut tnc = 0.0
  let mut tt = x
  let mut del = delta
  if x < 0.0 {
    negdel = true
    tt = -tt
    del = -del
  }
  ignore(tt)
  // initialize twin series
  // Guenther, J. (1978). Statist. Computn. Simuln. vol.6, 199.
  let xx = x * x / (x * x + df)
  if xx > 0.0 {
    let lambda = del * del
    let mut p = 0.5 * share_numdistrib__exp(lambda * -0.5)
    let mut q = r2pi * p * del
    let mut s = 0.5 - p
    let mut a = 0.5
    let b = 0.5 * df
    let rxb = share_numdistrib__exptf(1.0 - xx, b)
    let albeta = alnrpi +
      share_numdistrib__lngamma(b) +
      -share_numdistrib__lngamma(a + b)
    let mut xodd = to_double(ibeta(Flo(xx), Flo(a), Flo(b)))
    let mut godd = 2.0 *
      rxb *
      share_numdistrib__exp(a * share_numdistrib__log(xx) - albeta)
    let mut xeven = 1.0 - rxb
    let mut geven = b * xx * rxb
    tnc = p * xodd + q * xeven
    // repeat until convergence or iteration limit
    while true {
      a = a + 1.0
      xodd = xodd - godd
      xeven = xeven - geven
      godd = godd * xx * (a + b + -1.0) / a
      geven = geven * xx * (a + b + -0.5) / (a + 0.5)
      p = p * lambda / (2.0 * it.to_double())
      q = q * lambda / (2.0 * it.to_double() + 1.0)
      s = s - p
      tnc = tnc + p * xodd + q * xeven
      it = it + 1L
      let errbd = 2.0 * s * (xodd - godd)
      if errbd < errmax || it > itrmax {
        break
      }
    }
  }
  if it > itrmax {
    d_print(list1(Str("Warning: cdf_noncentral_student_t didn't converge")))
    |> ignore
    d_funmake(q_cdf_noncentral_student_t, list([list1(q_mlist), q_x, q_df, q_delta]))
  } else {
    let e = ftake(q_p_erf, [Flo(-del / r2)])
    tnc = tnc +
      to_double(d_float(num_add(Flo(0.5), num_mul(Flo(0.5), e))))
    Flo(if negdel { 1.0 - tnc } else { tnc })
  }
}

///|
/// Quantiles for the noncentral Student's t distribution
/// by the inverse method. Translation of file qnt.c from R.
/// Conditions: 0<=p<=1, df>0 (degrees of freedom)
fn qnct(p : Value, df : Value, ncp : Value) -> Value raise {
  let p = share_numdistrib__fl(p)
  share_numdistrib__fl(df) |> ignore
  let ncpd = share_numdistrib__fl(ncp)
  let accu = 1.0e-13
  let eps = 1.0e-11
  let dbl_max = 1.7976931348623157e308 // DBL_MAX
  let dbl_epsilon = 1.1102230246251568e-16 // DBL_EPSILON
  let cdf = fn(x : Double) raise { to_double(cdfnt(Flo(x), df, ncp)) }
  // 1. finding an upper and lower bound
  let mut pp = {
    let a = 1.0 - dbl_epsilon
    let b = p * (1.0 + eps)
    if a <= b {
      a
    } else {
      b
    }
  }
  let mut ux = if 1.0 >= ncpd { 1.0 } else { ncpd }
  while true {
    if ux >= dbl_max || cdf(ux) >= pp {
      break
    }
    ux = ux * 2.0
  }
  pp = p * (1.0 - eps)
  let mut lx = if -1.0 <= -ncpd { -1.0 } else { -ncpd }
  while true {
    if lx <= -dbl_max || cdf(lx) <= pp {
      break
    }
    lx = lx * 2.0
  }
  // 2. interval (lx,ux)  halving
  while true {
    let nx = 0.5 * (lx + ux)
    if cdf(nx) > p {
      ux = nx
    } else {
      lx = nx
    }
    if ux - lx <= accu {
      break
    }
  }
  Flo(0.5 * (lx + ux))
}

// Normal random simulation

///|
///  Generates random normal variates, with mean=0 and var=1,
///  using the Box-Mueller method.
///  Reference:
///     Knuth, D.E. (1981) Seminumerical Algorithms.
///     The Art of Computer Programming. Addison-Wesley.
fn rndnormal_box() -> Value raise {
  let st = share_numdistrib__st
  if st.rnormal_iset == 0 {
    let mut v1 = 0.0
    let mut v2 = 0.0
    let mut rsq = 0.0
    while true {
      v1 = 2.0 * share_numdistrib__random() - 1.0
      v2 = 2.0 * share_numdistrib__random() - 1.0
      rsq = v1 * v1 + v2 * v2
      if rsq < 1.0 && rsq > 0.0 {
        break
      }
    }
    let fac = share_numdistrib__sqrt(
      -2.0 * share_numdistrib__log(rsq) * (1.0 / rsq),
    )
    st.rnormal_gset = v1 * fac
    st.rnormal_iset = 1
    Flo(v2 * fac)
  } else {
    st.rnormal_iset = 0
    Flo(st.rnormal_gset)
  }
}

///|
///  The sample size ss must be a non negative integer.
///  If ss=0, returns a number, otherwise a maxima list
///  of length ss
fn rndnormal(ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndnormal_box())
}

// Exponential random simulation

///|
///  Generates random exponential variates (m),
///  using the inverse method.
fn rndexp_inverse(m : Value) -> Value raise {
  let m = share_numdistrib__fl(m)
  while true {
    let u = share_numdistrib__random()
    if u != 0.0 {
      break
    }
  }
  Flo(-share_numdistrib__log(1.0 - share_numdistrib__random()) / m)
}

///|
fn rndexp(m : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndexp_inverse(m))
}

// Gamma random simulation

///|
///  Generates random gamma variates (a, b), combining
///  Ahrens-Dieter and Cheng-Feast methods.
///  References:
///    [1] a >= 1
///        Cheng, R.C.H. and Feast, G.M. (1979).
///        Some simple gamma variate generators.
///        Appl. Stat., 28, 3, 290-295.
///    [2] 0 < a < 1.
///        Ahrens, J.H. and Dieter, U. (1974).
///        Computer methods for sampling from gamma, beta,
///        poisson and binomial distributions.
///        Computing, 12, 223-246.
fn rndgamma_ahrens_cheng(aa : Value, bb : Value) -> Value raise {
  let aa = share_numdistrib__fl(aa)
  let bb = share_numdistrib__fl(bb)
  let a = aa - 1.0
  if aa <= 1.0 {
    // Ahrens-Dieter algorithm
    let e1 = 0.36787944117144233
    let r = aa * e1
    let mut x = 0.0
    let mut tt = 0.0
    let step = fn() raise {
      let q = share_numdistrib__random() * (r + 1.0)
      if q < 1.0 {
        x = share_numdistrib__exptf(q, 1.0 / aa)
        tt = share_numdistrib__exp(-x)
      } else {
        x = 1.0 - share_numdistrib__log(1.0 + (1.0 - q) / r)
        tt = share_numdistrib__exptf(x, a)
      }
    }
    step()
    while true {
      if share_numdistrib__random() < tt {
        break
      }
      step()
    }
    Flo(bb * x)
  } else {
    // Cheng-Feast algorithm GKM3
    let mut w = 0.0
    while true {
      let b = (aa - 1.0 / (6.0 * aa)) / a
      let c = 2.0 / a
      let d = 2.0 + c
      let mut u1 = 0.0
      let mut u2 = 0.0
      if aa < 2.5 {
        // GKM1
        u1 = share_numdistrib__random()
        u2 = share_numdistrib__random()
      } else {
        // GKM2
        let f = 1.0 / share_numdistrib__sqrt(aa)
        while true {
          u1 = share_numdistrib__random()
          u2 = u1 + (1.0 - 1.86 * share_numdistrib__random()) * f
          if 0.0 < u2 && u2 < 1.0 {
            break
          }
        }
      }
      w = b * (u1 / u2)
      if c * u2 + -d + w + 1.0 / w <= 0.0 ||
        c * share_numdistrib__log(u2) +
        -share_numdistrib__log(w) +
        w +
        -1.0 <
        0.0 {
        break
      }
    }
    Flo(bb * a * w)
  }
}

///|
fn rndgamma(a : Value, b : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndgamma_ahrens_cheng(a, b))
}

// Chi^2 random simulation

///|
fn rndchi2(n : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndgamma_ahrens_cheng(
    num_mul(n, Flo(0.5)),
    Flo(2.0),
  ))
}

// Noncentral Chi^2 random simulation

///|
/// Generates random noncentral chi^2 variates (df, lambda)
/// based on the fact that the noncentral chi^2 can be decomposed
/// as the sum of a central chisquare with df degrees of freedom plus a
/// noncentral chisquare with zero degrees of freedom (which is a Poisson
/// mixture of central chisquares with integer degrees of freedom),
/// see Formula (29.5b-c) in Johnson, Kotz, Balakrishnan (1995).
fn rndnchi2_chi2_poisson(df : Value, lambda : Value) -> Value raise {
  let dfd = share_numdistrib__fl(df)
  let lambda = share_numdistrib__fl(lambda)
  if lambda == 0.0 {
    rndgamma(Flo(0.5 * dfd), Flo(2.0), Fix(0L))
  } else {
    let mut r = to_double(rndpoisson(Flo(lambda / 2.0), Fix(0L)))
    if r > 0.0 {
      r = share_numdistrib__fl(rndchi2(Flo(2.0 * r), Fix(0L)))
    }
    r = r + share_numdistrib__fl(rndgamma(Flo(0.5 * dfd), Flo(2.0), Fix(0L)))
    Flo(r)
  }
}

///|
fn rndnchi2(df : Value, lambda : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndnchi2_chi2_poisson(df, lambda))
}

// Student's t random simulation

///|
///  Generates random Student's t variates (n), based
///  on the fact that Z/sqrt(Y/n) is a Student's t random
///  variable with n degrees of freedom, if Z~N(0,1)
///  and Y~chi^2(n).
fn rndstudent_ratio(n : Value) -> Value raise {
  let nd = share_numdistrib__fl(n)
  let z = to_double(rndnormal(Fix(0L)))
  let y = to_double(rndchi2(n, Fix(0L)))
  Flo(z / share_numdistrib__sqrt(y / nd))
}

///|
fn rndstudent(n : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndstudent_ratio(n))
}

// Noncentral Student's t random simulation

///|
///  Generates random Noncentral Student variates (n), based
///  on the fact that X/sqrt(Y/n) is a Noncentral Student random
///  variable with n degrees of freedom and noncentrality parameter k,
///  if X~N(k,1) and Y~chi^2(n).
fn rndncstudent_ratio(n : Value, k : Value) -> Value raise {
  let nd = share_numdistrib__fl(n)
  let kd = share_numdistrib__fl(k)
  let x = kd + to_double(rndnormal(Fix(0L)))
  let y = to_double(rndchi2(n, Fix(0L)))
  Flo(x / share_numdistrib__sqrt(y / nd))
}

///|
fn rndncstudent(n : Value, k : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndncstudent_ratio(n, k))
}

// Snedecor's F random simulation

///|
///  Generates random Snedecor's F variates (m,n), based
///  on the fact that (X/m)/(Y/n) is a Snedecor's F random
///  variable with m and n degrees of freedom, if X~chi^2(m)
///  and Y~chi^2(n).
fn rndf_ratio(m : Value, n : Value) -> Value raise {
  let md = share_numdistrib__fl(m)
  let nd = share_numdistrib__fl(n)
  let x = to_double(rndchi2(m, Fix(0L)))
  let y = to_double(rndchi2(n, Fix(0L)))
  Flo(nd * x / (md * y))
}

///|
fn rndf(m : Value, n : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndf_ratio(m, n))
}

// Beta random simulation

///|
///  Generates random beta variates (a, b)
///  Reference:
///    [1] Cheng, R.C.H. (1978). Generating Beta Variates
///        with Nonintegral Shape Parameters.
///        Communications of the ACM, 21:317-322
///  Comments:
///    [1] Algorithms BB and BC
///    [2] This is a translation from C of the
///        ranlib.c library. R statistical package uses this same
///        algorithm but in a more structured style.
///    [3] Some global variables are defined in order to
///        save time when many random variables are generated.
fn rndbeta_cheng0(aa : Value, bb : Value) -> Value raise {
  let aa = share_numdistrib__fl(aa)
  let bb = share_numdistrib__fl(bb)
  let st = share_numdistrib__st
  let expmax = 7.0
  let infnty = 1.0e304
  let mut qsame = false
  if st.rbeta_olda == aa && st.rbeta_oldb == bb {
    qsame = true
  } else {
    qsame = false
    st.rbeta_olda = aa
    st.rbeta_oldb = bb
  }
  let mut u1 = 0.0
  let mut u2 = 0.0
  let mut v = 0.0
  let mut w = 0.0
  let mut z = 0.0
  let mut tt = 0.0
  let mut r = 0.0
  let mut s = 0.0
  let mut y = 0.0
  let mut genbet : Value = Nil
  let set_w = fn() {
    if v <= expmax {
      w = st.rbeta_a * share_numdistrib__exp(v)
    } else {
      w = infnty
    }
  }
  let step_result = fn() {
    if w == infnty {
      genbet = q_rndbeta_encountered_infnty
    } else if aa != st.rbeta_a {
      genbet = Flo(st.rbeta_b / (st.rbeta_b + w))
    } else {
      genbet = Flo(w / (st.rbeta_b + w))
    }
  }
  // labels: 0 start, 40, 70, 100, 120, 130, 160, 170, 190, 200, 230
  let mut lbl = 0
  while true {
    match lbl {
      0 => {
        if (if aa <= bb { aa } else { bb }) <= 1.0 {
          lbl = 100
          continue
        }
        // Algorithm BB - Initialize
        if qsame {
          lbl = 40
          continue
        }
        st.rbeta_a = if aa <= bb { aa } else { bb }
        st.rbeta_b = if aa >= bb { aa } else { bb }
        st.rbeta_alpha = st.rbeta_a + st.rbeta_b
        st.rbeta_beta = share_numdistrib__sqrt(
          (st.rbeta_alpha - 2.0) /
          (2.0 * st.rbeta_a * st.rbeta_b - st.rbeta_alpha),
        )
        st.rbeta_gamma = st.rbeta_a + 1.0 / st.rbeta_beta
        lbl = 40
      }
      40 => {
        u1 = share_numdistrib__random()
        // Step 1
        u2 = share_numdistrib__random()
        v = st.rbeta_beta * share_numdistrib__log(u1 / (1.0 - u1))
        set_w()
        z = u2 * share_numdistrib__expti(u1, 2L)
        r = st.rbeta_gamma * v - 1.3862944
        s = st.rbeta_a + r + -w
        // Step 2
        if s + 2.609438 >= 5.0 * z {
          lbl = 70
          continue
        }
        // Step 3
        tt = share_numdistrib__log(z)
        if s > tt {
          lbl = 70
          continue
        }
        // Step 4
        if r +
          st.rbeta_alpha *
          share_numdistrib__log(st.rbeta_alpha / (st.rbeta_b + w)) <
          tt {
          lbl = 40
          continue
        }
        lbl = 70
      }
      70 => {
        // Step 5
        step_result()
        break
      }
      100 => {
        // Algorithm BC - Initialize
        if qsame {
          lbl = 120
          continue
        }
        st.rbeta_a = if aa >= bb { aa } else { bb }
        st.rbeta_b = if aa <= bb { aa } else { bb }
        st.rbeta_alpha = st.rbeta_a + st.rbeta_b
        st.rbeta_beta = 1.0 / st.rbeta_b
        st.rbeta_delta = 1.0 + st.rbeta_a + -st.rbeta_b
        st.rbeta_k1 = st.rbeta_delta *
          (1.38889e-2 + 4.16667e-2 * st.rbeta_b) /
          (st.rbeta_a * st.rbeta_beta - 0.777778)
        st.rbeta_k2 = 0.25 + (0.5 + 0.25 / st.rbeta_delta) * st.rbeta_b
        lbl = 120
      }
      120 => {
        u1 = share_numdistrib__random()
        // Step 1
        u2 = share_numdistrib__random()
        if u1 >= 0.5 {
          lbl = 130
          continue
        }
        // Step 2
        y = u1 * u2
        z = u1 * y
        if 0.25 * u2 + z + -y >= st.rbeta_k1 {
          lbl = 120
          continue
        }
        lbl = 170
      }
      130 => {
        // Step 3
        z = share_numdistrib__expti(u1, 2L) * u2
        if z > 0.25 {
          lbl = 160
          continue
        }
        v = st.rbeta_beta * share_numdistrib__log(u1 / (1.0 - u1))
        set_w()
        lbl = 200
      }
      160 => {
        if z >= st.rbeta_k2 {
          lbl = 120
          continue
        }
        lbl = 170
      }
      170 => {
        // Step 4 Step 5
        v = st.rbeta_beta * share_numdistrib__log(u1 / (1.0 - u1))
        set_w()
        // s190
        if st.rbeta_alpha *
          (share_numdistrib__log(st.rbeta_alpha / (st.rbeta_b + w)) + v) -
          1.3862944 <
          share_numdistrib__log(z) {
          lbl = 120
          continue
        }
        lbl = 200
      }
      200 => {
        // Step 6
        step_result()
        break
      }
      _ => break
    }
  }
  ignore(tt)
  genbet
}

///|
fn rndbeta_cheng(aa : Value, bb : Value) -> Value raise {
  let mut genbet = rndbeta_cheng0(aa, bb)
  while eq(genbet, q_rndbeta_encountered_infnty) {
    genbet = rndbeta_cheng0(aa, bb)
  }
  genbet
}

///|
fn rndbeta(a : Value, b : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndbeta_cheng(a, b))
}

// Binomial random simulation

///|
/// One term of the Stirling's formula correction of rndbinomial-kachit:
/// (/ (/ (+ 13860.0 (- (/ (+ 462.0 (- (/ (+ 132.0 (- (/ (+ 99.0
///    (- (/ 140.0 v2))) v2))) v2))) v2))) v) 166320.0)
fn share_numdistrib__stirling(v : Double, v2 : Double) -> Double {
  let t0 = 99.0 + -(140.0 / v2)
  let t1 = 132.0 + -(t0 / v2)
  let t2 = 462.0 + -(t1 / v2)
  let t3 = 13860.0 + -(t2 / v2)
  t3 / v / 166320.0
}

///|
///  Generates random binomial variates (n p)
///  Reference:
///    [1] Kachitvichyanukul, V., Schmeiser, B.W.
///        Binomial Random Variate Generation.
///        Communications of the ACM, 31, 2
///        (February, 1988) 216
///  Comments:
///    [1] Algorithm BTPE
///    [2] This is a translation from C of the
///        ranlib.c library. R statistical package uses this same
///        algorithm but in a more structured style.
///    [3] Some global variables are defined in order to
///        save time when many random variables are generated.
fn rndbinomial_kachit(n : Value, pp : Value) -> Value raise {
  let n = share_numdistrib__int(n)
  let pp = share_numdistrib__fl(pp)
  let st = share_numdistrib__st
  let nd = n.to_double()
  let mut u = 0.0
  let mut v = 0.0
  let mut x = 0.0
  let mut f = 0.0
  let mut ix = 0L
  let mut k = 0L
  // labels: 0 start, 10, 20, 30, 40, 50, 60, 70, 80, 100, 120, 130, 140,
  // 150, 160, 170
  let mut lbl = 0
  while true {
    match lbl {
      0 => {
        if pp != st.rbin_psave {
          lbl = 10
          continue
        }
        if n != st.rbin_nsave {
          lbl = 20
          continue
        }
        if st.rbin_xnp < 30.0 {
          lbl = 150
          continue
        }
        lbl = 30
      }
      10 => {
        // setup, perform only when parameters change
        st.rbin_psave = pp
        st.rbin_p = {
          let a = st.rbin_psave
          let b = 1.0 - st.rbin_psave
          if a <= b {
            a
          } else {
            b
          }
        }
        st.rbin_q = 1.0 - st.rbin_p
        lbl = 20
      }
      20 => {
        st.rbin_xnp = nd * st.rbin_p
        st.rbin_nsave = n
        if st.rbin_xnp < 30.0 {
          lbl = 140
          continue
        }
        st.rbin_ffm = st.rbin_xnp + st.rbin_p
        st.rbin_m = share_numdistrib__round(st.rbin_ffm)
        st.rbin_fm = st.rbin_m
        let fm = st.rbin_fm.to_double()
        st.rbin_xnpq = st.rbin_xnp * st.rbin_q
        st.rbin_p1 = 0.5 +
          share_numdistrib__round(
            2.195 * share_numdistrib__sqrt(st.rbin_xnpq) - 4.6 * st.rbin_q,
          ).to_double()
        st.rbin_xm = 0.5 + fm
        st.rbin_xl = st.rbin_xm - st.rbin_p1
        st.rbin_xr = st.rbin_xm + st.rbin_p1
        st.rbin_c = 0.134 + 20.5 / (15.3 + fm)
        st.rbin_al = (st.rbin_ffm - st.rbin_xl) /
          (st.rbin_ffm - st.rbin_xl * st.rbin_p)
        st.rbin_xll = st.rbin_al * (1.0 + 0.5 * st.rbin_al)
        st.rbin_al = (st.rbin_xr - st.rbin_ffm) / (st.rbin_xr * st.rbin_q)
        st.rbin_xlr = st.rbin_al * (1.0 + 0.5 * st.rbin_al)
        st.rbin_p2 = st.rbin_p1 * (1.0 + st.rbin_c + st.rbin_c)
        st.rbin_p3 = st.rbin_p2 + st.rbin_c / st.rbin_xll
        st.rbin_p4 = st.rbin_p3 + st.rbin_c / st.rbin_xlr
        lbl = 30
      }
      30 => {
        // generate variate
        u = st.rbin_p4 * share_numdistrib__random()
        v = share_numdistrib__random()
        // triangular region
        if u > st.rbin_p1 {
          lbl = 40
          continue
        }
        ix = share_numdistrib__round(st.rbin_xm + -(st.rbin_p1 * v) + u)
        lbl = 170
      }
      40 => {
        // parallelogram region
        if u > st.rbin_p2 {
          lbl = 50
          continue
        }
        x = st.rbin_xl + (u - st.rbin_p1) / st.rbin_c
        v = v * st.rbin_c + 1.0 + -((st.rbin_xm - x).abs() / st.rbin_p1)
        if v > 1.0 || v <= 0.0 {
          lbl = 30
          continue
        }
        ix = share_numdistrib__round(x)
        lbl = 70
      }
      50 => {
        // left tail
        if u > st.rbin_p3 {
          lbl = 60
          continue
        }
        ix = share_numdistrib__round(
          st.rbin_xl + share_numdistrib__log(v) / st.rbin_xll,
        )
        if ix < 0L {
          lbl = 30
          continue
        }
        v = v * (u - st.rbin_p2) * st.rbin_xll
        lbl = 70
      }
      60 => {
        // right tail
        ix = share_numdistrib__round(
          st.rbin_xr - share_numdistrib__log(v) / st.rbin_xlr,
        )
        if ix > n {
          lbl = 30
          continue
        }
        v = v * (u - st.rbin_p3) * st.rbin_xlr
        lbl = 70
      }
      70 => {
        // determine appropriate way to perform accept/reject test
        k = (ix - st.rbin_m).abs()
        if k > 20L && k.to_double() < st.rbin_xnpq / 2.0 - 1.0 {
          lbl = 130
          continue
        }
        // explicit evaluation
        f = 1.0
        st.rbin_r = st.rbin_p / st.rbin_q
        st.rbin_g = st.rbin_r * (nd + 1.0)
        let t1 = st.rbin_m - ix
        lbl = if t1 < 0L { 80 } else if t1 == 0L { 120 } else { 100 }
      }
      80 => {
        let mp = st.rbin_m + 1L
        for i = mp; i <= ix; i = i + 1L {
          f = f * (st.rbin_g / i.to_double() - st.rbin_r)
        }
        lbl = 120
      }
      100 => {
        let ix1 = ix + 1L
        for i = ix1; i <= st.rbin_m; i = i + 1L {
          f = f / (st.rbin_g / i.to_double() - st.rbin_r)
        }
        lbl = 120
      }
      120 => {
        if v <= f {
          lbl = 170
          continue
        }
        lbl = 30
      }
      130 => {
        // squeezing using upper and lower bounds on alog(f(x))
        let kd = k.to_double()
        let amaxp = kd /
          st.rbin_xnpq *
          ((kd * (kd / 3.0 + 0.625) + 0.1666666666666) / st.rbin_xnpq + 0.5)
        let ynorm = -((k * k).to_double() / (2.0 * st.rbin_xnpq))
        let alv = share_numdistrib__log(v)
        if alv < ynorm - amaxp {
          lbl = 170
          continue
        }
        if alv > ynorm + amaxp {
          lbl = 30
          continue
        }
        // Stirling's formula to machine accuracy for
        // the final acceptance / rejection test
        let fm = st.rbin_fm.to_double()
        let x1 = ix.to_double() + 1.0
        let f1 = fm + 1.0
        let z = nd + 1.0 + -fm
        let w = nd + 1.0 + -ix.to_double()
        let z2 = z * z
        let x2 = x1 * x1
        let f2 = f1 * f1
        let w2 = w * w
        let bnd = st.rbin_xm * share_numdistrib__log(f1 / x1) +
          ((n + -st.rbin_m).to_double() + 0.5) * share_numdistrib__log(z / w) +
          (ix + -st.rbin_m).to_double() *
          share_numdistrib__log(w * st.rbin_p / (x1 * st.rbin_q)) +
          share_numdistrib__stirling(f1, f2) +
          share_numdistrib__stirling(z, z2) +
          share_numdistrib__stirling(x1, x2) +
          share_numdistrib__stirling(w, w2)
        if alv <= bnd {
          lbl = 170
          continue
        }
        lbl = 30
      }
      140 => {
        // inverse cdf logic for mean less than 30
        st.rbin_qn = share_numdistrib__expti(st.rbin_q, n)
        st.rbin_r = st.rbin_p / st.rbin_q
        st.rbin_g = st.rbin_r * (nd + 1.0)
        lbl = 150
      }
      150 => {
        ix = 0L
        f = st.rbin_qn
        u = share_numdistrib__random()
        lbl = 160
      }
      160 => {
        if u < f {
          lbl = 170
          continue
        }
        if ix > 110L {
          lbl = 150
          continue
        }
        u = u - f
        ix = ix + 1L
        f = f * (st.rbin_g / ix.to_double() - st.rbin_r)
      }
      _ => break
    }
  }
  if st.rbin_psave > 0.5 {
    Fix(n - ix)
  } else {
    Fix(ix)
  }
}

///|
fn rndbinomial(n : Value, p : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndbinomial_kachit(n, p))
}

// Poisson random simulation

///|
let share_numdistrib__fact : Array[Double] = [
  1.0, 1.0, 2.0, 6.0, 24.0, 120.0, 720.0, 5040.0, 40320.0, 362880.0,
]

///|
///  Generates random Poisson variates (m)
///  Reference:
///    [1] Ahrens, J.H. and Dieter, U.
///        Computer Generation of Poisson Deviates
///        From Modified Normal Distributions.
///        ACM Trans. Math. Software, 8, 2
///        (June 1982),163-179
///  Comments:
///    [1] Slightly modified version of the program in the
///        above article
///    [2] This is a translation from C of the
///        ranlib.c library. R statistical package uses this same
///        algorithm but in a more structured style.
///    [3] Some global variables are defined in order to
///        save time when many random variables are generated.
fn rndpoisson_ahrens(mu : Value) -> Value raise {
  let mu = share_numdistrib__fl(mu)
  let st = share_numdistrib__st
  // This algorithm doesn't handle MU = 0 correctly; *RPOS-S* and friends
  // aren't initialized. So just handle the special case here and bail out.
  if mu == 0.0 {
    return Fix(0L)
  }
  let a0 = -0.5
  let a1 = 0.3333333
  let a2 = -0.2500068
  let a3 = 0.2000118
  let a4 = -0.1661269
  let a5 = 0.1421878
  let a6 = -0.1384794
  let a7 = 0.125006
  let fact = share_numdistrib__fact
  let mut ignpoi = 0L
  let mut kflag = 0
  let mut del = 0.0
  let mut difmuk = 0.0
  let mut e = 0.0
  let mut fk = 0.0
  let mut fx = 0.0
  let mut fy = 0.0
  let mut g = 0.0
  let mut px = 0.0
  let mut py = 0.0
  let mut tt = 0.0
  let mut u = 0.0
  let mut v = 0.0
  let mut x = 0.0
  let mut xx = 0.0
  // labels: 0 start, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100, 110, 120,
  // 130, 150, 200
  let mut lbl = 0
  while true {
    match lbl {
      0 => {
        if mu == st.rpos_muprev {
          lbl = 10
          continue
        }
        if mu < 10.0 {
          lbl = 120
          continue
        }
        // Case A. (Recalculation of, *rpos-s*, *rpos-d*, *rpos-l* if mu
        // has changed)
        st.rpos_muprev = mu
        st.rpos_s = share_numdistrib__sqrt(mu)
        st.rpos_d = 6.0 * mu * mu
        st.rpos_l = share_numdistrib__floor(mu - 1.1484)
        lbl = 10
      }
      10 => {
        // Step n. Normal sample
        g = mu + st.rpos_s * to_double(rndnormal(Fix(0L)))
        if g < 0.0 {
          lbl = 20
          continue
        }
        ignpoi = share_numdistrib__floor(g)
        // Step I. Immediate acceptance if ignpoi is large enough
        if ignpoi >= st.rpos_l {
          break
        }
        // Step S. Squeez acceptance
        fk = ignpoi.to_double()
        difmuk = mu - fk
        u = share_numdistrib__random()
        if st.rpos_d * u >= difmuk * difmuk * difmuk {
          break
        }
        lbl = 20
      }
      20 => {
        // Step P. Preparations for steps Q and H.
        // (Recalculations of parameters if necessary)
        // .3989423...=(2*%pi)^(-.5)  .416667...E-1=1./24.  .1428571...=1./7.
        // The quantities *rpos-b1*, *rpos-b2*, *rpos-c3*, *rpos-c2*,
        // *rpos-c1*, *rpos-c0* are for thr Hermite approximations to the
        // discrete normal probabilities fk.
        // c=0.1069/mu guarantees majorization by the 'hat'-function.
        if mu == st.rpos_muold {
          lbl = 30
          continue
        }
        st.rpos_muold = mu
        st.rpos_omega = 0.39894228040143 / st.rpos_s
        st.rpos_b1 = 0.41666666666667e-1 / mu
        st.rpos_b2 = 0.3 * st.rpos_b1 * st.rpos_b1
        st.rpos_c3 = 0.14285714285714 * st.rpos_b1 * st.rpos_b2
        st.rpos_c2 = st.rpos_b2 - 15.0 * st.rpos_c3
        st.rpos_c1 = st.rpos_b1 + -6.0 * st.rpos_b2 + 45.0 * st.rpos_c3
        st.rpos_c0 = 1.0 + -st.rpos_b1 + 3.0 * st.rpos_b2 + -15.0 * st.rpos_c3
        st.rpos_c = 0.1069 / mu
        lbl = 30
      }
      30 => {
        if g < 0.0 {
          lbl = 50
          continue
        }
        // subroutine F is called
        kflag = 0
        lbl = 70
      }
      40 => {
        // Step Q. Quotient acceptance (rare case)
        if fy - u * fy <= py * share_numdistrib__exp(px - fx) {
          break
        }
        lbl = 50
      }
      50 => {
        // Step E. Exponential sample - rndexp is called for
        // standard exponential variate e and sample tt from the Laplace
        // 'hat' (if tt <= -.6744 then pk < fk for all mu >= 10.)
        e = to_double(rndexp(Flo(1.0), Fix(0L)))
        u = share_numdistrib__random()
        u = u + (u - 1.0)
        tt = 1.8 +
          (if (u > 0.0 && e < 0.0) || (u < 0.0 && e > 0.0) { -e } else { e })
        if tt <= -0.6744 {
          lbl = 50
          continue
        }
        ignpoi = share_numdistrib__floor(mu + st.rpos_s * tt)
        fk = ignpoi.to_double()
        difmuk = mu - fk
        // subroutine F is called
        kflag = 1
        lbl = 70
      }
      60 => {
        // Step F. Hat acceptance (E is repeated on rejection)
        if st.rpos_c * u.abs() >
          py * share_numdistrib__exp(px + e) -
          fy * share_numdistrib__exp(fx + e) {
          lbl = 50
          continue
        }
        break
      }
      70 => {
        // Step F. Subroutine F. Calculation of px, py, fx, fy.
        // Case ignpoi < 10  uses factorials from table fact
        if ignpoi >= 10L {
          lbl = 80
          continue
        }
        px = -mu
        py = share_numdistrib__expti(mu, ignpoi) /
          to_double(aref1(vector(fact.map(x => Value::Flo(x))), ignpoi.to_int()))
        lbl = 110
      }
      80 => {
        // Case ignpoi >= 10 uses polynomial approximation
        // a0-a7 for accuracy when advisable
        // .8333333E-1=1./12.  .3989423=(2*%pi)^(-.5)
        del = 8.333333333333333e-2 / fk
        del = del - 4.8 * del * del * del
        v = difmuk / fk
        if v.abs() <= 0.25 {
          lbl = 90
          continue
        }
        px = fk * share_numdistrib__log(1.0 + v) + -difmuk + -del
        lbl = 100
      }
      90 => {
        px = fk *
          v *
          v *
          (((((((a7 * v + a6) * v + a5) * v + a4) * v + a3) * v + a2) * v + a1) *
          v +
          a0) +
          -del
        lbl = 100
      }
      100 => {
        py = 0.39894228040143 / share_numdistrib__sqrt(fk)
        lbl = 110
      }
      110 => {
        x = (0.5 - difmuk) / st.rpos_s
        xx = x * x
        fx = -0.5 * xx
        fy = st.rpos_omega *
          (((st.rpos_c3 * xx + st.rpos_c2) * xx + st.rpos_c1) * xx +
          st.rpos_c0)
        lbl = if kflag <= 0 { 40 } else { 60 }
      }
      120 => {
        // Case B. Start new table and calculate *rpos-p0* if necessary
        st.rpos_muprev = 0.0
        if mu == st.rpos_muold {
          lbl = 130
          continue
        }
        st.rpos_muold = mu
        st.rpos_m = {
          let fm = share_numdistrib__floor(mu)
          if 1L >= fm {
            1L
          } else {
            fm
          }
        }
        st.rpos_l = 0L
        st.rpos_p = share_numdistrib__exp(-mu)
        st.rpos_p0 = st.rpos_p
        st.rpos_q = st.rpos_p
        lbl = 130
      }
      130 => {
        // Step U. Uniform sample for inversion method
        u = share_numdistrib__random()
        ignpoi = 0L
        if u <= st.rpos_p0 {
          break
        }
        // Step T.
        if st.rpos_l == 0L {
          lbl = 150
          continue
        }
        let mut j = 1L
        if u > 0.458 {
          j = if st.rpos_l <= st.rpos_m { st.rpos_l } else { st.rpos_m }
        }
        let mut found = false
        for k = j; k <= st.rpos_l; k = k + 1L {
          if u <= st.rpos_pp[(k - 1L).to_int()] {
            ignpoi = k
            found = true
            break
          }
        }
        if found {
          break
        }
        if st.rpos_l == 35L {
          lbl = 130
          continue
        }
        lbl = 150
      }
      150 => {
        // Step C. Creation of new Poisson probabilities p
        // and their cumulatives *rpos-q*=*rpos-pp*(k)
        st.rpos_l = st.rpos_l + 1L
        let mut found = false
        for k = st.rpos_l; k <= 35L; k = k + 1L {
          st.rpos_p = st.rpos_p * mu / k.to_double()
          st.rpos_q = st.rpos_q + st.rpos_p
          st.rpos_pp[(k - 1L).to_int()] = st.rpos_q
          if u <= st.rpos_q {
            st.rpos_l = k
            ignpoi = k
            found = true
            break
          }
        }
        if found {
          break
        }
        st.rpos_l = 35L
        lbl = 130
      }
      _ => break
    }
  }
  Fix(ignpoi)
}

///|
///  The sample size ss must be a non negative integer.
///  If ss=0, returns a number, otherwise a maxima list
///  of length ss
fn rndpoisson(m : Value, ss : Value) -> Value raise {
  share_numdistrib__fl(m) |> ignore
  share_numdistrib__int(ss) |> ignore
  share_numdistrib__sample(ss, () => rndpoisson_ahrens(m))
}

// Geometric random simulation

///|
///  Generates random geometric variates (p)
///  by simulation of Bernoulli trials.
fn rndgeo_trials(p : Value) -> Value raise {
  let p = share_numdistrib__fl(p)
  let mut sum = 0L
  while true {
    if share_numdistrib__random() <= p {
      break
    }
    sum = sum + 1L
  }
  Fix(sum)
}

///|
fn rndgeo(p : Value, ss : Value) -> Value raise {
  share_numdistrib__fl(p) |> ignore
  share_numdistrib__int(ss) |> ignore
  share_numdistrib__sample(ss, () => rndgeo_trials(p))
}

// Hypergeometric random simulation

///|
let share_numdistrib__al : Array[Double] = [
  0.0,
  0.0, // ln(0!)=ln(1)
   0.0, // ln(1!)=ln(1)
   0.6931471805599453, // ln(2)
   1.791759469228055, // ln(6)
   3.1780538303479458, // ln(24)
   4.787491742782046, 6.579251212010101, 8.525161361065415,
]

///|
///  Computes the logarithm of the factorial log(n!)
///  This function is called from rndhypergeo-kachit
fn afc(i : Value) -> Value raise {
  let i = share_numdistrib__int(i)
  let di = i.to_double()
  if i <= 7L {
    aref1(vector(share_numdistrib__al.map(x => Value::Flo(x))), (i + 1L).to_int())
  } else {
    Flo(
      (di + 0.5) * share_numdistrib__log(di) +
      -di +
      0.8333333333333334 / di +
      -0.002777777777777778 / di / di / di +
      0.9189385332046728,
    )
  }
}

///|
fn share_numdistrib__afc(i : Value) -> Double raise {
  to_double(afc(i))
}

///|
///  Generates random hypergeometric variates (n1, n2, n),
///  Reference:
///    [1] Kachitvichyanukul, V., Schmeiser, B.W. (1985)
///        Computer generation of hypergeometric random variates.
///        Journal of Statistical Computation and Simulation 22, 127-145.
///  Comments:
///    [1] This is a translation from C of the
///        rhyper.c file in the R statistical package.
///    [2] Some global variables are defined in order to
///        save time when many random variables are generated.
fn rndhypergeo_kachit(nn1 : Value, nn2 : Value, kk : Value) -> Value raise {
  let nn1 = share_numdistrib__int(nn1)
  let nn2 = share_numdistrib__int(nn2)
  let kk = share_numdistrib__int(kk)
  let st = share_numdistrib__st
  let con = 57.56462733
  let deltal = 0.0078
  let deltau = 0.0034
  let scale = 1.0e25
  let afcd = share_numdistrib__afc
  let mut ix = 0L
  // if new parameter values, initialize
  let mut reject = true
  let mut setup1 = false
  let mut setup2 = false
  if nn1 != st.rhyp_n1s || nn2 != st.rhyp_n2s {
    setup1 = true
    setup2 = true
  } else if kk != st.rhyp_ks {
    setup1 = false
    setup2 = true
  } else {
    setup1 = false
    setup2 = false
  }
  if setup1 {
    st.rhyp_n1s = nn1
    st.rhyp_n2s = nn2
    st.rhyp_tn = nn1 + nn2
    if nn1 <= nn2 {
      st.rhyp_n1 = nn1
      st.rhyp_n2 = nn2
    } else {
      st.rhyp_n1 = nn2
      st.rhyp_n2 = nn1
    }
  }
  if setup2 {
    st.rhyp_ks = kk
    if kk + kk >= st.rhyp_tn {
      st.rhyp_k = st.rhyp_tn - kk
    } else {
      st.rhyp_k = kk
    }
  }
  if setup1 || setup2 {
    st.rhyp_m = (st.rhyp_k.to_double() + 1.0) *
      (st.rhyp_n1.to_double() + 1.0) /
      (st.rhyp_tn.to_double() + 2.0)
    st.rhyp_minjx = {
      let v = st.rhyp_k - st.rhyp_n2
      if 0L >= v {
        0L
      } else {
        v
      }
    }
    st.rhyp_maxjx = if st.rhyp_n1 <= st.rhyp_k {
      st.rhyp_n1
    } else {
      st.rhyp_k
    }
  }
  let n1 = st.rhyp_n1
  let n2 = st.rhyp_n2
  let k = st.rhyp_k
  // generate random variate --- Three basic cases
  if st.rhyp_minjx == st.rhyp_maxjx {
    // I: degenerate distribution
    ix = st.rhyp_maxjx
  } else if st.rhyp_m - st.rhyp_minjx.to_double() < 10.0 {
    // II: inverse transformation
    if setup1 || setup2 {
      if k < n2 {
        st.rhyp_w = share_numdistrib__exp(
          con +
          afcd(Fix(n2)) +
          afcd(Fix(n1 + n2 + -k)) +
          -afcd(Fix(n2 - k)) +
          -afcd(Fix(n1 + n2)),
        )
      } else {
        st.rhyp_w = share_numdistrib__exp(
          con +
          afcd(Fix(n1)) +
          afcd(Fix(k)) +
          -afcd(Fix(k - n2)) +
          -afcd(Fix(n1 + n2)),
        )
      }
    }
    let mut p = 0.0
    let mut u = 0.0
    let mut lbl = 10
    while true {
      if lbl == 10 {
        p = st.rhyp_w
        ix = st.rhyp_minjx
        u = share_numdistrib__random() * scale
      }
      // l20
      if u > p {
        u = u - p
        p = p * (n1 - ix).to_double() * (k - ix).to_double()
        ix = ix + 1L
        p = p / ix.to_double() / (n2 + -k + ix).to_double()
        lbl = if ix > st.rhyp_maxjx { 10 } else { 20 }
      } else {
        break
      }
    }
  } else {
    // III : h2pe
    if setup1 || setup2 {
      let tn = st.rhyp_tn
      // (sqrt <rational>): a single-float in CL
      st.rhyp_s = Float::from_double(to_double(
        num_div(
          Fix((tn - k) * k * n1 * n2),
          Fix((tn - 1L) * tn * tn),
        )
        |> lsqrt,
      )).to_double()
      st.rhyp_d = share_numdistrib__round(1.5 * st.rhyp_s).to_double() + 0.5
      st.rhyp_xl = st.rhyp_m + -st.rhyp_d + 0.5
      st.rhyp_xr = st.rhyp_m + st.rhyp_d + 0.5
      // (afc *rhyp-m*) etc.: *RHYP-M* is a float, so these signal a type
      // error, as in SBCL.
      let m : Value = Flo(st.rhyp_m)
      st.rhyp_a = afcd(m) +
        afcd(num_sub(Fix(n1), m)) +
        afcd(num_sub(Fix(k), m)) +
        afcd(num_add(num_add(Fix(n2), Fix(-k)), m))
      let xl = st.rhyp_xl
      let xr = st.rhyp_xr
      let rnd = fn(x : Double) -> Value { Fix(share_numdistrib__round(x)) }
      st.rhyp_kl = share_numdistrib__exp(
        st.rhyp_a -
        afcd(rnd(xl)) -
        afcd(rnd(n1.to_double() - xl)) -
        afcd(rnd(k.to_double() - xl)) -
        afcd(rnd((n2 + -k).to_double() + xl)),
      )
      st.rhyp_kr = share_numdistrib__exp(
        st.rhyp_a -
        afcd(rnd(xr - 1.0)) -
        afcd(rnd(n1.to_double() + -xr + 1.0)) -
        afcd(rnd(k.to_double() + -xr + 1.0)) -
        afcd(rnd((n2 + -k).to_double() + xr + -1.0)),
      )
      st.rhyp_lamdl = -share_numdistrib__log(
        xl *
        ((n2 + -k).to_double() + xl) /
        (n1.to_double() + -xl + 1.0) /
        (k.to_double() + -xl + 1.0),
      )
      st.rhyp_lamdr = -share_numdistrib__log(
        (n1.to_double() + -xr + 1.0) *
        (k.to_double() + -xr + 1.0) /
        xr /
        ((n2 + -k).to_double() + xr),
      )
      st.rhyp_p1 = st.rhyp_d + st.rhyp_d
      st.rhyp_p2 = st.rhyp_p1 + st.rhyp_kl / st.rhyp_lamdl
      st.rhyp_p3 = st.rhyp_p2 + st.rhyp_kr / st.rhyp_lamdr
      st.rhyp_h2pe_bound = true
    }
    let m = st.rhyp_m
    while true {
      // l30
      let u0 = share_numdistrib__random()
      if !st.rhyp_h2pe_bound {
        raise LispError::SimpleError("The variable *RHYP-P3* is unbound.")
      }
      let u = u0 * st.rhyp_p3
      let mut v = share_numdistrib__random()
      if u < st.rhyp_p1 {
        // rectangular region
        ix = share_numdistrib__round(st.rhyp_xl + u)
      } else if u <= st.rhyp_p2 {
        // left tail
        ix = share_numdistrib__round(
          st.rhyp_xl + share_numdistrib__log(v) / st.rhyp_lamdl,
        )
        if ix < st.rhyp_minjx {
          continue
        }
        v = v * (u - st.rhyp_p1) * st.rhyp_lamdl
      } else {
        // right tail
        ix = share_numdistrib__round(
          st.rhyp_xr - share_numdistrib__log(v) / st.rhyp_lamdr,
        )
        if ix > st.rhyp_maxjx {
          continue
        }
        v = v * (u - st.rhyp_p2) * st.rhyp_lamdr
      }
      // acceptance/rejection test
      if m < 100.0 || ix <= 50L {
        // explicit evaluation
        let mut f : Value = Flo(1.0)
        let mv : Value = Flo(m)
        if num_lt(mv, Fix(ix)) {
          let mut i = num_add(mv, Fix(1L))
          while !num_gt(i, Fix(ix)) {
            f = num_div(
              num_div(
                num_mul(
                  num_mul(f, num_add(num_add(Fix(n1), num_neg(i)), Fix(1L))),
                  num_add(num_add(Fix(k), num_neg(i)), Fix(1L)),
                ),
                num_add(Fix(n2 + -k), i),
              ),
              i,
            )
            i = num_add(i, Fix(1L))
          }
        } else if num_gt(mv, Fix(ix)) {
          let mut i : Value = Fix(ix + 1L)
          while !num_gt(i, mv) {
            f = num_div(
              num_div(
                num_mul(num_mul(f, i), num_add(Fix(n2 + -k), i)),
                num_sub(Fix(n1), i),
              ),
              num_sub(Fix(k), i),
            )
            i = num_add(i, Fix(1L))
          }
        }
        if v <= to_double(f) {
          reject = false
        }
      } else {
        // squeeze using upper and lower bounds
        let y = ix.to_double()
        let y1 = y + 1.0
        let ym = y - m
        let yn = (n1 + -k).to_double() + 1.0
        let yk = (k.to_double() + -y) + 1.0
        let nk = (n2 + -k).to_double() + y1
        let r = -ym / y1
        st.rhyp_s = ym / yn
        let tt = ym / yk
        let e = -ym / nk
        let g = yn * yk / (y1 * nk) - 1.0
        let mut dg = 1.0
        if g < 1.0 {
          dg = 1.0 + g
        }
        let s = st.rhyp_s
        let gu = g * (1.0 + g * (-0.5 + g / 3.0))
        let gl = gu - g * g * g * g * 0.25 / dg
        let xm = m + 0.5
        let xn = n1.to_double() + -m + 0.5
        let xk = k.to_double() + -m + 0.5
        let nm = (n2 + -k).to_double() + xm
        let ub = y * gu +
          -m * gl +
          deltau +
          xm * r * (1.0 + r * (-0.5 + r / 3.0)) +
          xn * s * (1.0 + s * (-0.5 + s / 3.0)) +
          xk * tt * (1.0 + tt * (-0.5 + tt / 3.0)) +
          nm * e * (1.0 + e * (-0.5 + e / 3.0))
        // test against upper bound
        let alv = share_numdistrib__log(v)
        if alv > ub {
          reject = true
        } else {
          let mut dr = r * r * r * r * xm
          if r < 0.0 {
            dr = dr / (1.0 + r)
          }
          let mut ds = s * s * s * s * xn
          if s < 0.0 {
            ds = ds / (1.0 + s)
          }
          let mut dt = tt * tt * tt * tt * xk
          if tt < 0.0 {
            dt = dt / (1.0 + tt)
          }
          let mut de = e * e * e * e * nm
          if e < 0.0 {
            de = de / (1.0 + e)
          }
          if alv <
            ub - 0.25 * (dr + ds + dt + de) - (y + m) * (gl - gu) - deltal {
            reject = false
          } else if alv <=
            st.rhyp_a -
            afcd(Fix(ix)) -
            afcd(Fix(n1 - ix)) -
            afcd(Fix(k - ix)) -
            afcd(Fix(n2 + -k + ix)) {
            reject = false
          } else {
            reject = true
          }
        }
      }
      if !reject {
        break
      }
    }
  }
  // return appropriate variate
  if kk + kk >= st.rhyp_tn {
    if nn1 > nn2 {
      Fix(kk + -nn2 + ix)
    } else {
      Fix(nn1 - ix)
    }
  } else if nn1 > nn2 {
    Fix(kk - ix)
  } else {
    Fix(ix)
  }
}

///|
fn rndhypergeo(n1 : Value, n2 : Value, n : Value, ss : Value) -> Value raise {
  share_numdistrib__int(n1) |> ignore
  share_numdistrib__int(n2) |> ignore
  share_numdistrib__int(n) |> ignore
  share_numdistrib__int(ss) |> ignore
  share_numdistrib__sample(ss, () => rndhypergeo_kachit(n1, n2, n))
}

// Negative binomial random simulation

///|
///  Generates random negative binomial variates (n p)
///  Reference:
///    [1] Devroye, L. (1986)
///        Non-Uniform Random Variate Generation.
///        Springer Verlag, p. 480
///  Comments:
///    [1] This is a translation from C of the
///        rnbinom.c file in the R statistical package.
fn rndnegbinom_devroye(n : Value, p : Value) -> Value raise {
  let p = share_numdistrib__fl(p)
  rndpoisson(rndgamma(n, Flo((1.0 - p) / p), Fix(0L)), Fix(0L))
}

///|
fn rndnegbinom(n : Value, p : Value, ss : Value) -> Value raise {
  share_numdistrib__sample(ss, () => rndnegbinom_devroye(n, p))
}

///|
fn init_share_numdistrib() -> Unit raise {

}
